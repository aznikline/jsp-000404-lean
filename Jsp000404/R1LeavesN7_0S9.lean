import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S7
import Jsp000404.R1LeavesN7_0S8

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x14 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4131 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h4716 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h4717 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h4718 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h4719 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h4721c : ((m.d 1 3) < (m.d 1 5) ∧ 2 * m.lam ≤ (m.d 1 5) - (m.d 1 3) ∧ (m.d 1 5) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 1 5) ≤ z)))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  have p4721_0 := h4721c.1
  have p4721_1 := h4721c.2.1
  have p4721_2 := h4721c.2.2.1
  have p4721_3 := h4721c.2.2.2
  rcases p4721_3 (m.d 0 1) (by simp) with h5231 | h5231
  · rcases p4721_3 (m.d 1 2) (by simp) with h5232 | h5232
    · linarith only [h10, h5232, hlam]
    · rcases p4721_3 (m.d 1 3) (by simp) with h5234 | h5234
      · rcases p4721_3 (m.d 1 4) (by simp) with h5235 | h5235
        · linarith only [h4129, h5235, hlam]
        · rcases p4721_3 (m.d 1 5) (by simp) with h5237 | h5237
          · linarith only [h4130, h5237, hlam]
          · rcases h1emax with h5239 | h5239 | h5239 | h5239 | h5239
            · linarith only [h0, h4, h4716, h4718, h5239, hc45, hlam, hphi, ht01, ht0b, ht5b]
            · rcases h2bigk with h5241c | h5241c | h5241c | h5241c | h5241c | h5241c | h5241c | h5241c | h5241c | h5241c | h5241c | h5241c | h5241c | h5241c | h5241c | h5241c | h5241c | h5241c | h5241c | h5241c | h5241c | h5241c | h5241c | h5241c | h5241c
              · have p5241_0 := h5241c.1
                have p5241_1 := h5241c.2.1
                have p5241_2 := h5241c.2.2.1
                have p5241_3 := h5241c.2.2.2
                linarith only [hlam, p5241_0]
              · have p5241_0 := h5241c.1
                have p5241_1 := h5241c.2.1
                have p5241_2 := h5241c.2.2.1
                have p5241_3 := h5241c.2.2.2
                linarith only [h10, h3576, h4, h4131, hlam, p4721_1, p5241_2]
              · have p5241_0 := h5241c.1
                have p5241_1 := h5241c.2.1
                have p5241_2 := h5241c.2.2.1
                have p5241_3 := h5241c.2.2.2
                linarith only [h0, h10, h3576, h4131, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4721_1, p5241_1]
              · have p5241_0 := h5241c.1
                have p5241_1 := h5241c.2.1
                have p5241_2 := h5241c.2.2.1
                have p5241_3 := h5241c.2.2.2
                linarith only [h0, h3576, h4131, h4718, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5241_1]
              · have p5241_0 := h5241c.1
                have p5241_1 := h5241c.2.1
                have p5241_2 := h5241c.2.2.1
                have p5241_3 := h5241c.2.2.2
                rcases p5241_3 (m.d 0 2) (by simp) with h5246 | h5246
                · rcases p5241_3 (m.d 1 2) (by simp) with h5247 | h5247
                  · linarith only [h0, h5247, hlam]
                  · rcases p5241_3 (m.d 2 3) (by simp) with h5249 | h5249
                    · linarith only [h4, h5249, hlam]
                    · linarith only [h4717, h5249, hlam]
                · linarith only [h5246, hlam, p5241_0]
              · have p5241_0 := h5241c.1
                have p5241_1 := h5241c.2.1
                have p5241_2 := h5241c.2.2.1
                have p5241_3 := h5241c.2.2.2
                linarith only [h0, hlam, p5241_1]
              · have p5241_0 := h5241c.1
                have p5241_1 := h5241c.2.1
                have p5241_2 := h5241c.2.2.1
                have p5241_3 := h5241c.2.2.2
                linarith only [hlam, p5241_0]
              · have p5241_0 := h5241c.1
                have p5241_1 := h5241c.2.1
                have p5241_2 := h5241c.2.2.1
                have p5241_3 := h5241c.2.2.2
                linarith only [h10, hlam, p5241_0]
              · have p5241_0 := h5241c.1
                have p5241_1 := h5241c.2.1
                have p5241_2 := h5241c.2.2.1
                have p5241_3 := h5241c.2.2.2
                linarith only [h3576, hlam, p5241_0]
              · have p5241_0 := h5241c.1
                have p5241_1 := h5241c.2.1
                have p5241_2 := h5241c.2.2.1
                have p5241_3 := h5241c.2.2.2
                linarith only [h4058, hlam, p5241_0]
              · have p5241_0 := h5241c.1
                have p5241_1 := h5241c.2.1
                have p5241_2 := h5241c.2.2.1
                have p5241_3 := h5241c.2.2.2
                linarith only [h4, hlam, p5241_0]
              · have p5241_0 := h5241c.1
                have p5241_1 := h5241c.2.1
                have p5241_2 := h5241c.2.2.1
                have p5241_3 := h5241c.2.2.2
                rcases p5241_3 (m.d 0 2) (by simp) with h5259 | h5259
                · rcases p5241_3 (m.d 1 2) (by simp) with h5260 | h5260
                  · linarith only [h5260, hlam, p5241_0]
                  · rcases p5241_3 (m.d 2 3) (by simp) with h5262 | h5262
                    · rcases p5241_3 (m.d 2 4) (by simp) with h5263 | h5263
                      · linarith only [h4716, h5263, hlam]
                      · linarith only [h3576, h5263, hlam]
                    · linarith only [h5262, hlam, p5241_0]
                · linarith only [h0, h5259, hlam]
              · have p5241_0 := h5241c.1
                have p5241_1 := h5241c.2.1
                have p5241_2 := h5241c.2.2.1
                have p5241_3 := h5241c.2.2.2
                linarith only [hlam, p5241_0]
              · have p5241_0 := h5241c.1
                have p5241_1 := h5241c.2.1
                have p5241_2 := h5241c.2.2.1
                have p5241_3 := h5241c.2.2.2
                linarith only [h3576, h4, h4131, h4718, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5241_1]
              · have p5241_0 := h5241c.1
                have p5241_1 := h5241c.2.1
                have p5241_2 := h5241c.2.2.1
                have p5241_3 := h5241c.2.2.2
                linarith only [h0, h4, h4058, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5241_1]
              · have p5241_0 := h5241c.1
                have p5241_1 := h5241c.2.1
                have p5241_2 := h5241c.2.2.1
                have p5241_3 := h5241c.2.2.2
                linarith only [h5, hlam, p5241_0]
              · have p5241_0 := h5241c.1
                have p5241_1 := h5241c.2.1
                have p5241_2 := h5241c.2.2.1
                have p5241_3 := h5241c.2.2.2
                rcases p5241_3 (m.d 0 2) (by simp) with h5272 | h5272
                · rcases p5241_3 (m.d 1 2) (by simp) with h5273 | h5273
                  · linarith only [h5273, hlam, p5241_0]
                  · rcases p5241_3 (m.d 2 3) (by simp) with h5275 | h5275
                    · rcases p5241_3 (m.d 2 4) (by simp) with h5276 | h5276
                      · rcases p5241_3 (m.d 2 5) (by simp) with h5277 | h5277
                        · linarith only [h4718, h5277, hlam]
                        · linarith only [h4058, h5277, hlam]
                      · linarith only [h5276, hlam, p5241_0]
                    · linarith only [h10, h5275, hlam]
                · linarith only [h0, h5272, hlam]
              · have p5241_0 := h5241c.1
                have p5241_1 := h5241c.2.1
                have p5241_2 := h5241c.2.2.1
                have p5241_3 := h5241c.2.2.2
                linarith only [h4716, hlam, p5241_0]
              · have p5241_0 := h5241c.1
                have p5241_1 := h5241c.2.1
                have p5241_2 := h5241c.2.2.1
                have p5241_3 := h5241c.2.2.2
                linarith only [hlam, p5241_0]
              · have p5241_0 := h5241c.1
                have p5241_1 := h5241c.2.1
                have p5241_2 := h5241c.2.2.1
                have p5241_3 := h5241c.2.2.2
                linarith only [h3576, h4131, h4718, hc12, hc24, hlam, hphi, p5241_1]
              · have p5241_0 := h5241c.1
                have p5241_1 := h5241c.2.1
                have p5241_2 := h5241c.2.2.1
                have p5241_3 := h5241c.2.2.2
                linarith only [h6, hlam, p5241_0]
              · have p5241_0 := h5241c.1
                have p5241_1 := h5241c.2.1
                have p5241_2 := h5241c.2.2.1
                have p5241_3 := h5241c.2.2.2
                rcases p5241_3 (m.d 0 2) (by simp) with h5287 | h5287
                · rcases p5241_3 (m.d 1 2) (by simp) with h5288 | h5288
                  · linarith only [h5288, hlam, p5241_0]
                  · rcases p5241_3 (m.d 2 3) (by simp) with h5290 | h5290
                    · rcases p5241_3 (m.d 2 4) (by simp) with h5291 | h5291
                      · rcases p5241_3 (m.d 2 5) (by simp) with h5292 | h5292
                        · rcases h4bigk with h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c
                          · have p5293_0 := h5293c.1
                            have p5293_1 := h5293c.2.1
                            have p5293_2 := h5293c.2.2.1
                            have p5293_3 := h5293c.2.2.2
                            linarith only [hlam, p5293_0]
                          · have p5293_0 := h5293c.1
                            have p5293_1 := h5293c.2.1
                            have p5293_2 := h5293c.2.2.1
                            have p5293_3 := h5293c.2.2.2
                            rcases p5293_3 (m.d 0 4) (by simp) with h5295 | h5295
                            · rcases p5293_3 (m.d 1 4) (by simp) with h5296 | h5296
                              · linarith only [h2, h5296, hlam]
                              · rcases p5293_3 (m.d 2 4) (by simp) with h5298 | h5298
                                · linarith only [h5, h5298, hlam]
                                · linarith only [h3576, h5298, hlam]
                            · linarith only [h2, h5295, hlam]
                          · have p5293_0 := h5293c.1
                            have p5293_1 := h5293c.2.1
                            have p5293_2 := h5293c.2.2.1
                            have p5293_3 := h5293c.2.2.2
                            linarith only [h0, h3576, h4, h4131, h4718, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5293_1]
                          · have p5293_0 := h5293c.1
                            have p5293_1 := h5293c.2.1
                            have p5293_2 := h5293c.2.2.1
                            have p5293_3 := h5293c.2.2.2
                            rcases p5293_3 (m.d 0 4) (by simp) with h5303 | h5303
                            · rcases p5293_3 (m.d 1 4) (by simp) with h5304 | h5304
                              · linarith only [h2, h5304, hlam]
                              · linarith only [h4129, h5304, hlam]
                            · linarith only [h5303, h7, hlam]
                          · have p5293_0 := h5293c.1
                            have p5293_1 := h5293c.2.1
                            have p5293_2 := h5293c.2.2.1
                            have p5293_3 := h5293c.2.2.2
                            rcases p5293_3 (m.d 0 4) (by simp) with h5308 | h5308
                            · rcases p5293_3 (m.d 1 4) (by simp) with h5309 | h5309
                              · linarith only [h2, h5309, hlam]
                              · rcases p5293_3 (m.d 2 4) (by simp) with h5311 | h5311
                                · linarith only [h5, h5311, hlam]
                                · linarith only [h4718, h5311, hlam]
                            · linarith only [h5308, hlam, p5293_0]
                          · have p5293_0 := h5293c.1
                            have p5293_1 := h5293c.2.1
                            have p5293_2 := h5293c.2.2.1
                            have p5293_3 := h5293c.2.2.2
                            linarith only [h2, hlam, p5293_0]
                          · have p5293_0 := h5293c.1
                            have p5293_1 := h5293c.2.1
                            have p5293_2 := h5293c.2.2.1
                            have p5293_3 := h5293c.2.2.2
                            linarith only [hlam, p5293_0]
                          · have p5293_0 := h5293c.1
                            have p5293_1 := h5293c.2.1
                            have p5293_2 := h5293c.2.2.1
                            have p5293_3 := h5293c.2.2.2
                            linarith only [h3576, hlam, p5293_1]
                          · have p5293_0 := h5293c.1
                            have p5293_1 := h5293c.2.1
                            have p5293_2 := h5293c.2.2.1
                            have p5293_3 := h5293c.2.2.2
                            linarith only [h0, h10, h4, h4131, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4721_1, p5293_1]
                          · have p5293_0 := h5293c.1
                            have p5293_1 := h5293c.2.1
                            have p5293_2 := h5293c.2.2.1
                            have p5293_3 := h5293c.2.2.2
                            linarith only [h4131, hlam, p5293_0]
                          · have p5293_0 := h5293c.1
                            have p5293_1 := h5293c.2.1
                            have p5293_2 := h5293c.2.2.1
                            have p5293_3 := h5293c.2.2.2
                            linarith only [h5, hlam, p5293_0]
                          · have p5293_0 := h5293c.1
                            have p5293_1 := h5293c.2.1
                            have p5293_2 := h5293c.2.2.1
                            have p5293_3 := h5293c.2.2.2
                            rcases p5293_3 (m.d 0 4) (by simp) with h5321 | h5321
                            · rcases p5293_3 (m.d 1 4) (by simp) with h5322 | h5322
                              · linarith only [h3576, h5322, hlam]
                              · rcases p5293_3 (m.d 2 4) (by simp) with h5324 | h5324
                                · rcases p5293_3 (m.d 3 4) (by simp) with h5325 | h5325
                                  · linarith only [h4716, h5325, hlam]
                                  · rcases p5293_3 (m.d 4 5) (by simp) with h5327 | h5327
                                    · linarith only [h4718, h5327, hlam]
                                    · linarith only [h4131, h5327, hlam]
                                · linarith only [h3576, h5324, hlam]
                            · linarith only [h2, h5321, hlam]
                          · have p5293_0 := h5293c.1
                            have p5293_1 := h5293c.2.1
                            have p5293_2 := h5293c.2.2.1
                            have p5293_3 := h5293c.2.2.2
                            linarith only [hlam, p5293_0]
                          · have p5293_0 := h5293c.1
                            have p5293_1 := h5293c.2.1
                            have p5293_2 := h5293c.2.2.1
                            have p5293_3 := h5293c.2.2.2
                            rcases p5293_3 (m.d 0 4) (by simp) with h5333 | h5333
                            · rcases p5293_3 (m.d 1 4) (by simp) with h5334 | h5334
                              · linarith only [h3576, h5334, hlam]
                              · linarith only [h4129, h5334, hlam]
                            · linarith only [h5333, h7, hlam]
                          · have p5293_0 := h5293c.1
                            have p5293_1 := h5293c.2.1
                            have p5293_2 := h5293c.2.2.1
                            have p5293_3 := h5293c.2.2.2
                            linarith only [h0, h4131, h5, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p5293_1]
                          · have p5293_0 := h5293c.1
                            have p5293_1 := h5293c.2.1
                            have p5293_2 := h5293c.2.2.1
                            have p5293_3 := h5293c.2.2.2
                            linarith only [h7, hlam, p5293_0]
                          · have p5293_0 := h5293c.1
                            have p5293_1 := h5293c.2.1
                            have p5293_2 := h5293c.2.2.1
                            have p5293_3 := h5293c.2.2.2
                            linarith only [h4129, hlam, p5293_0]
                          · have p5293_0 := h5293c.1
                            have p5293_1 := h5293c.2.1
                            have p5293_2 := h5293c.2.2.1
                            have p5293_3 := h5293c.2.2.2
                            linarith only [h4716, hlam, p5293_0]
                          · have p5293_0 := h5293c.1
                            have p5293_1 := h5293c.2.1
                            have p5293_2 := h5293c.2.2.1
                            have p5293_3 := h5293c.2.2.2
                            linarith only [hlam, p5293_0]
                          · have p5293_0 := h5293c.1
                            have p5293_1 := h5293c.2.1
                            have p5293_2 := h5293c.2.2.1
                            have p5293_3 := h5293c.2.2.2
                            linarith only [h4719, hlam, p5293_0]
                          · have p5293_0 := h5293c.1
                            have p5293_1 := h5293c.2.1
                            have p5293_2 := h5293c.2.2.1
                            have p5293_3 := h5293c.2.2.2
                            linarith only [h9, hlam, p5293_0]
                          · have p5293_0 := h5293c.1
                            have p5293_1 := h5293c.2.1
                            have p5293_2 := h5293c.2.2.1
                            have p5293_3 := h5293c.2.2.2
                            linarith only [h0, h3576, h4, h4716, h4718, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5293_1]
                          · have p5293_0 := h5293c.1
                            have p5293_1 := h5293c.2.1
                            have p5293_2 := h5293c.2.2.1
                            have p5293_3 := h5293c.2.2.2
                            linarith only [h4718, hlam, p5293_0]
                          · have p5293_0 := h5293c.1
                            have p5293_1 := h5293c.2.1
                            have p5293_2 := h5293c.2.2.1
                            have p5293_3 := h5293c.2.2.2
                            linarith only [h0, h4, h4716, h4718, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5293_1]
                          · have p5293_0 := h5293c.1
                            have p5293_1 := h5293c.2.1
                            have p5293_2 := h5293c.2.2.1
                            have p5293_3 := h5293c.2.2.2
                            linarith only [hlam, p5293_0]
                        · linarith only [h5292, hlam, p5241_0]
                      · linarith only [h3576, h5291, hlam]
                    · linarith only [h10, h5290, hlam]
                · linarith only [h0, h5287, hlam]
              · have p5241_0 := h5241c.1
                have p5241_1 := h5241c.2.1
                have p5241_2 := h5241c.2.2.1
                have p5241_3 := h5241c.2.2.2
                linarith only [h4717, hlam, p5241_0]
              · have p5241_0 := h5241c.1
                have p5241_1 := h5241c.2.1
                have p5241_2 := h5241c.2.2.1
                have p5241_3 := h5241c.2.2.2
                linarith only [h4718, hlam, p5241_1]
              · have p5241_0 := h5241c.1
                have p5241_1 := h5241c.2.1
                have p5241_2 := h5241c.2.2.1
                have p5241_3 := h5241c.2.2.2
                linarith only [hlam, p5241_0]
            · linarith only [h5239, hc15, hlam, hphi, ht01, ht0b, ht5b, p4721_1]
            · rcases h2bigk with h5357c | h5357c | h5357c | h5357c | h5357c | h5357c | h5357c | h5357c | h5357c | h5357c | h5357c | h5357c | h5357c | h5357c | h5357c | h5357c | h5357c | h5357c | h5357c | h5357c | h5357c | h5357c | h5357c | h5357c | h5357c
              · have p5357_0 := h5357c.1
                have p5357_1 := h5357c.2.1
                have p5357_2 := h5357c.2.2.1
                have p5357_3 := h5357c.2.2.2
                linarith only [hlam, p5357_0]
              · have p5357_0 := h5357c.1
                have p5357_1 := h5357c.2.1
                have p5357_2 := h5357c.2.2.1
                have p5357_3 := h5357c.2.2.2
                linarith only [h10, h3576, h4, h4131, hlam, p4721_1, p5357_2]
              · have p5357_0 := h5357c.1
                have p5357_1 := h5357c.2.1
                have p5357_2 := h5357c.2.2.1
                have p5357_3 := h5357c.2.2.2
                linarith only [h10, h3576, h4131, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4721_1, p5357_1]
              · have p5357_0 := h5357c.1
                have p5357_1 := h5357c.2.1
                have p5357_2 := h5357c.2.2.1
                have p5357_3 := h5357c.2.2.2
                linarith only [h0, h3576, h4131, h4718, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5357_1]
              · have p5357_0 := h5357c.1
                have p5357_1 := h5357c.2.1
                have p5357_2 := h5357c.2.2.1
                have p5357_3 := h5357c.2.2.2
                rcases p5357_3 (m.d 0 2) (by simp) with h5362 | h5362
                · rcases p5357_3 (m.d 1 2) (by simp) with h5363 | h5363
                  · linarith only [h0, h5363, hlam]
                  · rcases p5357_3 (m.d 2 3) (by simp) with h5365 | h5365
                    · linarith only [h4, h5365, hlam]
                    · linarith only [h4717, h5365, hlam]
                · linarith only [h5362, hlam, p5357_0]
              · have p5357_0 := h5357c.1
                have p5357_1 := h5357c.2.1
                have p5357_2 := h5357c.2.2.1
                have p5357_3 := h5357c.2.2.2
                linarith only [h0, hlam, p5357_1]
              · have p5357_0 := h5357c.1
                have p5357_1 := h5357c.2.1
                have p5357_2 := h5357c.2.2.1
                have p5357_3 := h5357c.2.2.2
                linarith only [hlam, p5357_0]
              · have p5357_0 := h5357c.1
                have p5357_1 := h5357c.2.1
                have p5357_2 := h5357c.2.2.1
                have p5357_3 := h5357c.2.2.2
                linarith only [h10, hlam, p5357_0]
              · have p5357_0 := h5357c.1
                have p5357_1 := h5357c.2.1
                have p5357_2 := h5357c.2.2.1
                have p5357_3 := h5357c.2.2.2
                linarith only [h3576, hlam, p5357_0]
              · have p5357_0 := h5357c.1
                have p5357_1 := h5357c.2.1
                have p5357_2 := h5357c.2.2.1
                have p5357_3 := h5357c.2.2.2
                linarith only [h4058, hlam, p5357_0]
              · have p5357_0 := h5357c.1
                have p5357_1 := h5357c.2.1
                have p5357_2 := h5357c.2.2.1
                have p5357_3 := h5357c.2.2.2
                linarith only [h4, hlam, p5357_0]
              · have p5357_0 := h5357c.1
                have p5357_1 := h5357c.2.1
                have p5357_2 := h5357c.2.2.1
                have p5357_3 := h5357c.2.2.2
                rcases p5357_3 (m.d 0 2) (by simp) with h5375 | h5375
                · rcases p5357_3 (m.d 1 2) (by simp) with h5376 | h5376
                  · linarith only [h5376, hlam, p5357_0]
                  · rcases p5357_3 (m.d 2 3) (by simp) with h5378 | h5378
                    · rcases p5357_3 (m.d 2 4) (by simp) with h5379 | h5379
                      · linarith only [h4716, h5379, hlam]
                      · linarith only [h3576, h5379, hlam]
                    · linarith only [h5378, hlam, p5357_0]
                · linarith only [h0, h5375, hlam]
              · have p5357_0 := h5357c.1
                have p5357_1 := h5357c.2.1
                have p5357_2 := h5357c.2.2.1
                have p5357_3 := h5357c.2.2.2
                linarith only [hlam, p5357_0]
              · have p5357_0 := h5357c.1
                have p5357_1 := h5357c.2.1
                have p5357_2 := h5357c.2.2.1
                have p5357_3 := h5357c.2.2.2
                linarith only [h3576, h4131, h4718, hc12, hc23, hlam, hphi, p5357_1]
              · have p5357_0 := h5357c.1
                have p5357_1 := h5357c.2.1
                have p5357_2 := h5357c.2.2.1
                have p5357_3 := h5357c.2.2.2
                linarith only [h0, h4, h4058, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5357_1]
              · have p5357_0 := h5357c.1
                have p5357_1 := h5357c.2.1
                have p5357_2 := h5357c.2.2.1
                have p5357_3 := h5357c.2.2.2
                linarith only [h5, hlam, p5357_0]
              · have p5357_0 := h5357c.1
                have p5357_1 := h5357c.2.1
                have p5357_2 := h5357c.2.2.1
                have p5357_3 := h5357c.2.2.2
                rcases p5357_3 (m.d 0 2) (by simp) with h5388 | h5388
                · rcases p5357_3 (m.d 1 2) (by simp) with h5389 | h5389
                  · linarith only [h5389, hlam, p5357_0]
                  · rcases p5357_3 (m.d 2 3) (by simp) with h5391 | h5391
                    · rcases p5357_3 (m.d 2 4) (by simp) with h5392 | h5392
                      · rcases p5357_3 (m.d 2 5) (by simp) with h5393 | h5393
                        · linarith only [h4718, h5393, hlam]
                        · linarith only [h4058, h5393, hlam]
                      · linarith only [h5392, hlam, p5357_0]
                    · linarith only [h10, h5391, hlam]
                · linarith only [h0, h5388, hlam]
              · have p5357_0 := h5357c.1
                have p5357_1 := h5357c.2.1
                have p5357_2 := h5357c.2.2.1
                have p5357_3 := h5357c.2.2.2
                linarith only [h4716, hlam, p5357_0]
              · have p5357_0 := h5357c.1
                have p5357_1 := h5357c.2.1
                have p5357_2 := h5357c.2.2.1
                have p5357_3 := h5357c.2.2.2
                linarith only [hlam, p5357_0]
              · have p5357_0 := h5357c.1
                have p5357_1 := h5357c.2.1
                have p5357_2 := h5357c.2.2.1
                have p5357_3 := h5357c.2.2.2
                linarith only [h3576, h4131, h4718, hc12, hc24, hlam, hphi, p5357_1]
              · have p5357_0 := h5357c.1
                have p5357_1 := h5357c.2.1
                have p5357_2 := h5357c.2.2.1
                have p5357_3 := h5357c.2.2.2
                linarith only [h6, hlam, p5357_0]
              · have p5357_0 := h5357c.1
                have p5357_1 := h5357c.2.1
                have p5357_2 := h5357c.2.2.1
                have p5357_3 := h5357c.2.2.2
                rcases p5357_3 (m.d 0 2) (by simp) with h5403 | h5403
                · rcases p5357_3 (m.d 1 2) (by simp) with h5404 | h5404
                  · linarith only [h5404, hlam, p5357_0]
                  · rcases p5357_3 (m.d 2 3) (by simp) with h5406 | h5406
                    · rcases p5357_3 (m.d 2 4) (by simp) with h5407 | h5407
                      · rcases p5357_3 (m.d 2 5) (by simp) with h5408 | h5408
                        · rcases h4bigk with h5409c | h5409c | h5409c | h5409c | h5409c | h5409c | h5409c | h5409c | h5409c | h5409c | h5409c | h5409c | h5409c | h5409c | h5409c | h5409c | h5409c | h5409c | h5409c | h5409c | h5409c | h5409c | h5409c | h5409c | h5409c
                          · have p5409_0 := h5409c.1
                            have p5409_1 := h5409c.2.1
                            have p5409_2 := h5409c.2.2.1
                            have p5409_3 := h5409c.2.2.2
                            linarith only [hlam, p5409_0]
                          · have p5409_0 := h5409c.1
                            have p5409_1 := h5409c.2.1
                            have p5409_2 := h5409c.2.2.1
                            have p5409_3 := h5409c.2.2.2
                            rcases p5409_3 (m.d 0 4) (by simp) with h5411 | h5411
                            · rcases p5409_3 (m.d 1 4) (by simp) with h5412 | h5412
                              · linarith only [h2, h5412, hlam]
                              · rcases p5409_3 (m.d 2 4) (by simp) with h5414 | h5414
                                · linarith only [h5, h5414, hlam]
                                · linarith only [h3576, h5414, hlam]
                            · linarith only [h2, h5411, hlam]
                          · have p5409_0 := h5409c.1
                            have p5409_1 := h5409c.2.1
                            have p5409_2 := h5409c.2.2.1
                            have p5409_3 := h5409c.2.2.2
                            linarith only [h3576, h4131, h4718, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5409_1]
                          · have p5409_0 := h5409c.1
                            have p5409_1 := h5409c.2.1
                            have p5409_2 := h5409c.2.2.1
                            have p5409_3 := h5409c.2.2.2
                            rcases p5409_3 (m.d 0 4) (by simp) with h5419 | h5419
                            · rcases p5409_3 (m.d 1 4) (by simp) with h5420 | h5420
                              · linarith only [h2, h5420, hlam]
                              · linarith only [h4129, h5420, hlam]
                            · linarith only [h5419, h7, hlam]
                          · have p5409_0 := h5409c.1
                            have p5409_1 := h5409c.2.1
                            have p5409_2 := h5409c.2.2.1
                            have p5409_3 := h5409c.2.2.2
                            rcases p5409_3 (m.d 0 4) (by simp) with h5424 | h5424
                            · rcases p5409_3 (m.d 1 4) (by simp) with h5425 | h5425
                              · linarith only [h2, h5425, hlam]
                              · rcases p5409_3 (m.d 2 4) (by simp) with h5427 | h5427
                                · linarith only [h5, h5427, hlam]
                                · linarith only [h4718, h5427, hlam]
                            · linarith only [h5424, hlam, p5409_0]
                          · have p5409_0 := h5409c.1
                            have p5409_1 := h5409c.2.1
                            have p5409_2 := h5409c.2.2.1
                            have p5409_3 := h5409c.2.2.2
                            linarith only [h2, hlam, p5409_0]
                          · have p5409_0 := h5409c.1
                            have p5409_1 := h5409c.2.1
                            have p5409_2 := h5409c.2.2.1
                            have p5409_3 := h5409c.2.2.2
                            linarith only [hlam, p5409_0]
                          · have p5409_0 := h5409c.1
                            have p5409_1 := h5409c.2.1
                            have p5409_2 := h5409c.2.2.1
                            have p5409_3 := h5409c.2.2.2
                            linarith only [h3576, hlam, p5409_1]
                          · have p5409_0 := h5409c.1
                            have p5409_1 := h5409c.2.1
                            have p5409_2 := h5409c.2.2.1
                            have p5409_3 := h5409c.2.2.2
                            linarith only [h4131, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4721_1, p5409_1]
                          · have p5409_0 := h5409c.1
                            have p5409_1 := h5409c.2.1
                            have p5409_2 := h5409c.2.2.1
                            have p5409_3 := h5409c.2.2.2
                            linarith only [h4131, hlam, p5409_0]
                          · have p5409_0 := h5409c.1
                            have p5409_1 := h5409c.2.1
                            have p5409_2 := h5409c.2.2.1
                            have p5409_3 := h5409c.2.2.2
                            linarith only [h5, hlam, p5409_0]
                          · have p5409_0 := h5409c.1
                            have p5409_1 := h5409c.2.1
                            have p5409_2 := h5409c.2.2.1
                            have p5409_3 := h5409c.2.2.2
                            rcases p5409_3 (m.d 0 4) (by simp) with h5437 | h5437
                            · rcases p5409_3 (m.d 1 4) (by simp) with h5438 | h5438
                              · linarith only [h3576, h5438, hlam]
                              · rcases p5409_3 (m.d 2 4) (by simp) with h5440 | h5440
                                · rcases p5409_3 (m.d 3 4) (by simp) with h5441 | h5441
                                  · linarith only [h4716, h5441, hlam]
                                  · rcases p5409_3 (m.d 4 5) (by simp) with h5443 | h5443
                                    · linarith only [h4718, h5443, hlam]
                                    · linarith only [h4131, h5443, hlam]
                                · linarith only [h3576, h5440, hlam]
                            · linarith only [h2, h5437, hlam]
                          · have p5409_0 := h5409c.1
                            have p5409_1 := h5409c.2.1
                            have p5409_2 := h5409c.2.2.1
                            have p5409_3 := h5409c.2.2.2
                            linarith only [hlam, p5409_0]
                          · have p5409_0 := h5409c.1
                            have p5409_1 := h5409c.2.1
                            have p5409_2 := h5409c.2.2.1
                            have p5409_3 := h5409c.2.2.2
                            rcases p5409_3 (m.d 0 4) (by simp) with h5449 | h5449
                            · rcases p5409_3 (m.d 1 4) (by simp) with h5450 | h5450
                              · linarith only [h3576, h5450, hlam]
                              · linarith only [h4129, h5450, hlam]
                            · linarith only [h5449, h7, hlam]
                          · have p5409_0 := h5409c.1
                            have p5409_1 := h5409c.2.1
                            have p5409_2 := h5409c.2.2.1
                            have p5409_3 := h5409c.2.2.2
                            linarith only [h0, h4, h4131, h4716, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p5409_1]
                          · have p5409_0 := h5409c.1
                            have p5409_1 := h5409c.2.1
                            have p5409_2 := h5409c.2.2.1
                            have p5409_3 := h5409c.2.2.2
                            linarith only [h7, hlam, p5409_0]
                          · have p5409_0 := h5409c.1
                            have p5409_1 := h5409c.2.1
                            have p5409_2 := h5409c.2.2.1
                            have p5409_3 := h5409c.2.2.2
                            linarith only [h4129, hlam, p5409_0]
                          · have p5409_0 := h5409c.1
                            have p5409_1 := h5409c.2.1
                            have p5409_2 := h5409c.2.2.1
                            have p5409_3 := h5409c.2.2.2
                            linarith only [h4716, hlam, p5409_0]
                          · have p5409_0 := h5409c.1
                            have p5409_1 := h5409c.2.1
                            have p5409_2 := h5409c.2.2.1
                            have p5409_3 := h5409c.2.2.2
                            linarith only [hlam, p5409_0]
                          · have p5409_0 := h5409c.1
                            have p5409_1 := h5409c.2.1
                            have p5409_2 := h5409c.2.2.1
                            have p5409_3 := h5409c.2.2.2
                            linarith only [h4719, hlam, p5409_0]
                          · have p5409_0 := h5409c.1
                            have p5409_1 := h5409c.2.1
                            have p5409_2 := h5409c.2.2.1
                            have p5409_3 := h5409c.2.2.2
                            linarith only [h9, hlam, p5409_0]
                          · have p5409_0 := h5409c.1
                            have p5409_1 := h5409c.2.1
                            have p5409_2 := h5409c.2.2.1
                            have p5409_3 := h5409c.2.2.2
                            linarith only [h0, h3576, h4, h4716, h4718, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5409_1]
                          · have p5409_0 := h5409c.1
                            have p5409_1 := h5409c.2.1
                            have p5409_2 := h5409c.2.2.1
                            have p5409_3 := h5409c.2.2.2
                            linarith only [h4718, hlam, p5409_0]
                          · have p5409_0 := h5409c.1
                            have p5409_1 := h5409c.2.1
                            have p5409_2 := h5409c.2.2.1
                            have p5409_3 := h5409c.2.2.2
                            linarith only [h0, h4, h4716, h4718, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5409_1]
                          · have p5409_0 := h5409c.1
                            have p5409_1 := h5409c.2.1
                            have p5409_2 := h5409c.2.2.1
                            have p5409_3 := h5409c.2.2.2
                            linarith only [hlam, p5409_0]
                        · linarith only [h5408, hlam, p5357_0]
                      · linarith only [h3576, h5407, hlam]
                    · linarith only [h10, h5406, hlam]
                · linarith only [h0, h5403, hlam]
              · have p5357_0 := h5357c.1
                have p5357_1 := h5357c.2.1
                have p5357_2 := h5357c.2.2.1
                have p5357_3 := h5357c.2.2.2
                linarith only [h4717, hlam, p5357_0]
              · have p5357_0 := h5357c.1
                have p5357_1 := h5357c.2.1
                have p5357_2 := h5357c.2.2.1
                have p5357_3 := h5357c.2.2.2
                linarith only [h4718, hlam, p5357_1]
              · have p5357_0 := h5357c.1
                have p5357_1 := h5357c.2.1
                have p5357_2 := h5357c.2.2.1
                have p5357_3 := h5357c.2.2.2
                linarith only [hlam, p5357_0]
            · rcases h2bigk with h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c
              · have p5472_0 := h5472c.1
                have p5472_1 := h5472c.2.1
                have p5472_2 := h5472c.2.2.1
                have p5472_3 := h5472c.2.2.2
                linarith only [hlam, p5472_0]
              · have p5472_0 := h5472c.1
                have p5472_1 := h5472c.2.1
                have p5472_2 := h5472c.2.2.1
                have p5472_3 := h5472c.2.2.2
                linarith only [h10, h4, h4058, hlam, p4721_1, p5472_2]
              · have p5472_0 := h5472c.1
                have p5472_1 := h5472c.2.1
                have p5472_2 := h5472c.2.2.1
                have p5472_3 := h5472c.2.2.2
                linarith only [h0, h10, hc01, hc15, hlam, hphi, ht0b, ht5b, p4721_1, p5472_1]
              · have p5472_0 := h5472c.1
                have p5472_1 := h5472c.2.1
                have p5472_2 := h5472c.2.2.1
                have p5472_3 := h5472c.2.2.2
                linarith only [h0, h3576, h4131, h4718, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5472_1]
              · have p5472_0 := h5472c.1
                have p5472_1 := h5472c.2.1
                have p5472_2 := h5472c.2.2.1
                have p5472_3 := h5472c.2.2.2
                rcases p5472_3 (m.d 0 2) (by simp) with h5477 | h5477
                · rcases p5472_3 (m.d 1 2) (by simp) with h5478 | h5478
                  · linarith only [h0, h5478, hlam]
                  · rcases p5472_3 (m.d 2 3) (by simp) with h5480 | h5480
                    · linarith only [h4, h5480, hlam]
                    · linarith only [h4717, h5480, hlam]
                · linarith only [h5477, hlam, p5472_0]
              · have p5472_0 := h5472c.1
                have p5472_1 := h5472c.2.1
                have p5472_2 := h5472c.2.2.1
                have p5472_3 := h5472c.2.2.2
                linarith only [h0, hlam, p5472_1]
              · have p5472_0 := h5472c.1
                have p5472_1 := h5472c.2.1
                have p5472_2 := h5472c.2.2.1
                have p5472_3 := h5472c.2.2.2
                linarith only [hlam, p5472_0]
              · have p5472_0 := h5472c.1
                have p5472_1 := h5472c.2.1
                have p5472_2 := h5472c.2.2.1
                have p5472_3 := h5472c.2.2.2
                linarith only [h10, hlam, p5472_0]
              · have p5472_0 := h5472c.1
                have p5472_1 := h5472c.2.1
                have p5472_2 := h5472c.2.2.1
                have p5472_3 := h5472c.2.2.2
                linarith only [h3576, hlam, p5472_0]
              · have p5472_0 := h5472c.1
                have p5472_1 := h5472c.2.1
                have p5472_2 := h5472c.2.2.1
                have p5472_3 := h5472c.2.2.2
                linarith only [h4058, hlam, p5472_0]
              · have p5472_0 := h5472c.1
                have p5472_1 := h5472c.2.1
                have p5472_2 := h5472c.2.2.1
                have p5472_3 := h5472c.2.2.2
                linarith only [h4, hlam, p5472_0]
              · have p5472_0 := h5472c.1
                have p5472_1 := h5472c.2.1
                have p5472_2 := h5472c.2.2.1
                have p5472_3 := h5472c.2.2.2
                rcases p5472_3 (m.d 0 2) (by simp) with h5490 | h5490
                · rcases p5472_3 (m.d 1 2) (by simp) with h5491 | h5491
                  · linarith only [h5491, hlam, p5472_0]
                  · rcases p5472_3 (m.d 2 3) (by simp) with h5493 | h5493
                    · rcases p5472_3 (m.d 2 4) (by simp) with h5494 | h5494
                      · linarith only [h4716, h5494, hlam]
                      · linarith only [h3576, h5494, hlam]
                    · linarith only [h5493, hlam, p5472_0]
                · linarith only [h0, h5490, hlam]
              · have p5472_0 := h5472c.1
                have p5472_1 := h5472c.2.1
                have p5472_2 := h5472c.2.2.1
                have p5472_3 := h5472c.2.2.2
                linarith only [hlam, p5472_0]
              · have p5472_0 := h5472c.1
                have p5472_1 := h5472c.2.1
                have p5472_2 := h5472c.2.2.1
                have p5472_3 := h5472c.2.2.2
                linarith only [h3576, h4131, h4718, hc12, hc23, hlam, hphi, p5472_1]
              · have p5472_0 := h5472c.1
                have p5472_1 := h5472c.2.1
                have p5472_2 := h5472c.2.2.1
                have p5472_3 := h5472c.2.2.2
                linarith only [h0, h4, h4058, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5472_1]
              · have p5472_0 := h5472c.1
                have p5472_1 := h5472c.2.1
                have p5472_2 := h5472c.2.2.1
                have p5472_3 := h5472c.2.2.2
                linarith only [h5, hlam, p5472_0]
              · have p5472_0 := h5472c.1
                have p5472_1 := h5472c.2.1
                have p5472_2 := h5472c.2.2.1
                have p5472_3 := h5472c.2.2.2
                rcases p5472_3 (m.d 0 2) (by simp) with h5503 | h5503
                · rcases p5472_3 (m.d 1 2) (by simp) with h5504 | h5504
                  · linarith only [h5504, hlam, p5472_0]
                  · rcases p5472_3 (m.d 2 3) (by simp) with h5506 | h5506
                    · rcases p5472_3 (m.d 2 4) (by simp) with h5507 | h5507
                      · rcases p5472_3 (m.d 2 5) (by simp) with h5508 | h5508
                        · linarith only [h4718, h5508, hlam]
                        · linarith only [h4058, h5508, hlam]
                      · linarith only [h5507, hlam, p5472_0]
                    · linarith only [h10, h5506, hlam]
                · linarith only [h0, h5503, hlam]
              · have p5472_0 := h5472c.1
                have p5472_1 := h5472c.2.1
                have p5472_2 := h5472c.2.2.1
                have p5472_3 := h5472c.2.2.2
                linarith only [h4716, hlam, p5472_0]
              · have p5472_0 := h5472c.1
                have p5472_1 := h5472c.2.1
                have p5472_2 := h5472c.2.2.1
                have p5472_3 := h5472c.2.2.2
                linarith only [hlam, p5472_0]
              · have p5472_0 := h5472c.1
                have p5472_1 := h5472c.2.1
                have p5472_2 := h5472c.2.2.1
                have p5472_3 := h5472c.2.2.2
                linarith only [h3576, h4131, h4718, hc12, hc24, hlam, hphi, p5472_1]
              · have p5472_0 := h5472c.1
                have p5472_1 := h5472c.2.1
                have p5472_2 := h5472c.2.2.1
                have p5472_3 := h5472c.2.2.2
                linarith only [h6, hlam, p5472_0]
              · have p5472_0 := h5472c.1
                have p5472_1 := h5472c.2.1
                have p5472_2 := h5472c.2.2.1
                have p5472_3 := h5472c.2.2.2
                rcases p5472_3 (m.d 0 2) (by simp) with h5518 | h5518
                · rcases p5472_3 (m.d 1 2) (by simp) with h5519 | h5519
                  · linarith only [h5519, hlam, p5472_0]
                  · rcases p5472_3 (m.d 2 3) (by simp) with h5521 | h5521
                    · rcases p5472_3 (m.d 2 4) (by simp) with h5522 | h5522
                      · rcases p5472_3 (m.d 2 5) (by simp) with h5523 | h5523
                        · rcases h4bigk with h5524c | h5524c | h5524c | h5524c | h5524c | h5524c | h5524c | h5524c | h5524c | h5524c | h5524c | h5524c | h5524c | h5524c | h5524c | h5524c | h5524c | h5524c | h5524c | h5524c | h5524c | h5524c | h5524c | h5524c | h5524c
                          · have p5524_0 := h5524c.1
                            have p5524_1 := h5524c.2.1
                            have p5524_2 := h5524c.2.2.1
                            have p5524_3 := h5524c.2.2.2
                            linarith only [hlam, p5524_0]
                          · have p5524_0 := h5524c.1
                            have p5524_1 := h5524c.2.1
                            have p5524_2 := h5524c.2.2.1
                            have p5524_3 := h5524c.2.2.2
                            rcases p5524_3 (m.d 0 4) (by simp) with h5526 | h5526
                            · rcases p5524_3 (m.d 1 4) (by simp) with h5527 | h5527
                              · linarith only [h2, h5527, hlam]
                              · rcases p5524_3 (m.d 2 4) (by simp) with h5529 | h5529
                                · linarith only [h5, h5529, hlam]
                                · linarith only [h3576, h5529, hlam]
                            · linarith only [h2, h5526, hlam]
                          · have p5524_0 := h5524c.1
                            have p5524_1 := h5524c.2.1
                            have p5524_2 := h5524c.2.2.1
                            have p5524_3 := h5524c.2.2.2
                            linarith only [h3576, h4131, h4718, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5524_1]
                          · have p5524_0 := h5524c.1
                            have p5524_1 := h5524c.2.1
                            have p5524_2 := h5524c.2.2.1
                            have p5524_3 := h5524c.2.2.2
                            rcases p5524_3 (m.d 0 4) (by simp) with h5534 | h5534
                            · rcases p5524_3 (m.d 1 4) (by simp) with h5535 | h5535
                              · linarith only [h2, h5535, hlam]
                              · linarith only [h4129, h5535, hlam]
                            · linarith only [h5534, h7, hlam]
                          · have p5524_0 := h5524c.1
                            have p5524_1 := h5524c.2.1
                            have p5524_2 := h5524c.2.2.1
                            have p5524_3 := h5524c.2.2.2
                            rcases p5524_3 (m.d 0 4) (by simp) with h5539 | h5539
                            · rcases p5524_3 (m.d 1 4) (by simp) with h5540 | h5540
                              · linarith only [h2, h5540, hlam]
                              · rcases p5524_3 (m.d 2 4) (by simp) with h5542 | h5542
                                · linarith only [h5, h5542, hlam]
                                · linarith only [h4718, h5542, hlam]
                            · linarith only [h5539, hlam, p5524_0]
                          · have p5524_0 := h5524c.1
                            have p5524_1 := h5524c.2.1
                            have p5524_2 := h5524c.2.2.1
                            have p5524_3 := h5524c.2.2.2
                            linarith only [h2, hlam, p5524_0]
                          · have p5524_0 := h5524c.1
                            have p5524_1 := h5524c.2.1
                            have p5524_2 := h5524c.2.2.1
                            have p5524_3 := h5524c.2.2.2
                            linarith only [hlam, p5524_0]
                          · have p5524_0 := h5524c.1
                            have p5524_1 := h5524c.2.1
                            have p5524_2 := h5524c.2.2.1
                            have p5524_3 := h5524c.2.2.2
                            linarith only [h3576, hlam, p5524_1]
                          · have p5524_0 := h5524c.1
                            have p5524_1 := h5524c.2.1
                            have p5524_2 := h5524c.2.2.1
                            have p5524_3 := h5524c.2.2.2
                            linarith only [h4131, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4721_1, p5524_1]
                          · have p5524_0 := h5524c.1
                            have p5524_1 := h5524c.2.1
                            have p5524_2 := h5524c.2.2.1
                            have p5524_3 := h5524c.2.2.2
                            linarith only [h4131, hlam, p5524_0]
                          · have p5524_0 := h5524c.1
                            have p5524_1 := h5524c.2.1
                            have p5524_2 := h5524c.2.2.1
                            have p5524_3 := h5524c.2.2.2
                            linarith only [h5, hlam, p5524_0]
                          · have p5524_0 := h5524c.1
                            have p5524_1 := h5524c.2.1
                            have p5524_2 := h5524c.2.2.1
                            have p5524_3 := h5524c.2.2.2
                            rcases p5524_3 (m.d 0 4) (by simp) with h5552 | h5552
                            · rcases p5524_3 (m.d 1 4) (by simp) with h5553 | h5553
                              · linarith only [h3576, h5553, hlam]
                              · rcases p5524_3 (m.d 2 4) (by simp) with h5555 | h5555
                                · rcases p5524_3 (m.d 3 4) (by simp) with h5556 | h5556
                                  · linarith only [h4716, h5556, hlam]
                                  · rcases p5524_3 (m.d 4 5) (by simp) with h5558 | h5558
                                    · linarith only [h4718, h5558, hlam]
                                    · linarith only [h4131, h5558, hlam]
                                · linarith only [h3576, h5555, hlam]
                            · linarith only [h2, h5552, hlam]
                          · have p5524_0 := h5524c.1
                            have p5524_1 := h5524c.2.1
                            have p5524_2 := h5524c.2.2.1
                            have p5524_3 := h5524c.2.2.2
                            linarith only [hlam, p5524_0]
                          · have p5524_0 := h5524c.1
                            have p5524_1 := h5524c.2.1
                            have p5524_2 := h5524c.2.2.1
                            have p5524_3 := h5524c.2.2.2
                            rcases p5524_3 (m.d 0 4) (by simp) with h5564 | h5564
                            · rcases p5524_3 (m.d 1 4) (by simp) with h5565 | h5565
                              · linarith only [h3576, h5565, hlam]
                              · linarith only [h4129, h5565, hlam]
                            · linarith only [h5564, h7, hlam]
                          · have p5524_0 := h5524c.1
                            have p5524_1 := h5524c.2.1
                            have p5524_2 := h5524c.2.2.1
                            have p5524_3 := h5524c.2.2.2
                            linarith only [h0, h4, h4131, h4716, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p5524_1]
                          · have p5524_0 := h5524c.1
                            have p5524_1 := h5524c.2.1
                            have p5524_2 := h5524c.2.2.1
                            have p5524_3 := h5524c.2.2.2
                            linarith only [h7, hlam, p5524_0]
                          · have p5524_0 := h5524c.1
                            have p5524_1 := h5524c.2.1
                            have p5524_2 := h5524c.2.2.1
                            have p5524_3 := h5524c.2.2.2
                            linarith only [h4129, hlam, p5524_0]
                          · have p5524_0 := h5524c.1
                            have p5524_1 := h5524c.2.1
                            have p5524_2 := h5524c.2.2.1
                            have p5524_3 := h5524c.2.2.2
                            linarith only [h4716, hlam, p5524_0]
                          · have p5524_0 := h5524c.1
                            have p5524_1 := h5524c.2.1
                            have p5524_2 := h5524c.2.2.1
                            have p5524_3 := h5524c.2.2.2
                            linarith only [hlam, p5524_0]
                          · have p5524_0 := h5524c.1
                            have p5524_1 := h5524c.2.1
                            have p5524_2 := h5524c.2.2.1
                            have p5524_3 := h5524c.2.2.2
                            linarith only [h4719, hlam, p5524_0]
                          · have p5524_0 := h5524c.1
                            have p5524_1 := h5524c.2.1
                            have p5524_2 := h5524c.2.2.1
                            have p5524_3 := h5524c.2.2.2
                            linarith only [h9, hlam, p5524_0]
                          · have p5524_0 := h5524c.1
                            have p5524_1 := h5524c.2.1
                            have p5524_2 := h5524c.2.2.1
                            have p5524_3 := h5524c.2.2.2
                            linarith only [h0, h3576, h4, h4716, h4718, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5524_1]
                          · have p5524_0 := h5524c.1
                            have p5524_1 := h5524c.2.1
                            have p5524_2 := h5524c.2.2.1
                            have p5524_3 := h5524c.2.2.2
                            linarith only [h4718, hlam, p5524_0]
                          · have p5524_0 := h5524c.1
                            have p5524_1 := h5524c.2.1
                            have p5524_2 := h5524c.2.2.1
                            have p5524_3 := h5524c.2.2.2
                            linarith only [h0, h4, h4716, h4718, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5524_1]
                          · have p5524_0 := h5524c.1
                            have p5524_1 := h5524c.2.1
                            have p5524_2 := h5524c.2.2.1
                            have p5524_3 := h5524c.2.2.2
                            linarith only [hlam, p5524_0]
                        · linarith only [h5523, hlam, p5472_0]
                      · linarith only [h3576, h5522, hlam]
                    · linarith only [h10, h5521, hlam]
                · linarith only [h0, h5518, hlam]
              · have p5472_0 := h5472c.1
                have p5472_1 := h5472c.2.1
                have p5472_2 := h5472c.2.2.1
                have p5472_3 := h5472c.2.2.2
                linarith only [h4717, hlam, p5472_0]
              · have p5472_0 := h5472c.1
                have p5472_1 := h5472c.2.1
                have p5472_2 := h5472c.2.2.1
                have p5472_3 := h5472c.2.2.2
                linarith only [h4718, hlam, p5472_1]
              · have p5472_0 := h5472c.1
                have p5472_1 := h5472c.2.1
                have p5472_2 := h5472c.2.2.1
                have p5472_3 := h5472c.2.2.2
                linarith only [hlam, p5472_0]
      · linarith only [h4130, h5234, hlam]
  · linarith only [h3, h5231, hlam]

set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x15 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4131 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h4716 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h4717 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h4718 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h4719 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h4721c : ((m.d 1 4) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 1 4) ∧ (m.d 0 1) - (m.d 1 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 4) ∨ (m.d 0 1) ≤ z)))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  have p4721_0 := h4721c.1
  have p4721_1 := h4721c.2.1
  have p4721_2 := h4721c.2.2.1
  have p4721_3 := h4721c.2.2.2
  linarith only [h2, hlam, p4721_0]

set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x16 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4131 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h4716 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h4717 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h4718 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h4719 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h4721c : ((m.d 1 4) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 1 4) ∧ (m.d 1 2) - (m.d 1 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 4) ∨ (m.d 1 2) ≤ z)))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  have p4721_0 := h4721c.1
  have p4721_1 := h4721c.2.1
  have p4721_2 := h4721c.2.2.1
  have p4721_3 := h4721c.2.2.2
  linarith only [h0, h4, h4131, h4716, h4718, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4721_1]

set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x17 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4131 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h4716 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h4717 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h4718 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h4719 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h4721c : ((m.d 1 4) < (m.d 1 3) ∧ 2 * m.lam ≤ (m.d 1 3) - (m.d 1 4) ∧ (m.d 1 3) - (m.d 1 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 4) ∨ (m.d 1 3) ≤ z)))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  have p4721_0 := h4721c.1
  have p4721_1 := h4721c.2.1
  have p4721_2 := h4721c.2.2.1
  have p4721_3 := h4721c.2.2.2
  linarith only [h4129, hlam, p4721_1]

set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x18 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4131 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h4716 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h4717 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h4718 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h4719 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h4721c : ((m.d 1 4) < (m.d 1 4) ∧ 2 * m.lam ≤ (m.d 1 4) - (m.d 1 4) ∧ (m.d 1 4) - (m.d 1 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 4) ∨ (m.d 1 4) ≤ z)))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  have p4721_0 := h4721c.1
  have p4721_1 := h4721c.2.1
  have p4721_2 := h4721c.2.2.1
  have p4721_3 := h4721c.2.2.2
  linarith only [hlam, p4721_0]

set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x19 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4131 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h4716 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h4717 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h4718 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h4719 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h4721c : ((m.d 1 4) < (m.d 1 5) ∧ 2 * m.lam ≤ (m.d 1 5) - (m.d 1 4) ∧ (m.d 1 5) - (m.d 1 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 4) ∨ (m.d 1 5) ≤ z)))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  have p4721_0 := h4721c.1
  have p4721_1 := h4721c.2.1
  have p4721_2 := h4721c.2.2.1
  have p4721_3 := h4721c.2.2.2
  linarith only [h4131, hlam, p4721_1]

set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x20 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4131 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h4716 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h4717 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h4718 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h4719 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h4721c : ((m.d 1 5) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 1 5) ∧ (m.d 0 1) - (m.d 1 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 5) ∨ (m.d 0 1) ≤ z)))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  have p4721_0 := h4721c.1
  have p4721_1 := h4721c.2.1
  have p4721_2 := h4721c.2.2.1
  have p4721_3 := h4721c.2.2.2
  linarith only [h3, hlam, p4721_0]

set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x21 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4131 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h4716 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h4717 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h4718 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h4719 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h4721c : ((m.d 1 5) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 1 5) ∧ (m.d 1 2) - (m.d 1 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 5) ∨ (m.d 1 2) ≤ z)))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  have p4721_0 := h4721c.1
  have p4721_1 := h4721c.2.1
  have p4721_2 := h4721c.2.2.1
  have p4721_3 := h4721c.2.2.2
  linarith only [h0, h4, h4131, h4716, h4718, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4721_1]

set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x22 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4131 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h4716 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h4717 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h4718 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h4719 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h4721c : ((m.d 1 5) < (m.d 1 3) ∧ 2 * m.lam ≤ (m.d 1 3) - (m.d 1 5) ∧ (m.d 1 3) - (m.d 1 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 5) ∨ (m.d 1 3) ≤ z)))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  have p4721_0 := h4721c.1
  have p4721_1 := h4721c.2.1
  have p4721_2 := h4721c.2.2.1
  have p4721_3 := h4721c.2.2.2
  linarith only [h4130, hlam, p4721_0]

set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x23 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4131 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h4716 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h4717 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h4718 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h4719 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h4721c : ((m.d 1 5) < (m.d 1 4) ∧ 2 * m.lam ≤ (m.d 1 4) - (m.d 1 5) ∧ (m.d 1 4) - (m.d 1 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 5) ∨ (m.d 1 4) ≤ z)))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  have p4721_0 := h4721c.1
  have p4721_1 := h4721c.2.1
  have p4721_2 := h4721c.2.2.1
  have p4721_3 := h4721c.2.2.2
  linarith only [h0, h4, h4131, h4716, h4718, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p4721_1]

set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x24 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4131 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h4716 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h4717 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h4718 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h4719 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h4721c : ((m.d 1 5) < (m.d 1 5) ∧ 2 * m.lam ≤ (m.d 1 5) - (m.d 1 5) ∧ (m.d 1 5) - (m.d 1 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 5) ∨ (m.d 1 5) ≤ z)))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  have p4721_0 := h4721c.1
  have p4721_1 := h4721c.2.1
  have p4721_2 := h4721c.2.2.1
  have p4721_3 := h4721c.2.2.2
  linarith only [hlam, p4721_0]

set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4131 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h4716 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h4717 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h4718 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h4719 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  rcases h1bigk with h4721c | h4721c | h4721c | h4721c | h4721c | h4721c | h4721c | h4721c | h4721c | h4721c | h4721c | h4721c | h4721c | h4721c | h4721c | h4721c | h4721c | h4721c | h4721c | h4721c | h4721c | h4721c | h4721c | h4721c | h4721c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130 h4131 h4716 h4717 h4718 h4719 h4721c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130 h4131 h4716 h4717 h4718 h4719 h4721c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x2 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130 h4131 h4716 h4717 h4718 h4719 h4721c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x3 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130 h4131 h4716 h4717 h4718 h4719 h4721c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x4 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130 h4131 h4716 h4717 h4718 h4719 h4721c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x5 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130 h4131 h4716 h4717 h4718 h4719 h4721c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x6 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130 h4131 h4716 h4717 h4718 h4719 h4721c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x7 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130 h4131 h4716 h4717 h4718 h4719 h4721c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x8 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130 h4131 h4716 h4717 h4718 h4719 h4721c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x9 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130 h4131 h4716 h4717 h4718 h4719 h4721c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x10 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130 h4131 h4716 h4717 h4718 h4719 h4721c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x11 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130 h4131 h4716 h4717 h4718 h4719 h4721c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x12 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130 h4131 h4716 h4717 h4718 h4719 h4721c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x13 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130 h4131 h4716 h4717 h4718 h4719 h4721c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x14 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130 h4131 h4716 h4717 h4718 h4719 h4721c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x15 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130 h4131 h4716 h4717 h4718 h4719 h4721c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x16 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130 h4131 h4716 h4717 h4718 h4719 h4721c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x17 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130 h4131 h4716 h4717 h4718 h4719 h4721c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x18 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130 h4131 h4716 h4717 h4718 h4719 h4721c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x19 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130 h4131 h4716 h4717 h4718 h4719 h4721c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x20 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130 h4131 h4716 h4717 h4718 h4719 h4721c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x21 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130 h4131 h4716 h4717 h4718 h4719 h4721c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x22 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130 h4131 h4716 h4717 h4718 h4719 h4721c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x23 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130 h4131 h4716 h4717 h4718 h4719 h4721c
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1_x24 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130 h4131 h4716 h4717 h4718 h4719 h4721c

set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4131 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h4716 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h4717 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h4718 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  rcases m.htr 3 4 5 (by decide) (by decide) with h4719 | h4719
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130 h4131 h4716 h4717 h4718 h4719
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130 h4131 h4716 h4717 h4718 h4719

end R2N4
