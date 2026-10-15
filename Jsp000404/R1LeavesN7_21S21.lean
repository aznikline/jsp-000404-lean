import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_21S20

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5244000 in
set_option maxHeartbeats 5244000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s7_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3473 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4044 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4238 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4335 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4336 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4337 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4338 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h2bigk := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h3473 := hg3473
  have h4044 := hg4044
  have h4238 := hg4238
  rcases m.htr 0 4 5 (by decide) (by decide) with h5246 | h5246
  · rcases m.htr 1 2 3 (by decide) (by decide) with h5247 | h5247
    · rcases m.htr 1 2 4 (by decide) (by decide) with h5248 | h5248
      · rcases m.htr 1 2 5 (by decide) (by decide) with h5249 | h5249
        · rcases m.htr 1 3 4 (by decide) (by decide) with h5250 | h5250
          · rcases m.htr 1 3 5 (by decide) (by decide) with h5251 | h5251
            · rcases m.htr 1 4 5 (by decide) (by decide) with h5252 | h5252
              · rcases m.htr 2 3 4 (by decide) (by decide) with h5253 | h5253
                · linarith only [h4335, h4338, h5247, h5251, h5253, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h5255 | h5255
                  · linarith only [h4335, h4338, h5255, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5257 | h5257
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5258 | h5258
                      · rcases h1bigk with h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c
                        · have p5259_0 := h5259c.1
                          have p5259_1 := h5259c.2.1
                          have p5259_2 := h5259c.2.2.1
                          have p5259_3 := h5259c.2.2.2
                          linarith only [hlam, p5259_0]
                        · have p5259_0 := h5259c.1
                          have p5259_1 := h5259c.2.1
                          have p5259_2 := h5259c.2.2.1
                          have p5259_3 := h5259c.2.2.2
                          linarith only [h0, hlam, p5259_0]
                        · have p5259_0 := h5259c.1
                          have p5259_1 := h5259c.2.1
                          have p5259_2 := h5259c.2.2.1
                          have p5259_3 := h5259c.2.2.2
                          linarith only [h3473, hlam, p5259_0]
                        · have p5259_0 := h5259c.1
                          have p5259_1 := h5259c.2.1
                          have p5259_2 := h5259c.2.2.1
                          have p5259_3 := h5259c.2.2.2
                          linarith only [h4044, hlam, p5259_0]
                        · have p5259_0 := h5259c.1
                          have p5259_1 := h5259c.2.1
                          have p5259_2 := h5259c.2.2.1
                          have p5259_3 := h5259c.2.2.2
                          linarith only [h4238, hlam, p5259_0]
                        · have p5259_0 := h5259c.1
                          have p5259_1 := h5259c.2.1
                          have p5259_2 := h5259c.2.2.1
                          have p5259_3 := h5259c.2.2.2
                          rcases p5259_3 (m.d 0 1) (by simp) with h5265 | h5265
                          · linarith only [h5265, hlam, p5259_0]
                          · rcases p5259_3 (m.d 1 2) (by simp) with h5267 | h5267
                            · rcases p5259_3 (m.d 1 3) (by simp) with h5268 | h5268
                              · linarith only [h5247, h5268, hlam]
                              · linarith only [h3473, h5268, hlam]
                            · linarith only [h5267, hlam, p5259_0]
                        · have p5259_0 := h5259c.1
                          have p5259_1 := h5259c.2.1
                          have p5259_2 := h5259c.2.2.1
                          have p5259_3 := h5259c.2.2.2
                          linarith only [hlam, p5259_0]
                        · have p5259_0 := h5259c.1
                          have p5259_1 := h5259c.2.1
                          have p5259_2 := h5259c.2.2.1
                          have p5259_3 := h5259c.2.2.2
                          linarith only [h4338, h5250, h5258, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5259_1]
                        · have p5259_0 := h5259c.1
                          have p5259_1 := h5259c.2.1
                          have p5259_2 := h5259c.2.2.1
                          have p5259_3 := h5259c.2.2.2
                          linarith only [h4044, h4336, h5257, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5259_1, u4ehi4]
                        · have p5259_0 := h5259c.1
                          have p5259_1 := h5259c.2.1
                          have p5259_2 := h5259c.2.2.1
                          have p5259_3 := h5259c.2.2.2
                          linarith only [h3473, h4338, h5251, hc01, hc12, hlam, hphi, p5259_1]
                        · have p5259_0 := h5259c.1
                          have p5259_1 := h5259c.2.1
                          have p5259_2 := h5259c.2.2.1
                          have p5259_3 := h5259c.2.2.2
                          rcases p5259_3 (m.d 0 1) (by simp) with h5276 | h5276
                          · linarith only [h5276, hlam, p5259_0]
                          · rcases p5259_3 (m.d 1 2) (by simp) with h5278 | h5278
                            · rcases p5259_3 (m.d 1 3) (by simp) with h5279 | h5279
                              · rcases p5259_3 (m.d 1 4) (by simp) with h5280 | h5280
                                · linarith only [h5250, h5280, hlam]
                                · linarith only [h4044, h5280, hlam]
                              · linarith only [h5279, hlam, p5259_0]
                            · linarith only [h0, h5278, hlam]
                        · have p5259_0 := h5259c.1
                          have p5259_1 := h5259c.2.1
                          have p5259_2 := h5259c.2.2.1
                          have p5259_3 := h5259c.2.2.2
                          linarith only [h5247, hlam, p5259_0]
                        · have p5259_0 := h5259c.1
                          have p5259_1 := h5259c.2.1
                          have p5259_2 := h5259c.2.2.1
                          have p5259_3 := h5259c.2.2.2
                          linarith only [hlam, p5259_0]
                        · have p5259_0 := h5259c.1
                          have p5259_1 := h5259c.2.1
                          have p5259_2 := h5259c.2.2.1
                          have p5259_3 := h5259c.2.2.2
                          linarith only [h4044, h4336, h5257, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p5259_1, u4ehi4]
                        · have p5259_0 := h5259c.1
                          have p5259_1 := h5259c.2.1
                          have p5259_2 := h5259c.2.2.1
                          have p5259_3 := h5259c.2.2.2
                          linarith only [h3473, h4338, h5247, h5251, hc01, hc12, hlam, hphi, p5259_1]
                        · have p5259_0 := h5259c.1
                          have p5259_1 := h5259c.2.1
                          have p5259_2 := h5259c.2.2.1
                          have p5259_3 := h5259c.2.2.2
                          rcases p5259_3 (m.d 0 1) (by simp) with h5289 | h5289
                          · linarith only [h5289, hlam, p5259_0]
                          · rcases p5259_3 (m.d 1 2) (by simp) with h5291 | h5291
                            · rcases p5259_3 (m.d 1 3) (by simp) with h5292 | h5292
                              · rcases p5259_3 (m.d 1 4) (by simp) with h5293 | h5293
                                · rcases p5259_3 (m.d 1 5) (by simp) with h5294 | h5294
                                  · linarith only [h5252, h5294, hlam]
                                  · linarith only [h4238, h5294, hlam]
                                · linarith only [h5293, hlam, p5259_0]
                              · linarith only [h3473, h5292, hlam]
                            · linarith only [h0, h5291, hlam]
                        · have p5259_0 := h5259c.1
                          have p5259_1 := h5259c.2.1
                          have p5259_2 := h5259c.2.2.1
                          have p5259_3 := h5259c.2.2.2
                          linarith only [h5248, hlam, p5259_0]
                        · have p5259_0 := h5259c.1
                          have p5259_1 := h5259c.2.1
                          have p5259_2 := h5259c.2.2.1
                          have p5259_3 := h5259c.2.2.2
                          linarith only [h5250, hlam, p5259_1]
                        · have p5259_0 := h5259c.1
                          have p5259_1 := h5259c.2.1
                          have p5259_2 := h5259c.2.2.1
                          have p5259_3 := h5259c.2.2.2
                          linarith only [hlam, p5259_0]
                        · have p5259_0 := h5259c.1
                          have p5259_1 := h5259c.2.1
                          have p5259_2 := h5259c.2.2.1
                          have p5259_3 := h5259c.2.2.2
                          linarith only [h3473, h4338, h5251, hc01, hc14, hlam, hphi, p5259_1]
                        · have p5259_0 := h5259c.1
                          have p5259_1 := h5259c.2.1
                          have p5259_2 := h5259c.2.2.1
                          have p5259_3 := h5259c.2.2.2
                          rcases p5259_3 (m.d 0 1) (by simp) with h5304 | h5304
                          · linarith only [h5304, hlam, p5259_0]
                          · rcases p5259_3 (m.d 1 2) (by simp) with h5306 | h5306
                            · rcases p5259_3 (m.d 1 3) (by simp) with h5307 | h5307
                              · rcases p5259_3 (m.d 1 4) (by simp) with h5308 | h5308
                                · rcases p5259_3 (m.d 1 5) (by simp) with h5309 | h5309
                                  · rcases h2bigk with h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c
                                    · have p5310_0 := h5310c.1
                                      have p5310_1 := h5310c.2.1
                                      have p5310_2 := h5310c.2.2.1
                                      have p5310_3 := h5310c.2.2.2
                                      linarith only [hlam, p5310_0]
                                    · have p5310_0 := h5310c.1
                                      have p5310_1 := h5310c.2.1
                                      have p5310_2 := h5310c.2.2.1
                                      have p5310_3 := h5310c.2.2.2
                                      linarith only [h0, hlam, p5310_0]
                                    · have p5310_0 := h5310c.1
                                      have p5310_1 := h5310c.2.1
                                      have p5310_2 := h5310c.2.2.1
                                      have p5310_3 := h5310c.2.2.2
                                      rcases p5310_3 (m.d 0 2) (by simp) with h5313 | h5313
                                      · rcases p5310_3 (m.d 1 2) (by simp) with h5314 | h5314
                                        · rcases p5310_3 (m.d 2 3) (by simp) with h5315 | h5315
                                          · linarith only [h5315, hlam, p5310_0]
                                          · rcases p5310_3 (m.d 2 4) (by simp) with h5317 | h5317
                                            · linarith only [h4336, h5317, hlam]
                                            · linarith only [h5253, h5317, hlam]
                                        · linarith only [h5247, h5314, hlam]
                                      · linarith only [h5313, hlam, p5310_0]
                                    · have p5310_0 := h5310c.1
                                      have p5310_1 := h5310c.2.1
                                      have p5310_2 := h5310c.2.2.1
                                      have p5310_3 := h5310c.2.2.2
                                      linarith only [h5257, hc02, hlam, hphi, ht0b, ht45, ht5b, p5310_1, u4ehi4]
                                    · have p5310_0 := h5310c.1
                                      have p5310_1 := h5310c.2.1
                                      have p5310_2 := h5310c.2.2.1
                                      have p5310_3 := h5310c.2.2.2
                                      rcases p5310_3 (m.d 0 2) (by simp) with h5323 | h5323
                                      · rcases p5310_3 (m.d 1 2) (by simp) with h5324 | h5324
                                        · rcases p5310_3 (m.d 2 3) (by simp) with h5325 | h5325
                                          · linarith only [h4335, h5325, hlam]
                                          · rcases p5310_3 (m.d 2 4) (by simp) with h5327 | h5327
                                            · linarith only [h4336, h5327, hlam]
                                            · linarith only [h5257, h5327, hlam]
                                        · linarith only [h5249, h5324, hlam]
                                      · linarith only [h5323, hlam, p5310_0]
                                    · have p5310_0 := h5310c.1
                                      have p5310_1 := h5310c.2.1
                                      have p5310_2 := h5310c.2.2.1
                                      have p5310_3 := h5310c.2.2.2
                                      linarith only [h4336, h5257, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5310_1, u4ehi4]
                                    · have p5310_0 := h5310c.1
                                      have p5310_1 := h5310c.2.1
                                      have p5310_2 := h5310c.2.2.1
                                      have p5310_3 := h5310c.2.2.2
                                      linarith only [hlam, p5310_0]
                                    · have p5310_0 := h5310c.1
                                      have p5310_1 := h5310c.2.1
                                      have p5310_2 := h5310c.2.2.1
                                      have p5310_3 := h5310c.2.2.2
                                      rcases p5310_3 (m.d 0 2) (by simp) with h5334 | h5334
                                      · linarith only [h0, h5334, hlam]
                                      · linarith only [h4335, h5334, hlam]
                                    · have p5310_0 := h5310c.1
                                      have p5310_1 := h5310c.2.1
                                      have p5310_2 := h5310c.2.2.1
                                      have p5310_3 := h5310c.2.2.2
                                      linarith only [h5257, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5310_1, u4ehi4]
                                    · have p5310_0 := h5310c.1
                                      have p5310_1 := h5310c.2.1
                                      have p5310_2 := h5310c.2.2.1
                                      have p5310_3 := h5310c.2.2.2
                                      rcases p5310_3 (m.d 0 2) (by simp) with h5338 | h5338
                                      · linarith only [h0, h5338, hlam]
                                      · linarith only [h4337, h5338, hlam]
                                    · have p5310_0 := h5310c.1
                                      have p5310_1 := h5310c.2.1
                                      have p5310_2 := h5310c.2.2.1
                                      have p5310_3 := h5310c.2.2.2
                                      linarith only [h4335, hlam, p5310_0]
                                    · have p5310_0 := h5310c.1
                                      have p5310_1 := h5310c.2.1
                                      have p5310_2 := h5310c.2.2.1
                                      have p5310_3 := h5310c.2.2.2
                                      linarith only [h5247, hlam, p5310_0]
                                    · have p5310_0 := h5310c.1
                                      have p5310_1 := h5310c.2.1
                                      have p5310_2 := h5310c.2.2.1
                                      have p5310_3 := h5310c.2.2.2
                                      linarith only [hlam, p5310_0]
                                    · have p5310_0 := h5310c.1
                                      have p5310_1 := h5310c.2.1
                                      have p5310_2 := h5310c.2.2.1
                                      have p5310_3 := h5310c.2.2.2
                                      linarith only [h5253, hlam, p5310_1]
                                    · have p5310_0 := h5310c.1
                                      have p5310_1 := h5310c.2.1
                                      have p5310_2 := h5310c.2.2.1
                                      have p5310_3 := h5310c.2.2.2
                                      linarith only [h5255, hlam, p5310_1]
                                    · have p5310_0 := h5310c.1
                                      have p5310_1 := h5310c.2.1
                                      have p5310_2 := h5310c.2.2.1
                                      have p5310_3 := h5310c.2.2.2
                                      linarith only [h4336, hlam, p5310_0]
                                    · have p5310_0 := h5310c.1
                                      have p5310_1 := h5310c.2.1
                                      have p5310_2 := h5310c.2.2.1
                                      have p5310_3 := h5310c.2.2.2
                                      linarith only [h5248, hlam, p5310_0]
                                    · have p5310_0 := h5310c.1
                                      have p5310_1 := h5310c.2.1
                                      have p5310_2 := h5310c.2.2.1
                                      have p5310_3 := h5310c.2.2.2
                                      rcases p5310_3 (m.d 0 2) (by simp) with h5348 | h5348
                                      · rcases p5310_3 (m.d 1 2) (by simp) with h5349 | h5349
                                        · rcases p5310_3 (m.d 2 3) (by simp) with h5350 | h5350
                                          · linarith only [h5253, h5350, hlam]
                                          · rcases p5310_3 (m.d 2 4) (by simp) with h5352 | h5352
                                            · rcases p5310_3 (m.d 2 5) (by simp) with h5353 | h5353
                                              · linarith only [h5257, h5353, hlam]
                                              · linarith only [h5255, h5353, hlam]
                                            · linarith only [h5253, h5352, hlam]
                                        · linarith only [h5247, h5349, hlam]
                                      · linarith only [h4335, h5348, hlam]
                                    · have p5310_0 := h5310c.1
                                      have p5310_1 := h5310c.2.1
                                      have p5310_2 := h5310c.2.2.1
                                      have p5310_3 := h5310c.2.2.2
                                      linarith only [hlam, p5310_0]
                                    · have p5310_0 := h5310c.1
                                      have p5310_1 := h5310c.2.1
                                      have p5310_2 := h5310c.2.2.1
                                      have p5310_3 := h5310c.2.2.2
                                      linarith only [h4336, h5257, hc02, hlam, hphi, ht0b, ht45, ht5b, p5310_1, u4ehi4]
                                    · have p5310_0 := h5310c.1
                                      have p5310_1 := h5310c.2.1
                                      have p5310_2 := h5310c.2.2.1
                                      have p5310_3 := h5310c.2.2.2
                                      linarith only [h4337, hlam, p5310_0]
                                    · have p5310_0 := h5310c.1
                                      have p5310_1 := h5310c.2.1
                                      have p5310_2 := h5310c.2.2.1
                                      have p5310_3 := h5310c.2.2.2
                                      linarith only [h5249, hlam, p5310_0]
                                    · have p5310_0 := h5310c.1
                                      have p5310_1 := h5310c.2.1
                                      have p5310_2 := h5310c.2.2.1
                                      have p5310_3 := h5310c.2.2.2
                                      rcases p5310_3 (m.d 0 2) (by simp) with h5363 | h5363
                                      · rcases p5310_3 (m.d 1 2) (by simp) with h5364 | h5364
                                        · rcases p5310_3 (m.d 2 3) (by simp) with h5365 | h5365
                                          · linarith only [h5255, h5365, hlam]
                                          · rcases p5310_3 (m.d 2 4) (by simp) with h5367 | h5367
                                            · rcases p5310_3 (m.d 2 5) (by simp) with h5368 | h5368
                                              · rcases h5bigk with h5369c | h5369c | h5369c | h5369c | h5369c | h5369c | h5369c | h5369c | h5369c | h5369c | h5369c | h5369c | h5369c | h5369c | h5369c | h5369c | h5369c | h5369c | h5369c | h5369c | h5369c | h5369c | h5369c | h5369c | h5369c
                                                · have p5369_0 := h5369c.1
                                                  have p5369_1 := h5369c.2.1
                                                  have p5369_2 := h5369c.2.2.1
                                                  have p5369_3 := h5369c.2.2.2
                                                  linarith only [hlam, p5369_0]
                                                · have p5369_0 := h5369c.1
                                                  have p5369_1 := h5369c.2.1
                                                  have p5369_2 := h5369c.2.2.1
                                                  have p5369_3 := h5369c.2.2.2
                                                  linarith only [h4238, hlam, p5369_1]
                                                · have p5369_0 := h5369c.1
                                                  have p5369_1 := h5369c.2.1
                                                  have p5369_2 := h5369c.2.2.1
                                                  have p5369_3 := h5369c.2.2.2
                                                  linarith only [hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5310_1, p5369_1]
                                                · have p5369_0 := h5369c.1
                                                  have p5369_1 := h5369c.2.1
                                                  have p5369_2 := h5369c.2.2.1
                                                  have p5369_3 := h5369c.2.2.2
                                                  linarith only [h4338, hlam, p5369_0]
                                                · have p5369_0 := h5369c.1
                                                  have p5369_1 := h5369c.2.1
                                                  have p5369_2 := h5369c.2.2.1
                                                  have p5369_3 := h5369c.2.2.2
                                                  linarith only [h4338, h5247, h5251, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5369_1, u4ehi4]
                                                · have p5369_0 := h5369c.1
                                                  have p5369_1 := h5369c.2.1
                                                  have p5369_2 := h5369c.2.2.1
                                                  have p5369_3 := h5369c.2.2.2
                                                  linarith only [h4337, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5310_1, p5369_1]
                                                · have p5369_0 := h5369c.1
                                                  have p5369_1 := h5369c.2.1
                                                  have p5369_2 := h5369c.2.2.1
                                                  have p5369_3 := h5369c.2.2.2
                                                  linarith only [hlam, p5369_0]
                                                · have p5369_0 := h5369c.1
                                                  have p5369_1 := h5369c.2.1
                                                  have p5369_2 := h5369c.2.2.1
                                                  have p5369_3 := h5369c.2.2.2
                                                  linarith only [h5249, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5310_1, p5369_1]
                                                · have p5369_0 := h5369c.1
                                                  have p5369_1 := h5369c.2.1
                                                  have p5369_2 := h5369c.2.2.1
                                                  have p5369_3 := h5369c.2.2.2
                                                  linarith only [h4337, h4338, h5247, h5251, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5310_1, p5369_1]
                                                · have p5369_0 := h5369c.1
                                                  have p5369_1 := h5369c.2.1
                                                  have p5369_2 := h5369c.2.2.1
                                                  have p5369_3 := h5369c.2.2.2
                                                  rcases p5369_3 (m.d 0 5) (by simp) with h5379 | h5379
                                                  · linarith only [h4238, h5379, hlam]
                                                  · linarith only [h5246, h5379, hlam]
                                                · have p5369_0 := h5369c.1
                                                  have p5369_1 := h5369c.2.1
                                                  have p5369_2 := h5369c.2.2.1
                                                  have p5369_3 := h5369c.2.2.2
                                                  linarith only [h4337, hlam, p5369_1]
                                                · have p5369_0 := h5369c.1
                                                  have p5369_1 := h5369c.2.1
                                                  have p5369_2 := h5369c.2.2.1
                                                  have p5369_3 := h5369c.2.2.2
                                                  linarith only [h5249, hlam, p5369_1]
                                                · have p5369_0 := h5369c.1
                                                  have p5369_1 := h5369c.2.1
                                                  have p5369_2 := h5369c.2.2.1
                                                  have p5369_3 := h5369c.2.2.2
                                                  linarith only [hlam, p5369_0]
                                                · have p5369_0 := h5369c.1
                                                  have p5369_1 := h5369c.2.1
                                                  have p5369_2 := h5369c.2.2.1
                                                  have p5369_3 := h5369c.2.2.2
                                                  linarith only [h5255, hlam, p5369_1]
                                                · have p5369_0 := h5369c.1
                                                  have p5369_1 := h5369c.2.1
                                                  have p5369_2 := h5369c.2.2.1
                                                  have p5369_3 := h5369c.2.2.2
                                                  linarith only [h0, h4337, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5369_1, u4ehi4]
                                                · have p5369_0 := h5369c.1
                                                  have p5369_1 := h5369c.2.1
                                                  have p5369_2 := h5369c.2.2.1
                                                  have p5369_3 := h5369c.2.2.2
                                                  linarith only [h5247, h5251, hc12, hlam, hphi, ht01, ht0b, ht5b, p5369_1, u5ehi0]
                                                · have p5369_0 := h5369c.1
                                                  have p5369_1 := h5369c.2.1
                                                  have p5369_2 := h5369c.2.2.1
                                                  have p5369_3 := h5369c.2.2.2
                                                  linarith only [h5251, hlam, p5369_1]
                                                · have p5369_0 := h5369c.1
                                                  have p5369_1 := h5369c.2.1
                                                  have p5369_2 := h5369c.2.2.1
                                                  have p5369_3 := h5369c.2.2.2
                                                  linarith only [h5247, h5251, hc12, hlam, hphi, ht01, ht0b, ht5b, p5369_1, u5ehi2]
                                                · have p5369_0 := h5369c.1
                                                  have p5369_1 := h5369c.2.1
                                                  have p5369_2 := h5369c.2.2.1
                                                  have p5369_3 := h5369c.2.2.2
                                                  linarith only [hlam, p5369_0]
                                                · have p5369_0 := h5369c.1
                                                  have p5369_1 := h5369c.2.1
                                                  have p5369_2 := h5369c.2.2.1
                                                  have p5369_3 := h5369c.2.2.2
                                                  linarith only [h5247, h5250, h5258, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5369_1, u4ehi4]
                                                · have p5369_0 := h5369c.1
                                                  have p5369_1 := h5369c.2.1
                                                  have p5369_2 := h5369c.2.2.1
                                                  have p5369_3 := h5369c.2.2.2
                                                  linarith only [h5246, hlam, p5369_1]
                                                · have p5369_0 := h5369c.1
                                                  have p5369_1 := h5369c.2.1
                                                  have p5369_2 := h5369c.2.2.1
                                                  have p5369_3 := h5369c.2.2.2
                                                  linarith only [h5252, hlam, p5369_1]
                                                · have p5369_0 := h5369c.1
                                                  have p5369_1 := h5369c.2.1
                                                  have p5369_2 := h5369c.2.2.1
                                                  have p5369_3 := h5369c.2.2.2
                                                  linarith only [h5257, hlam, p5369_1]
                                                · have p5369_0 := h5369c.1
                                                  have p5369_1 := h5369c.2.1
                                                  have p5369_2 := h5369c.2.2.1
                                                  have p5369_3 := h5369c.2.2.2
                                                  linarith only [h5258, hlam, p5369_1]
                                                · have p5369_0 := h5369c.1
                                                  have p5369_1 := h5369c.2.1
                                                  have p5369_2 := h5369c.2.2.1
                                                  have p5369_3 := h5369c.2.2.2
                                                  linarith only [hlam, p5369_0]
                                              · linarith only [h5255, h5368, hlam]
                                            · linarith only [h5253, h5367, hlam]
                                        · linarith only [h5247, h5364, hlam]
                                      · linarith only [h4335, h5363, hlam]
                                    · have p5310_0 := h5310c.1
                                      have p5310_1 := h5310c.2.1
                                      have p5310_2 := h5310c.2.2.1
                                      have p5310_3 := h5310c.2.2.2
                                      linarith only [h5257, hlam, p5310_1]
                                    · have p5310_0 := h5310c.1
                                      have p5310_1 := h5310c.2.1
                                      have p5310_2 := h5310c.2.2.1
                                      have p5310_3 := h5310c.2.2.2
                                      linarith only [hlam, p5310_0]
                                  · linarith only [h5309, hlam, p5259_0]
                                · linarith only [h4044, h5308, hlam]
                              · linarith only [h3473, h5307, hlam]
                            · linarith only [h0, h5306, hlam]
                        · have p5259_0 := h5259c.1
                          have p5259_1 := h5259c.2.1
                          have p5259_2 := h5259c.2.2.1
                          have p5259_3 := h5259c.2.2.2
                          linarith only [h5249, hlam, p5259_0]
                        · have p5259_0 := h5259c.1
                          have p5259_1 := h5259c.2.1
                          have p5259_2 := h5259c.2.2.1
                          have p5259_3 := h5259c.2.2.2
                          linarith only [h5251, hlam, p5259_0]
                        · have p5259_0 := h5259c.1
                          have p5259_1 := h5259c.2.1
                          have p5259_2 := h5259c.2.2.1
                          have p5259_3 := h5259c.2.2.2
                          linarith only [h5252, hlam, p5259_0]
                        · have p5259_0 := h5259c.1
                          have p5259_1 := h5259c.2.1
                          have p5259_2 := h5259c.2.2.1
                          have p5259_3 := h5259c.2.2.2
                          linarith only [hlam, p5259_0]
                      · linarith only [h5253, h5257, h5258, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5412 | h5412
                      · linarith only [h5247, h5250, h5257, h5412, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                      · linarith only [h4338, h5246, h5412, hlam]
              · linarith only [h4044, h5246, h5252, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h5416 | h5416
              · linarith only [h5250, h5251, h5416, hlam]
              · linarith only [h4044, h5246, h5416, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h5419 | h5419
            · linarith only [h3473, h4338, h5250, h5419, hc01, hc34, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h5421 | h5421
              · rcases m.htr 2 3 4 (by decide) (by decide) with h5422 | h5422
                · linarith only [h3473, h4335, h5250, h5422, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h5424 | h5424
                  · linarith only [h4335, h4338, h5424, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5426 | h5426
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5427 | h5427
                      · rcases h1bigk with h5428c | h5428c | h5428c | h5428c | h5428c | h5428c | h5428c | h5428c | h5428c | h5428c | h5428c | h5428c | h5428c | h5428c | h5428c | h5428c | h5428c | h5428c | h5428c | h5428c | h5428c | h5428c | h5428c | h5428c | h5428c
                        · have p5428_0 := h5428c.1
                          have p5428_1 := h5428c.2.1
                          have p5428_2 := h5428c.2.2.1
                          have p5428_3 := h5428c.2.2.2
                          linarith only [hlam, p5428_0]
                        · have p5428_0 := h5428c.1
                          have p5428_1 := h5428c.2.1
                          have p5428_2 := h5428c.2.2.1
                          have p5428_3 := h5428c.2.2.2
                          linarith only [h0, hlam, p5428_0]
                        · have p5428_0 := h5428c.1
                          have p5428_1 := h5428c.2.1
                          have p5428_2 := h5428c.2.2.1
                          have p5428_3 := h5428c.2.2.2
                          linarith only [h3473, hlam, p5428_0]
                        · have p5428_0 := h5428c.1
                          have p5428_1 := h5428c.2.1
                          have p5428_2 := h5428c.2.2.1
                          have p5428_3 := h5428c.2.2.2
                          linarith only [h4044, hlam, p5428_0]
                        · have p5428_0 := h5428c.1
                          have p5428_1 := h5428c.2.1
                          have p5428_2 := h5428c.2.2.1
                          have p5428_3 := h5428c.2.2.2
                          linarith only [h4238, hlam, p5428_0]
                        · have p5428_0 := h5428c.1
                          have p5428_1 := h5428c.2.1
                          have p5428_2 := h5428c.2.2.1
                          have p5428_3 := h5428c.2.2.2
                          rcases p5428_3 (m.d 0 1) (by simp) with h5434 | h5434
                          · linarith only [h5434, hlam, p5428_0]
                          · rcases p5428_3 (m.d 1 2) (by simp) with h5436 | h5436
                            · rcases p5428_3 (m.d 1 3) (by simp) with h5437 | h5437
                              · linarith only [h5247, h5437, hlam]
                              · linarith only [h3473, h5437, hlam]
                            · linarith only [h5436, hlam, p5428_0]
                        · have p5428_0 := h5428c.1
                          have p5428_1 := h5428c.2.1
                          have p5428_2 := h5428c.2.2.1
                          have p5428_3 := h5428c.2.2.2
                          linarith only [hlam, p5428_0]
                        · have p5428_0 := h5428c.1
                          have p5428_1 := h5428c.2.1
                          have p5428_2 := h5428c.2.2.1
                          have p5428_3 := h5428c.2.2.2
                          linarith only [h3473, hc01, hc12, hlam, hphi, p5428_1]
                        · have p5428_0 := h5428c.1
                          have p5428_1 := h5428c.2.1
                          have p5428_2 := h5428c.2.2.1
                          have p5428_3 := h5428c.2.2.2
                          linarith only [h4044, hc01, hc12, hlam, hphi, p5428_1]
                        · have p5428_0 := h5428c.1
                          have p5428_1 := h5428c.2.1
                          have p5428_2 := h5428c.2.2.1
                          have p5428_3 := h5428c.2.2.2
                          linarith only [h4238, hc01, hc12, hlam, hphi, p5428_1]
                        · have p5428_0 := h5428c.1
                          have p5428_1 := h5428c.2.1
                          have p5428_2 := h5428c.2.2.1
                          have p5428_3 := h5428c.2.2.2
                          linarith only [h5250, hc01, hc34, hlam, hphi, ht12, ht23, p5428_1]
                        · have p5428_0 := h5428c.1
                          have p5428_1 := h5428c.2.1
                          have p5428_2 := h5428c.2.2.1
                          have p5428_3 := h5428c.2.2.2
                          linarith only [h5247, hlam, p5428_0]
                        · have p5428_0 := h5428c.1
                          have p5428_1 := h5428c.2.1
                          have p5428_2 := h5428c.2.2.1
                          have p5428_3 := h5428c.2.2.2
                          linarith only [hlam, p5428_0]
                        · have p5428_0 := h5428c.1
                          have p5428_1 := h5428c.2.1
                          have p5428_2 := h5428c.2.2.1
                          have p5428_3 := h5428c.2.2.2
                          linarith only [h5250, hlam, p5428_0]
                        · have p5428_0 := h5428c.1
                          have p5428_1 := h5428c.2.1
                          have p5428_2 := h5428c.2.2.1
                          have p5428_3 := h5428c.2.2.2
                          linarith only [h5419, hlam, p5428_1]
                        · have p5428_0 := h5428c.1
                          have p5428_1 := h5428c.2.1
                          have p5428_2 := h5428c.2.2.1
                          have p5428_3 := h5428c.2.2.2
                          rcases p5428_3 (m.d 0 1) (by simp) with h5450 | h5450
                          · linarith only [h5450, hlam, p5428_0]
                          · rcases p5428_3 (m.d 1 2) (by simp) with h5452 | h5452
                            · rcases p5428_3 (m.d 1 3) (by simp) with h5453 | h5453
                              · linarith only [h5250, h5453, hlam]
                              · linarith only [h3473, h5453, hlam]
                            · linarith only [h0, h5452, hlam]
                        · have p5428_0 := h5428c.1
                          have p5428_1 := h5428c.2.1
                          have p5428_2 := h5428c.2.2.1
                          have p5428_3 := h5428c.2.2.2
                          linarith only [h5248, hlam, p5428_0]
                        · have p5428_0 := h5428c.1
                          have p5428_1 := h5428c.2.1
                          have p5428_2 := h5428c.2.2.1
                          have p5428_3 := h5428c.2.2.2
                          linarith only [h3473, hc01, hc14, hlam, hphi, p5428_1]
                        · have p5428_0 := h5428c.1
                          have p5428_1 := h5428c.2.1
                          have p5428_2 := h5428c.2.2.1
                          have p5428_3 := h5428c.2.2.2
                          linarith only [hlam, p5428_0]
                        · have p5428_0 := h5428c.1
                          have p5428_1 := h5428c.2.1
                          have p5428_2 := h5428c.2.2.1
                          have p5428_3 := h5428c.2.2.2
                          linarith only [h3473, h5250, h5419, hc01, hc34, hlam, hphi, ht12, ht23, p5428_1]
                        · have p5428_0 := h5428c.1
                          have p5428_1 := h5428c.2.1
                          have p5428_2 := h5428c.2.2.1
                          have p5428_3 := h5428c.2.2.2
                          rcases p5428_3 (m.d 0 1) (by simp) with h5461 | h5461
                          · linarith only [h5461, hlam, p5428_0]
                          · rcases p5428_3 (m.d 1 2) (by simp) with h5463 | h5463
                            · rcases p5428_3 (m.d 1 3) (by simp) with h5464 | h5464
                              · linarith only [h5419, h5464, hlam]
                              · linarith only [h3473, h5464, hlam]
                            · linarith only [h0, h5463, hlam]
                        · have p5428_0 := h5428c.1
                          have p5428_1 := h5428c.2.1
                          have p5428_2 := h5428c.2.2.1
                          have p5428_3 := h5428c.2.2.2
                          linarith only [h5249, hlam, p5428_0]
                        · have p5428_0 := h5428c.1
                          have p5428_1 := h5428c.2.1
                          have p5428_2 := h5428c.2.2.1
                          have p5428_3 := h5428c.2.2.2
                          linarith only [h3473, hc01, hc15, hlam, hphi, p5428_1]
                        · have p5428_0 := h5428c.1
                          have p5428_1 := h5428c.2.1
                          have p5428_2 := h5428c.2.2.1
                          have p5428_3 := h5428c.2.2.2
                          linarith only [h5421, hlam, p5428_0]
                        · have p5428_0 := h5428c.1
                          have p5428_1 := h5428c.2.1
                          have p5428_2 := h5428c.2.2.1
                          have p5428_3 := h5428c.2.2.2
                          linarith only [hlam, p5428_0]
                      · linarith only [h4044, h5250, h5426, h5427, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5473 | h5473
                      · rcases h1bigk with h5474c | h5474c | h5474c | h5474c | h5474c | h5474c | h5474c | h5474c | h5474c | h5474c | h5474c | h5474c | h5474c | h5474c | h5474c | h5474c | h5474c | h5474c | h5474c | h5474c | h5474c | h5474c | h5474c | h5474c | h5474c
                        · have p5474_0 := h5474c.1
                          have p5474_1 := h5474c.2.1
                          have p5474_2 := h5474c.2.2.1
                          have p5474_3 := h5474c.2.2.2
                          linarith only [hlam, p5474_0]
                        · have p5474_0 := h5474c.1
                          have p5474_1 := h5474c.2.1
                          have p5474_2 := h5474c.2.2.1
                          have p5474_3 := h5474c.2.2.2
                          linarith only [h0, hlam, p5474_0]
                        · have p5474_0 := h5474c.1
                          have p5474_1 := h5474c.2.1
                          have p5474_2 := h5474c.2.2.1
                          have p5474_3 := h5474c.2.2.2
                          linarith only [h3473, hlam, p5474_0]
                        · have p5474_0 := h5474c.1
                          have p5474_1 := h5474c.2.1
                          have p5474_2 := h5474c.2.2.1
                          have p5474_3 := h5474c.2.2.2
                          linarith only [h4044, hlam, p5474_0]
                        · have p5474_0 := h5474c.1
                          have p5474_1 := h5474c.2.1
                          have p5474_2 := h5474c.2.2.1
                          have p5474_3 := h5474c.2.2.2
                          linarith only [h4238, hlam, p5474_0]
                        · have p5474_0 := h5474c.1
                          have p5474_1 := h5474c.2.1
                          have p5474_2 := h5474c.2.2.1
                          have p5474_3 := h5474c.2.2.2
                          rcases p5474_3 (m.d 0 1) (by simp) with h5480 | h5480
                          · linarith only [h5480, hlam, p5474_0]
                          · rcases p5474_3 (m.d 1 2) (by simp) with h5482 | h5482
                            · rcases p5474_3 (m.d 1 3) (by simp) with h5483 | h5483
                              · linarith only [h5247, h5483, hlam]
                              · linarith only [h3473, h5483, hlam]
                            · linarith only [h5482, hlam, p5474_0]
                        · have p5474_0 := h5474c.1
                          have p5474_1 := h5474c.2.1
                          have p5474_2 := h5474c.2.2.1
                          have p5474_3 := h5474c.2.2.2
                          linarith only [hlam, p5474_0]
                        · have p5474_0 := h5474c.1
                          have p5474_1 := h5474c.2.1
                          have p5474_2 := h5474c.2.2.1
                          have p5474_3 := h5474c.2.2.2
                          linarith only [h3473, hc01, hc12, hlam, hphi, p5474_1]
                        · have p5474_0 := h5474c.1
                          have p5474_1 := h5474c.2.1
                          have p5474_2 := h5474c.2.2.1
                          have p5474_3 := h5474c.2.2.2
                          linarith only [h4044, h5246, h5426, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5474_1, u4ehi2]
                        · have p5474_0 := h5474c.1
                          have p5474_1 := h5474c.2.1
                          have p5474_2 := h5474c.2.2.1
                          have p5474_3 := h5474c.2.2.2
                          linarith only [h4238, hc01, hc12, hlam, hphi, p5474_1]
                        · have p5474_0 := h5474c.1
                          have p5474_1 := h5474c.2.1
                          have p5474_2 := h5474c.2.2.1
                          have p5474_3 := h5474c.2.2.2
                          linarith only [h5250, hc01, hc34, hlam, hphi, ht12, ht23, p5474_1]
                        · have p5474_0 := h5474c.1
                          have p5474_1 := h5474c.2.1
                          have p5474_2 := h5474c.2.2.1
                          have p5474_3 := h5474c.2.2.2
                          linarith only [h5247, hlam, p5474_0]
                        · have p5474_0 := h5474c.1
                          have p5474_1 := h5474c.2.1
                          have p5474_2 := h5474c.2.2.1
                          have p5474_3 := h5474c.2.2.2
                          linarith only [hlam, p5474_0]
                        · have p5474_0 := h5474c.1
                          have p5474_1 := h5474c.2.1
                          have p5474_2 := h5474c.2.2.1
                          have p5474_3 := h5474c.2.2.2
                          linarith only [h5250, hlam, p5474_0]
                        · have p5474_0 := h5474c.1
                          have p5474_1 := h5474c.2.1
                          have p5474_2 := h5474c.2.2.1
                          have p5474_3 := h5474c.2.2.2
                          linarith only [h5419, hlam, p5474_1]
                        · have p5474_0 := h5474c.1
                          have p5474_1 := h5474c.2.1
                          have p5474_2 := h5474c.2.2.1
                          have p5474_3 := h5474c.2.2.2
                          rcases p5474_3 (m.d 0 1) (by simp) with h5496 | h5496
                          · linarith only [h5496, hlam, p5474_0]
                          · rcases p5474_3 (m.d 1 2) (by simp) with h5498 | h5498
                            · rcases p5474_3 (m.d 1 3) (by simp) with h5499 | h5499
                              · linarith only [h5250, h5499, hlam]
                              · linarith only [h3473, h5499, hlam]
                            · linarith only [h0, h5498, hlam]
                        · have p5474_0 := h5474c.1
                          have p5474_1 := h5474c.2.1
                          have p5474_2 := h5474c.2.2.1
                          have p5474_3 := h5474c.2.2.2
                          linarith only [h5248, hlam, p5474_0]
                        · have p5474_0 := h5474c.1
                          have p5474_1 := h5474c.2.1
                          have p5474_2 := h5474c.2.2.1
                          have p5474_3 := h5474c.2.2.2
                          linarith only [h3473, hc01, hc14, hlam, hphi, p5474_1]
                        · have p5474_0 := h5474c.1
                          have p5474_1 := h5474c.2.1
                          have p5474_2 := h5474c.2.2.1
                          have p5474_3 := h5474c.2.2.2
                          linarith only [hlam, p5474_0]
                        · have p5474_0 := h5474c.1
                          have p5474_1 := h5474c.2.1
                          have p5474_2 := h5474c.2.2.1
                          have p5474_3 := h5474c.2.2.2
                          linarith only [h4238, h5246, h5250, h5426, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p5474_1, u4ehi2]
                        · have p5474_0 := h5474c.1
                          have p5474_1 := h5474c.2.1
                          have p5474_2 := h5474c.2.2.1
                          have p5474_3 := h5474c.2.2.2
                          rcases p5474_3 (m.d 0 1) (by simp) with h5507 | h5507
                          · linarith only [h5507, hlam, p5474_0]
                          · rcases p5474_3 (m.d 1 2) (by simp) with h5509 | h5509
                            · rcases p5474_3 (m.d 1 3) (by simp) with h5510 | h5510
                              · linarith only [h5419, h5510, hlam]
                              · linarith only [h3473, h5510, hlam]
                            · linarith only [h0, h5509, hlam]
                        · have p5474_0 := h5474c.1
                          have p5474_1 := h5474c.2.1
                          have p5474_2 := h5474c.2.2.1
                          have p5474_3 := h5474c.2.2.2
                          linarith only [h5249, hlam, p5474_0]
                        · have p5474_0 := h5474c.1
                          have p5474_1 := h5474c.2.1
                          have p5474_2 := h5474c.2.2.1
                          have p5474_3 := h5474c.2.2.2
                          linarith only [h3473, hc01, hc15, hlam, hphi, p5474_1]
                        · have p5474_0 := h5474c.1
                          have p5474_1 := h5474c.2.1
                          have p5474_2 := h5474c.2.2.1
                          have p5474_3 := h5474c.2.2.2
                          linarith only [h5421, hlam, p5474_0]
                        · have p5474_0 := h5474c.1
                          have p5474_1 := h5474c.2.1
                          have p5474_2 := h5474c.2.2.1
                          have p5474_3 := h5474c.2.2.2
                          linarith only [hlam, p5474_0]
                      · linarith only [h4044, h5246, h5250, h5473, hlam]
              · linarith only [h4044, h5246, h5421, hlam]
        · linarith only [h0, h4337, h5249, hlam]
      · linarith only [h0, h4336, h5248, hlam]
    · linarith only [h0, h4335, h5247, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h5523 | h5523
    · rcases m.htr 1 2 4 (by decide) (by decide) with h5524 | h5524
      · rcases m.htr 1 2 5 (by decide) (by decide) with h5525 | h5525
        · rcases m.htr 1 3 4 (by decide) (by decide) with h5526 | h5526
          · rcases m.htr 1 3 5 (by decide) (by decide) with h5527 | h5527
            · rcases m.htr 1 4 5 (by decide) (by decide) with h5528 | h5528
              · rcases m.htr 2 3 4 (by decide) (by decide) with h5529 | h5529
                · linarith only [h4335, h4338, h5523, h5527, h5529, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h5531 | h5531
                  · linarith only [h4336, h4338, h5246, h5523, h5526, h5528, h5529, h5531, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5533 | h5533
                    · linarith only [h4336, h5246, h5533, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5535 | h5535
                      · linarith only [h5246, h5523, h5526, h5535, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                      · rcases h1bigk with h5537c | h5537c | h5537c | h5537c | h5537c | h5537c | h5537c | h5537c | h5537c | h5537c | h5537c | h5537c | h5537c | h5537c | h5537c | h5537c | h5537c | h5537c | h5537c | h5537c | h5537c | h5537c | h5537c | h5537c | h5537c
                        · have p5537_0 := h5537c.1
                          have p5537_1 := h5537c.2.1
                          have p5537_2 := h5537c.2.2.1
                          have p5537_3 := h5537c.2.2.2
                          linarith only [hlam, p5537_0]
                        · have p5537_0 := h5537c.1
                          have p5537_1 := h5537c.2.1
                          have p5537_2 := h5537c.2.2.1
                          have p5537_3 := h5537c.2.2.2
                          linarith only [h0, hlam, p5537_0]
                        · have p5537_0 := h5537c.1
                          have p5537_1 := h5537c.2.1
                          have p5537_2 := h5537c.2.2.1
                          have p5537_3 := h5537c.2.2.2
                          linarith only [h3473, hlam, p5537_0]
                        · have p5537_0 := h5537c.1
                          have p5537_1 := h5537c.2.1
                          have p5537_2 := h5537c.2.2.1
                          have p5537_3 := h5537c.2.2.2
                          linarith only [h4044, hlam, p5537_0]
                        · have p5537_0 := h5537c.1
                          have p5537_1 := h5537c.2.1
                          have p5537_2 := h5537c.2.2.1
                          have p5537_3 := h5537c.2.2.2
                          linarith only [h4238, hlam, p5537_0]
                        · have p5537_0 := h5537c.1
                          have p5537_1 := h5537c.2.1
                          have p5537_2 := h5537c.2.2.1
                          have p5537_3 := h5537c.2.2.2
                          rcases p5537_3 (m.d 0 1) (by simp) with h5543 | h5543
                          · linarith only [h5543, hlam, p5537_0]
                          · rcases p5537_3 (m.d 1 2) (by simp) with h5545 | h5545
                            · rcases p5537_3 (m.d 1 3) (by simp) with h5546 | h5546
                              · linarith only [h5523, h5546, hlam]
                              · linarith only [h3473, h5546, hlam]
                            · linarith only [h5545, hlam, p5537_0]
                        · have p5537_0 := h5537c.1
                          have p5537_1 := h5537c.2.1
                          have p5537_2 := h5537c.2.2.1
                          have p5537_3 := h5537c.2.2.2
                          linarith only [hlam, p5537_0]
                        · have p5537_0 := h5537c.1
                          have p5537_1 := h5537c.2.1
                          have p5537_2 := h5537c.2.2.1
                          have p5537_3 := h5537c.2.2.2
                          linarith only [h3473, hc01, hc12, hlam, hphi, p5537_1]
                        · have p5537_0 := h5537c.1
                          have p5537_1 := h5537c.2.1
                          have p5537_2 := h5537c.2.2.1
                          have p5537_3 := h5537c.2.2.2
                          linarith only [h4044, hc01, hc12, hlam, hphi, p5537_1]
                        · have p5537_0 := h5537c.1
                          have p5537_1 := h5537c.2.1
                          have p5537_2 := h5537c.2.2.1
                          have p5537_3 := h5537c.2.2.2
                          linarith only [h4336, h5246, h5528, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5537_1, u4ehi2]
                        · have p5537_0 := h5537c.1
                          have p5537_1 := h5537c.2.1
                          have p5537_2 := h5537c.2.2.1
                          have p5537_3 := h5537c.2.2.2
                          rcases p5537_3 (m.d 0 1) (by simp) with h5554 | h5554
                          · linarith only [h5554, hlam, p5537_0]
                          · rcases p5537_3 (m.d 1 2) (by simp) with h5556 | h5556
                            · rcases p5537_3 (m.d 1 3) (by simp) with h5557 | h5557
                              · rcases p5537_3 (m.d 1 4) (by simp) with h5558 | h5558
                                · linarith only [h5526, h5558, hlam]
                                · linarith only [h4044, h5558, hlam]
                              · linarith only [h5557, hlam, p5537_0]
                            · linarith only [h0, h5556, hlam]
                        · have p5537_0 := h5537c.1
                          have p5537_1 := h5537c.2.1
                          have p5537_2 := h5537c.2.2.1
                          have p5537_3 := h5537c.2.2.2
                          linarith only [h5523, hlam, p5537_0]
                        · have p5537_0 := h5537c.1
                          have p5537_1 := h5537c.2.1
                          have p5537_2 := h5537c.2.2.1
                          have p5537_3 := h5537c.2.2.2
                          linarith only [hlam, p5537_0]
                        · have p5537_0 := h5537c.1
                          have p5537_1 := h5537c.2.1
                          have p5537_2 := h5537c.2.2.1
                          have p5537_3 := h5537c.2.2.2
                          linarith only [h4336, h5246, h5528, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p5537_1, u4ehi2]
                        · have p5537_0 := h5537c.1
                          have p5537_1 := h5537c.2.1
                          have p5537_2 := h5537c.2.2.1
                          have p5537_3 := h5537c.2.2.2
                          linarith only [h4336, h5246, h5523, h5528, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5537_1, u4ehi2]
                        · have p5537_0 := h5537c.1
                          have p5537_1 := h5537c.2.1
                          have p5537_2 := h5537c.2.2.1
                          have p5537_3 := h5537c.2.2.2
                          rcases p5537_3 (m.d 0 1) (by simp) with h5567 | h5567
                          · linarith only [h5567, hlam, p5537_0]
                          · rcases p5537_3 (m.d 1 2) (by simp) with h5569 | h5569
                            · rcases p5537_3 (m.d 1 3) (by simp) with h5570 | h5570
                              · rcases p5537_3 (m.d 1 4) (by simp) with h5571 | h5571
                                · rcases p5537_3 (m.d 1 5) (by simp) with h5572 | h5572
                                  · linarith only [h5528, h5572, hlam]
                                  · linarith only [h4238, h5572, hlam]
                                · linarith only [h5571, hlam, p5537_0]
                              · linarith only [h3473, h5570, hlam]
                            · linarith only [h0, h5569, hlam]
                        · have p5537_0 := h5537c.1
                          have p5537_1 := h5537c.2.1
                          have p5537_2 := h5537c.2.2.1
                          have p5537_3 := h5537c.2.2.2
                          linarith only [h5524, hlam, p5537_0]
                        · have p5537_0 := h5537c.1
                          have p5537_1 := h5537c.2.1
                          have p5537_2 := h5537c.2.2.1
                          have p5537_3 := h5537c.2.2.2
                          linarith only [h5526, hlam, p5537_1]
                        · have p5537_0 := h5537c.1
                          have p5537_1 := h5537c.2.1
                          have p5537_2 := h5537c.2.2.1
                          have p5537_3 := h5537c.2.2.2
                          linarith only [hlam, p5537_0]
                        · have p5537_0 := h5537c.1
                          have p5537_1 := h5537c.2.1
                          have p5537_2 := h5537c.2.2.1
                          have p5537_3 := h5537c.2.2.2
                          linarith only [h4336, h5246, h5528, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p5537_1, u4ehi2]
                        · have p5537_0 := h5537c.1
                          have p5537_1 := h5537c.2.1
                          have p5537_2 := h5537c.2.2.1
                          have p5537_3 := h5537c.2.2.2
                          rcases p5537_3 (m.d 0 1) (by simp) with h5582 | h5582
                          · linarith only [h5582, hlam, p5537_0]
                          · rcases p5537_3 (m.d 1 2) (by simp) with h5584 | h5584
                            · rcases p5537_3 (m.d 1 3) (by simp) with h5585 | h5585
                              · rcases p5537_3 (m.d 1 4) (by simp) with h5586 | h5586
                                · rcases p5537_3 (m.d 1 5) (by simp) with h5587 | h5587
                                  · rcases h2bigk with h5588c | h5588c | h5588c | h5588c | h5588c | h5588c | h5588c | h5588c | h5588c | h5588c | h5588c | h5588c | h5588c | h5588c | h5588c | h5588c | h5588c | h5588c | h5588c | h5588c | h5588c | h5588c | h5588c | h5588c | h5588c
                                    · have p5588_0 := h5588c.1
                                      have p5588_1 := h5588c.2.1
                                      have p5588_2 := h5588c.2.2.1
                                      have p5588_3 := h5588c.2.2.2
                                      linarith only [hlam, p5588_0]
                                    · have p5588_0 := h5588c.1
                                      have p5588_1 := h5588c.2.1
                                      have p5588_2 := h5588c.2.2.1
                                      have p5588_3 := h5588c.2.2.2
                                      linarith only [h0, hlam, p5588_0]
                                    · have p5588_0 := h5588c.1
                                      have p5588_1 := h5588c.2.1
                                      have p5588_2 := h5588c.2.2.1
                                      have p5588_3 := h5588c.2.2.2
                                      rcases p5588_3 (m.d 0 2) (by simp) with h5591 | h5591
                                      · rcases p5588_3 (m.d 1 2) (by simp) with h5592 | h5592
                                        · rcases p5588_3 (m.d 2 3) (by simp) with h5593 | h5593
                                          · linarith only [h5593, hlam, p5588_0]
                                          · rcases p5588_3 (m.d 2 4) (by simp) with h5595 | h5595
                                            · linarith only [h4336, h5595, hlam]
                                            · linarith only [h5529, h5595, hlam]
                                        · linarith only [h5523, h5592, hlam]
                                      · linarith only [h5591, hlam, p5588_0]
                                    · have p5588_0 := h5588c.1
                                      have p5588_1 := h5588c.2.1
                                      have p5588_2 := h5588c.2.2.1
                                      have p5588_3 := h5588c.2.2.2
                                      rcases p5588_3 (m.d 0 2) (by simp) with h5600 | h5600
                                      · rcases p5588_3 (m.d 1 2) (by simp) with h5601 | h5601
                                        · rcases p5588_3 (m.d 2 3) (by simp) with h5602 | h5602
                                          · linarith only [h4335, h5602, hlam]
                                          · rcases p5588_3 (m.d 2 4) (by simp) with h5604 | h5604
                                            · linarith only [h5604, hlam, p5588_0]
                                            · rcases p5588_3 (m.d 2 5) (by simp) with h5606 | h5606
                                              · linarith only [h4337, h5606, hlam]
                                              · linarith only [h5533, h5606, hlam]
                                        · linarith only [h5524, h5601, hlam]
                                      · linarith only [h5600, hlam, p5588_0]
                                    · have p5588_0 := h5588c.1
                                      have p5588_1 := h5588c.2.1
                                      have p5588_2 := h5588c.2.2.1
                                      have p5588_3 := h5588c.2.2.2
                                      rcases p5588_3 (m.d 0 2) (by simp) with h5611 | h5611
                                      · rcases p5588_3 (m.d 1 2) (by simp) with h5612 | h5612
                                        · rcases p5588_3 (m.d 2 3) (by simp) with h5613 | h5613
                                          · linarith only [h4335, h5613, hlam]
                                          · rcases p5588_3 (m.d 2 4) (by simp) with h5615 | h5615
                                            · linarith only [h4336, h5615, hlam]
                                            · rcases p5588_3 (m.d 2 5) (by simp) with h5617 | h5617
                                              · linarith only [h5617, hlam, p5588_0]
                                              · rcases h5bigk with h5619c | h5619c | h5619c | h5619c | h5619c | h5619c | h5619c | h5619c | h5619c | h5619c | h5619c | h5619c | h5619c | h5619c | h5619c | h5619c | h5619c | h5619c | h5619c | h5619c | h5619c | h5619c | h5619c | h5619c | h5619c
                                                · have p5619_0 := h5619c.1
                                                  have p5619_1 := h5619c.2.1
                                                  have p5619_2 := h5619c.2.2.1
                                                  have p5619_3 := h5619c.2.2.2
                                                  linarith only [hlam, p5619_0]
                                                · have p5619_0 := h5619c.1
                                                  have p5619_1 := h5619c.2.1
                                                  have p5619_2 := h5619c.2.2.1
                                                  have p5619_3 := h5619c.2.2.2
                                                  linarith only [h4238, hlam, p5619_1]
                                                · have p5619_0 := h5619c.1
                                                  have p5619_1 := h5619c.2.1
                                                  have p5619_2 := h5619c.2.2.1
                                                  have p5619_3 := h5619c.2.2.2
                                                  linarith only [h4338, h5523, h5527, hc12, hlam, hphi, ht01, ht0b, ht5b, p5619_1, u5ehi2]
                                                · have p5619_0 := h5619c.1
                                                  have p5619_1 := h5619c.2.1
                                                  have p5619_2 := h5619c.2.2.1
                                                  have p5619_3 := h5619c.2.2.2
                                                  linarith only [h4338, hlam, p5619_0]
                                                · have p5619_0 := h5619c.1
                                                  have p5619_1 := h5619c.2.1
                                                  have p5619_2 := h5619c.2.2.1
                                                  have p5619_3 := h5619c.2.2.2
                                                  linarith only [h5246, hlam, p5619_0]
                                                · have p5619_0 := h5619c.1
                                                  have p5619_1 := h5619c.2.1
                                                  have p5619_2 := h5619c.2.2.1
                                                  have p5619_3 := h5619c.2.2.2
                                                  rcases p5619_3 (m.d 0 5) (by simp) with h5625 | h5625
                                                  · linarith only [h4238, h5625, hlam]
                                                  · rcases p5619_3 (m.d 1 5) (by simp) with h5627 | h5627
                                                    · rcases p5619_3 (m.d 2 5) (by simp) with h5628 | h5628
                                                      · linarith only [h5525, h5628, hlam]
                                                      · rcases p5619_3 (m.d 3 5) (by simp) with h5630 | h5630
                                                        · linarith only [h5527, h5630, hlam]
                                                        · linarith only [h4338, h5630, hlam]
                                                    · linarith only [h4238, h5627, hlam]
                                                · have p5619_0 := h5619c.1
                                                  have p5619_1 := h5619c.2.1
                                                  have p5619_2 := h5619c.2.2.1
                                                  have p5619_3 := h5619c.2.2.2
                                                  linarith only [hlam, p5619_0]
                                                · have p5619_0 := h5619c.1
                                                  have p5619_1 := h5619c.2.1
                                                  have p5619_2 := h5619c.2.2.1
                                                  have p5619_3 := h5619c.2.2.2
                                                  rcases p5619_3 (m.d 0 5) (by simp) with h5635 | h5635
                                                  · linarith only [h4238, h5635, hlam]
                                                  · linarith only [h4337, h5635, hlam]
                                                · have p5619_0 := h5619c.1
                                                  have p5619_1 := h5619c.2.1
                                                  have p5619_2 := h5619c.2.2.1
                                                  have p5619_3 := h5619c.2.2.2
                                                  linarith only [h3473, h4338, h5523, h5526, h5528, hc01, hc12, hlam, hphi, p5619_1]
                                                · have p5619_0 := h5619c.1
                                                  have p5619_1 := h5619c.2.1
                                                  have p5619_2 := h5619c.2.2.1
                                                  have p5619_3 := h5619c.2.2.2
                                                  linarith only [h5523, h5526, h5528, h5529, h5535, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5619_1]
                                                · have p5619_0 := h5619c.1
                                                  have p5619_1 := h5619c.2.1
                                                  have p5619_2 := h5619c.2.2.1
                                                  have p5619_3 := h5619c.2.2.2
                                                  linarith only [h4337, hlam, p5619_1]
                                                · have p5619_0 := h5619c.1
                                                  have p5619_1 := h5619c.2.1
                                                  have p5619_2 := h5619c.2.2.1
                                                  have p5619_3 := h5619c.2.2.2
                                                  linarith only [h5525, hlam, p5619_1]
                                                · have p5619_0 := h5619c.1
                                                  have p5619_1 := h5619c.2.1
                                                  have p5619_2 := h5619c.2.2.1
                                                  have p5619_3 := h5619c.2.2.2
                                                  linarith only [hlam, p5619_0]
                                                · have p5619_0 := h5619c.1
                                                  have p5619_1 := h5619c.2.1
                                                  have p5619_2 := h5619c.2.2.1
                                                  have p5619_3 := h5619c.2.2.2
                                                  linarith only [h5531, hlam, p5619_1]
                                                · have p5619_0 := h5619c.1
                                                  have p5619_1 := h5619c.2.1
                                                  have p5619_2 := h5619c.2.2.1
                                                  have p5619_3 := h5619c.2.2.2
                                                  linarith only [h5533, hlam, p5619_0]
                                                · have p5619_0 := h5619c.1
                                                  have p5619_1 := h5619c.2.1
                                                  have p5619_2 := h5619c.2.2.1
                                                  have p5619_3 := h5619c.2.2.2
                                                  linarith only [h4337, h5523, h5527, h5533, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5619_1, u4ehi2]
                                                · have p5619_0 := h5619c.1
                                                  have p5619_1 := h5619c.2.1
                                                  have p5619_2 := h5619c.2.2.1
                                                  have p5619_3 := h5619c.2.2.2
                                                  linarith only [h5527, hlam, p5619_1]
                                                · have p5619_0 := h5619c.1
                                                  have p5619_1 := h5619c.2.1
                                                  have p5619_2 := h5619c.2.2.1
                                                  have p5619_3 := h5619c.2.2.2
                                                  linarith only [h5523, h5527, h5533, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5619_1, u4ehi2]
                                                · have p5619_0 := h5619c.1
                                                  have p5619_1 := h5619c.2.1
                                                  have p5619_2 := h5619c.2.2.1
                                                  have p5619_3 := h5619c.2.2.2
                                                  linarith only [hlam, p5619_0]
                                                · have p5619_0 := h5619c.1
                                                  have p5619_1 := h5619c.2.1
                                                  have p5619_2 := h5619c.2.2.1
                                                  have p5619_3 := h5619c.2.2.2
                                                  linarith only [h5535, hlam, p5619_0]
                                                · have p5619_0 := h5619c.1
                                                  have p5619_1 := h5619c.2.1
                                                  have p5619_2 := h5619c.2.2.1
                                                  have p5619_3 := h5619c.2.2.2
                                                  linarith only [h4337, h5533, hc45, hlam, hphi, p5619_1, u4ehi2]
                                                · have p5619_0 := h5619c.1
                                                  have p5619_1 := h5619c.2.1
                                                  have p5619_2 := h5619c.2.2.1
                                                  have p5619_3 := h5619c.2.2.2
                                                  linarith only [h5528, hlam, p5619_1]
                                                · have p5619_0 := h5619c.1
                                                  have p5619_1 := h5619c.2.1
                                                  have p5619_2 := h5619c.2.2.1
                                                  have p5619_3 := h5619c.2.2.2
                                                  linarith only [h5523, h5526, h5528, h5533, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5619_1, u4ehi2]
                                                · have p5619_0 := h5619c.1
                                                  have p5619_1 := h5619c.2.1
                                                  have p5619_2 := h5619c.2.2.1
                                                  have p5619_3 := h5619c.2.2.2
                                                  linarith only [h5523, h5526, h5528, hc12, hlam, hphi, ht01, ht0b, ht5b, p5619_1, u5ehi3]
                                                · have p5619_0 := h5619c.1
                                                  have p5619_1 := h5619c.2.1
                                                  have p5619_2 := h5619c.2.2.1
                                                  have p5619_3 := h5619c.2.2.2
                                                  linarith only [hlam, p5619_0]
                                        · linarith only [h5525, h5612, hlam]
                                      · linarith only [h5611, hlam, p5588_0]
                                    · have p5588_0 := h5588c.1
                                      have p5588_1 := h5588c.2.1
                                      have p5588_2 := h5588c.2.2.1
                                      have p5588_3 := h5588c.2.2.2
                                      linarith only [h4336, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5588_1, u4ehi2]
                                    · have p5588_0 := h5588c.1
                                      have p5588_1 := h5588c.2.1
                                      have p5588_2 := h5588c.2.2.1
                                      have p5588_3 := h5588c.2.2.2
                                      linarith only [hlam, p5588_0]
                                    · have p5588_0 := h5588c.1
                                      have p5588_1 := h5588c.2.1
                                      have p5588_2 := h5588c.2.2.1
                                      have p5588_3 := h5588c.2.2.2
                                      linarith only [h5523, h5526, h5528, h5529, h5535, hlam, p5588_2]
                                    · have p5588_0 := h5588c.1
                                      have p5588_1 := h5588c.2.1
                                      have p5588_2 := h5588c.2.2.1
                                      have p5588_3 := h5588c.2.2.2
                                      rcases p5588_3 (m.d 0 2) (by simp) with h5660 | h5660
                                      · linarith only [h0, h5660, hlam]
                                      · linarith only [h4336, h5660, hlam]
                                    · have p5588_0 := h5588c.1
                                      have p5588_1 := h5588c.2.1
                                      have p5588_2 := h5588c.2.2.1
                                      have p5588_3 := h5588c.2.2.2
                                      rcases p5588_3 (m.d 0 2) (by simp) with h5663 | h5663
                                      · linarith only [h0, h5663, hlam]
                                      · linarith only [h4337, h5663, hlam]
                                    · have p5588_0 := h5588c.1
                                      have p5588_1 := h5588c.2.1
                                      have p5588_2 := h5588c.2.2.1
                                      have p5588_3 := h5588c.2.2.2
                                      linarith only [h4335, hlam, p5588_0]
                                    · have p5588_0 := h5588c.1
                                      have p5588_1 := h5588c.2.1
                                      have p5588_2 := h5588c.2.2.1
                                      have p5588_3 := h5588c.2.2.2
                                      linarith only [h5523, hlam, p5588_0]
                                    · have p5588_0 := h5588c.1
                                      have p5588_1 := h5588c.2.1
                                      have p5588_2 := h5588c.2.2.1
                                      have p5588_3 := h5588c.2.2.2
                                      linarith only [hlam, p5588_0]
                                    · have p5588_0 := h5588c.1
                                      have p5588_1 := h5588c.2.1
                                      have p5588_2 := h5588c.2.2.1
                                      have p5588_3 := h5588c.2.2.2
                                      linarith only [h5529, hlam, p5588_1]
                                    · have p5588_0 := h5588c.1
                                      have p5588_1 := h5588c.2.1
                                      have p5588_2 := h5588c.2.2.1
                                      have p5588_3 := h5588c.2.2.2
                                      linarith only [h5531, hlam, p5588_1]
                                    · have p5588_0 := h5588c.1
                                      have p5588_1 := h5588c.2.1
                                      have p5588_2 := h5588c.2.2.1
                                      have p5588_3 := h5588c.2.2.2
                                      linarith only [h4336, hlam, p5588_0]
                                    · have p5588_0 := h5588c.1
                                      have p5588_1 := h5588c.2.1
                                      have p5588_2 := h5588c.2.2.1
                                      have p5588_3 := h5588c.2.2.2
                                      linarith only [h5524, hlam, p5588_0]
                                    · have p5588_0 := h5588c.1
                                      have p5588_1 := h5588c.2.1
                                      have p5588_2 := h5588c.2.2.1
                                      have p5588_3 := h5588c.2.2.2
                                      linarith only [h4336, h5246, h5523, h5526, h5528, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5588_1]
                                    · have p5588_0 := h5588c.1
                                      have p5588_1 := h5588c.2.1
                                      have p5588_2 := h5588c.2.2.1
                                      have p5588_3 := h5588c.2.2.2
                                      linarith only [hlam, p5588_0]
                                    · have p5588_0 := h5588c.1
                                      have p5588_1 := h5588c.2.1
                                      have p5588_2 := h5588c.2.2.1
                                      have p5588_3 := h5588c.2.2.2
                                      linarith only [h5533, hlam, p5588_0]
                                    · have p5588_0 := h5588c.1
                                      have p5588_1 := h5588c.2.1
                                      have p5588_2 := h5588c.2.2.1
                                      have p5588_3 := h5588c.2.2.2
                                      linarith only [h4337, hlam, p5588_0]
                                    · have p5588_0 := h5588c.1
                                      have p5588_1 := h5588c.2.1
                                      have p5588_2 := h5588c.2.2.1
                                      have p5588_3 := h5588c.2.2.2
                                      linarith only [h5525, hlam, p5588_0]
                                    · have p5588_0 := h5588c.1
                                      have p5588_1 := h5588c.2.1
                                      have p5588_2 := h5588c.2.2.1
                                      have p5588_3 := h5588c.2.2.2
                                      rcases p5588_3 (m.d 0 2) (by simp) with h5678 | h5678
                                      · rcases p5588_3 (m.d 1 2) (by simp) with h5679 | h5679
                                        · rcases p5588_3 (m.d 2 3) (by simp) with h5680 | h5680
                                          · linarith only [h5531, h5680, hlam]
                                          · rcases p5588_3 (m.d 2 4) (by simp) with h5682 | h5682
                                            · linarith only [h5533, h5682, hlam]
                                            · linarith only [h5529, h5682, hlam]
                                        · linarith only [h5523, h5679, hlam]
                                      · linarith only [h4335, h5678, hlam]
                                    · have p5588_0 := h5588c.1
                                      have p5588_1 := h5588c.2.1
                                      have p5588_2 := h5588c.2.2.1
                                      have p5588_3 := h5588c.2.2.2
                                      linarith only [h4337, hc02, hlam, hphi, ht0b, ht45, ht5b, p5588_1, u4ehi2]
                                    · have p5588_0 := h5588c.1
                                      have p5588_1 := h5588c.2.1
                                      have p5588_2 := h5588c.2.2.1
                                      have p5588_3 := h5588c.2.2.2
                                      linarith only [hlam, p5588_0]
                                  · linarith only [h5587, hlam, p5537_0]
                                · linarith only [h4044, h5586, hlam]
                              · linarith only [h3473, h5585, hlam]
                            · linarith only [h0, h5584, hlam]
                        · have p5537_0 := h5537c.1
                          have p5537_1 := h5537c.2.1
                          have p5537_2 := h5537c.2.2.1
                          have p5537_3 := h5537c.2.2.2
                          linarith only [h5525, hlam, p5537_0]
                        · have p5537_0 := h5537c.1
                          have p5537_1 := h5537c.2.1
                          have p5537_2 := h5537c.2.2.1
                          have p5537_3 := h5537c.2.2.2
                          linarith only [h5527, hlam, p5537_0]
                        · have p5537_0 := h5537c.1
                          have p5537_1 := h5537c.2.1
                          have p5537_2 := h5537c.2.2.1
                          have p5537_3 := h5537c.2.2.2
                          linarith only [h5528, hlam, p5537_0]
                        · have p5537_0 := h5537c.1
                          have p5537_1 := h5537c.2.1
                          have p5537_2 := h5537c.2.2.1
                          have p5537_3 := h5537c.2.2.2
                          linarith only [hlam, p5537_0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h5697 | h5697
                · linarith only [h4335, h4338, h5523, h5527, h5697, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h5699 | h5699
                  · linarith only [h4338, h5697, h5699, hc03, hc34, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5701 | h5701
                    · linarith only [h0, h4238, h4336, h5528, h5701, hc01, hc12, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5703 | h5703
                      · linarith only [h5526, h5528, h5703, hlam]
                      · rcases h1bigk with h5705c | h5705c | h5705c | h5705c | h5705c | h5705c | h5705c | h5705c | h5705c | h5705c | h5705c | h5705c | h5705c | h5705c | h5705c | h5705c | h5705c | h5705c | h5705c | h5705c | h5705c | h5705c | h5705c | h5705c | h5705c
                        · have p5705_0 := h5705c.1
                          have p5705_1 := h5705c.2.1
                          have p5705_2 := h5705c.2.2.1
                          have p5705_3 := h5705c.2.2.2
                          linarith only [hlam, p5705_0]
                        · have p5705_0 := h5705c.1
                          have p5705_1 := h5705c.2.1
                          have p5705_2 := h5705c.2.2.1
                          have p5705_3 := h5705c.2.2.2
                          linarith only [h0, hlam, p5705_0]
                        · have p5705_0 := h5705c.1
                          have p5705_1 := h5705c.2.1
                          have p5705_2 := h5705c.2.2.1
                          have p5705_3 := h5705c.2.2.2
                          linarith only [h3473, hlam, p5705_0]
                        · have p5705_0 := h5705c.1
                          have p5705_1 := h5705c.2.1
                          have p5705_2 := h5705c.2.2.1
                          have p5705_3 := h5705c.2.2.2
                          linarith only [h4044, hlam, p5705_0]
                        · have p5705_0 := h5705c.1
                          have p5705_1 := h5705c.2.1
                          have p5705_2 := h5705c.2.2.1
                          have p5705_3 := h5705c.2.2.2
                          linarith only [h4238, hlam, p5705_0]
                        · have p5705_0 := h5705c.1
                          have p5705_1 := h5705c.2.1
                          have p5705_2 := h5705c.2.2.1
                          have p5705_3 := h5705c.2.2.2
                          rcases p5705_3 (m.d 0 1) (by simp) with h5711 | h5711
                          · linarith only [h5711, hlam, p5705_0]
                          · rcases p5705_3 (m.d 1 2) (by simp) with h5713 | h5713
                            · rcases p5705_3 (m.d 1 3) (by simp) with h5714 | h5714
                              · linarith only [h5523, h5714, hlam]
                              · linarith only [h3473, h5714, hlam]
                            · linarith only [h5713, hlam, p5705_0]
                        · have p5705_0 := h5705c.1
                          have p5705_1 := h5705c.2.1
                          have p5705_2 := h5705c.2.2.1
                          have p5705_3 := h5705c.2.2.2
                          linarith only [hlam, p5705_0]
                        · have p5705_0 := h5705c.1
                          have p5705_1 := h5705c.2.1
                          have p5705_2 := h5705c.2.2.1
                          have p5705_3 := h5705c.2.2.2
                          linarith only [h3473, hc01, hc12, hlam, hphi, p5705_1]
                        · have p5705_0 := h5705c.1
                          have p5705_1 := h5705c.2.1
                          have p5705_2 := h5705c.2.2.1
                          have p5705_3 := h5705c.2.2.2
                          linarith only [h4044, hc01, hc12, hlam, hphi, p5705_1]
                        · have p5705_0 := h5705c.1
                          have p5705_1 := h5705c.2.1
                          have p5705_2 := h5705c.2.2.1
                          have p5705_3 := h5705c.2.2.2
                          linarith only [h3473, h4338, h5527, hc01, hc12, hlam, hphi, p5705_1]
                        · have p5705_0 := h5705c.1
                          have p5705_1 := h5705c.2.1
                          have p5705_2 := h5705c.2.2.1
                          have p5705_3 := h5705c.2.2.2
                          rcases p5705_3 (m.d 0 1) (by simp) with h5722 | h5722
                          · linarith only [h5722, hlam, p5705_0]
                          · rcases p5705_3 (m.d 1 2) (by simp) with h5724 | h5724
                            · rcases p5705_3 (m.d 1 3) (by simp) with h5725 | h5725
                              · rcases p5705_3 (m.d 1 4) (by simp) with h5726 | h5726
                                · linarith only [h5526, h5726, hlam]
                                · linarith only [h4044, h5726, hlam]
                              · linarith only [h5725, hlam, p5705_0]
                            · linarith only [h0, h5724, hlam]
                        · have p5705_0 := h5705c.1
                          have p5705_1 := h5705c.2.1
                          have p5705_2 := h5705c.2.2.1
                          have p5705_3 := h5705c.2.2.2
                          linarith only [h5523, hlam, p5705_0]
                        · have p5705_0 := h5705c.1
                          have p5705_1 := h5705c.2.1
                          have p5705_2 := h5705c.2.2.1
                          have p5705_3 := h5705c.2.2.2
                          linarith only [hlam, p5705_0]
                        · have p5705_0 := h5705c.1
                          have p5705_1 := h5705c.2.1
                          have p5705_2 := h5705c.2.2.1
                          have p5705_3 := h5705c.2.2.2
                          linarith only [h4044, hc01, hc13, hlam, hphi, p5705_1]
                        · have p5705_0 := h5705c.1
                          have p5705_1 := h5705c.2.1
                          have p5705_2 := h5705c.2.2.1
                          have p5705_3 := h5705c.2.2.2
                          linarith only [h3473, h4338, h5523, h5527, hc01, hc12, hlam, hphi, p5705_1]
                        · have p5705_0 := h5705c.1
                          have p5705_1 := h5705c.2.1
                          have p5705_2 := h5705c.2.2.1
                          have p5705_3 := h5705c.2.2.2
                          linarith only [h5528, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5705_1]
                        · have p5705_0 := h5705c.1
                          have p5705_1 := h5705c.2.1
                          have p5705_2 := h5705c.2.2.1
                          have p5705_3 := h5705c.2.2.2
                          linarith only [h5524, hlam, p5705_0]
                        · have p5705_0 := h5705c.1
                          have p5705_1 := h5705c.2.1
                          have p5705_2 := h5705c.2.2.1
                          have p5705_3 := h5705c.2.2.2
                          linarith only [h5526, hlam, p5705_1]
                        · have p5705_0 := h5705c.1
                          have p5705_1 := h5705c.2.1
                          have p5705_2 := h5705c.2.2.1
                          have p5705_3 := h5705c.2.2.2
                          linarith only [hlam, p5705_0]
                        · have p5705_0 := h5705c.1
                          have p5705_1 := h5705c.2.1
                          have p5705_2 := h5705c.2.2.1
                          have p5705_3 := h5705c.2.2.2
                          linarith only [h5528, hlam, p5705_1]
                        · have p5705_0 := h5705c.1
                          have p5705_1 := h5705c.2.1
                          have p5705_2 := h5705c.2.2.1
                          have p5705_3 := h5705c.2.2.2
                          rcases p5705_3 (m.d 0 1) (by simp) with h5740 | h5740
                          · linarith only [h5740, hlam, p5705_0]
                          · rcases p5705_3 (m.d 1 2) (by simp) with h5742 | h5742
                            · rcases p5705_3 (m.d 1 3) (by simp) with h5743 | h5743
                              · rcases p5705_3 (m.d 1 4) (by simp) with h5744 | h5744
                                · linarith only [h5528, h5744, hlam]
                                · linarith only [h4044, h5744, hlam]
                              · linarith only [h3473, h5743, hlam]
                            · linarith only [h0, h5742, hlam]
                        · have p5705_0 := h5705c.1
                          have p5705_1 := h5705c.2.1
                          have p5705_2 := h5705c.2.2.1
                          have p5705_3 := h5705c.2.2.2
                          linarith only [h5525, hlam, p5705_0]
                        · have p5705_0 := h5705c.1
                          have p5705_1 := h5705c.2.1
                          have p5705_2 := h5705c.2.2.1
                          have p5705_3 := h5705c.2.2.2
                          linarith only [h5527, hlam, p5705_0]
                        · have p5705_0 := h5705c.1
                          have p5705_1 := h5705c.2.1
                          have p5705_2 := h5705c.2.2.1
                          have p5705_3 := h5705c.2.2.2
                          linarith only [h4044, hc01, hc15, hlam, hphi, p5705_1]
                        · have p5705_0 := h5705c.1
                          have p5705_1 := h5705c.2.1
                          have p5705_2 := h5705c.2.2.1
                          have p5705_3 := h5705c.2.2.2
                          linarith only [hlam, p5705_0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h5753 | h5753
              · linarith only [h5246, h5526, h5527, h5753, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h5755 | h5755
                · rcases m.htr 2 3 5 (by decide) (by decide) with h5756 | h5756
                  · linarith only [h3473, h5527, h5756, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5758 | h5758
                    · linarith only [h4044, h5753, h5758, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5760 | h5760
                      · linarith only [h4044, h4335, h5753, h5755, h5760, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                      · linarith only [h3473, h4335, h5527, h5755, h5760, hc45, hlam, hphi, u4ehi3]
                · linarith only [h5526, h5527, h5755, hc23, hc35, hlam, hphi]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h5764 | h5764
            · linarith only [h4338, h5526, h5764, hc03, hc34, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h5766 | h5766
              · rcases m.htr 2 3 4 (by decide) (by decide) with h5767 | h5767
                · linarith only [h5246, h5526, h5766, h5767, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h5769 | h5769
                  · linarith only [h3473, h4336, h5246, h5526, h5764, h5766, h5767, h5769, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5771 | h5771
                    · linarith only [h4336, h5246, h5771, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5773 | h5773
                      · rcases h1bigk with h5774c | h5774c | h5774c | h5774c | h5774c | h5774c | h5774c | h5774c | h5774c | h5774c | h5774c | h5774c | h5774c | h5774c | h5774c | h5774c | h5774c | h5774c | h5774c | h5774c | h5774c | h5774c | h5774c | h5774c | h5774c
                        · have p5774_0 := h5774c.1
                          have p5774_1 := h5774c.2.1
                          have p5774_2 := h5774c.2.2.1
                          have p5774_3 := h5774c.2.2.2
                          linarith only [hlam, p5774_0]
                        · have p5774_0 := h5774c.1
                          have p5774_1 := h5774c.2.1
                          have p5774_2 := h5774c.2.2.1
                          have p5774_3 := h5774c.2.2.2
                          linarith only [h0, hlam, p5774_0]
                        · have p5774_0 := h5774c.1
                          have p5774_1 := h5774c.2.1
                          have p5774_2 := h5774c.2.2.1
                          have p5774_3 := h5774c.2.2.2
                          linarith only [h3473, hlam, p5774_0]
                        · have p5774_0 := h5774c.1
                          have p5774_1 := h5774c.2.1
                          have p5774_2 := h5774c.2.2.1
                          have p5774_3 := h5774c.2.2.2
                          linarith only [h4044, hlam, p5774_0]
                        · have p5774_0 := h5774c.1
                          have p5774_1 := h5774c.2.1
                          have p5774_2 := h5774c.2.2.1
                          have p5774_3 := h5774c.2.2.2
                          linarith only [h4238, hlam, p5774_0]
                        · have p5774_0 := h5774c.1
                          have p5774_1 := h5774c.2.1
                          have p5774_2 := h5774c.2.2.1
                          have p5774_3 := h5774c.2.2.2
                          rcases p5774_3 (m.d 0 1) (by simp) with h5780 | h5780
                          · linarith only [h5780, hlam, p5774_0]
                          · rcases p5774_3 (m.d 1 2) (by simp) with h5782 | h5782
                            · rcases p5774_3 (m.d 1 3) (by simp) with h5783 | h5783
                              · linarith only [h5523, h5783, hlam]
                              · linarith only [h3473, h5783, hlam]
                            · linarith only [h5782, hlam, p5774_0]
                        · have p5774_0 := h5774c.1
                          have p5774_1 := h5774c.2.1
                          have p5774_2 := h5774c.2.2.1
                          have p5774_3 := h5774c.2.2.2
                          linarith only [hlam, p5774_0]
                        · have p5774_0 := h5774c.1
                          have p5774_1 := h5774c.2.1
                          have p5774_2 := h5774c.2.2.1
                          have p5774_3 := h5774c.2.2.2
                          linarith only [h3473, hc01, hc12, hlam, hphi, p5774_1]
                        · have p5774_0 := h5774c.1
                          have p5774_1 := h5774c.2.1
                          have p5774_2 := h5774c.2.2.1
                          have p5774_3 := h5774c.2.2.2
                          linarith only [h4336, h5246, h5766, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5774_1, u4ehi2]
                        · have p5774_0 := h5774c.1
                          have p5774_1 := h5774c.2.1
                          have p5774_2 := h5774c.2.2.1
                          have p5774_3 := h5774c.2.2.2
                          linarith only [h4238, hc01, hc12, hlam, hphi, p5774_1]
                        · have p5774_0 := h5774c.1
                          have p5774_1 := h5774c.2.1
                          have p5774_2 := h5774c.2.2.1
                          have p5774_3 := h5774c.2.2.2
                          linarith only [h5526, hc01, hc34, hlam, hphi, ht12, ht23, p5774_1]
                        · have p5774_0 := h5774c.1
                          have p5774_1 := h5774c.2.1
                          have p5774_2 := h5774c.2.2.1
                          have p5774_3 := h5774c.2.2.2
                          linarith only [h5523, hlam, p5774_0]
                        · have p5774_0 := h5774c.1
                          have p5774_1 := h5774c.2.1
                          have p5774_2 := h5774c.2.2.1
                          have p5774_3 := h5774c.2.2.2
                          linarith only [hlam, p5774_0]
                        · have p5774_0 := h5774c.1
                          have p5774_1 := h5774c.2.1
                          have p5774_2 := h5774c.2.2.1
                          have p5774_3 := h5774c.2.2.2
                          linarith only [h5526, hlam, p5774_0]
                        · have p5774_0 := h5774c.1
                          have p5774_1 := h5774c.2.1
                          have p5774_2 := h5774c.2.2.1
                          have p5774_3 := h5774c.2.2.2
                          linarith only [h5764, hlam, p5774_1]
                        · have p5774_0 := h5774c.1
                          have p5774_1 := h5774c.2.1
                          have p5774_2 := h5774c.2.2.1
                          have p5774_3 := h5774c.2.2.2
                          rcases p5774_3 (m.d 0 1) (by simp) with h5796 | h5796
                          · linarith only [h5796, hlam, p5774_0]
                          · rcases p5774_3 (m.d 1 2) (by simp) with h5798 | h5798
                            · rcases p5774_3 (m.d 1 3) (by simp) with h5799 | h5799
                              · linarith only [h5526, h5799, hlam]
                              · linarith only [h3473, h5799, hlam]
                            · linarith only [h0, h5798, hlam]
                        · have p5774_0 := h5774c.1
                          have p5774_1 := h5774c.2.1
                          have p5774_2 := h5774c.2.2.1
                          have p5774_3 := h5774c.2.2.2
                          linarith only [h5524, hlam, p5774_0]
                        · have p5774_0 := h5774c.1
                          have p5774_1 := h5774c.2.1
                          have p5774_2 := h5774c.2.2.1
                          have p5774_3 := h5774c.2.2.2
                          linarith only [h3473, hc01, hc14, hlam, hphi, p5774_1]
                        · have p5774_0 := h5774c.1
                          have p5774_1 := h5774c.2.1
                          have p5774_2 := h5774c.2.2.1
                          have p5774_3 := h5774c.2.2.2
                          linarith only [hlam, p5774_0]
                        · have p5774_0 := h5774c.1
                          have p5774_1 := h5774c.2.1
                          have p5774_2 := h5774c.2.2.1
                          have p5774_3 := h5774c.2.2.2
                          linarith only [h4336, h5246, h5526, h5766, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p5774_1, u4ehi2]
                        · have p5774_0 := h5774c.1
                          have p5774_1 := h5774c.2.1
                          have p5774_2 := h5774c.2.2.1
                          have p5774_3 := h5774c.2.2.2
                          rcases p5774_3 (m.d 0 1) (by simp) with h5807 | h5807
                          · linarith only [h5807, hlam, p5774_0]
                          · rcases p5774_3 (m.d 1 2) (by simp) with h5809 | h5809
                            · rcases p5774_3 (m.d 1 3) (by simp) with h5810 | h5810
                              · linarith only [h5764, h5810, hlam]
                              · linarith only [h3473, h5810, hlam]
                            · linarith only [h0, h5809, hlam]
                        · have p5774_0 := h5774c.1
                          have p5774_1 := h5774c.2.1
                          have p5774_2 := h5774c.2.2.1
                          have p5774_3 := h5774c.2.2.2
                          linarith only [h5525, hlam, p5774_0]
                        · have p5774_0 := h5774c.1
                          have p5774_1 := h5774c.2.1
                          have p5774_2 := h5774c.2.2.1
                          have p5774_3 := h5774c.2.2.2
                          linarith only [h3473, hc01, hc15, hlam, hphi, p5774_1]
                        · have p5774_0 := h5774c.1
                          have p5774_1 := h5774c.2.1
                          have p5774_2 := h5774c.2.2.1
                          have p5774_3 := h5774c.2.2.2
                          linarith only [h5766, hlam, p5774_0]
                        · have p5774_0 := h5774c.1
                          have p5774_1 := h5774c.2.1
                          have p5774_2 := h5774c.2.2.1
                          have p5774_3 := h5774c.2.2.2
                          linarith only [hlam, p5774_0]
                      · linarith only [h3473, h5526, h5773, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h5819 | h5819
                · linarith only [h3473, h4335, h5526, h5819, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h5821 | h5821
                  · linarith only [h4335, h4338, h5821, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5823 | h5823
                    · linarith only [h4336, h5246, h5823, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5825 | h5825
                      · linarith only [h3473, h5526, h5766, h5825, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h3473, h5526, h5825, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
        · linarith only [h0, h4337, h5525, hlam]
      · linarith only [h0, h4336, h5524, hlam]
    · linarith only [h0, h4335, h5523, hlam]

set_option maxHeartbeats 5244000 in
set_option maxHeartbeats 5244000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s7_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3473 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4044 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4238 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4335 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4336 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4337 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2bigk := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h3473 := hg3473
  have h4044 := hg4044
  have h4238 := hg4238
  rcases m.htr 0 3 5 (by decide) (by decide) with h4338 | h4338
  · exact r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s7_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg3473 hg4044 hg4238 h4335 h4336 h4337 h4338
  · exact r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s7_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg3473 hg4044 hg4238 h4335 h4336 h4337 h4338

set_option maxHeartbeats 5244000 in
set_option maxHeartbeats 5244000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s7_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3473 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4044 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4238 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4335 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4336 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4337 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h3473 := hg3473
  have h4044 := hg4044
  have h4238 := hg4238
  rcases m.htr 0 3 5 (by decide) (by decide) with h5831 | h5831
  · linarith only [h4335, h4337, h5831, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h5833 | h5833
    · linarith only [h4336, h4337, h5833, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h5835 | h5835
      · rcases m.htr 1 2 4 (by decide) (by decide) with h5836 | h5836
        · rcases m.htr 1 2 5 (by decide) (by decide) with h5837 | h5837
          · linarith only [h4336, h4337, h5837, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5839 | h5839
            · rcases m.htr 1 3 5 (by decide) (by decide) with h5840 | h5840
              · linarith only [h3473, h5831, h5835, h5837, h5840, hc01, hc25, hlam, hphi, ht12]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h5842 | h5842
                · linarith only [h4336, h4337, h5833, h5835, h5837, h5839, h5842, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h5844 | h5844
                  · linarith only [h0, h4335, h5837, h5844, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                  · linarith only [h5839, h5840, h5844, hc23, hc35, hlam, hphi]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h5847 | h5847
              · linarith only [h3473, h5831, h5836, h5837, h5839, h5847, hc01, hc25, hlam, hphi, ht12]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h5849 | h5849
                · linarith only [h4336, h5833, h5836, h5837, h5849, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h5851 | h5851
                  · linarith only [h3473, h5839, h5851, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h5853 | h5853
                    · linarith only [h3473, h4336, h5847, h5851, h5853, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h5855 | h5855
                      · linarith only [h0, h4336, h5837, h5849, h5853, h5855, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
                      · linarith only [h0, h4336, h5837, h5855, hc45, hlam, hphi, u4ehi2]
        · linarith only [h0, h4336, h5836, hlam]
      · linarith only [h0, h4335, h5835, hlam]

set_option maxHeartbeats 5244000 in
set_option maxHeartbeats 5244000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s7_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3473 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4044 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4238 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4335 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4336 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h3473 := hg3473
  have h4044 := hg4044
  have h4238 := hg4238
  rcases m.htr 0 2 5 (by decide) (by decide) with h4337 | h4337
  · exact r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s7_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg3473 hg4044 hg4238 h4335 h4336 h4337
  · exact r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s7_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg3473 hg4044 hg4238 h4335 h4336 h4337

end R2N4
