import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_1S28

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5820000 in
set_option maxHeartbeats 5820000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h15533 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h15534 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  rcases m.htr 0 2 3 (by decide) (by decide) with h17284 | h17284
  · rcases m.htr 0 2 4 (by decide) (by decide) with h17285 | h17285
    · rcases m.htr 0 2 5 (by decide) (by decide) with h17286 | h17286
      · rcases m.htr 0 3 4 (by decide) (by decide) with h17287 | h17287
        · rcases m.htr 0 3 5 (by decide) (by decide) with h17288 | h17288
          · linarith only [h15532, h15534, h17288, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h17290 | h17290
            · linarith only [h15532, h15534, h17287, h17290, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h17292 | h17292
              · rcases m.htr 1 2 4 (by decide) (by decide) with h17293 | h17293
                · rcases m.htr 1 2 5 (by decide) (by decide) with h17294 | h17294
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h17295 | h17295
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h17296 | h17296
                      · linarith only [h15532, h15534, h17288, h17294, h17296, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h17298 | h17298
                        · linarith only [h15533, h15534, h17290, h17298, hlam]
                        · linarith only [h15532, h15534, h17295, h17298, hc34, hc45, hlam, hphi]
                    · linarith only [h17287, h17288, h17292, h17295, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h15533, h17286, h17294, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h17285, h17293, hlam]
              · linarith only [h0, h15532, h17284, h17292, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h17305 | h17305
          · linarith only [h15533, h15534, h17287, h17305, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h17307 | h17307
            · linarith only [h15533, h15534, h17307, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h17309 | h17309
              · rcases m.htr 1 2 4 (by decide) (by decide) with h17310 | h17310
                · rcases m.htr 1 2 5 (by decide) (by decide) with h17311 | h17311
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h17312 | h17312
                    · linarith only [h15532, h15534, h17287, h17312, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h17314 | h17314
                      · linarith only [h15532, h15534, h17305, h17314, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h17316 | h17316
                        · linarith only [h15533, h15534, h17287, h17307, h17314, h17316, hc03, hc35, hlam, hphi]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h17318 | h17318
                          · linarith only [h15532, h15534, h17309, h17316, h17318, hc34, hc45, hlam, hphi]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h17320 | h17320
                            · linarith only [h15532, h17305, h17309, h17320, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h17322 | h17322
                              · linarith only [h15533, h15534, h17310, h17316, h17322, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h17324 | h17324
                                · linarith only [h15532, h15534, h17309, h17316, h17324, hc23, hc34, hlam, hphi]
                                · rcases h0bigk with h17326c | h17326c | h17326c | h17326c | h17326c | h17326c | h17326c | h17326c | h17326c | h17326c | h17326c | h17326c | h17326c | h17326c | h17326c | h17326c | h17326c | h17326c | h17326c | h17326c | h17326c | h17326c | h17326c | h17326c | h17326c
                                  · have p17326_0 := h17326c.1
                                    have p17326_1 := h17326c.2.1
                                    have p17326_2 := h17326c.2.2.1
                                    have p17326_3 := h17326c.2.2.2
                                    linarith only [hlam, p17326_0]
                                  · have p17326_0 := h17326c.1
                                    have p17326_1 := h17326c.2.1
                                    have p17326_2 := h17326c.2.2.1
                                    have p17326_3 := h17326c.2.2.2
                                    linarith only [h0, hlam, p17326_1]
                                  · have p17326_0 := h17326c.1
                                    have p17326_1 := h17326c.2.1
                                    have p17326_2 := h17326c.2.2.1
                                    have p17326_3 := h17326c.2.2.2
                                    linarith only [h15532, h15534, h17309, h17314, hc23, hc35, hlam, hphi, p17326_1]
                                  · have p17326_0 := h17326c.1
                                    have p17326_1 := h17326c.2.1
                                    have p17326_2 := h17326c.2.2.1
                                    have p17326_3 := h17326c.2.2.2
                                    linarith only [h15532, h15534, h17287, h17309, h17314, h17324, hc23, hc45, hlam, hphi, ht34, p17326_1]
                                  · have p17326_0 := h17326c.1
                                    have p17326_1 := h17326c.2.1
                                    have p17326_2 := h17326c.2.2.1
                                    have p17326_3 := h17326c.2.2.2
                                    linarith only [h15534, hlam, p17326_1]
                                  · have p17326_0 := h17326c.1
                                    have p17326_1 := h17326c.2.1
                                    have p17326_2 := h17326c.2.2.1
                                    have p17326_3 := h17326c.2.2.2
                                    rcases p17326_3 (m.d 0 1) (by simp) with h17332 | h17332
                                    · linarith only [h0, h17332, hlam]
                                    · rcases p17326_3 (m.d 0 2) (by simp) with h17334 | h17334
                                      · rcases p17326_3 (m.d 0 3) (by simp) with h17335 | h17335
                                        · linarith only [h17284, h17335, hlam]
                                        · rcases p17326_3 (m.d 0 4) (by simp) with h17337 | h17337
                                          · linarith only [h17285, h17337, hlam]
                                          · rcases p17326_3 (m.d 0 5) (by simp) with h17339 | h17339
                                            · linarith only [h17286, h17339, hlam]
                                            · linarith only [h15534, h17339, hlam]
                                      · linarith only [h0, h17334, hlam]
                                  · have p17326_0 := h17326c.1
                                    have p17326_1 := h17326c.2.1
                                    have p17326_2 := h17326c.2.2.1
                                    have p17326_3 := h17326c.2.2.2
                                    linarith only [hlam, p17326_0]
                                  · have p17326_0 := h17326c.1
                                    have p17326_1 := h17326c.2.1
                                    have p17326_2 := h17326c.2.2.1
                                    have p17326_3 := h17326c.2.2.2
                                    rcases p17326_3 (m.d 0 1) (by simp) with h17344 | h17344
                                    · linarith only [h0, h17344, hlam]
                                    · linarith only [h15532, h17344, hlam]
                                  · have p17326_0 := h17326c.1
                                    have p17326_1 := h17326c.2.1
                                    have p17326_2 := h17326c.2.2.1
                                    have p17326_3 := h17326c.2.2.2
                                    rcases p17326_3 (m.d 0 1) (by simp) with h17347 | h17347
                                    · linarith only [h0, h17347, hlam]
                                    · linarith only [h15533, h17347, hlam]
                                  · have p17326_0 := h17326c.1
                                    have p17326_1 := h17326c.2.1
                                    have p17326_2 := h17326c.2.2.1
                                    have p17326_3 := h17326c.2.2.2
                                    rcases p17326_3 (m.d 0 1) (by simp) with h17350 | h17350
                                    · linarith only [h0, h17350, hlam]
                                    · rcases p17326_3 (m.d 0 2) (by simp) with h17352 | h17352
                                      · rcases p17326_3 (m.d 0 3) (by simp) with h17353 | h17353
                                        · linarith only [h17284, h17353, hlam]
                                        · rcases p17326_3 (m.d 0 4) (by simp) with h17355 | h17355
                                          · linarith only [h17285, h17355, hlam]
                                          · rcases p17326_3 (m.d 0 5) (by simp) with h17357 | h17357
                                            · linarith only [h17286, h17357, hlam]
                                            · rcases h2bigk with h17359c | h17359c | h17359c | h17359c | h17359c | h17359c | h17359c | h17359c | h17359c | h17359c | h17359c | h17359c | h17359c | h17359c | h17359c | h17359c | h17359c | h17359c | h17359c | h17359c | h17359c | h17359c | h17359c | h17359c | h17359c
                                              · have p17359_0 := h17359c.1
                                                have p17359_1 := h17359c.2.1
                                                have p17359_2 := h17359c.2.2.1
                                                have p17359_3 := h17359c.2.2.2
                                                linarith only [hlam, p17359_0]
                                              · have p17359_0 := h17359c.1
                                                have p17359_1 := h17359c.2.1
                                                have p17359_2 := h17359c.2.2.1
                                                have p17359_3 := h17359c.2.2.2
                                                linarith only [h0, hlam, p17359_1]
                                              · have p17359_0 := h17359c.1
                                                have p17359_1 := h17359c.2.1
                                                have p17359_2 := h17359c.2.2.1
                                                have p17359_3 := h17359c.2.2.2
                                                linarith only [h15533, h15534, h17309, h17312, hlam, p17326_1, p17359_2]
                                              · have p17359_0 := h17359c.1
                                                have p17359_1 := h17359c.2.1
                                                have p17359_2 := h17359c.2.2.1
                                                have p17359_3 := h17359c.2.2.2
                                                linarith only [h15533, h15534, h17310, hlam, p17326_1, p17359_2]
                                              · have p17359_0 := h17359c.1
                                                have p17359_1 := h17359c.2.1
                                                have p17359_2 := h17359c.2.2.1
                                                have p17359_3 := h17359c.2.2.2
                                                rcases p17359_3 (m.d 0 2) (by simp) with h17364 | h17364
                                                · rcases p17359_3 (m.d 1 2) (by simp) with h17365 | h17365
                                                  · rcases p17359_3 (m.d 2 3) (by simp) with h17366 | h17366
                                                    · linarith only [h17284, h17366, hlam]
                                                    · rcases p17359_3 (m.d 2 4) (by simp) with h17368 | h17368
                                                      · linarith only [h17285, h17368, hlam]
                                                      · rcases p17359_3 (m.d 2 5) (by simp) with h17370 | h17370
                                                        · linarith only [h17370, hlam, p17359_0]
                                                        · rcases h3bigk with h17372c | h17372c | h17372c | h17372c | h17372c | h17372c | h17372c | h17372c | h17372c | h17372c | h17372c | h17372c | h17372c | h17372c | h17372c | h17372c | h17372c | h17372c | h17372c | h17372c | h17372c | h17372c | h17372c | h17372c | h17372c
                                                          · have p17372_0 := h17372c.1
                                                            have p17372_1 := h17372c.2.1
                                                            have p17372_2 := h17372c.2.2.1
                                                            have p17372_3 := h17372c.2.2.2
                                                            linarith only [hlam, p17372_0]
                                                          · have p17372_0 := h17372c.1
                                                            have p17372_1 := h17372c.2.1
                                                            have p17372_2 := h17372c.2.2.1
                                                            have p17372_3 := h17372c.2.2.2
                                                            linarith only [h0, h15532, h15534, h17309, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17326_1, p17372_1]
                                                          · have p17372_0 := h17372c.1
                                                            have p17372_1 := h17372c.2.1
                                                            have p17372_2 := h17372c.2.2.1
                                                            have p17372_3 := h17372c.2.2.2
                                                            linarith only [h0, h15533, h15534, h17287, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17326_1, p17372_1]
                                                          · have p17372_0 := h17372c.1
                                                            have p17372_1 := h17372c.2.1
                                                            have p17372_2 := h17372c.2.2.1
                                                            have p17372_3 := h17372c.2.2.2
                                                            linarith only [h17287, hlam, p17372_0]
                                                          · have p17372_0 := h17372c.1
                                                            have p17372_1 := h17372c.2.1
                                                            have p17372_2 := h17372c.2.2.1
                                                            have p17372_3 := h17372c.2.2.2
                                                            linarith only [h17305, hlam, p17372_0]
                                                          · have p17372_0 := h17372c.1
                                                            have p17372_1 := h17372c.2.1
                                                            have p17372_2 := h17372c.2.2.1
                                                            have p17372_3 := h17372c.2.2.2
                                                            linarith only [h15532, hlam, p17372_0]
                                                          · have p17372_0 := h17372c.1
                                                            have p17372_1 := h17372c.2.1
                                                            have p17372_2 := h17372c.2.2.1
                                                            have p17372_3 := h17372c.2.2.2
                                                            linarith only [hlam, p17372_0]
                                                          · have p17372_0 := h17372c.1
                                                            have p17372_1 := h17372c.2.1
                                                            have p17372_2 := h17372c.2.2.1
                                                            have p17372_3 := h17372c.2.2.2
                                                            linarith only [h0, h15532, h15534, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17326_1, p17372_1]
                                                          · have p17372_0 := h17372c.1
                                                            have p17372_1 := h17372c.2.1
                                                            have p17372_2 := h17372c.2.2.1
                                                            have p17372_3 := h17372c.2.2.2
                                                            linarith only [h17312, hlam, p17372_0]
                                                          · have p17372_0 := h17372c.1
                                                            have p17372_1 := h17372c.2.1
                                                            have p17372_2 := h17372c.2.2.1
                                                            have p17372_3 := h17372c.2.2.2
                                                            linarith only [h17314, hlam, p17372_0]
                                                          · have p17372_0 := h17372c.1
                                                            have p17372_1 := h17372c.2.1
                                                            have p17372_2 := h17372c.2.2.1
                                                            have p17372_3 := h17372c.2.2.2
                                                            linarith only [h17284, hlam, p17372_0]
                                                          · have p17372_0 := h17372c.1
                                                            have p17372_1 := h17372c.2.1
                                                            have p17372_2 := h17372c.2.2.1
                                                            have p17372_3 := h17372c.2.2.2
                                                            linarith only [h17309, hlam, p17372_0]
                                                          · have p17372_0 := h17372c.1
                                                            have p17372_1 := h17372c.2.1
                                                            have p17372_2 := h17372c.2.2.1
                                                            have p17372_3 := h17372c.2.2.2
                                                            linarith only [hlam, p17372_0]
                                                          · have p17372_0 := h17372c.1
                                                            have p17372_1 := h17372c.2.1
                                                            have p17372_2 := h17372c.2.2.1
                                                            have p17372_3 := h17372c.2.2.2
                                                            linarith only [h17318, hlam, p17372_0]
                                                          · have p17372_0 := h17372c.1
                                                            have p17372_1 := h17372c.2.1
                                                            have p17372_2 := h17372c.2.2.1
                                                            have p17372_3 := h17372c.2.2.2
                                                            linarith only [h17320, hlam, p17372_0]
                                                          · have p17372_0 := h17372c.1
                                                            have p17372_1 := h17372c.2.1
                                                            have p17372_2 := h17372c.2.2.1
                                                            have p17372_3 := h17372c.2.2.2
                                                            linarith only [h17324, hc03, hc45, hlam, hphi, ht34, p17372_1]
                                                          · have p17372_0 := h17372c.1
                                                            have p17372_1 := h17372c.2.1
                                                            have p17372_2 := h17372c.2.2.1
                                                            have p17372_3 := h17372c.2.2.2
                                                            linarith only [h17309, h17324, hc23, hc45, hlam, hphi, ht34, p17372_1]
                                                          · have p17372_0 := h17372c.1
                                                            have p17372_1 := h17372c.2.1
                                                            have p17372_2 := h17372c.2.2.1
                                                            have p17372_3 := h17372c.2.2.2
                                                            linarith only [h17324, hc23, hc45, hlam, hphi, ht34, p17372_1]
                                                          · have p17372_0 := h17372c.1
                                                            have p17372_1 := h17372c.2.1
                                                            have p17372_2 := h17372c.2.2.1
                                                            have p17372_3 := h17372c.2.2.2
                                                            linarith only [hlam, p17372_0]
                                                          · have p17372_0 := h17372c.1
                                                            have p17372_1 := h17372c.2.1
                                                            have p17372_2 := h17372c.2.2.1
                                                            have p17372_3 := h17372c.2.2.2
                                                            linarith only [h17324, hlam, p17372_1]
                                                          · have p17372_0 := h17372c.1
                                                            have p17372_1 := h17372c.2.1
                                                            have p17372_2 := h17372c.2.2.1
                                                            have p17372_3 := h17372c.2.2.2
                                                            rcases p17372_3 (m.d 0 3) (by simp) with h17393 | h17393
                                                            · linarith only [h17393, hlam, p17372_0]
                                                            · rcases p17372_3 (m.d 1 3) (by simp) with h17395 | h17395
                                                              · linarith only [h17314, h17395, hlam]
                                                              · rcases p17372_3 (m.d 2 3) (by simp) with h17397 | h17397
                                                                · linarith only [h17320, h17397, hlam]
                                                                · rcases p17372_3 (m.d 3 4) (by simp) with h17399 | h17399
                                                                  · linarith only [h17324, h17399, hlam]
                                                                  · linarith only [h17287, h17399, hlam]
                                                          · have p17372_0 := h17372c.1
                                                            have p17372_1 := h17372c.2.1
                                                            have p17372_2 := h17372c.2.2.1
                                                            have p17372_3 := h17372c.2.2.2
                                                            rcases p17372_3 (m.d 0 3) (by simp) with h17402 | h17402
                                                            · linarith only [h17305, h17402, hlam]
                                                            · linarith only [h15532, h17402, hlam]
                                                          · have p17372_0 := h17372c.1
                                                            have p17372_1 := h17372c.2.1
                                                            have p17372_2 := h17372c.2.2.1
                                                            have p17372_3 := h17372c.2.2.2
                                                            rcases p17372_3 (m.d 0 3) (by simp) with h17405 | h17405
                                                            · linarith only [h17305, h17405, hlam]
                                                            · linarith only [h17284, h17405, hlam]
                                                          · have p17372_0 := h17372c.1
                                                            have p17372_1 := h17372c.2.1
                                                            have p17372_2 := h17372c.2.2.1
                                                            have p17372_3 := h17372c.2.2.2
                                                            linarith only [h15532, h17287, h17309, h17324, hc23, hc45, hlam, hphi, ht34, p17372_1]
                                                          · have p17372_0 := h17372c.1
                                                            have p17372_1 := h17372c.2.1
                                                            have p17372_2 := h17372c.2.2.1
                                                            have p17372_3 := h17372c.2.2.2
                                                            linarith only [hlam, p17372_0]
                                                  · linarith only [h17311, h17365, hlam]
                                                · linarith only [h17364, hlam, p17359_0]
                                              · have p17359_0 := h17359c.1
                                                have p17359_1 := h17359c.2.1
                                                have p17359_2 := h17359c.2.2.1
                                                have p17359_3 := h17359c.2.2.2
                                                linarith only [h15534, hc01, hc12, hlam, hphi, p17326_1, p17359_1]
                                              · have p17359_0 := h17359c.1
                                                have p17359_1 := h17359c.2.1
                                                have p17359_2 := h17359c.2.2.1
                                                have p17359_3 := h17359c.2.2.2
                                                linarith only [hlam, p17359_0]
                                              · have p17359_0 := h17359c.1
                                                have p17359_1 := h17359c.2.1
                                                have p17359_2 := h17359c.2.2.1
                                                have p17359_3 := h17359c.2.2.2
                                                linarith only [h0, h15532, h15534, h17309, hlam, p17326_1, p17359_2]
                                              · have p17359_0 := h17359c.1
                                                have p17359_1 := h17359c.2.1
                                                have p17359_2 := h17359c.2.2.1
                                                have p17359_3 := h17359c.2.2.2
                                                linarith only [h0, h15533, h15534, h17310, hlam, p17326_1, p17359_2]
                                              · have p17359_0 := h17359c.1
                                                have p17359_1 := h17359c.2.1
                                                have p17359_2 := h17359c.2.2.1
                                                have p17359_3 := h17359c.2.2.2
                                                rcases p17359_3 (m.d 0 2) (by simp) with h17416 | h17416
                                                · linarith only [h0, h17416, hlam]
                                                · linarith only [h17286, h17416, hlam]
                                              · have p17359_0 := h17359c.1
                                                have p17359_1 := h17359c.2.1
                                                have p17359_2 := h17359c.2.2.1
                                                have p17359_3 := h17359c.2.2.2
                                                linarith only [h17284, hlam, p17359_0]
                                              · have p17359_0 := h17359c.1
                                                have p17359_1 := h17359c.2.1
                                                have p17359_2 := h17359c.2.2.1
                                                have p17359_3 := h17359c.2.2.2
                                                linarith only [h17309, hlam, p17359_0]
                                              · have p17359_0 := h17359c.1
                                                have p17359_1 := h17359c.2.1
                                                have p17359_2 := h17359c.2.2.1
                                                have p17359_3 := h17359c.2.2.2
                                                linarith only [hlam, p17359_0]
                                              · have p17359_0 := h17359c.1
                                                have p17359_1 := h17359c.2.1
                                                have p17359_2 := h17359c.2.2.1
                                                have p17359_3 := h17359c.2.2.2
                                                linarith only [h17318, hlam, p17359_0]
                                              · have p17359_0 := h17359c.1
                                                have p17359_1 := h17359c.2.1
                                                have p17359_2 := h17359c.2.2.1
                                                have p17359_3 := h17359c.2.2.2
                                                linarith only [h17320, hlam, p17359_0]
                                              · have p17359_0 := h17359c.1
                                                have p17359_1 := h17359c.2.1
                                                have p17359_2 := h17359c.2.2.1
                                                have p17359_3 := h17359c.2.2.2
                                                linarith only [h17285, hlam, p17359_0]
                                              · have p17359_0 := h17359c.1
                                                have p17359_1 := h17359c.2.1
                                                have p17359_2 := h17359c.2.2.1
                                                have p17359_3 := h17359c.2.2.2
                                                linarith only [h17310, hlam, p17359_0]
                                              · have p17359_0 := h17359c.1
                                                have p17359_1 := h17359c.2.1
                                                have p17359_2 := h17359c.2.2.1
                                                have p17359_3 := h17359c.2.2.2
                                                linarith only [h15533, h15534, h17310, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p17326_1, p17359_1]
                                              · have p17359_0 := h17359c.1
                                                have p17359_1 := h17359c.2.1
                                                have p17359_2 := h17359c.2.2.1
                                                have p17359_3 := h17359c.2.2.2
                                                linarith only [hlam, p17359_0]
                                              · have p17359_0 := h17359c.1
                                                have p17359_1 := h17359c.2.1
                                                have p17359_2 := h17359c.2.2.1
                                                have p17359_3 := h17359c.2.2.2
                                                linarith only [h17322, hlam, p17359_1]
                                              · have p17359_0 := h17359c.1
                                                have p17359_1 := h17359c.2.1
                                                have p17359_2 := h17359c.2.2.1
                                                have p17359_3 := h17359c.2.2.2
                                                linarith only [h17286, hlam, p17359_0]
                                              · have p17359_0 := h17359c.1
                                                have p17359_1 := h17359c.2.1
                                                have p17359_2 := h17359c.2.2.1
                                                have p17359_3 := h17359c.2.2.2
                                                linarith only [h17311, hlam, p17359_0]
                                              · have p17359_0 := h17359c.1
                                                have p17359_1 := h17359c.2.1
                                                have p17359_2 := h17359c.2.2.1
                                                have p17359_3 := h17359c.2.2.2
                                                linarith only [h0, h17286, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17326_1, p17359_1]
                                              · have p17359_0 := h17359c.1
                                                have p17359_1 := h17359c.2.1
                                                have p17359_2 := h17359c.2.2.1
                                                have p17359_3 := h17359c.2.2.2
                                                linarith only [h0, h17286, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p17326_1, p17359_1]
                                              · have p17359_0 := h17359c.1
                                                have p17359_1 := h17359c.2.1
                                                have p17359_2 := h17359c.2.2.1
                                                have p17359_3 := h17359c.2.2.2
                                                linarith only [hlam, p17359_0]
                                      · linarith only [h17286, h17352, hlam]
                                  · have p17326_0 := h17326c.1
                                    have p17326_1 := h17326c.2.1
                                    have p17326_2 := h17326c.2.2.1
                                    have p17326_3 := h17326c.2.2.2
                                    linarith only [h15532, hlam, p17326_1]
                                  · have p17326_0 := h17326c.1
                                    have p17326_1 := h17326c.2.1
                                    have p17326_2 := h17326c.2.2.1
                                    have p17326_3 := h17326c.2.2.2
                                    linarith only [h17284, hlam, p17326_1]
                                  · have p17326_0 := h17326c.1
                                    have p17326_1 := h17326c.2.1
                                    have p17326_2 := h17326c.2.2.1
                                    have p17326_3 := h17326c.2.2.2
                                    linarith only [hlam, p17326_0]
                                  · have p17326_0 := h17326c.1
                                    have p17326_1 := h17326c.2.1
                                    have p17326_2 := h17326c.2.2.1
                                    have p17326_3 := h17326c.2.2.2
                                    linarith only [h17287, hlam, p17326_1]
                                  · have p17326_0 := h17326c.1
                                    have p17326_1 := h17326c.2.1
                                    have p17326_2 := h17326c.2.2.1
                                    have p17326_3 := h17326c.2.2.2
                                    linarith only [h17305, hlam, p17326_1]
                                  · have p17326_0 := h17326c.1
                                    have p17326_1 := h17326c.2.1
                                    have p17326_2 := h17326c.2.2.1
                                    have p17326_3 := h17326c.2.2.2
                                    linarith only [h15533, hlam, p17326_0]
                                  · have p17326_0 := h17326c.1
                                    have p17326_1 := h17326c.2.1
                                    have p17326_2 := h17326c.2.2.1
                                    have p17326_3 := h17326c.2.2.2
                                    linarith only [h17285, hlam, p17326_0]
                                  · have p17326_0 := h17326c.1
                                    have p17326_1 := h17326c.2.1
                                    have p17326_2 := h17326c.2.2.1
                                    have p17326_3 := h17326c.2.2.2
                                    linarith only [h15532, h15533, h15534, h17309, h17314, h17324, hc23, hc45, hlam, hphi, ht34, p17326_1]
                                  · have p17326_0 := h17326c.1
                                    have p17326_1 := h17326c.2.1
                                    have p17326_2 := h17326c.2.2.1
                                    have p17326_3 := h17326c.2.2.2
                                    linarith only [hlam, p17326_0]
                                  · have p17326_0 := h17326c.1
                                    have p17326_1 := h17326c.2.1
                                    have p17326_2 := h17326c.2.2.1
                                    have p17326_3 := h17326c.2.2.2
                                    linarith only [h17307, hlam, p17326_0]
                                  · have p17326_0 := h17326c.1
                                    have p17326_1 := h17326c.2.1
                                    have p17326_2 := h17326c.2.2.1
                                    have p17326_3 := h17326c.2.2.2
                                    linarith only [h15533, h15534, h17314, h17324, hc14, hc45, hlam, hphi, p17326_1]
                                  · have p17326_0 := h17326c.1
                                    have p17326_1 := h17326c.2.1
                                    have p17326_2 := h17326c.2.2.1
                                    have p17326_3 := h17326c.2.2.2
                                    linarith only [h17286, hlam, p17326_1]
                                  · have p17326_0 := h17326c.1
                                    have p17326_1 := h17326c.2.1
                                    have p17326_2 := h17326c.2.2.1
                                    have p17326_3 := h17326c.2.2.2
                                    rcases p17326_3 (m.d 0 1) (by simp) with h17447 | h17447
                                    · linarith only [h15534, h17447, hlam]
                                    · linarith only [h15532, h17447, hlam]
                                  · have p17326_0 := h17326c.1
                                    have p17326_1 := h17326c.2.1
                                    have p17326_2 := h17326c.2.2.1
                                    have p17326_3 := h17326c.2.2.2
                                    rcases p17326_3 (m.d 0 1) (by simp) with h17450 | h17450
                                    · linarith only [h15534, h17450, hlam]
                                    · linarith only [h15533, h17450, hlam]
                                  · have p17326_0 := h17326c.1
                                    have p17326_1 := h17326c.2.1
                                    have p17326_2 := h17326c.2.2.1
                                    have p17326_3 := h17326c.2.2.2
                                    linarith only [hlam, p17326_0]
                  · linarith only [h0, h17286, h17311, hlam]
                · linarith only [h0, h17285, h17310, hlam]
              · linarith only [h0, h17284, h17309, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h17457 | h17457
        · rcases m.htr 0 3 5 (by decide) (by decide) with h17458 | h17458
          · linarith only [h15532, h15534, h17458, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h17460 | h17460
            · linarith only [h0, h15533, h17286, h17460, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h17462 | h17462
              · rcases m.htr 1 2 4 (by decide) (by decide) with h17463 | h17463
                · rcases m.htr 1 2 5 (by decide) (by decide) with h17464 | h17464
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h17465 | h17465
                    · linarith only [h0, h15532, h17286, h17464, h17465, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h15532, h17286, h17457, h17464, h17465, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h17468 | h17468
                    · linarith only [h0, h15532, h17464, h17468, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h15532, h17457, h17462, h17464, h17468, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · linarith only [h0, h15533, h17285, h17286, h17463, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h17284, h17462, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h17473 | h17473
          · linarith only [h15532, h15534, h17473, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h17475 | h17475
            · linarith only [h0, h15533, h17286, h17475, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h17477 | h17477
              · rcases m.htr 1 2 4 (by decide) (by decide) with h17478 | h17478
                · rcases m.htr 1 2 5 (by decide) (by decide) with h17479 | h17479
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h17480 | h17480
                    · linarith only [h0, h15532, h17286, h17457, h17479, h17480, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h17482 | h17482
                      · linarith only [h0, h15532, h17286, h17473, h17482, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h17484 | h17484
                        · linarith only [h0, h15533, h17286, h17475, h17479, h17484, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h17486 | h17486
                          · linarith only [h17284, h17286, h17457, h17479, h17486, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h17488 | h17488
                            · linarith only [h0, h15532, h17286, h17477, h17479, h17488, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h17490 | h17490
                              · linarith only [h0, h15533, h17286, h17478, h17479, h17484, h17490, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h17492 | h17492
                                · linarith only [h0, h15533, h17286, h17479, h17480, h17484, h17492, hc13, hc34, hlam, hphi]
                                · rcases h0bigk with h17494c | h17494c | h17494c | h17494c | h17494c | h17494c | h17494c | h17494c | h17494c | h17494c | h17494c | h17494c | h17494c | h17494c | h17494c | h17494c | h17494c | h17494c | h17494c | h17494c | h17494c | h17494c | h17494c | h17494c | h17494c
                                  · have p17494_0 := h17494c.1
                                    have p17494_1 := h17494c.2.1
                                    have p17494_2 := h17494c.2.2.1
                                    have p17494_3 := h17494c.2.2.2
                                    linarith only [hlam, p17494_0]
                                  · have p17494_0 := h17494c.1
                                    have p17494_1 := h17494c.2.1
                                    have p17494_2 := h17494c.2.2.1
                                    have p17494_3 := h17494c.2.2.2
                                    linarith only [h0, hlam, p17494_1]
                                  · have p17494_0 := h17494c.1
                                    have p17494_1 := h17494c.2.1
                                    have p17494_2 := h17494c.2.2.1
                                    have p17494_3 := h17494c.2.2.2
                                    linarith only [h0, h17286, h17479, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17494_1]
                                  · have p17494_0 := h17494c.1
                                    have p17494_1 := h17494c.2.1
                                    have p17494_2 := h17494c.2.2.1
                                    have p17494_3 := h17494c.2.2.2
                                    linarith only [h0, h17286, h17479, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p17494_1]
                                  · have p17494_0 := h17494c.1
                                    have p17494_1 := h17494c.2.1
                                    have p17494_2 := h17494c.2.2.1
                                    have p17494_3 := h17494c.2.2.2
                                    linarith only [h15534, hlam, p17494_1]
                                  · have p17494_0 := h17494c.1
                                    have p17494_1 := h17494c.2.1
                                    have p17494_2 := h17494c.2.2.1
                                    have p17494_3 := h17494c.2.2.2
                                    linarith only [h17286, h17479, hc01, hc12, hlam, hphi, p17494_1]
                                  · have p17494_0 := h17494c.1
                                    have p17494_1 := h17494c.2.1
                                    have p17494_2 := h17494c.2.2.1
                                    have p17494_3 := h17494c.2.2.2
                                    linarith only [hlam, p17494_0]
                                  · have p17494_0 := h17494c.1
                                    have p17494_1 := h17494c.2.1
                                    have p17494_2 := h17494c.2.2.1
                                    have p17494_3 := h17494c.2.2.2
                                    linarith only [h15532, h17286, h17477, h17479, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17494_1]
                                  · have p17494_0 := h17494c.1
                                    have p17494_1 := h17494c.2.1
                                    have p17494_2 := h17494c.2.2.1
                                    have p17494_3 := h17494c.2.2.2
                                    linarith only [h15533, h17286, h17477, h17479, h17480, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17494_1]
                                  · have p17494_0 := h17494c.1
                                    have p17494_1 := h17494c.2.1
                                    have p17494_2 := h17494c.2.2.1
                                    have p17494_3 := h17494c.2.2.2
                                    linarith only [h17286, hlam, p17494_0]
                                  · have p17494_0 := h17494c.1
                                    have p17494_1 := h17494c.2.1
                                    have p17494_2 := h17494c.2.2.1
                                    have p17494_3 := h17494c.2.2.2
                                    linarith only [h15532, hlam, p17494_1]
                                  · have p17494_0 := h17494c.1
                                    have p17494_1 := h17494c.2.1
                                    have p17494_2 := h17494c.2.2.1
                                    have p17494_3 := h17494c.2.2.2
                                    linarith only [h17284, hlam, p17494_1]
                                  · have p17494_0 := h17494c.1
                                    have p17494_1 := h17494c.2.1
                                    have p17494_2 := h17494c.2.2.1
                                    have p17494_3 := h17494c.2.2.2
                                    linarith only [hlam, p17494_0]
                                  · have p17494_0 := h17494c.1
                                    have p17494_1 := h17494c.2.1
                                    have p17494_2 := h17494c.2.2.1
                                    have p17494_3 := h17494c.2.2.2
                                    linarith only [h17457, hlam, p17494_1]
                                  · have p17494_0 := h17494c.1
                                    have p17494_1 := h17494c.2.1
                                    have p17494_2 := h17494c.2.2.1
                                    have p17494_3 := h17494c.2.2.2
                                    linarith only [h17473, hlam, p17494_1]
                                  · have p17494_0 := h17494c.1
                                    have p17494_1 := h17494c.2.1
                                    have p17494_2 := h17494c.2.2.1
                                    have p17494_3 := h17494c.2.2.2
                                    linarith only [h15533, hlam, p17494_0]
                                  · have p17494_0 := h17494c.1
                                    have p17494_1 := h17494c.2.1
                                    have p17494_2 := h17494c.2.2.1
                                    have p17494_3 := h17494c.2.2.2
                                    linarith only [h17285, hlam, p17494_0]
                                  · have p17494_0 := h17494c.1
                                    have p17494_1 := h17494c.2.1
                                    have p17494_2 := h17494c.2.2.1
                                    have p17494_3 := h17494c.2.2.2
                                    linarith only [h0, h15532, h15533, h17286, h17477, h17479, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17494_1]
                                  · have p17494_0 := h17494c.1
                                    have p17494_1 := h17494c.2.1
                                    have p17494_2 := h17494c.2.2.1
                                    have p17494_3 := h17494c.2.2.2
                                    linarith only [hlam, p17494_0]
                                  · have p17494_0 := h17494c.1
                                    have p17494_1 := h17494c.2.1
                                    have p17494_2 := h17494c.2.2.1
                                    have p17494_3 := h17494c.2.2.2
                                    linarith only [h17475, hlam, p17494_0]
                                  · have p17494_0 := h17494c.1
                                    have p17494_1 := h17494c.2.1
                                    have p17494_2 := h17494c.2.2.1
                                    have p17494_3 := h17494c.2.2.2
                                    linarith only [h15532, h15534, h17477, h17482, hc23, hc35, hlam, hphi, p17494_1]
                                  · have p17494_0 := h17494c.1
                                    have p17494_1 := h17494c.2.1
                                    have p17494_2 := h17494c.2.2.1
                                    have p17494_3 := h17494c.2.2.2
                                    linarith only [h0, h15533, h17286, h17477, h17479, h17480, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17494_1]
                                  · have p17494_0 := h17494c.1
                                    have p17494_1 := h17494c.2.1
                                    have p17494_2 := h17494c.2.2.1
                                    have p17494_3 := h17494c.2.2.2
                                    rcases p17494_3 (m.d 0 1) (by simp) with h17517 | h17517
                                    · linarith only [h15534, h17517, hlam]
                                    · linarith only [h15532, h17517, hlam]
                                  · have p17494_0 := h17494c.1
                                    have p17494_1 := h17494c.2.1
                                    have p17494_2 := h17494c.2.2.1
                                    have p17494_3 := h17494c.2.2.2
                                    rcases p17494_3 (m.d 0 1) (by simp) with h17520 | h17520
                                    · linarith only [h15534, h17520, hlam]
                                    · linarith only [h15533, h17520, hlam]
                                  · have p17494_0 := h17494c.1
                                    have p17494_1 := h17494c.2.1
                                    have p17494_2 := h17494c.2.2.1
                                    have p17494_3 := h17494c.2.2.2
                                    linarith only [hlam, p17494_0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h17524 | h17524
                    · linarith only [h0, h15532, h17479, h17524, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h17526 | h17526
                      · linarith only [h0, h15533, h17479, h17524, h17526, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h17528 | h17528
                        · linarith only [h0, h15533, h17475, h17479, h17528, hc05, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h17530 | h17530
                          · linarith only [h15532, h17457, h17477, h17530, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h17532 | h17532
                            · linarith only [h0, h15533, h17477, h17479, h17524, h17532, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · linarith only [h0, h15533, h17477, h17479, h17524, h17532, hc23, hc35, hlam, hphi]
                · linarith only [h0, h15533, h17285, h17286, h17478, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h17284, h17477, hlam]
    · linarith only [h0, h15533, h17285, hlam]
  · linarith only [h0, h15532, h17284, hlam]

set_option maxHeartbeats 5820000 in
set_option maxHeartbeats 5820000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h15533 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  rcases m.htr 0 1 5 (by decide) (by decide) with h15534 | h15534
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 h15533 h15534
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 h15533 h15534

set_option maxHeartbeats 5820000 in
set_option maxHeartbeats 5820000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h15533 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h17539 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  rcases m.htr 0 2 3 (by decide) (by decide) with h17540 | h17540
  · rcases m.htr 0 2 4 (by decide) (by decide) with h17541 | h17541
    · rcases m.htr 0 2 5 (by decide) (by decide) with h17542 | h17542
      · rcases m.htr 0 3 4 (by decide) (by decide) with h17543 | h17543
        · linarith only [h15532, h15533, h17543, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h17545 | h17545
          · rcases m.htr 0 4 5 (by decide) (by decide) with h17546 | h17546
            · rcases m.htr 1 2 3 (by decide) (by decide) with h17547 | h17547
              · rcases m.htr 1 2 4 (by decide) (by decide) with h17548 | h17548
                · rcases m.htr 1 2 5 (by decide) (by decide) with h17549 | h17549
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h17550 | h17550
                    · linarith only [h15532, h15533, h17543, h17548, h17550, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h17552 | h17552
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h17553 | h17553
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h17554 | h17554
                          · linarith only [h15532, h15533, h17547, h17550, h17554, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h17556 | h17556
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h17557 | h17557
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h17558 | h17558
                                · rcases h0bigk with h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [hlam, p17559_0]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [h0, hlam, p17559_1]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [h15533, h17550, hc03, hc34, hlam, hphi, p17559_1]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [h15533, hlam, p17559_1]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    rcases p17559_3 (m.d 0 1) (by simp) with h17564 | h17564
                                    · rcases p17559_3 (m.d 0 2) (by simp) with h17565 | h17565
                                      · rcases p17559_3 (m.d 0 3) (by simp) with h17566 | h17566
                                        · linarith only [h15532, h17566, hlam]
                                        · linarith only [h17545, h17566, hlam]
                                      · linarith only [h17542, h17565, hlam]
                                    · linarith only [h17539, h17564, hlam]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [h0, h15532, h17552, h17558, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p17559_1]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [hlam, p17559_0]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    rcases p17559_3 (m.d 0 1) (by simp) with h17573 | h17573
                                    · linarith only [h0, h17573, hlam]
                                    · linarith only [h15532, h17573, hlam]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [h0, h15532, h15533, h17547, h17556, h17558, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p17559_1]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    rcases p17559_3 (m.d 0 1) (by simp) with h17577 | h17577
                                    · linarith only [h0, h17577, hlam]
                                    · linarith only [h17539, h17577, hlam]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [h15532, hlam, p17559_1]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [h17540, hlam, p17559_1]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [hlam, p17559_0]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [h17543, hlam, p17559_1]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    rcases p17559_3 (m.d 0 1) (by simp) with h17584 | h17584
                                    · rcases p17559_3 (m.d 0 2) (by simp) with h17585 | h17585
                                      · rcases p17559_3 (m.d 0 3) (by simp) with h17586 | h17586
                                        · rcases p17559_3 (m.d 0 4) (by simp) with h17587 | h17587
                                          · rcases p17559_3 (m.d 0 5) (by simp) with h17588 | h17588
                                            · linarith only [h17545, h17588, hlam]
                                            · rcases h2bigk with h17590c | h17590c | h17590c | h17590c | h17590c | h17590c | h17590c | h17590c | h17590c | h17590c | h17590c | h17590c | h17590c | h17590c | h17590c | h17590c | h17590c | h17590c | h17590c | h17590c | h17590c | h17590c | h17590c | h17590c | h17590c
                                              · have p17590_0 := h17590c.1
                                                have p17590_1 := h17590c.2.1
                                                have p17590_2 := h17590c.2.2.1
                                                have p17590_3 := h17590c.2.2.2
                                                linarith only [hlam, p17590_0]
                                              · have p17590_0 := h17590c.1
                                                have p17590_1 := h17590c.2.1
                                                have p17590_2 := h17590c.2.2.1
                                                have p17590_3 := h17590c.2.2.2
                                                linarith only [h0, hlam, p17590_1]
                                              · have p17590_0 := h17590c.1
                                                have p17590_1 := h17590c.2.1
                                                have p17590_2 := h17590c.2.2.1
                                                have p17590_3 := h17590c.2.2.2
                                                rcases p17590_3 (m.d 0 2) (by simp) with h17593 | h17593
                                                · rcases p17590_3 (m.d 1 2) (by simp) with h17594 | h17594
                                                  · rcases p17590_3 (m.d 2 3) (by simp) with h17595 | h17595
                                                    · linarith only [h17595, hlam, p17590_0]
                                                    · rcases p17590_3 (m.d 2 4) (by simp) with h17597 | h17597
                                                      · linarith only [h17541, h17597, hlam]
                                                      · linarith only [h17554, h17597, hlam]
                                                  · linarith only [h17547, h17594, hlam]
                                                · linarith only [h17593, hlam, p17590_0]
                                              · have p17590_0 := h17590c.1
                                                have p17590_1 := h17590c.2.1
                                                have p17590_2 := h17590c.2.2.1
                                                have p17590_3 := h17590c.2.2.2
                                                rcases p17590_3 (m.d 0 2) (by simp) with h17602 | h17602
                                                · rcases p17590_3 (m.d 1 2) (by simp) with h17603 | h17603
                                                  · rcases p17590_3 (m.d 2 3) (by simp) with h17604 | h17604
                                                    · linarith only [h17540, h17604, hlam]
                                                    · rcases p17590_3 (m.d 2 4) (by simp) with h17606 | h17606
                                                      · linarith only [h17606, hlam, p17590_0]
                                                      · rcases p17590_3 (m.d 2 5) (by simp) with h17608 | h17608
                                                        · linarith only [h17542, h17608, hlam]
                                                        · rcases h3bigk with h17610c | h17610c | h17610c | h17610c | h17610c | h17610c | h17610c | h17610c | h17610c | h17610c | h17610c | h17610c | h17610c | h17610c | h17610c | h17610c | h17610c | h17610c | h17610c | h17610c | h17610c | h17610c | h17610c | h17610c | h17610c
                                                          · have p17610_0 := h17610c.1
                                                            have p17610_1 := h17610c.2.1
                                                            have p17610_2 := h17610c.2.2.1
                                                            have p17610_3 := h17610c.2.2.2
                                                            linarith only [hlam, p17610_0]
                                                          · have p17610_0 := h17610c.1
                                                            have p17610_1 := h17610c.2.1
                                                            have p17610_2 := h17610c.2.2.1
                                                            have p17610_3 := h17610c.2.2.2
                                                            linarith only [h15532, h15533, h17547, h17550, h17556, h17558, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p17610_1]
                                                          · have p17610_0 := h17610c.1
                                                            have p17610_1 := h17610c.2.1
                                                            have p17610_2 := h17610c.2.2.1
                                                            have p17610_3 := h17610c.2.2.2
                                                            linarith only [h15532, h15533, h17550, h17556, h17558, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p17610_1]
                                                          · have p17610_0 := h17610c.1
                                                            have p17610_1 := h17610c.2.1
                                                            have p17610_2 := h17610c.2.2.1
                                                            have p17610_3 := h17610c.2.2.2
                                                            linarith only [h17543, hlam, p17610_0]
                                                          · have p17610_0 := h17610c.1
                                                            have p17610_1 := h17610c.2.1
                                                            have p17610_2 := h17610c.2.2.1
                                                            have p17610_3 := h17610c.2.2.2
                                                            rcases p17610_3 (m.d 0 3) (by simp) with h17615 | h17615
                                                            · rcases p17610_3 (m.d 1 3) (by simp) with h17616 | h17616
                                                              · linarith only [h15532, h17616, hlam]
                                                              · linarith only [h17552, h17616, hlam]
                                                            · linarith only [h17615, hlam, p17610_0]
                                                          · have p17610_0 := h17610c.1
                                                            have p17610_1 := h17610c.2.1
                                                            have p17610_2 := h17610c.2.2.1
                                                            have p17610_3 := h17610c.2.2.2
                                                            linarith only [h15532, hlam, p17610_0]
                                                          · have p17610_0 := h17610c.1
                                                            have p17610_1 := h17610c.2.1
                                                            have p17610_2 := h17610c.2.2.1
                                                            have p17610_3 := h17610c.2.2.2
                                                            linarith only [hlam, p17610_0]
                                                          · have p17610_0 := h17610c.1
                                                            have p17610_1 := h17610c.2.1
                                                            have p17610_2 := h17610c.2.2.1
                                                            have p17610_3 := h17610c.2.2.2
                                                            linarith only [h15532, h15533, h17550, h17556, h17558, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p17610_1]
                                                          · have p17610_0 := h17610c.1
                                                            have p17610_1 := h17610c.2.1
                                                            have p17610_2 := h17610c.2.2.1
                                                            have p17610_3 := h17610c.2.2.2
                                                            linarith only [h17550, hlam, p17610_0]
                                                          · have p17610_0 := h17610c.1
                                                            have p17610_1 := h17610c.2.1
                                                            have p17610_2 := h17610c.2.2.1
                                                            have p17610_3 := h17610c.2.2.2
                                                            linarith only [h15532, h15533, h17550, h17558, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p17610_1]
                                                          · have p17610_0 := h17610c.1
                                                            have p17610_1 := h17610c.2.1
                                                            have p17610_2 := h17610c.2.2.1
                                                            have p17610_3 := h17610c.2.2.2
                                                            linarith only [h17540, hlam, p17610_0]
                                                          · have p17610_0 := h17610c.1
                                                            have p17610_1 := h17610c.2.1
                                                            have p17610_2 := h17610c.2.2.1
                                                            have p17610_3 := h17610c.2.2.2
                                                            linarith only [h17547, hlam, p17610_0]
                                                          · have p17610_0 := h17610c.1
                                                            have p17610_1 := h17610c.2.1
                                                            have p17610_2 := h17610c.2.2.1
                                                            have p17610_3 := h17610c.2.2.2
                                                            linarith only [hlam, p17610_0]
                                                          · have p17610_0 := h17610c.1
                                                            have p17610_1 := h17610c.2.1
                                                            have p17610_2 := h17610c.2.2.1
                                                            have p17610_3 := h17610c.2.2.2
                                                            linarith only [h17554, hlam, p17610_0]
                                                          · have p17610_0 := h17610c.1
                                                            have p17610_1 := h17610c.2.1
                                                            have p17610_2 := h17610c.2.2.1
                                                            have p17610_3 := h17610c.2.2.2
                                                            linarith only [h17554, h17558, hc02, hc45, hlam, hphi, ht0b, ht5b, p17590_1, p17610_1]
                                                          · have p17610_0 := h17610c.1
                                                            have p17610_1 := h17610c.2.1
                                                            have p17610_2 := h17610c.2.2.1
                                                            have p17610_3 := h17610c.2.2.2
                                                            linarith only [h17539, h17549, h17556, h17558, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p17559_1, p17610_1]
                                                          · have p17610_0 := h17610c.1
                                                            have p17610_1 := h17610c.2.1
                                                            have p17610_2 := h17610c.2.2.1
                                                            have p17610_3 := h17610c.2.2.2
                                                            rcases p17610_3 (m.d 0 3) (by simp) with h17631 | h17631
                                                            · linarith only [h17543, h17631, hlam]
                                                            · linarith only [h15532, h17631, hlam]
                                                          · have p17610_0 := h17610c.1
                                                            have p17610_1 := h17610c.2.1
                                                            have p17610_2 := h17610c.2.2.1
                                                            have p17610_3 := h17610c.2.2.2
                                                            rcases p17610_3 (m.d 0 3) (by simp) with h17634 | h17634
                                                            · linarith only [h17543, h17634, hlam]
                                                            · linarith only [h17540, h17634, hlam]
                                                          · have p17610_0 := h17610c.1
                                                            have p17610_1 := h17610c.2.1
                                                            have p17610_2 := h17610c.2.2.1
                                                            have p17610_3 := h17610c.2.2.2
                                                            linarith only [hlam, p17610_0]
                                                          · have p17610_0 := h17610c.1
                                                            have p17610_1 := h17610c.2.1
                                                            have p17610_2 := h17610c.2.2.1
                                                            have p17610_3 := h17610c.2.2.2
                                                            linarith only [h15532, h15533, h17539, h17549, h17550, h17556, hlam, p17559_1, p17610_2]
                                                          · have p17610_0 := h17610c.1
                                                            have p17610_1 := h17610c.2.1
                                                            have p17610_2 := h17610c.2.2.1
                                                            have p17610_3 := h17610c.2.2.2
                                                            linarith only [h17545, hlam, p17610_0]
                                                          · have p17610_0 := h17610c.1
                                                            have p17610_1 := h17610c.2.1
                                                            have p17610_2 := h17610c.2.2.1
                                                            have p17610_3 := h17610c.2.2.2
                                                            linarith only [h17552, hlam, p17610_0]
                                                          · have p17610_0 := h17610c.1
                                                            have p17610_1 := h17610c.2.1
                                                            have p17610_2 := h17610c.2.2.1
                                                            have p17610_3 := h17610c.2.2.2
                                                            linarith only [h17556, hlam, p17610_0]
                                                          · have p17610_0 := h17610c.1
                                                            have p17610_1 := h17610c.2.1
                                                            have p17610_2 := h17610c.2.2.1
                                                            have p17610_3 := h17610c.2.2.2
                                                            linarith only [h17558, hlam, p17610_0]
                                                          · have p17610_0 := h17610c.1
                                                            have p17610_1 := h17610c.2.1
                                                            have p17610_2 := h17610c.2.2.1
                                                            have p17610_3 := h17610c.2.2.2
                                                            linarith only [hlam, p17610_0]
                                                  · linarith only [h17548, h17603, hlam]
                                                · linarith only [h17602, hlam, p17590_0]
                                              · have p17590_0 := h17590c.1
                                                have p17590_1 := h17590c.2.1
                                                have p17590_2 := h17590c.2.2.1
                                                have p17590_3 := h17590c.2.2.2
                                                rcases p17590_3 (m.d 0 2) (by simp) with h17646 | h17646
                                                · rcases p17590_3 (m.d 1 2) (by simp) with h17647 | h17647
                                                  · rcases p17590_3 (m.d 2 3) (by simp) with h17648 | h17648
                                                    · linarith only [h17540, h17648, hlam]
                                                    · linarith only [h17556, h17648, hlam]
                                                  · linarith only [h17549, h17647, hlam]
                                                · linarith only [h17646, hlam, p17590_0]
                                              · have p17590_0 := h17590c.1
                                                have p17590_1 := h17590c.2.1
                                                have p17590_2 := h17590c.2.2.1
                                                have p17590_3 := h17590c.2.2.2
                                                linarith only [h0, h15532, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p17559_1, p17590_1]
                                              · have p17590_0 := h17590c.1
                                                have p17590_1 := h17590c.2.1
                                                have p17590_2 := h17590c.2.2.1
                                                have p17590_3 := h17590c.2.2.2
                                                linarith only [hlam, p17590_0]
                                              · have p17590_0 := h17590c.1
                                                have p17590_1 := h17590c.2.1
                                                have p17590_2 := h17590c.2.2.1
                                                have p17590_3 := h17590c.2.2.2
                                                rcases p17590_3 (m.d 0 2) (by simp) with h17655 | h17655
                                                · linarith only [h0, h17655, hlam]
                                                · linarith only [h17540, h17655, hlam]
                                              · have p17590_0 := h17590c.1
                                                have p17590_1 := h17590c.2.1
                                                have p17590_2 := h17590c.2.2.1
                                                have p17590_3 := h17590c.2.2.2
                                                rcases p17590_3 (m.d 0 2) (by simp) with h17658 | h17658
                                                · linarith only [h0, h17658, hlam]
                                                · linarith only [h17541, h17658, hlam]
                                              · have p17590_0 := h17590c.1
                                                have p17590_1 := h17590c.2.1
                                                have p17590_2 := h17590c.2.2.1
                                                have p17590_3 := h17590c.2.2.2
                                                linarith only [h0, h15532, h17539, h17549, hlam, p17559_1, p17590_2]
                                              · have p17590_0 := h17590c.1
                                                have p17590_1 := h17590c.2.1
                                                have p17590_2 := h17590c.2.2.1
                                                have p17590_3 := h17590c.2.2.2
                                                linarith only [h17540, hlam, p17590_0]
                                              · have p17590_0 := h17590c.1
                                                have p17590_1 := h17590c.2.1
                                                have p17590_2 := h17590c.2.2.1
                                                have p17590_3 := h17590c.2.2.2
                                                linarith only [h17547, hlam, p17590_0]
                                              · have p17590_0 := h17590c.1
                                                have p17590_1 := h17590c.2.1
                                                have p17590_2 := h17590c.2.2.1
                                                have p17590_3 := h17590c.2.2.2
                                                linarith only [hlam, p17590_0]
                                              · have p17590_0 := h17590c.1
                                                have p17590_1 := h17590c.2.1
                                                have p17590_2 := h17590c.2.2.1
                                                have p17590_3 := h17590c.2.2.2
                                                linarith only [h17554, hlam, p17590_0]
                                              · have p17590_0 := h17590c.1
                                                have p17590_1 := h17590c.2.1
                                                have p17590_2 := h17590c.2.2.1
                                                have p17590_3 := h17590c.2.2.2
                                                linarith only [h15532, h15533, h17547, h17550, h17556, h17558, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p17590_1]
                                              · have p17590_0 := h17590c.1
                                                have p17590_1 := h17590c.2.1
                                                have p17590_2 := h17590c.2.2.1
                                                have p17590_3 := h17590c.2.2.2
                                                linarith only [h17541, hlam, p17590_0]
                                              · have p17590_0 := h17590c.1
                                                have p17590_1 := h17590c.2.1
                                                have p17590_2 := h17590c.2.2.1
                                                have p17590_3 := h17590c.2.2.2
                                                linarith only [h17548, hlam, p17590_0]
                                              · have p17590_0 := h17590c.1
                                                have p17590_1 := h17590c.2.1
                                                have p17590_2 := h17590c.2.2.1
                                                have p17590_3 := h17590c.2.2.2
                                                linarith only [h0, h17541, h17556, h17558, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p17590_1]
                                              · have p17590_0 := h17590c.1
                                                have p17590_1 := h17590c.2.1
                                                have p17590_2 := h17590c.2.2.1
                                                have p17590_3 := h17590c.2.2.2
                                                linarith only [hlam, p17590_0]
                                              · have p17590_0 := h17590c.1
                                                have p17590_1 := h17590c.2.1
                                                have p17590_2 := h17590c.2.2.1
                                                have p17590_3 := h17590c.2.2.2
                                                rcases p17590_3 (m.d 0 2) (by simp) with h17671 | h17671
                                                · rcases p17590_3 (m.d 1 2) (by simp) with h17672 | h17672
                                                  · rcases p17590_3 (m.d 2 3) (by simp) with h17673 | h17673
                                                    · linarith only [h17554, h17673, hlam]
                                                    · linarith only [h17556, h17673, hlam]
                                                  · linarith only [h17549, h17672, hlam]
                                                · linarith only [h17542, h17671, hlam]
                                              · have p17590_0 := h17590c.1
                                                have p17590_1 := h17590c.2.1
                                                have p17590_2 := h17590c.2.2.1
                                                have p17590_3 := h17590c.2.2.2
                                                linarith only [h17542, hlam, p17590_0]
                                              · have p17590_0 := h17590c.1
                                                have p17590_1 := h17590c.2.1
                                                have p17590_2 := h17590c.2.2.1
                                                have p17590_3 := h17590c.2.2.2
                                                linarith only [h17549, hlam, p17590_0]
                                              · have p17590_0 := h17590c.1
                                                have p17590_1 := h17590c.2.1
                                                have p17590_2 := h17590c.2.2.1
                                                have p17590_3 := h17590c.2.2.2
                                                linarith only [h17556, hlam, p17590_1]
                                              · have p17590_0 := h17590c.1
                                                have p17590_1 := h17590c.2.1
                                                have p17590_2 := h17590c.2.2.1
                                                have p17590_3 := h17590c.2.2.2
                                                linarith only [h17557, hlam, p17590_0]
                                              · have p17590_0 := h17590c.1
                                                have p17590_1 := h17590c.2.1
                                                have p17590_2 := h17590c.2.2.1
                                                have p17590_3 := h17590c.2.2.2
                                                linarith only [hlam, p17590_0]
                                          · linarith only [h17546, h17587, hlam]
                                        · linarith only [h17545, h17586, hlam]
                                      · linarith only [h17542, h17585, hlam]
                                    · linarith only [h17539, h17584, hlam]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [h15532, h15533, h17550, hc13, hc34, hlam, hphi, p17559_1]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [h17541, hlam, p17559_0]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    rcases p17559_3 (m.d 0 1) (by simp) with h17689 | h17689
                                    · linarith only [h15533, h17689, hlam]
                                    · linarith only [h15532, h17689, hlam]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [hlam, p17559_0]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    rcases p17559_3 (m.d 0 1) (by simp) with h17693 | h17693
                                    · linarith only [h15533, h17693, hlam]
                                    · linarith only [h17539, h17693, hlam]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [h17539, hlam, p17559_0]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [h17542, hlam, p17559_1]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [h17545, hlam, p17559_0]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [h17546, hlam, p17559_1]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [hlam, p17559_0]
                                · linarith only [h15532, h15533, h17550, h17558, hc13, hc45, hlam, hphi, ht34]
                              · linarith only [h15532, h15533, h17552, h17553, h17554, h17556, h17557, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h15532, h15533, h17545, h17550, h17556, hc23, hc34, hlam, hphi]
                        · linarith only [h15532, h15533, h17553, hc13, hc45, hlam, hphi, ht34]
                      · linarith only [h15532, h15533, h17545, h17550, h17552, hc13, hc34, hlam, hphi]
                  · linarith only [h0, h17542, h17549, hlam]
                · linarith only [h0, h17541, h17548, hlam]
              · linarith only [h0, h17540, h17547, hlam]
            · linarith only [h15533, h17539, h17546, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h17710 | h17710
            · rcases m.htr 1 2 3 (by decide) (by decide) with h17711 | h17711
              · rcases m.htr 1 2 4 (by decide) (by decide) with h17712 | h17712
                · rcases m.htr 1 2 5 (by decide) (by decide) with h17713 | h17713
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h17714 | h17714
                    · linarith only [h15532, h15533, h17543, h17712, h17714, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h17716 | h17716
                      · linarith only [h15532, h17545, h17716, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h17718 | h17718
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h17719 | h17719
                          · linarith only [h15533, h17539, h17540, h17714, h17716, h17719, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h17721 | h17721
                            · linarith only [h15532, h17545, h17711, h17721, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h17723 | h17723
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h17724 | h17724
                                · rcases h0bigk with h17725c | h17725c | h17725c | h17725c | h17725c | h17725c | h17725c | h17725c | h17725c | h17725c | h17725c | h17725c | h17725c | h17725c | h17725c | h17725c | h17725c | h17725c | h17725c | h17725c | h17725c | h17725c | h17725c | h17725c | h17725c
                                  · have p17725_0 := h17725c.1
                                    have p17725_1 := h17725c.2.1
                                    have p17725_2 := h17725c.2.2.1
                                    have p17725_3 := h17725c.2.2.2
                                    linarith only [hlam, p17725_0]
                                  · have p17725_0 := h17725c.1
                                    have p17725_1 := h17725c.2.1
                                    have p17725_2 := h17725c.2.2.1
                                    have p17725_3 := h17725c.2.2.2
                                    linarith only [h0, hlam, p17725_1]
                                  · have p17725_0 := h17725c.1
                                    have p17725_1 := h17725c.2.1
                                    have p17725_2 := h17725c.2.2.1
                                    have p17725_3 := h17725c.2.2.2
                                    linarith only [h15532, h15533, h17711, h17714, hc23, hc34, hlam, hphi, p17725_1]
                                  · have p17725_0 := h17725c.1
                                    have p17725_1 := h17725c.2.1
                                    have p17725_2 := h17725c.2.2.1
                                    have p17725_3 := h17725c.2.2.2
                                    linarith only [h15533, hlam, p17725_1]
                                  · have p17725_0 := h17725c.1
                                    have p17725_1 := h17725c.2.1
                                    have p17725_2 := h17725c.2.2.1
                                    have p17725_3 := h17725c.2.2.2
                                    linarith only [h15532, h15533, h17545, h17711, h17714, hc23, hc34, hlam, hphi, p17725_1]
                                  · have p17725_0 := h17725c.1
                                    have p17725_1 := h17725c.2.1
                                    have p17725_2 := h17725c.2.2.1
                                    have p17725_3 := h17725c.2.2.2
                                    rcases p17725_3 (m.d 0 1) (by simp) with h17731 | h17731
                                    · linarith only [h0, h17731, hlam]
                                    · rcases p17725_3 (m.d 0 2) (by simp) with h17733 | h17733
                                      · rcases p17725_3 (m.d 0 3) (by simp) with h17734 | h17734
                                        · linarith only [h17540, h17734, hlam]
                                        · rcases p17725_3 (m.d 0 4) (by simp) with h17736 | h17736
                                          · linarith only [h17541, h17736, hlam]
                                          · linarith only [h15533, h17736, hlam]
                                      · linarith only [h0, h17733, hlam]
                                  · have p17725_0 := h17725c.1
                                    have p17725_1 := h17725c.2.1
                                    have p17725_2 := h17725c.2.2.1
                                    have p17725_3 := h17725c.2.2.2
                                    linarith only [hlam, p17725_0]
                                  · have p17725_0 := h17725c.1
                                    have p17725_1 := h17725c.2.1
                                    have p17725_2 := h17725c.2.2.1
                                    have p17725_3 := h17725c.2.2.2
                                    rcases p17725_3 (m.d 0 1) (by simp) with h17741 | h17741
                                    · linarith only [h0, h17741, hlam]
                                    · linarith only [h15532, h17741, hlam]
                                  · have p17725_0 := h17725c.1
                                    have p17725_1 := h17725c.2.1
                                    have p17725_2 := h17725c.2.2.1
                                    have p17725_3 := h17725c.2.2.2
                                    rcases p17725_3 (m.d 0 1) (by simp) with h17744 | h17744
                                    · linarith only [h0, h17744, hlam]
                                    · rcases p17725_3 (m.d 0 2) (by simp) with h17746 | h17746
                                      · rcases p17725_3 (m.d 0 3) (by simp) with h17747 | h17747
                                        · linarith only [h17540, h17747, hlam]
                                        · rcases p17725_3 (m.d 0 4) (by simp) with h17749 | h17749
                                          · linarith only [h17541, h17749, hlam]
                                          · rcases p17725_3 (m.d 0 5) (by simp) with h17751 | h17751
                                            · linarith only [h17542, h17751, hlam]
                                            · rcases h2bigk with h17753c | h17753c | h17753c | h17753c | h17753c | h17753c | h17753c | h17753c | h17753c | h17753c | h17753c | h17753c | h17753c | h17753c | h17753c | h17753c | h17753c | h17753c | h17753c | h17753c | h17753c | h17753c | h17753c | h17753c | h17753c
                                              · have p17753_0 := h17753c.1
                                                have p17753_1 := h17753c.2.1
                                                have p17753_2 := h17753c.2.2.1
                                                have p17753_3 := h17753c.2.2.2
                                                linarith only [hlam, p17753_0]
                                              · have p17753_0 := h17753c.1
                                                have p17753_1 := h17753c.2.1
                                                have p17753_2 := h17753c.2.2.1
                                                have p17753_3 := h17753c.2.2.2
                                                linarith only [h0, hlam, p17753_1]
                                              · have p17753_0 := h17753c.1
                                                have p17753_1 := h17753c.2.1
                                                have p17753_2 := h17753c.2.2.1
                                                have p17753_3 := h17753c.2.2.2
                                                linarith only [h15532, h15533, h17711, hlam, p17725_1, p17753_2]
                                              · have p17753_0 := h17753c.1
                                                have p17753_1 := h17753c.2.1
                                                have p17753_2 := h17753c.2.2.1
                                                have p17753_3 := h17753c.2.2.2
                                                rcases p17753_3 (m.d 0 2) (by simp) with h17757 | h17757
                                                · rcases p17753_3 (m.d 1 2) (by simp) with h17758 | h17758
                                                  · rcases p17753_3 (m.d 2 3) (by simp) with h17759 | h17759
                                                    · linarith only [h17540, h17759, hlam]
                                                    · rcases p17753_3 (m.d 2 4) (by simp) with h17761 | h17761
                                                      · linarith only [h17761, hlam, p17753_0]
                                                      · rcases p17753_3 (m.d 2 5) (by simp) with h17763 | h17763
                                                        · linarith only [h17542, h17763, hlam]
                                                        · rcases h3bigk with h17765c | h17765c | h17765c | h17765c | h17765c | h17765c | h17765c | h17765c | h17765c | h17765c | h17765c | h17765c | h17765c | h17765c | h17765c | h17765c | h17765c | h17765c | h17765c | h17765c | h17765c | h17765c | h17765c | h17765c | h17765c
                                                          · have p17765_0 := h17765c.1
                                                            have p17765_1 := h17765c.2.1
                                                            have p17765_2 := h17765c.2.2.1
                                                            have p17765_3 := h17765c.2.2.2
                                                            linarith only [hlam, p17765_0]
                                                          · have p17765_0 := h17765c.1
                                                            have p17765_1 := h17765c.2.1
                                                            have p17765_2 := h17765c.2.2.1
                                                            have p17765_3 := h17765c.2.2.2
                                                            linarith only [h17545, hc13, hc35, hlam, hphi, p17765_1]
                                                          · have p17765_0 := h17765c.1
                                                            have p17765_1 := h17765c.2.1
                                                            have p17765_2 := h17765c.2.2.1
                                                            have p17765_3 := h17765c.2.2.2
                                                            linarith only [h0, h15533, h17539, h17545, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17725_1, p17765_1]
                                                          · have p17765_0 := h17765c.1
                                                            have p17765_1 := h17765c.2.1
                                                            have p17765_2 := h17765c.2.2.1
                                                            have p17765_3 := h17765c.2.2.2
                                                            linarith only [h17543, hlam, p17765_0]
                                                          · have p17765_0 := h17765c.1
                                                            have p17765_1 := h17765c.2.1
                                                            have p17765_2 := h17765c.2.2.1
                                                            have p17765_3 := h17765c.2.2.2
                                                            linarith only [h17545, hlam, p17765_0]
                                                          · have p17765_0 := h17765c.1
                                                            have p17765_1 := h17765c.2.1
                                                            have p17765_2 := h17765c.2.2.1
                                                            have p17765_3 := h17765c.2.2.2
                                                            linarith only [h15532, hlam, p17765_0]
                                                          · have p17765_0 := h17765c.1
                                                            have p17765_1 := h17765c.2.1
                                                            have p17765_2 := h17765c.2.2.1
                                                            have p17765_3 := h17765c.2.2.2
                                                            linarith only [hlam, p17765_0]
                                                          · have p17765_0 := h17765c.1
                                                            have p17765_1 := h17765c.2.1
                                                            have p17765_2 := h17765c.2.2.1
                                                            have p17765_3 := h17765c.2.2.2
                                                            linarith only [h0, h15533, h17539, h17716, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17725_1, p17765_1]
                                                          · have p17765_0 := h17765c.1
                                                            have p17765_1 := h17765c.2.1
                                                            have p17765_2 := h17765c.2.2.1
                                                            have p17765_3 := h17765c.2.2.2
                                                            linarith only [h17714, hlam, p17765_0]
                                                          · have p17765_0 := h17765c.1
                                                            have p17765_1 := h17765c.2.1
                                                            have p17765_2 := h17765c.2.2.1
                                                            have p17765_3 := h17765c.2.2.2
                                                            linarith only [h17716, hlam, p17765_0]
                                                          · have p17765_0 := h17765c.1
                                                            have p17765_1 := h17765c.2.1
                                                            have p17765_2 := h17765c.2.2.1
                                                            have p17765_3 := h17765c.2.2.2
                                                            linarith only [h17540, hlam, p17765_0]
                                                          · have p17765_0 := h17765c.1
                                                            have p17765_1 := h17765c.2.1
                                                            have p17765_2 := h17765c.2.2.1
                                                            have p17765_3 := h17765c.2.2.2
                                                            linarith only [h17711, hlam, p17765_0]
                                                          · have p17765_0 := h17765c.1
                                                            have p17765_1 := h17765c.2.1
                                                            have p17765_2 := h17765c.2.2.1
                                                            have p17765_3 := h17765c.2.2.2
                                                            linarith only [hlam, p17765_0]
                                                          · have p17765_0 := h17765c.1
                                                            have p17765_1 := h17765c.2.1
                                                            have p17765_2 := h17765c.2.2.1
                                                            have p17765_3 := h17765c.2.2.2
                                                            linarith only [h17719, hlam, p17765_0]
                                                          · have p17765_0 := h17765c.1
                                                            have p17765_1 := h17765c.2.1
                                                            have p17765_2 := h17765c.2.2.1
                                                            have p17765_3 := h17765c.2.2.2
                                                            linarith only [h17721, hlam, p17765_0]
                                                          · have p17765_0 := h17765c.1
                                                            have p17765_1 := h17765c.2.1
                                                            have p17765_2 := h17765c.2.2.1
                                                            have p17765_3 := h17765c.2.2.2
                                                            rcases p17765_3 (m.d 0 3) (by simp) with h17781 | h17781
                                                            · linarith only [h17781, hlam, p17765_0]
                                                            · rcases p17765_3 (m.d 1 3) (by simp) with h17783 | h17783
                                                              · linarith only [h17714, h17783, hlam]
                                                              · rcases p17765_3 (m.d 2 3) (by simp) with h17785 | h17785
                                                                · linarith only [h17719, h17785, hlam]
                                                                · rcases p17765_3 (m.d 3 4) (by simp) with h17787 | h17787
                                                                  · rcases p17765_3 (m.d 3 5) (by simp) with h17788 | h17788
                                                                    · linarith only [h17724, h17788, hlam]
                                                                    · linarith only [h17545, h17788, hlam]
                                                                  · linarith only [h17787, hlam, p17765_0]
                                                          · have p17765_0 := h17765c.1
                                                            have p17765_1 := h17765c.2.1
                                                            have p17765_2 := h17765c.2.2.1
                                                            have p17765_3 := h17765c.2.2.2
                                                            rcases p17765_3 (m.d 0 3) (by simp) with h17792 | h17792
                                                            · linarith only [h17543, h17792, hlam]
                                                            · linarith only [h15532, h17792, hlam]
                                                          · have p17765_0 := h17765c.1
                                                            have p17765_1 := h17765c.2.1
                                                            have p17765_2 := h17765c.2.2.1
                                                            have p17765_3 := h17765c.2.2.2
                                                            rcases p17765_3 (m.d 0 3) (by simp) with h17795 | h17795
                                                            · linarith only [h17543, h17795, hlam]
                                                            · linarith only [h17540, h17795, hlam]
                                                          · have p17765_0 := h17765c.1
                                                            have p17765_1 := h17765c.2.1
                                                            have p17765_2 := h17765c.2.2.1
                                                            have p17765_3 := h17765c.2.2.2
                                                            linarith only [hlam, p17765_0]
                                                          · have p17765_0 := h17765c.1
                                                            have p17765_1 := h17765c.2.1
                                                            have p17765_2 := h17765c.2.2.1
                                                            have p17765_3 := h17765c.2.2.2
                                                            linarith only [h17545, hc03, hc34, hlam, hphi, p17765_1]
                                                          · have p17765_0 := h17765c.1
                                                            have p17765_1 := h17765c.2.1
                                                            have p17765_2 := h17765c.2.2.1
                                                            have p17765_3 := h17765c.2.2.2
                                                            rcases p17765_3 (m.d 0 3) (by simp) with h17800 | h17800
                                                            · linarith only [h17800, hlam, p17765_0]
                                                            · rcases p17765_3 (m.d 1 3) (by simp) with h17802 | h17802
                                                              · linarith only [h17716, h17802, hlam]
                                                              · rcases p17765_3 (m.d 2 3) (by simp) with h17804 | h17804
                                                                · linarith only [h17721, h17804, hlam]
                                                                · rcases p17765_3 (m.d 3 4) (by simp) with h17806 | h17806
                                                                  · rcases p17765_3 (m.d 3 5) (by simp) with h17807 | h17807
                                                                    · rcases h5bigk with h17808c | h17808c | h17808c | h17808c | h17808c | h17808c | h17808c | h17808c | h17808c | h17808c | h17808c | h17808c | h17808c | h17808c | h17808c | h17808c | h17808c | h17808c | h17808c | h17808c | h17808c | h17808c | h17808c | h17808c | h17808c
                                                                      · have p17808_0 := h17808c.1
                                                                        have p17808_1 := h17808c.2.1
                                                                        have p17808_2 := h17808c.2.2.1
                                                                        have p17808_3 := h17808c.2.2.2
                                                                        linarith only [hlam, p17808_0]
                                                                      · have p17808_0 := h17808c.1
                                                                        have p17808_1 := h17808c.2.1
                                                                        have p17808_2 := h17808c.2.2.1
                                                                        have p17808_3 := h17808c.2.2.2
                                                                        linarith only [h0, h15533, h17539, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p17725_1, p17808_1]
                                                                      · have p17808_0 := h17808c.1
                                                                        have p17808_1 := h17808c.2.1
                                                                        have p17808_2 := h17808c.2.2.1
                                                                        have p17808_3 := h17808c.2.2.2
                                                                        linarith only [h0, h15533, h17539, h17721, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17725_1, p17808_1]
                                                                      · have p17808_0 := h17808c.1
                                                                        have p17808_1 := h17808c.2.1
                                                                        have p17808_2 := h17808c.2.2.1
                                                                        have p17808_3 := h17808c.2.2.2
                                                                        linarith only [h17545, hlam, p17808_1]
                                                                      · have p17808_0 := h17808c.1
                                                                        have p17808_1 := h17808c.2.1
                                                                        have p17808_2 := h17808c.2.2.1
                                                                        have p17808_3 := h17808c.2.2.2
                                                                        linarith only [h0, h15533, h17539, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p17725_1, p17808_1]
                                                                      · have p17808_0 := h17808c.1
                                                                        have p17808_1 := h17808c.2.1
                                                                        have p17808_2 := h17808c.2.2.1
                                                                        have p17808_3 := h17808c.2.2.2
                                                                        linarith only [h17539, hlam, p17808_0]
                                                                      · have p17808_0 := h17808c.1
                                                                        have p17808_1 := h17808c.2.1
                                                                        have p17808_2 := h17808c.2.2.1
                                                                        have p17808_3 := h17808c.2.2.2
                                                                        linarith only [hlam, p17808_0]
                                                                      · have p17808_0 := h17808c.1
                                                                        have p17808_1 := h17808c.2.1
                                                                        have p17808_2 := h17808c.2.2.1
                                                                        have p17808_3 := h17808c.2.2.2
                                                                        linarith only [h0, h15533, h17539, h17721, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17725_1, p17808_1]
                                                                      · have p17808_0 := h17808c.1
                                                                        have p17808_1 := h17808c.2.1
                                                                        have p17808_2 := h17808c.2.2.1
                                                                        have p17808_3 := h17808c.2.2.2
                                                                        linarith only [h17716, hlam, p17808_1]
                                                                      · have p17808_0 := h17808c.1
                                                                        have p17808_1 := h17808c.2.1
                                                                        have p17808_2 := h17808c.2.2.1
                                                                        have p17808_3 := h17808c.2.2.2
                                                                        linarith only [h0, h15533, h17539, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p17725_1, p17808_1]
                                                                      · have p17808_0 := h17808c.1
                                                                        have p17808_1 := h17808c.2.1
                                                                        have p17808_2 := h17808c.2.2.1
                                                                        have p17808_3 := h17808c.2.2.2
                                                                        linarith only [h17542, hlam, p17808_1]
                                                                      · have p17808_0 := h17808c.1
                                                                        have p17808_1 := h17808c.2.1
                                                                        have p17808_2 := h17808c.2.2.1
                                                                        have p17808_3 := h17808c.2.2.2
                                                                        linarith only [h17713, hlam, p17808_1]
                                                                      · have p17808_0 := h17808c.1
                                                                        have p17808_1 := h17808c.2.1
                                                                        have p17808_2 := h17808c.2.2.1
                                                                        have p17808_3 := h17808c.2.2.2
                                                                        linarith only [hlam, p17808_0]
                                                                      · have p17808_0 := h17808c.1
                                                                        have p17808_1 := h17808c.2.1
                                                                        have p17808_2 := h17808c.2.2.1
                                                                        have p17808_3 := h17808c.2.2.2
                                                                        linarith only [h17721, hlam, p17808_1]
                                                                      · have p17808_0 := h17808c.1
                                                                        have p17808_1 := h17808c.2.1
                                                                        have p17808_2 := h17808c.2.2.1
                                                                        have p17808_3 := h17808c.2.2.2
                                                                        linarith only [h0, h17542, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p17808_1]
                                                                      · have p17808_0 := h17808c.1
                                                                        have p17808_1 := h17808c.2.1
                                                                        have p17808_2 := h17808c.2.2.1
                                                                        have p17808_3 := h17808c.2.2.2
                                                                        linarith only [h15532, h17545, h17711, hc23, hc35, hlam, hphi, p17808_1]
                                                                      · have p17808_0 := h17808c.1
                                                                        have p17808_1 := h17808c.2.1
                                                                        have p17808_2 := h17808c.2.2.1
                                                                        have p17808_3 := h17808c.2.2.2
                                                                        linarith only [h17711, h17716, hc23, hc35, hlam, hphi, p17808_1]
                                                                      · have p17808_0 := h17808c.1
                                                                        have p17808_1 := h17808c.2.1
                                                                        have p17808_2 := h17808c.2.2.1
                                                                        have p17808_3 := h17808c.2.2.2
                                                                        linarith only [h17721, hc23, hc35, hlam, hphi, p17808_1]
                                                                      · have p17808_0 := h17808c.1
                                                                        have p17808_1 := h17808c.2.1
                                                                        have p17808_2 := h17808c.2.2.1
                                                                        have p17808_3 := h17808c.2.2.2
                                                                        linarith only [hlam, p17808_0]
                                                                      · have p17808_0 := h17808c.1
                                                                        have p17808_1 := h17808c.2.1
                                                                        have p17808_2 := h17808c.2.2.1
                                                                        have p17808_3 := h17808c.2.2.2
                                                                        rcases p17808_3 (m.d 0 5) (by simp) with h17828 | h17828
                                                                        · linarith only [h17545, h17828, hlam]
                                                                        · linarith only [h17710, h17828, hlam]
                                                                      · have p17808_0 := h17808c.1
                                                                        have p17808_1 := h17808c.2.1
                                                                        have p17808_2 := h17808c.2.2.1
                                                                        have p17808_3 := h17808c.2.2.2
                                                                        linarith only [h17710, hlam, p17808_0]
                                                                      · have p17808_0 := h17808c.1
                                                                        have p17808_1 := h17808c.2.1
                                                                        have p17808_2 := h17808c.2.2.1
                                                                        have p17808_3 := h17808c.2.2.2
                                                                        linarith only [h17718, hlam, p17808_0]
                                                                      · have p17808_0 := h17808c.1
                                                                        have p17808_1 := h17808c.2.1
                                                                        have p17808_2 := h17808c.2.2.1
                                                                        have p17808_3 := h17808c.2.2.2
                                                                        linarith only [h17723, hlam, p17808_0]
                                                                      · have p17808_0 := h17808c.1
                                                                        have p17808_1 := h17808c.2.1
                                                                        have p17808_2 := h17808c.2.2.1
                                                                        have p17808_3 := h17808c.2.2.2
                                                                        linarith only [h17724, hlam, p17808_0]
                                                                      · have p17808_0 := h17808c.1
                                                                        have p17808_1 := h17808c.2.1
                                                                        have p17808_2 := h17808c.2.2.1
                                                                        have p17808_3 := h17808c.2.2.2
                                                                        linarith only [hlam, p17808_0]
                                                                    · linarith only [h17807, hlam, p17765_0]
                                                                  · linarith only [h17543, h17806, hlam]
                                                          · have p17765_0 := h17765c.1
                                                            have p17765_1 := h17765c.2.1
                                                            have p17765_2 := h17765c.2.2.1
                                                            have p17765_3 := h17765c.2.2.2
                                                            rcases p17765_3 (m.d 0 3) (by simp) with h17838 | h17838
                                                            · linarith only [h17545, h17838, hlam]
                                                            · linarith only [h15532, h17838, hlam]
                                                          · have p17765_0 := h17765c.1
                                                            have p17765_1 := h17765c.2.1
                                                            have p17765_2 := h17765c.2.2.1
                                                            have p17765_3 := h17765c.2.2.2
                                                            rcases p17765_3 (m.d 0 3) (by simp) with h17841 | h17841
                                                            · linarith only [h17545, h17841, hlam]
                                                            · linarith only [h17540, h17841, hlam]
                                                          · have p17765_0 := h17765c.1
                                                            have p17765_1 := h17765c.2.1
                                                            have p17765_2 := h17765c.2.2.1
                                                            have p17765_3 := h17765c.2.2.2
                                                            linarith only [h17724, hlam, p17765_0]
                                                          · have p17765_0 := h17765c.1
                                                            have p17765_1 := h17765c.2.1
                                                            have p17765_2 := h17765c.2.2.1
                                                            have p17765_3 := h17765c.2.2.2
                                                            linarith only [hlam, p17765_0]
                                                  · linarith only [h17712, h17758, hlam]
                                                · linarith only [h17757, hlam, p17753_0]
                                              · have p17753_0 := h17753c.1
                                                have p17753_1 := h17753c.2.1
                                                have p17753_2 := h17753c.2.2.1
                                                have p17753_3 := h17753c.2.2.2
                                                linarith only [h15533, h17539, h17713, hlam, p17725_1, p17753_2]
                                              · have p17753_0 := h17753c.1
                                                have p17753_1 := h17753c.2.1
                                                have p17753_2 := h17753c.2.2.1
                                                have p17753_3 := h17753c.2.2.2
                                                linarith only [h15533, hc01, hc12, hlam, hphi, p17725_1, p17753_1]
                                              · have p17753_0 := h17753c.1
                                                have p17753_1 := h17753c.2.1
                                                have p17753_2 := h17753c.2.2.1
                                                have p17753_3 := h17753c.2.2.2
                                                linarith only [hlam, p17753_0]
                                              · have p17753_0 := h17753c.1
                                                have p17753_1 := h17753c.2.1
                                                have p17753_2 := h17753c.2.2.1
                                                have p17753_3 := h17753c.2.2.2
                                                linarith only [h0, h15532, h15533, h17711, hlam, p17725_1, p17753_2]
                                              · have p17753_0 := h17753c.1
                                                have p17753_1 := h17753c.2.1
                                                have p17753_2 := h17753c.2.2.1
                                                have p17753_3 := h17753c.2.2.2
                                                rcases p17753_3 (m.d 0 2) (by simp) with h17852 | h17852
                                                · linarith only [h0, h17852, hlam]
                                                · linarith only [h17541, h17852, hlam]
                                              · have p17753_0 := h17753c.1
                                                have p17753_1 := h17753c.2.1
                                                have p17753_2 := h17753c.2.2.1
                                                have p17753_3 := h17753c.2.2.2
                                                linarith only [h0, h15533, h17539, h17713, hlam, p17725_1, p17753_2]
                                              · have p17753_0 := h17753c.1
                                                have p17753_1 := h17753c.2.1
                                                have p17753_2 := h17753c.2.2.1
                                                have p17753_3 := h17753c.2.2.2
                                                linarith only [h17540, hlam, p17753_0]
                                              · have p17753_0 := h17753c.1
                                                have p17753_1 := h17753c.2.1
                                                have p17753_2 := h17753c.2.2.1
                                                have p17753_3 := h17753c.2.2.2
                                                linarith only [h17711, hlam, p17753_0]
                                              · have p17753_0 := h17753c.1
                                                have p17753_1 := h17753c.2.1
                                                have p17753_2 := h17753c.2.2.1
                                                have p17753_3 := h17753c.2.2.2
                                                linarith only [hlam, p17753_0]
                                              · have p17753_0 := h17753c.1
                                                have p17753_1 := h17753c.2.1
                                                have p17753_2 := h17753c.2.2.1
                                                have p17753_3 := h17753c.2.2.2
                                                linarith only [h17719, hlam, p17753_0]
                                              · have p17753_0 := h17753c.1
                                                have p17753_1 := h17753c.2.1
                                                have p17753_2 := h17753c.2.2.1
                                                have p17753_3 := h17753c.2.2.2
                                                linarith only [h17721, hlam, p17753_0]
                                              · have p17753_0 := h17753c.1
                                                have p17753_1 := h17753c.2.1
                                                have p17753_2 := h17753c.2.2.1
                                                have p17753_3 := h17753c.2.2.2
                                                linarith only [h17541, hlam, p17753_0]
                                              · have p17753_0 := h17753c.1
                                                have p17753_1 := h17753c.2.1
                                                have p17753_2 := h17753c.2.2.1
                                                have p17753_3 := h17753c.2.2.2
                                                linarith only [h17712, hlam, p17753_0]
                                              · have p17753_0 := h17753c.1
                                                have p17753_1 := h17753c.2.1
                                                have p17753_2 := h17753c.2.2.1
                                                have p17753_3 := h17753c.2.2.2
                                                linarith only [h17541, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p17725_1, p17753_1]
                                              · have p17753_0 := h17753c.1
                                                have p17753_1 := h17753c.2.1
                                                have p17753_2 := h17753c.2.2.1
                                                have p17753_3 := h17753c.2.2.2
                                                linarith only [hlam, p17753_0]
                                              · have p17753_0 := h17753c.1
                                                have p17753_1 := h17753c.2.1
                                                have p17753_2 := h17753c.2.2.1
                                                have p17753_3 := h17753c.2.2.2
                                                linarith only [h0, h17541, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p17725_1, p17753_1]
                                              · have p17753_0 := h17753c.1
                                                have p17753_1 := h17753c.2.1
                                                have p17753_2 := h17753c.2.2.1
                                                have p17753_3 := h17753c.2.2.2
                                                linarith only [h17542, hlam, p17753_0]
                                              · have p17753_0 := h17753c.1
                                                have p17753_1 := h17753c.2.1
                                                have p17753_2 := h17753c.2.2.1
                                                have p17753_3 := h17753c.2.2.2
                                                linarith only [h17713, hlam, p17753_0]
                                              · have p17753_0 := h17753c.1
                                                have p17753_1 := h17753c.2.1
                                                have p17753_2 := h17753c.2.2.1
                                                have p17753_3 := h17753c.2.2.2
                                                linarith only [h15533, h17539, h17542, h17714, hc23, hc34, hlam, hphi, p17753_1]
                                              · have p17753_0 := h17753c.1
                                                have p17753_1 := h17753c.2.1
                                                have p17753_2 := h17753c.2.2.1
                                                have p17753_3 := h17753c.2.2.2
                                                linarith only [h17723, hlam, p17753_0]
                                              · have p17753_0 := h17753c.1
                                                have p17753_1 := h17753c.2.1
                                                have p17753_2 := h17753c.2.2.1
                                                have p17753_3 := h17753c.2.2.2
                                                linarith only [hlam, p17753_0]
                                      · linarith only [h17541, h17746, hlam]
                                  · have p17725_0 := h17725c.1
                                    have p17725_1 := h17725c.2.1
                                    have p17725_2 := h17725c.2.2.1
                                    have p17725_3 := h17725c.2.2.2
                                    rcases p17725_3 (m.d 0 1) (by simp) with h17872 | h17872
                                    · linarith only [h0, h17872, hlam]
                                    · linarith only [h17539, h17872, hlam]
                                  · have p17725_0 := h17725c.1
                                    have p17725_1 := h17725c.2.1
                                    have p17725_2 := h17725c.2.2.1
                                    have p17725_3 := h17725c.2.2.2
                                    linarith only [h15532, hlam, p17725_1]
                                  · have p17725_0 := h17725c.1
                                    have p17725_1 := h17725c.2.1
                                    have p17725_2 := h17725c.2.2.1
                                    have p17725_3 := h17725c.2.2.2
                                    linarith only [h17540, hlam, p17725_1]
                                  · have p17725_0 := h17725c.1
                                    have p17725_1 := h17725c.2.1
                                    have p17725_2 := h17725c.2.2.1
                                    have p17725_3 := h17725c.2.2.2
                                    linarith only [hlam, p17725_0]
                                  · have p17725_0 := h17725c.1
                                    have p17725_1 := h17725c.2.1
                                    have p17725_2 := h17725c.2.2.1
                                    have p17725_3 := h17725c.2.2.2
                                    linarith only [h17543, hlam, p17725_1]
                                  · have p17725_0 := h17725c.1
                                    have p17725_1 := h17725c.2.1
                                    have p17725_2 := h17725c.2.2.1
                                    have p17725_3 := h17725c.2.2.2
                                    linarith only [h17545, hlam, p17725_1]
                                  · have p17725_0 := h17725c.1
                                    have p17725_1 := h17725c.2.1
                                    have p17725_2 := h17725c.2.2.1
                                    have p17725_3 := h17725c.2.2.2
                                    linarith only [h15532, h15533, h17711, h17714, hc23, hc34, hlam, hphi, p17725_1]
                                  · have p17725_0 := h17725c.1
                                    have p17725_1 := h17725c.2.1
                                    have p17725_2 := h17725c.2.2.1
                                    have p17725_3 := h17725c.2.2.2
                                    linarith only [h17541, hlam, p17725_0]
                                  · have p17725_0 := h17725c.1
                                    have p17725_1 := h17725c.2.1
                                    have p17725_2 := h17725c.2.2.1
                                    have p17725_3 := h17725c.2.2.2
                                    rcases p17725_3 (m.d 0 1) (by simp) with h17882 | h17882
                                    · linarith only [h15533, h17882, hlam]
                                    · linarith only [h15532, h17882, hlam]
                                  · have p17725_0 := h17725c.1
                                    have p17725_1 := h17725c.2.1
                                    have p17725_2 := h17725c.2.2.1
                                    have p17725_3 := h17725c.2.2.2
                                    linarith only [hlam, p17725_0]
                                  · have p17725_0 := h17725c.1
                                    have p17725_1 := h17725c.2.1
                                    have p17725_2 := h17725c.2.2.1
                                    have p17725_3 := h17725c.2.2.2
                                    rcases p17725_3 (m.d 0 1) (by simp) with h17886 | h17886
                                    · linarith only [h15533, h17886, hlam]
                                    · linarith only [h17539, h17886, hlam]
                                  · have p17725_0 := h17725c.1
                                    have p17725_1 := h17725c.2.1
                                    have p17725_2 := h17725c.2.2.1
                                    have p17725_3 := h17725c.2.2.2
                                    linarith only [h17539, hlam, p17725_0]
                                  · have p17725_0 := h17725c.1
                                    have p17725_1 := h17725c.2.1
                                    have p17725_2 := h17725c.2.2.1
                                    have p17725_3 := h17725c.2.2.2
                                    linarith only [h17542, hlam, p17725_1]
                                  · have p17725_0 := h17725c.1
                                    have p17725_1 := h17725c.2.1
                                    have p17725_2 := h17725c.2.2.1
                                    have p17725_3 := h17725c.2.2.2
                                    linarith only [h15532, h15533, h17539, h17711, h17714, hc23, hc34, hlam, hphi, p17725_1]
                                  · have p17725_0 := h17725c.1
                                    have p17725_1 := h17725c.2.1
                                    have p17725_2 := h17725c.2.2.1
                                    have p17725_3 := h17725c.2.2.2
                                    linarith only [h17710, hlam, p17725_1]
                                  · have p17725_0 := h17725c.1
                                    have p17725_1 := h17725c.2.1
                                    have p17725_2 := h17725c.2.2.1
                                    have p17725_3 := h17725c.2.2.2
                                    linarith only [hlam, p17725_0]
                                · linarith only [h15532, h15533, h17711, h17714, h17724, hc23, hc45, hlam, hphi, ht34]
                              · linarith only [h15533, h17539, h17714, h17718, h17719, h17723, hc23, hc34, hlam, hphi]
                        · linarith only [h15532, h15533, h17711, h17718, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h17542, h17713, hlam]
                · linarith only [h0, h17541, h17712, hlam]
              · linarith only [h0, h17540, h17711, hlam]
            · linarith only [h15533, h17539, h17710, hlam]
      · linarith only [h0, h17539, h17542, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h17902 | h17902
      · rcases m.htr 0 3 4 (by decide) (by decide) with h17903 | h17903
        · linarith only [h0, h15532, h17541, h17903, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h17905 | h17905
          · rcases m.htr 0 4 5 (by decide) (by decide) with h17906 | h17906
            · rcases m.htr 1 2 3 (by decide) (by decide) with h17907 | h17907
              · rcases m.htr 1 2 4 (by decide) (by decide) with h17908 | h17908
                · rcases m.htr 1 2 5 (by decide) (by decide) with h17909 | h17909
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h17910 | h17910
                    · linarith only [h0, h15532, h17541, h17903, h17908, h17910, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h17912 | h17912
                      · linarith only [h0, h15532, h17541, h17908, h17912, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h0, h15532, h17541, h17905, h17907, h17908, h17912, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h17541, h17908, h17909, hc01, hc25, hlam, hphi, ht12]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h17916 | h17916
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h17917 | h17917
                    · linarith only [h0, h15532, h17541, h17903, h17908, h17917, hc02, hc24, hlam, hphi]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h17919 | h17919
                      · linarith only [h0, h15532, h17908, h17919, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h15532, h17905, h17907, h17908, h17919, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h0, h17539, h17541, h17902, h17916, hc04, hc15, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h15532, h17540, h17907, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · linarith only [h0, h15532, h17541, h17905, h17906, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h17925 | h17925
            · rcases m.htr 1 2 3 (by decide) (by decide) with h17926 | h17926
              · rcases m.htr 1 2 4 (by decide) (by decide) with h17927 | h17927
                · rcases m.htr 1 2 5 (by decide) (by decide) with h17928 | h17928
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h17929 | h17929
                    · linarith only [h0, h15532, h17541, h17927, h17929, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h17931 | h17931
                      · linarith only [h0, h15532, h17905, h17931, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h17933 | h17933
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h17934 | h17934
                          · linarith only [h0, h15532, h17541, h17926, h17927, h17929, h17934, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h17936 | h17936
                            · linarith only [h0, h17539, h17541, h17905, h17926, h17927, h17931, h17936, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h17938 | h17938
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h17939 | h17939
                                · rcases h0bigk with h17940c | h17940c | h17940c | h17940c | h17940c | h17940c | h17940c | h17940c | h17940c | h17940c | h17940c | h17940c | h17940c | h17940c | h17940c | h17940c | h17940c | h17940c | h17940c | h17940c | h17940c | h17940c | h17940c | h17940c | h17940c
                                  · have p17940_0 := h17940c.1
                                    have p17940_1 := h17940c.2.1
                                    have p17940_2 := h17940c.2.2.1
                                    have p17940_3 := h17940c.2.2.2
                                    linarith only [hlam, p17940_0]
                                  · have p17940_0 := h17940c.1
                                    have p17940_1 := h17940c.2.1
                                    have p17940_2 := h17940c.2.2.1
                                    have p17940_3 := h17940c.2.2.2
                                    linarith only [h0, hlam, p17940_1]
                                  · have p17940_0 := h17940c.1
                                    have p17940_1 := h17940c.2.1
                                    have p17940_2 := h17940c.2.2.1
                                    have p17940_3 := h17940c.2.2.2
                                    linarith only [h0, h17541, h17927, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17940_1]
                                  · have p17940_0 := h17940c.1
                                    have p17940_1 := h17940c.2.1
                                    have p17940_2 := h17940c.2.2.1
                                    have p17940_3 := h17940c.2.2.2
                                    linarith only [h15533, hlam, p17940_1]
                                  · have p17940_0 := h17940c.1
                                    have p17940_1 := h17940c.2.1
                                    have p17940_2 := h17940c.2.2.1
                                    have p17940_3 := h17940c.2.2.2
                                    linarith only [h0, h17541, h17927, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p17940_1]
                                  · have p17940_0 := h17940c.1
                                    have p17940_1 := h17940c.2.1
                                    have p17940_2 := h17940c.2.2.1
                                    have p17940_3 := h17940c.2.2.2
                                    linarith only [h17541, h17927, hc01, hc12, hlam, hphi, p17940_1]
                                  · have p17940_0 := h17940c.1
                                    have p17940_1 := h17940c.2.1
                                    have p17940_2 := h17940c.2.2.1
                                    have p17940_3 := h17940c.2.2.2
                                    linarith only [hlam, p17940_0]
                                  · have p17940_0 := h17940c.1
                                    have p17940_1 := h17940c.2.1
                                    have p17940_2 := h17940c.2.2.1
                                    have p17940_3 := h17940c.2.2.2
                                    linarith only [h15532, h17541, h17926, h17927, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17940_1]
                                  · have p17940_0 := h17940c.1
                                    have p17940_1 := h17940c.2.1
                                    have p17940_2 := h17940c.2.2.1
                                    have p17940_3 := h17940c.2.2.2
                                    linarith only [h17541, hlam, p17940_1]
                                  · have p17940_0 := h17940c.1
                                    have p17940_1 := h17940c.2.1
                                    have p17940_2 := h17940c.2.2.1
                                    have p17940_3 := h17940c.2.2.2
                                    linarith only [h17539, h17541, h17927, h17928, h17938, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p17940_1]
                                  · have p17940_0 := h17940c.1
                                    have p17940_1 := h17940c.2.1
                                    have p17940_2 := h17940c.2.2.1
                                    have p17940_3 := h17940c.2.2.2
                                    linarith only [h15532, hlam, p17940_1]
                                  · have p17940_0 := h17940c.1
                                    have p17940_1 := h17940c.2.1
                                    have p17940_2 := h17940c.2.2.1
                                    have p17940_3 := h17940c.2.2.2
                                    linarith only [h17540, hlam, p17940_1]
                                  · have p17940_0 := h17940c.1
                                    have p17940_1 := h17940c.2.1
                                    have p17940_2 := h17940c.2.2.1
                                    have p17940_3 := h17940c.2.2.2
                                    linarith only [hlam, p17940_0]
                                  · have p17940_0 := h17940c.1
                                    have p17940_1 := h17940c.2.1
                                    have p17940_2 := h17940c.2.2.1
                                    have p17940_3 := h17940c.2.2.2
                                    linarith only [h17903, hlam, p17940_1]
                                  · have p17940_0 := h17940c.1
                                    have p17940_1 := h17940c.2.1
                                    have p17940_2 := h17940c.2.2.1
                                    have p17940_3 := h17940c.2.2.2
                                    linarith only [h17905, hlam, p17940_1]
                                  · have p17940_0 := h17940c.1
                                    have p17940_1 := h17940c.2.1
                                    have p17940_2 := h17940c.2.2.1
                                    have p17940_3 := h17940c.2.2.2
                                    linarith only [h15532, h15533, h17926, h17929, hc23, hc34, hlam, hphi, p17940_1]
                                  · have p17940_0 := h17940c.1
                                    have p17940_1 := h17940c.2.1
                                    have p17940_2 := h17940c.2.2.1
                                    have p17940_3 := h17940c.2.2.2
                                    linarith only [h0, h15532, h17541, h17926, h17927, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17940_1]
                                  · have p17940_0 := h17940c.1
                                    have p17940_1 := h17940c.2.1
                                    have p17940_2 := h17940c.2.2.1
                                    have p17940_3 := h17940c.2.2.2
                                    rcases p17940_3 (m.d 0 1) (by simp) with h17958 | h17958
                                    · linarith only [h15533, h17958, hlam]
                                    · linarith only [h15532, h17958, hlam]
                                  · have p17940_0 := h17940c.1
                                    have p17940_1 := h17940c.2.1
                                    have p17940_2 := h17940c.2.2.1
                                    have p17940_3 := h17940c.2.2.2
                                    linarith only [hlam, p17940_0]
                                  · have p17940_0 := h17940c.1
                                    have p17940_1 := h17940c.2.1
                                    have p17940_2 := h17940c.2.2.1
                                    have p17940_3 := h17940c.2.2.2
                                    rcases p17940_3 (m.d 0 1) (by simp) with h17962 | h17962
                                    · linarith only [h15533, h17962, hlam]
                                    · linarith only [h17539, h17962, hlam]
                                  · have p17940_0 := h17940c.1
                                    have p17940_1 := h17940c.2.1
                                    have p17940_2 := h17940c.2.2.1
                                    have p17940_3 := h17940c.2.2.2
                                    linarith only [h17539, hlam, p17940_0]
                                  · have p17940_0 := h17940c.1
                                    have p17940_1 := h17940c.2.1
                                    have p17940_2 := h17940c.2.2.1
                                    have p17940_3 := h17940c.2.2.2
                                    linarith only [h17902, hlam, p17940_1]
                                  · have p17940_0 := h17940c.1
                                    have p17940_1 := h17940c.2.1
                                    have p17940_2 := h17940c.2.2.1
                                    have p17940_3 := h17940c.2.2.2
                                    linarith only [h15532, h15533, h17539, h17926, h17929, hc23, hc34, hlam, hphi, p17940_1]
                                  · have p17940_0 := h17940c.1
                                    have p17940_1 := h17940c.2.1
                                    have p17940_2 := h17940c.2.2.1
                                    have p17940_3 := h17940c.2.2.2
                                    linarith only [h17925, hlam, p17940_1]
                                  · have p17940_0 := h17940c.1
                                    have p17940_1 := h17940c.2.1
                                    have p17940_2 := h17940c.2.2.1
                                    have p17940_3 := h17940c.2.2.2
                                    linarith only [hlam, p17940_0]
                                · linarith only [h15532, h15533, h17926, h17929, h17939, hc23, hc45, hlam, hphi, ht34]
                              · linarith only [h0, h17539, h17541, h17933, h17938, hlam]
                        · linarith only [h0, h17539, h17541, h17926, h17927, h17931, h17933, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h17541, h17927, h17928, hc01, hc25, hlam, hphi, ht12]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h17974 | h17974
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h17975 | h17975
                    · linarith only [h0, h15532, h17903, h17927, h17975, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h17977 | h17977
                      · linarith only [h0, h15532, h17927, h17977, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h17979 | h17979
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h17980 | h17980
                          · linarith only [h15533, h17539, h17540, h17975, h17977, h17980, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · linarith only [h0, h17539, h17927, h17977, h17980, hc13, hc34, hlam, hphi]
                        · linarith only [h0, h17539, h17926, h17927, h17977, h17979, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h17539, h17541, h17902, h17974, hc04, hc15, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h17540, h17926, hlam]
            · linarith only [h0, h17539, h17541, h17925, hlam]
      · linarith only [h0, h17539, h17902, hlam]
  · linarith only [h0, h15532, h17540, hlam]

end R2N4
