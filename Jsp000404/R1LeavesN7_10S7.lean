import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 12300000 in
set_option maxHeartbeats 12300000 in
theorem r1l7_12_24_L_I_H_I_s1_x1_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h4281 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 2 5 (by decide) (by decide) with h4282 | h4282
  · rcases m.htr 0 3 4 (by decide) (by decide) with h4283 | h4283
    · rcases m.htr 0 4 5 (by decide) (by decide) with h4284 | h4284
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4285 | h4285
        · linarith only [h0, h2, h4281, h4285, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4287 | h4287
          · rcases m.htr 1 2 5 (by decide) (by decide) with h4288 | h4288
            · rcases m.htr 1 3 4 (by decide) (by decide) with h4289 | h4289
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4290 | h4290
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4291 | h4291
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4292 | h4292
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4293 | h4293
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4294 | h4294
                        · rcases h2bigk with h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c
                          · have p4295_0 := h4295c.1
                            have p4295_1 := h4295c.2.1
                            have p4295_2 := h4295c.2.2.1
                            have p4295_3 := h4295c.2.2.2
                            linarith only [hlam, p4295_0]
                          · have p4295_0 := h4295c.1
                            have p4295_1 := h4295c.2.1
                            have p4295_2 := h4295c.2.2.1
                            have p4295_3 := h4295c.2.2.2
                            linarith only [h4287, h4291, h4294, hc02, hc45, hlam, hphi, ht0b, ht5b, p4295_1]
                          · have p4295_0 := h4295c.1
                            have p4295_1 := h4295c.2.1
                            have p4295_2 := h4295c.2.2.1
                            have p4295_3 := h4295c.2.2.2
                            linarith only [h2, hlam, p4295_0]
                          · have p4295_0 := h4295c.1
                            have p4295_1 := h4295c.2.1
                            have p4295_2 := h4295c.2.2.1
                            have p4295_3 := h4295c.2.2.2
                            linarith only [h2, h4291, h4294, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4295_1]
                          · have p4295_0 := h4295c.1
                            have p4295_1 := h4295c.2.1
                            have p4295_2 := h4295c.2.2.1
                            have p4295_3 := h4295c.2.2.2
                            rcases p4295_3 (m.d 0 2) (by simp) with h4300 | h4300
                            · rcases p4295_3 (m.d 1 2) (by simp) with h4301 | h4301
                              · linarith only [h0, h4301, hlam]
                              · linarith only [h4288, h4301, hlam]
                            · linarith only [h4300, hlam, p4295_0]
                          · have p4295_0 := h4295c.1
                            have p4295_1 := h4295c.2.1
                            have p4295_2 := h4295c.2.2.1
                            have p4295_3 := h4295c.2.2.2
                            linarith only [h0, hlam, p4295_1]
                          · have p4295_0 := h4295c.1
                            have p4295_1 := h4295c.2.1
                            have p4295_2 := h4295c.2.2.1
                            have p4295_3 := h4295c.2.2.2
                            linarith only [hlam, p4295_0]
                          · have p4295_0 := h4295c.1
                            have p4295_1 := h4295c.2.1
                            have p4295_2 := h4295c.2.2.1
                            have p4295_3 := h4295c.2.2.2
                            linarith only [h4285, hlam, p4295_0]
                          · have p4295_0 := h4295c.1
                            have p4295_1 := h4295c.2.1
                            have p4295_2 := h4295c.2.2.1
                            have p4295_3 := h4295c.2.2.2
                            linarith only [h0, h4291, h4294, hc01, hc45, hlam, hphi, ht0b, ht5b, p4295_1]
                          · have p4295_0 := h4295c.1
                            have p4295_1 := h4295c.2.1
                            have p4295_2 := h4295c.2.2.1
                            have p4295_3 := h4295c.2.2.2
                            rcases p4295_3 (m.d 0 2) (by simp) with h4309 | h4309
                            · rcases p4295_3 (m.d 1 2) (by simp) with h4310 | h4310
                              · rcases p4295_3 (m.d 2 3) (by simp) with h4311 | h4311
                                · rcases p4295_3 (m.d 2 4) (by simp) with h4312 | h4312
                                  · linarith only [h4287, h4312, hlam]
                                  · linarith only [h4293, h4312, hlam]
                                · linarith only [h4292, h4311, hlam]
                              · linarith only [h4310, hlam, p4295_0]
                            · linarith only [h4282, h4309, hlam]
                          · have p4295_0 := h4295c.1
                            have p4295_1 := h4295c.2.1
                            have p4295_2 := h4295c.2.2.1
                            have p4295_3 := h4295c.2.2.2
                            linarith only [h4281, h4291, h4294, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4295_1]
                          · have p4295_0 := h4295c.1
                            have p4295_1 := h4295c.2.1
                            have p4295_2 := h4295c.2.2.1
                            have p4295_3 := h4295c.2.2.2
                            linarith only [h4287, h4291, h4294, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4295_1]
                          · have p4295_0 := h4295c.1
                            have p4295_1 := h4295c.2.1
                            have p4295_2 := h4295c.2.2.1
                            have p4295_3 := h4295c.2.2.2
                            linarith only [hlam, p4295_0]
                          · have p4295_0 := h4295c.1
                            have p4295_1 := h4295c.2.1
                            have p4295_2 := h4295c.2.2.1
                            have p4295_3 := h4295c.2.2.2
                            rcases p4295_3 (m.d 0 2) (by simp) with h4321 | h4321
                            · linarith only [h2, h4321, hlam]
                            · linarith only [h4281, h4321, hlam]
                          · have p4295_0 := h4295c.1
                            have p4295_1 := h4295c.2.1
                            have p4295_2 := h4295c.2.2.1
                            have p4295_3 := h4295c.2.2.2
                            rcases p4295_3 (m.d 0 2) (by simp) with h4324 | h4324
                            · linarith only [h2, h4324, hlam]
                            · linarith only [h4282, h4324, hlam]
                          · have p4295_0 := h4295c.1
                            have p4295_1 := h4295c.2.1
                            have p4295_2 := h4295c.2.2.1
                            have p4295_3 := h4295c.2.2.2
                            linarith only [h4281, hlam, p4295_0]
                          · have p4295_0 := h4295c.1
                            have p4295_1 := h4295c.2.1
                            have p4295_2 := h4295c.2.2.1
                            have p4295_3 := h4295c.2.2.2
                            linarith only [h4287, hlam, p4295_0]
                          · have p4295_0 := h4295c.1
                            have p4295_1 := h4295c.2.1
                            have p4295_2 := h4295c.2.2.1
                            have p4295_3 := h4295c.2.2.2
                            linarith only [h4291, hlam, p4295_0]
                          · have p4295_0 := h4295c.1
                            have p4295_1 := h4295c.2.1
                            have p4295_2 := h4295c.2.2.1
                            have p4295_3 := h4295c.2.2.2
                            linarith only [hlam, p4295_0]
                          · have p4295_0 := h4295c.1
                            have p4295_1 := h4295c.2.1
                            have p4295_2 := h4295c.2.2.1
                            have p4295_3 := h4295c.2.2.2
                            linarith only [h0, h4287, hc01, hc25, hlam, hphi, ht0b, ht5b, p4295_1]
                          · have p4295_0 := h4295c.1
                            have p4295_1 := h4295c.2.1
                            have p4295_2 := h4295c.2.2.1
                            have p4295_3 := h4295c.2.2.2
                            linarith only [h4282, hlam, p4295_0]
                          · have p4295_0 := h4295c.1
                            have p4295_1 := h4295c.2.1
                            have p4295_2 := h4295c.2.2.1
                            have p4295_3 := h4295c.2.2.2
                            linarith only [h4288, hlam, p4295_0]
                          · have p4295_0 := h4295c.1
                            have p4295_1 := h4295c.2.1
                            have p4295_2 := h4295c.2.2.1
                            have p4295_3 := h4295c.2.2.2
                            linarith only [h4292, hlam, p4295_0]
                          · have p4295_0 := h4295c.1
                            have p4295_1 := h4295c.2.1
                            have p4295_2 := h4295c.2.2.1
                            have p4295_3 := h4295c.2.2.2
                            linarith only [h4293, hlam, p4295_1]
                          · have p4295_0 := h4295c.1
                            have p4295_1 := h4295c.2.1
                            have p4295_2 := h4295c.2.2.1
                            have p4295_3 := h4295c.2.2.2
                            linarith only [hlam, p4295_0]
                        · linarith only [h0, h2, h4287, h4293, h4294, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4338 | h4338
                        · linarith only [h4291, h4293, h4338, hlam]
                        · rcases h2bigk with h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c
                          · have p4340_0 := h4340c.1
                            have p4340_1 := h4340c.2.1
                            have p4340_2 := h4340c.2.2.1
                            have p4340_3 := h4340c.2.2.2
                            linarith only [hlam, p4340_0]
                          · have p4340_0 := h4340c.1
                            have p4340_1 := h4340c.2.1
                            have p4340_2 := h4340c.2.2.1
                            have p4340_3 := h4340c.2.2.2
                            linarith only [h2, hc12, hc23, hlam, hphi, p4340_1]
                          · have p4340_0 := h4340c.1
                            have p4340_1 := h4340c.2.1
                            have p4340_2 := h4340c.2.2.1
                            have p4340_3 := h4340c.2.2.2
                            linarith only [h2, hlam, p4340_0]
                          · have p4340_0 := h4340c.1
                            have p4340_1 := h4340c.2.1
                            have p4340_2 := h4340c.2.2.1
                            have p4340_3 := h4340c.2.2.2
                            rcases p4340_3 (m.d 0 2) (by simp) with h4344 | h4344
                            · rcases p4340_3 (m.d 1 2) (by simp) with h4345 | h4345
                              · linarith only [h0, h4345, hlam]
                              · linarith only [h4287, h4345, hlam]
                            · linarith only [h4344, hlam, p4340_0]
                          · have p4340_0 := h4340c.1
                            have p4340_1 := h4340c.2.1
                            have p4340_2 := h4340c.2.2.1
                            have p4340_3 := h4340c.2.2.2
                            rcases p4340_3 (m.d 0 2) (by simp) with h4349 | h4349
                            · rcases p4340_3 (m.d 1 2) (by simp) with h4350 | h4350
                              · linarith only [h0, h4350, hlam]
                              · linarith only [h4288, h4350, hlam]
                            · linarith only [h4349, hlam, p4340_0]
                          · have p4340_0 := h4340c.1
                            have p4340_1 := h4340c.2.1
                            have p4340_2 := h4340c.2.2.1
                            have p4340_3 := h4340c.2.2.2
                            linarith only [h0, hlam, p4340_1]
                          · have p4340_0 := h4340c.1
                            have p4340_1 := h4340c.2.1
                            have p4340_2 := h4340c.2.2.1
                            have p4340_3 := h4340c.2.2.2
                            linarith only [hlam, p4340_0]
                          · have p4340_0 := h4340c.1
                            have p4340_1 := h4340c.2.1
                            have p4340_2 := h4340c.2.2.1
                            have p4340_3 := h4340c.2.2.2
                            linarith only [h4285, hlam, p4340_0]
                          · have p4340_0 := h4340c.1
                            have p4340_1 := h4340c.2.1
                            have p4340_2 := h4340c.2.2.1
                            have p4340_3 := h4340c.2.2.2
                            rcases p4340_3 (m.d 0 2) (by simp) with h4357 | h4357
                            · rcases p4340_3 (m.d 1 2) (by simp) with h4358 | h4358
                              · rcases p4340_3 (m.d 2 3) (by simp) with h4359 | h4359
                                · rcases p4340_3 (m.d 2 4) (by simp) with h4360 | h4360
                                  · linarith only [h4360, hlam, p4340_0]
                                  · rcases p4340_3 (m.d 2 5) (by simp) with h4362 | h4362
                                    · linarith only [h4288, h4362, hlam]
                                    · linarith only [h4293, h4362, hlam]
                                · linarith only [h4291, h4359, hlam]
                              · linarith only [h4358, hlam, p4340_0]
                            · linarith only [h4281, h4357, hlam]
                          · have p4340_0 := h4340c.1
                            have p4340_1 := h4340c.2.1
                            have p4340_2 := h4340c.2.2.1
                            have p4340_3 := h4340c.2.2.2
                            rcases p4340_3 (m.d 0 2) (by simp) with h4368 | h4368
                            · rcases p4340_3 (m.d 1 2) (by simp) with h4369 | h4369
                              · rcases p4340_3 (m.d 2 3) (by simp) with h4370 | h4370
                                · rcases p4340_3 (m.d 2 4) (by simp) with h4371 | h4371
                                  · linarith only [h4287, h4371, hlam]
                                  · rcases p4340_3 (m.d 2 5) (by simp) with h4373 | h4373
                                    · linarith only [h4373, hlam, p4340_0]
                                    · rcases h4bigk with h4375c | h4375c | h4375c | h4375c | h4375c | h4375c | h4375c | h4375c | h4375c | h4375c | h4375c | h4375c | h4375c | h4375c | h4375c | h4375c | h4375c | h4375c | h4375c | h4375c | h4375c | h4375c | h4375c | h4375c | h4375c
                                      · have p4375_0 := h4375c.1
                                        have p4375_1 := h4375c.2.1
                                        have p4375_2 := h4375c.2.2.1
                                        have p4375_3 := h4375c.2.2.2
                                        linarith only [hlam, p4375_0]
                                      · have p4375_0 := h4375c.1
                                        have p4375_1 := h4375c.2.1
                                        have p4375_2 := h4375c.2.2.1
                                        have p4375_3 := h4375c.2.2.2
                                        linarith only [h2, h4281, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4375_1]
                                      · have p4375_0 := h4375c.1
                                        have p4375_1 := h4375c.2.1
                                        have p4375_2 := h4375c.2.2.1
                                        have p4375_3 := h4375c.2.2.2
                                        linarith only [h2, h4281, h4291, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4375_1]
                                      · have p4375_0 := h4375c.1
                                        have p4375_1 := h4375c.2.1
                                        have p4375_2 := h4375c.2.2.1
                                        have p4375_3 := h4375c.2.2.2
                                        linarith only [h2, h4281, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4375_1]
                                      · have p4375_0 := h4375c.1
                                        have p4375_1 := h4375c.2.1
                                        have p4375_2 := h4375c.2.2.1
                                        have p4375_3 := h4375c.2.2.2
                                        linarith only [h2, h4281, h4291, h4293, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4375_1]
                                      · have p4375_0 := h4375c.1
                                        have p4375_1 := h4375c.2.1
                                        have p4375_2 := h4375c.2.2.1
                                        have p4375_3 := h4375c.2.2.2
                                        linarith only [h1, hlam, p4375_0]
                                      · have p4375_0 := h4375c.1
                                        have p4375_1 := h4375c.2.1
                                        have p4375_2 := h4375c.2.2.1
                                        have p4375_3 := h4375c.2.2.2
                                        linarith only [hlam, p4375_0]
                                      · have p4375_0 := h4375c.1
                                        have p4375_1 := h4375c.2.1
                                        have p4375_2 := h4375c.2.2.1
                                        have p4375_3 := h4375c.2.2.2
                                        linarith only [h0, h4287, h4291, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4375_1]
                                      · have p4375_0 := h4375c.1
                                        have p4375_1 := h4375c.2.1
                                        have p4375_2 := h4375c.2.2.1
                                        have p4375_3 := h4375c.2.2.2
                                        linarith only [h0, h2, h4287, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4375_1]
                                      · have p4375_0 := h4375c.1
                                        have p4375_1 := h4375c.2.1
                                        have p4375_2 := h4375c.2.2.1
                                        have p4375_3 := h4375c.2.2.2
                                        linarith only [h0, h2, h4287, h4291, h4293, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4375_1]
                                      · have p4375_0 := h4375c.1
                                        have p4375_1 := h4375c.2.1
                                        have p4375_2 := h4375c.2.2.1
                                        have p4375_3 := h4375c.2.2.2
                                        linarith only [h4281, hlam, p4375_0]
                                      · have p4375_0 := h4375c.1
                                        have p4375_1 := h4375c.2.1
                                        have p4375_2 := h4375c.2.2.1
                                        have p4375_3 := h4375c.2.2.2
                                        linarith only [h4287, hlam, p4375_0]
                                      · have p4375_0 := h4375c.1
                                        have p4375_1 := h4375c.2.1
                                        have p4375_2 := h4375c.2.2.1
                                        have p4375_3 := h4375c.2.2.2
                                        linarith only [hlam, p4375_0]
                                      · have p4375_0 := h4375c.1
                                        have p4375_1 := h4375c.2.1
                                        have p4375_2 := h4375c.2.2.1
                                        have p4375_3 := h4375c.2.2.2
                                        linarith only [h4293, hc34, hc45, hlam, hphi, p4375_1]
                                      · have p4375_0 := h4375c.1
                                        have p4375_1 := h4375c.2.1
                                        have p4375_2 := h4375c.2.2.1
                                        have p4375_3 := h4375c.2.2.2
                                        linarith only [h4293, hlam, p4375_0]
                                      · have p4375_0 := h4375c.1
                                        have p4375_1 := h4375c.2.1
                                        have p4375_2 := h4375c.2.2.1
                                        have p4375_3 := h4375c.2.2.2
                                        linarith only [h4283, hlam, p4375_0]
                                      · have p4375_0 := h4375c.1
                                        have p4375_1 := h4375c.2.1
                                        have p4375_2 := h4375c.2.2.1
                                        have p4375_3 := h4375c.2.2.2
                                        linarith only [h4289, hlam, p4375_0]
                                      · have p4375_0 := h4375c.1
                                        have p4375_1 := h4375c.2.1
                                        have p4375_2 := h4375c.2.2.1
                                        have p4375_3 := h4375c.2.2.2
                                        linarith only [h4291, hlam, p4375_0]
                                      · have p4375_0 := h4375c.1
                                        have p4375_1 := h4375c.2.1
                                        have p4375_2 := h4375c.2.2.1
                                        have p4375_3 := h4375c.2.2.2
                                        linarith only [hlam, p4375_0]
                                      · have p4375_0 := h4375c.1
                                        have p4375_1 := h4375c.2.1
                                        have p4375_2 := h4375c.2.2.1
                                        have p4375_3 := h4375c.2.2.2
                                        linarith only [h4338, hlam, p4375_0]
                                      · have p4375_0 := h4375c.1
                                        have p4375_1 := h4375c.2.1
                                        have p4375_2 := h4375c.2.2.1
                                        have p4375_3 := h4375c.2.2.2
                                        linarith only [h4284, hlam, p4375_0]
                                      · have p4375_0 := h4375c.1
                                        have p4375_1 := h4375c.2.1
                                        have p4375_2 := h4375c.2.2.1
                                        have p4375_3 := h4375c.2.2.2
                                        linarith only [h4290, hlam, p4375_0]
                                      · have p4375_0 := h4375c.1
                                        have p4375_1 := h4375c.2.1
                                        have p4375_2 := h4375c.2.2.1
                                        have p4375_3 := h4375c.2.2.2
                                        linarith only [hc24, hc45, hlam, hphi, p4375_1]
                                      · have p4375_0 := h4375c.1
                                        have p4375_1 := h4375c.2.1
                                        have p4375_2 := h4375c.2.2.1
                                        have p4375_3 := h4375c.2.2.2
                                        linarith only [h0, h2, h4287, h4290, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4375_1]
                                      · have p4375_0 := h4375c.1
                                        have p4375_1 := h4375c.2.1
                                        have p4375_2 := h4375c.2.2.1
                                        have p4375_3 := h4375c.2.2.2
                                        linarith only [hlam, p4375_0]
                                · linarith only [h4292, h4370, hlam]
                              · linarith only [h4369, hlam, p4340_0]
                            · linarith only [h4282, h4368, hlam]
                          · have p4340_0 := h4340c.1
                            have p4340_1 := h4340c.2.1
                            have p4340_2 := h4340c.2.2.1
                            have p4340_3 := h4340c.2.2.2
                            linarith only [h0, h4287, h4290, h4291, h4293, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4340_1]
                          · have p4340_0 := h4340c.1
                            have p4340_1 := h4340c.2.1
                            have p4340_2 := h4340c.2.2.1
                            have p4340_3 := h4340c.2.2.2
                            linarith only [h4287, h4290, h4291, h4293, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4340_1]
                          · have p4340_0 := h4340c.1
                            have p4340_1 := h4340c.2.1
                            have p4340_2 := h4340c.2.2.1
                            have p4340_3 := h4340c.2.2.2
                            linarith only [hlam, p4340_0]
                          · have p4340_0 := h4340c.1
                            have p4340_1 := h4340c.2.1
                            have p4340_2 := h4340c.2.2.1
                            have p4340_3 := h4340c.2.2.2
                            linarith only [h0, h2, h4287, h4290, h4293, hlam, p4340_2]
                          · have p4340_0 := h4340c.1
                            have p4340_1 := h4340c.2.1
                            have p4340_2 := h4340c.2.2.1
                            have p4340_3 := h4340c.2.2.2
                            rcases p4340_3 (m.d 0 2) (by simp) with h4408 | h4408
                            · linarith only [h2, h4408, hlam]
                            · linarith only [h4282, h4408, hlam]
                          · have p4340_0 := h4340c.1
                            have p4340_1 := h4340c.2.1
                            have p4340_2 := h4340c.2.2.1
                            have p4340_3 := h4340c.2.2.2
                            linarith only [h4281, hlam, p4340_0]
                          · have p4340_0 := h4340c.1
                            have p4340_1 := h4340c.2.1
                            have p4340_2 := h4340c.2.2.1
                            have p4340_3 := h4340c.2.2.2
                            linarith only [h4287, hlam, p4340_0]
                          · have p4340_0 := h4340c.1
                            have p4340_1 := h4340c.2.1
                            have p4340_2 := h4340c.2.2.1
                            have p4340_3 := h4340c.2.2.2
                            linarith only [h4291, hlam, p4340_0]
                          · have p4340_0 := h4340c.1
                            have p4340_1 := h4340c.2.1
                            have p4340_2 := h4340c.2.2.1
                            have p4340_3 := h4340c.2.2.2
                            linarith only [hlam, p4340_0]
                          · have p4340_0 := h4340c.1
                            have p4340_1 := h4340c.2.1
                            have p4340_2 := h4340c.2.2.1
                            have p4340_3 := h4340c.2.2.2
                            linarith only [h4293, hlam, p4340_0]
                          · have p4340_0 := h4340c.1
                            have p4340_1 := h4340c.2.1
                            have p4340_2 := h4340c.2.2.1
                            have p4340_3 := h4340c.2.2.2
                            linarith only [h4282, hlam, p4340_0]
                          · have p4340_0 := h4340c.1
                            have p4340_1 := h4340c.2.1
                            have p4340_2 := h4340c.2.2.1
                            have p4340_3 := h4340c.2.2.2
                            linarith only [h4288, hlam, p4340_0]
                          · have p4340_0 := h4340c.1
                            have p4340_1 := h4340c.2.1
                            have p4340_2 := h4340c.2.2.1
                            have p4340_3 := h4340c.2.2.2
                            linarith only [h4292, hlam, p4340_0]
                          · have p4340_0 := h4340c.1
                            have p4340_1 := h4340c.2.1
                            have p4340_2 := h4340c.2.2.1
                            have p4340_3 := h4340c.2.2.2
                            linarith only [h2, h4282, h4291, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4340_1]
                          · have p4340_0 := h4340c.1
                            have p4340_1 := h4340c.2.1
                            have p4340_2 := h4340c.2.2.1
                            have p4340_3 := h4340c.2.2.2
                            linarith only [hlam, p4340_0]
                    · linarith only [h0, h2, h4288, h4292, hlam]
                  · linarith only [h2, h4283, h4291, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4423 | h4423
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4424 | h4424
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4425 | h4425
                      · linarith only [h4287, h4290, h4425, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4427 | h4427
                        · linarith only [h4287, h4290, h4423, h4427, hlam]
                        · rcases h2bigk with h4429c | h4429c | h4429c | h4429c | h4429c | h4429c | h4429c | h4429c | h4429c | h4429c | h4429c | h4429c | h4429c | h4429c | h4429c | h4429c | h4429c | h4429c | h4429c | h4429c | h4429c | h4429c | h4429c | h4429c | h4429c
                          · have p4429_0 := h4429c.1
                            have p4429_1 := h4429c.2.1
                            have p4429_2 := h4429c.2.2.1
                            have p4429_3 := h4429c.2.2.2
                            linarith only [hlam, p4429_0]
                          · have p4429_0 := h4429c.1
                            have p4429_1 := h4429c.2.1
                            have p4429_2 := h4429c.2.2.1
                            have p4429_3 := h4429c.2.2.2
                            linarith only [h2, hc12, hc23, hlam, hphi, p4429_1]
                          · have p4429_0 := h4429c.1
                            have p4429_1 := h4429c.2.1
                            have p4429_2 := h4429c.2.2.1
                            have p4429_3 := h4429c.2.2.2
                            linarith only [h2, hlam, p4429_0]
                          · have p4429_0 := h4429c.1
                            have p4429_1 := h4429c.2.1
                            have p4429_2 := h4429c.2.2.1
                            have p4429_3 := h4429c.2.2.2
                            rcases p4429_3 (m.d 0 2) (by simp) with h4433 | h4433
                            · rcases p4429_3 (m.d 1 2) (by simp) with h4434 | h4434
                              · linarith only [h0, h4434, hlam]
                              · linarith only [h4287, h4434, hlam]
                            · linarith only [h4433, hlam, p4429_0]
                          · have p4429_0 := h4429c.1
                            have p4429_1 := h4429c.2.1
                            have p4429_2 := h4429c.2.2.1
                            have p4429_3 := h4429c.2.2.2
                            rcases p4429_3 (m.d 0 2) (by simp) with h4438 | h4438
                            · rcases p4429_3 (m.d 1 2) (by simp) with h4439 | h4439
                              · linarith only [h0, h4439, hlam]
                              · linarith only [h4288, h4439, hlam]
                            · linarith only [h4438, hlam, p4429_0]
                          · have p4429_0 := h4429c.1
                            have p4429_1 := h4429c.2.1
                            have p4429_2 := h4429c.2.2.1
                            have p4429_3 := h4429c.2.2.2
                            linarith only [h0, hlam, p4429_1]
                          · have p4429_0 := h4429c.1
                            have p4429_1 := h4429c.2.1
                            have p4429_2 := h4429c.2.2.1
                            have p4429_3 := h4429c.2.2.2
                            linarith only [hlam, p4429_0]
                          · have p4429_0 := h4429c.1
                            have p4429_1 := h4429c.2.1
                            have p4429_2 := h4429c.2.2.1
                            have p4429_3 := h4429c.2.2.2
                            linarith only [h4285, hlam, p4429_0]
                          · have p4429_0 := h4429c.1
                            have p4429_1 := h4429c.2.1
                            have p4429_2 := h4429c.2.2.1
                            have p4429_3 := h4429c.2.2.2
                            rcases p4429_3 (m.d 0 2) (by simp) with h4446 | h4446
                            · rcases p4429_3 (m.d 1 2) (by simp) with h4447 | h4447
                              · rcases p4429_3 (m.d 2 3) (by simp) with h4448 | h4448
                                · rcases p4429_3 (m.d 2 4) (by simp) with h4449 | h4449
                                  · linarith only [h4449, hlam, p4429_0]
                                  · rcases p4429_3 (m.d 2 5) (by simp) with h4451 | h4451
                                    · linarith only [h4288, h4451, hlam]
                                    · linarith only [h4425, h4451, hlam]
                                · linarith only [h4423, h4448, hlam]
                              · linarith only [h4447, hlam, p4429_0]
                            · linarith only [h4281, h4446, hlam]
                          · have p4429_0 := h4429c.1
                            have p4429_1 := h4429c.2.1
                            have p4429_2 := h4429c.2.2.1
                            have p4429_3 := h4429c.2.2.2
                            rcases p4429_3 (m.d 0 2) (by simp) with h4457 | h4457
                            · rcases p4429_3 (m.d 1 2) (by simp) with h4458 | h4458
                              · rcases p4429_3 (m.d 2 3) (by simp) with h4459 | h4459
                                · rcases p4429_3 (m.d 2 4) (by simp) with h4460 | h4460
                                  · linarith only [h4287, h4460, hlam]
                                  · rcases p4429_3 (m.d 2 5) (by simp) with h4462 | h4462
                                    · linarith only [h4462, hlam, p4429_0]
                                    · rcases h4bigk with h4464c | h4464c | h4464c | h4464c | h4464c | h4464c | h4464c | h4464c | h4464c | h4464c | h4464c | h4464c | h4464c | h4464c | h4464c | h4464c | h4464c | h4464c | h4464c | h4464c | h4464c | h4464c | h4464c | h4464c | h4464c
                                      · have p4464_0 := h4464c.1
                                        have p4464_1 := h4464c.2.1
                                        have p4464_2 := h4464c.2.2.1
                                        have p4464_3 := h4464c.2.2.2
                                        linarith only [hlam, p4464_0]
                                      · have p4464_0 := h4464c.1
                                        have p4464_1 := h4464c.2.1
                                        have p4464_2 := h4464c.2.2.1
                                        have p4464_3 := h4464c.2.2.2
                                        linarith only [h2, h4281, h4287, h4423, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4464_1]
                                      · have p4464_0 := h4464c.1
                                        have p4464_1 := h4464c.2.1
                                        have p4464_2 := h4464c.2.2.1
                                        have p4464_3 := h4464c.2.2.2
                                        linarith only [h2, h4281, h4423, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4464_1]
                                      · have p4464_0 := h4464c.1
                                        have p4464_1 := h4464c.2.1
                                        have p4464_2 := h4464c.2.2.1
                                        have p4464_3 := h4464c.2.2.2
                                        linarith only [h2, h4281, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4464_1]
                                      · have p4464_0 := h4464c.1
                                        have p4464_1 := h4464c.2.1
                                        have p4464_2 := h4464c.2.2.1
                                        have p4464_3 := h4464c.2.2.2
                                        linarith only [h2, h4281, h4287, h4290, h4423, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4464_1]
                                      · have p4464_0 := h4464c.1
                                        have p4464_1 := h4464c.2.1
                                        have p4464_2 := h4464c.2.2.1
                                        have p4464_3 := h4464c.2.2.2
                                        linarith only [h1, hlam, p4464_0]
                                      · have p4464_0 := h4464c.1
                                        have p4464_1 := h4464c.2.1
                                        have p4464_2 := h4464c.2.2.1
                                        have p4464_3 := h4464c.2.2.2
                                        linarith only [hlam, p4464_0]
                                      · have p4464_0 := h4464c.1
                                        have p4464_1 := h4464c.2.1
                                        have p4464_2 := h4464c.2.2.1
                                        have p4464_3 := h4464c.2.2.2
                                        linarith only [h4290, h4423, hc34, hc45, hlam, hphi, p4464_1]
                                      · have p4464_0 := h4464c.1
                                        have p4464_1 := h4464c.2.1
                                        have p4464_2 := h4464c.2.2.1
                                        have p4464_3 := h4464c.2.2.2
                                        linarith only [h2, h4281, h4284, h4290, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4464_1]
                                      · have p4464_0 := h4464c.1
                                        have p4464_1 := h4464c.2.1
                                        have p4464_2 := h4464c.2.2.1
                                        have p4464_3 := h4464c.2.2.2
                                        linarith only [h4290, hlam, p4464_0]
                                      · have p4464_0 := h4464c.1
                                        have p4464_1 := h4464c.2.1
                                        have p4464_2 := h4464c.2.2.1
                                        have p4464_3 := h4464c.2.2.2
                                        linarith only [h4281, hlam, p4464_0]
                                      · have p4464_0 := h4464c.1
                                        have p4464_1 := h4464c.2.1
                                        have p4464_2 := h4464c.2.2.1
                                        have p4464_3 := h4464c.2.2.2
                                        linarith only [h4287, hlam, p4464_0]
                                      · have p4464_0 := h4464c.1
                                        have p4464_1 := h4464c.2.1
                                        have p4464_2 := h4464c.2.2.1
                                        have p4464_3 := h4464c.2.2.2
                                        linarith only [hlam, p4464_0]
                                      · have p4464_0 := h4464c.1
                                        have p4464_1 := h4464c.2.1
                                        have p4464_2 := h4464c.2.2.1
                                        have p4464_3 := h4464c.2.2.2
                                        linarith only [h4425, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4429_1, p4464_1]
                                      · have p4464_0 := h4464c.1
                                        have p4464_1 := h4464c.2.1
                                        have p4464_2 := h4464c.2.2.1
                                        have p4464_3 := h4464c.2.2.2
                                        linarith only [h4425, hlam, p4464_0]
                                      · have p4464_0 := h4464c.1
                                        have p4464_1 := h4464c.2.1
                                        have p4464_2 := h4464c.2.2.1
                                        have p4464_3 := h4464c.2.2.2
                                        linarith only [h4283, hlam, p4464_0]
                                      · have p4464_0 := h4464c.1
                                        have p4464_1 := h4464c.2.1
                                        have p4464_2 := h4464c.2.2.1
                                        have p4464_3 := h4464c.2.2.2
                                        linarith only [h4289, hlam, p4464_0]
                                      · have p4464_0 := h4464c.1
                                        have p4464_1 := h4464c.2.1
                                        have p4464_2 := h4464c.2.2.1
                                        have p4464_3 := h4464c.2.2.2
                                        linarith only [h4423, hlam, p4464_0]
                                      · have p4464_0 := h4464c.1
                                        have p4464_1 := h4464c.2.1
                                        have p4464_2 := h4464c.2.2.1
                                        have p4464_3 := h4464c.2.2.2
                                        linarith only [hlam, p4464_0]
                                      · have p4464_0 := h4464c.1
                                        have p4464_1 := h4464c.2.1
                                        have p4464_2 := h4464c.2.2.1
                                        have p4464_3 := h4464c.2.2.2
                                        linarith only [h4427, hlam, p4464_0]
                                      · have p4464_0 := h4464c.1
                                        have p4464_1 := h4464c.2.1
                                        have p4464_2 := h4464c.2.2.1
                                        have p4464_3 := h4464c.2.2.2
                                        linarith only [h4284, hlam, p4464_0]
                                      · have p4464_0 := h4464c.1
                                        have p4464_1 := h4464c.2.1
                                        have p4464_2 := h4464c.2.2.1
                                        have p4464_3 := h4464c.2.2.2
                                        linarith only [h2, h4281, h4284, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4464_1]
                                      · have p4464_0 := h4464c.1
                                        have p4464_1 := h4464c.2.1
                                        have p4464_2 := h4464c.2.2.1
                                        have p4464_3 := h4464c.2.2.2
                                        linarith only [h2, h4281, h4284, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4464_1]
                                      · have p4464_0 := h4464c.1
                                        have p4464_1 := h4464c.2.1
                                        have p4464_2 := h4464c.2.2.1
                                        have p4464_3 := h4464c.2.2.2
                                        linarith only [h2, h4281, h4284, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4464_1]
                                      · have p4464_0 := h4464c.1
                                        have p4464_1 := h4464c.2.1
                                        have p4464_2 := h4464c.2.2.1
                                        have p4464_3 := h4464c.2.2.2
                                        linarith only [hlam, p4464_0]
                                · linarith only [h4424, h4459, hlam]
                              · linarith only [h4458, hlam, p4429_0]
                            · linarith only [h4282, h4457, hlam]
                          · have p4429_0 := h4429c.1
                            have p4429_1 := h4429c.2.1
                            have p4429_2 := h4429c.2.2.1
                            have p4429_3 := h4429c.2.2.2
                            linarith only [h4281, h4284, h4287, h4290, h4423, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4429_1]
                          · have p4429_0 := h4429c.1
                            have p4429_1 := h4429c.2.1
                            have p4429_2 := h4429c.2.2.1
                            have p4429_3 := h4429c.2.2.2
                            rcases p4429_3 (m.d 0 2) (by simp) with h4494 | h4494
                            · linarith only [h2, h4494, hlam]
                            · linarith only [h0, h4494, hlam]
                          · have p4429_0 := h4429c.1
                            have p4429_1 := h4429c.2.1
                            have p4429_2 := h4429c.2.2.1
                            have p4429_3 := h4429c.2.2.2
                            linarith only [hlam, p4429_0]
                          · have p4429_0 := h4429c.1
                            have p4429_1 := h4429c.2.1
                            have p4429_2 := h4429c.2.2.1
                            have p4429_3 := h4429c.2.2.2
                            linarith only [h2, h4281, h4284, h4287, h4290, hlam, p4429_2]
                          · have p4429_0 := h4429c.1
                            have p4429_1 := h4429c.2.1
                            have p4429_2 := h4429c.2.2.1
                            have p4429_3 := h4429c.2.2.2
                            rcases p4429_3 (m.d 0 2) (by simp) with h4499 | h4499
                            · linarith only [h2, h4499, hlam]
                            · linarith only [h4282, h4499, hlam]
                          · have p4429_0 := h4429c.1
                            have p4429_1 := h4429c.2.1
                            have p4429_2 := h4429c.2.2.1
                            have p4429_3 := h4429c.2.2.2
                            linarith only [h4281, hlam, p4429_0]
                          · have p4429_0 := h4429c.1
                            have p4429_1 := h4429c.2.1
                            have p4429_2 := h4429c.2.2.1
                            have p4429_3 := h4429c.2.2.2
                            linarith only [h4287, hlam, p4429_0]
                          · have p4429_0 := h4429c.1
                            have p4429_1 := h4429c.2.1
                            have p4429_2 := h4429c.2.2.1
                            have p4429_3 := h4429c.2.2.2
                            linarith only [h4423, hlam, p4429_0]
                          · have p4429_0 := h4429c.1
                            have p4429_1 := h4429c.2.1
                            have p4429_2 := h4429c.2.2.1
                            have p4429_3 := h4429c.2.2.2
                            linarith only [hlam, p4429_0]
                          · have p4429_0 := h4429c.1
                            have p4429_1 := h4429c.2.1
                            have p4429_2 := h4429c.2.2.1
                            have p4429_3 := h4429c.2.2.2
                            linarith only [h4425, hlam, p4429_0]
                          · have p4429_0 := h4429c.1
                            have p4429_1 := h4429c.2.1
                            have p4429_2 := h4429c.2.2.1
                            have p4429_3 := h4429c.2.2.2
                            linarith only [h4282, hlam, p4429_0]
                          · have p4429_0 := h4429c.1
                            have p4429_1 := h4429c.2.1
                            have p4429_2 := h4429c.2.2.1
                            have p4429_3 := h4429c.2.2.2
                            linarith only [h4288, hlam, p4429_0]
                          · have p4429_0 := h4429c.1
                            have p4429_1 := h4429c.2.1
                            have p4429_2 := h4429c.2.2.1
                            have p4429_3 := h4429c.2.2.2
                            linarith only [h4424, hlam, p4429_0]
                          · have p4429_0 := h4429c.1
                            have p4429_1 := h4429c.2.1
                            have p4429_2 := h4429c.2.2.1
                            have p4429_3 := h4429c.2.2.2
                            linarith only [h0, h4288, h4423, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4429_1]
                          · have p4429_0 := h4429c.1
                            have p4429_1 := h4429c.2.1
                            have p4429_2 := h4429c.2.2.1
                            have p4429_3 := h4429c.2.2.2
                            linarith only [hlam, p4429_0]
                    · linarith only [h2, h4281, h4284, h4287, h4290, h4423, h4424, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h2, h4281, h4284, h4287, h4290, h4423, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
              · linarith only [h4285, h4287, h4289, hlam]
            · linarith only [h2, h4282, h4287, h4288, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
          · linarith only [h2, h4281, h4287, hc12, hc23, hlam, hphi]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4517 | h4517
        · linarith only [h0, h2, h4281, h4517, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4519 | h4519
          · rcases m.htr 1 2 5 (by decide) (by decide) with h4520 | h4520
            · rcases m.htr 1 3 4 (by decide) (by decide) with h4521 | h4521
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4522 | h4522
                · linarith only [h1, h4284, h4522, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4524 | h4524
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4525 | h4525
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4526 | h4526
                      · linarith only [h0, h4284, h4519, h4526, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4528 | h4528
                        · linarith only [h1, h4284, h4519, h4524, h4528, hlam]
                        · rcases h2bigk with h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c
                          · have p4530_0 := h4530c.1
                            have p4530_1 := h4530c.2.1
                            have p4530_2 := h4530c.2.2.1
                            have p4530_3 := h4530c.2.2.2
                            linarith only [hlam, p4530_0]
                          · have p4530_0 := h4530c.1
                            have p4530_1 := h4530c.2.1
                            have p4530_2 := h4530c.2.2.1
                            have p4530_3 := h4530c.2.2.2
                            linarith only [h2, hc12, hc23, hlam, hphi, p4530_1]
                          · have p4530_0 := h4530c.1
                            have p4530_1 := h4530c.2.1
                            have p4530_2 := h4530c.2.2.1
                            have p4530_3 := h4530c.2.2.2
                            linarith only [h2, hlam, p4530_0]
                          · have p4530_0 := h4530c.1
                            have p4530_1 := h4530c.2.1
                            have p4530_2 := h4530c.2.2.1
                            have p4530_3 := h4530c.2.2.2
                            rcases p4530_3 (m.d 0 2) (by simp) with h4534 | h4534
                            · rcases p4530_3 (m.d 1 2) (by simp) with h4535 | h4535
                              · linarith only [h0, h4535, hlam]
                              · linarith only [h4519, h4535, hlam]
                            · linarith only [h4534, hlam, p4530_0]
                          · have p4530_0 := h4530c.1
                            have p4530_1 := h4530c.2.1
                            have p4530_2 := h4530c.2.2.1
                            have p4530_3 := h4530c.2.2.2
                            rcases p4530_3 (m.d 0 2) (by simp) with h4539 | h4539
                            · rcases p4530_3 (m.d 1 2) (by simp) with h4540 | h4540
                              · linarith only [h0, h4540, hlam]
                              · linarith only [h4520, h4540, hlam]
                            · linarith only [h4539, hlam, p4530_0]
                          · have p4530_0 := h4530c.1
                            have p4530_1 := h4530c.2.1
                            have p4530_2 := h4530c.2.2.1
                            have p4530_3 := h4530c.2.2.2
                            linarith only [h0, hlam, p4530_1]
                          · have p4530_0 := h4530c.1
                            have p4530_1 := h4530c.2.1
                            have p4530_2 := h4530c.2.2.1
                            have p4530_3 := h4530c.2.2.2
                            linarith only [hlam, p4530_0]
                          · have p4530_0 := h4530c.1
                            have p4530_1 := h4530c.2.1
                            have p4530_2 := h4530c.2.2.1
                            have p4530_3 := h4530c.2.2.2
                            linarith only [h4517, hlam, p4530_0]
                          · have p4530_0 := h4530c.1
                            have p4530_1 := h4530c.2.1
                            have p4530_2 := h4530c.2.2.1
                            have p4530_3 := h4530c.2.2.2
                            rcases p4530_3 (m.d 0 2) (by simp) with h4547 | h4547
                            · rcases p4530_3 (m.d 1 2) (by simp) with h4548 | h4548
                              · rcases p4530_3 (m.d 2 3) (by simp) with h4549 | h4549
                                · rcases p4530_3 (m.d 2 4) (by simp) with h4550 | h4550
                                  · linarith only [h4550, hlam, p4530_0]
                                  · rcases p4530_3 (m.d 2 5) (by simp) with h4552 | h4552
                                    · linarith only [h4520, h4552, hlam]
                                    · linarith only [h4526, h4552, hlam]
                                · linarith only [h4524, h4549, hlam]
                              · linarith only [h4548, hlam, p4530_0]
                            · linarith only [h4281, h4547, hlam]
                          · have p4530_0 := h4530c.1
                            have p4530_1 := h4530c.2.1
                            have p4530_2 := h4530c.2.2.1
                            have p4530_3 := h4530c.2.2.2
                            rcases p4530_3 (m.d 0 2) (by simp) with h4558 | h4558
                            · rcases p4530_3 (m.d 1 2) (by simp) with h4559 | h4559
                              · rcases p4530_3 (m.d 2 3) (by simp) with h4560 | h4560
                                · rcases p4530_3 (m.d 2 4) (by simp) with h4561 | h4561
                                  · linarith only [h4519, h4561, hlam]
                                  · rcases p4530_3 (m.d 2 5) (by simp) with h4563 | h4563
                                    · linarith only [h4563, hlam, p4530_0]
                                    · rcases h4bigk with h4565c | h4565c | h4565c | h4565c | h4565c | h4565c | h4565c | h4565c | h4565c | h4565c | h4565c | h4565c | h4565c | h4565c | h4565c | h4565c | h4565c | h4565c | h4565c | h4565c | h4565c | h4565c | h4565c | h4565c | h4565c
                                      · have p4565_0 := h4565c.1
                                        have p4565_1 := h4565c.2.1
                                        have p4565_2 := h4565c.2.2.1
                                        have p4565_3 := h4565c.2.2.2
                                        linarith only [hlam, p4565_0]
                                      · have p4565_0 := h4565c.1
                                        have p4565_1 := h4565c.2.1
                                        have p4565_2 := h4565c.2.2.1
                                        have p4565_3 := h4565c.2.2.2
                                        linarith only [h4284, h4519, h4524, hc34, hc45, hlam, hphi, p4565_1]
                                      · have p4565_0 := h4565c.1
                                        have p4565_1 := h4565c.2.1
                                        have p4565_2 := h4565c.2.2.1
                                        have p4565_3 := h4565c.2.2.2
                                        linarith only [h4284, h4524, hc34, hc45, hlam, hphi, p4565_1]
                                      · have p4565_0 := h4565c.1
                                        have p4565_1 := h4565c.2.1
                                        have p4565_2 := h4565c.2.2.1
                                        have p4565_3 := h4565c.2.2.2
                                        linarith only [h4284, hc34, hc45, hlam, hphi, p4565_1]
                                      · have p4565_0 := h4565c.1
                                        have p4565_1 := h4565c.2.1
                                        have p4565_2 := h4565c.2.2.1
                                        have p4565_3 := h4565c.2.2.2
                                        linarith only [h4284, hlam, p4565_0]
                                      · have p4565_0 := h4565c.1
                                        have p4565_1 := h4565c.2.1
                                        have p4565_2 := h4565c.2.2.1
                                        have p4565_3 := h4565c.2.2.2
                                        linarith only [h1, hlam, p4565_0]
                                      · have p4565_0 := h4565c.1
                                        have p4565_1 := h4565c.2.1
                                        have p4565_2 := h4565c.2.2.1
                                        have p4565_3 := h4565c.2.2.2
                                        linarith only [hlam, p4565_0]
                                      · have p4565_0 := h4565c.1
                                        have p4565_1 := h4565c.2.1
                                        have p4565_2 := h4565c.2.2.1
                                        have p4565_3 := h4565c.2.2.2
                                        linarith only [h1, h4524, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4565_1]
                                      · have p4565_0 := h4565c.1
                                        have p4565_1 := h4565c.2.1
                                        have p4565_2 := h4565c.2.2.1
                                        have p4565_3 := h4565c.2.2.2
                                        linarith only [h1, h4284, hc34, hc45, hlam, hphi, p4565_1]
                                      · have p4565_0 := h4565c.1
                                        have p4565_1 := h4565c.2.1
                                        have p4565_2 := h4565c.2.2.1
                                        have p4565_3 := h4565c.2.2.2
                                        linarith only [h4522, hlam, p4565_0]
                                      · have p4565_0 := h4565c.1
                                        have p4565_1 := h4565c.2.1
                                        have p4565_2 := h4565c.2.2.1
                                        have p4565_3 := h4565c.2.2.2
                                        linarith only [h4281, hlam, p4565_0]
                                      · have p4565_0 := h4565c.1
                                        have p4565_1 := h4565c.2.1
                                        have p4565_2 := h4565c.2.2.1
                                        have p4565_3 := h4565c.2.2.2
                                        linarith only [h4519, hlam, p4565_0]
                                      · have p4565_0 := h4565c.1
                                        have p4565_1 := h4565c.2.1
                                        have p4565_2 := h4565c.2.2.1
                                        have p4565_3 := h4565c.2.2.2
                                        linarith only [hlam, p4565_0]
                                      · have p4565_0 := h4565c.1
                                        have p4565_1 := h4565c.2.1
                                        have p4565_2 := h4565c.2.2.1
                                        have p4565_3 := h4565c.2.2.2
                                        linarith only [h4526, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4530_1, p4565_1]
                                      · have p4565_0 := h4565c.1
                                        have p4565_1 := h4565c.2.1
                                        have p4565_2 := h4565c.2.2.1
                                        have p4565_3 := h4565c.2.2.2
                                        linarith only [h4526, hlam, p4565_0]
                                      · have p4565_0 := h4565c.1
                                        have p4565_1 := h4565c.2.1
                                        have p4565_2 := h4565c.2.2.1
                                        have p4565_3 := h4565c.2.2.2
                                        linarith only [h4283, hlam, p4565_0]
                                      · have p4565_0 := h4565c.1
                                        have p4565_1 := h4565c.2.1
                                        have p4565_2 := h4565c.2.2.1
                                        have p4565_3 := h4565c.2.2.2
                                        linarith only [h4521, hlam, p4565_0]
                                      · have p4565_0 := h4565c.1
                                        have p4565_1 := h4565c.2.1
                                        have p4565_2 := h4565c.2.2.1
                                        have p4565_3 := h4565c.2.2.2
                                        linarith only [h4524, hlam, p4565_0]
                                      · have p4565_0 := h4565c.1
                                        have p4565_1 := h4565c.2.1
                                        have p4565_2 := h4565c.2.2.1
                                        have p4565_3 := h4565c.2.2.2
                                        linarith only [hlam, p4565_0]
                                      · have p4565_0 := h4565c.1
                                        have p4565_1 := h4565c.2.1
                                        have p4565_2 := h4565c.2.2.1
                                        have p4565_3 := h4565c.2.2.2
                                        linarith only [h4528, hlam, p4565_0]
                                      · have p4565_0 := h4565c.1
                                        have p4565_1 := h4565c.2.1
                                        have p4565_2 := h4565c.2.2.1
                                        have p4565_3 := h4565c.2.2.2
                                        linarith only [hc04, hc45, hlam, hphi, p4565_1]
                                      · have p4565_0 := h4565c.1
                                        have p4565_1 := h4565c.2.1
                                        have p4565_2 := h4565c.2.2.1
                                        have p4565_3 := h4565c.2.2.2
                                        linarith only [h4519, hc24, hc45, hlam, hphi, p4565_1]
                                      · have p4565_0 := h4565c.1
                                        have p4565_1 := h4565c.2.1
                                        have p4565_2 := h4565c.2.2.1
                                        have p4565_3 := h4565c.2.2.2
                                        linarith only [h4524, hc34, hc45, hlam, hphi, p4565_1]
                                      · have p4565_0 := h4565c.1
                                        have p4565_1 := h4565c.2.1
                                        have p4565_2 := h4565c.2.2.1
                                        have p4565_3 := h4565c.2.2.2
                                        linarith only [hc34, hc45, hlam, hphi, p4565_1]
                                      · have p4565_0 := h4565c.1
                                        have p4565_1 := h4565c.2.1
                                        have p4565_2 := h4565c.2.2.1
                                        have p4565_3 := h4565c.2.2.2
                                        linarith only [hlam, p4565_0]
                                · linarith only [h4525, h4560, hlam]
                              · linarith only [h4559, hlam, p4530_0]
                            · linarith only [h4282, h4558, hlam]
                          · have p4530_0 := h4530c.1
                            have p4530_1 := h4530c.2.1
                            have p4530_2 := h4530c.2.2.1
                            have p4530_3 := h4530c.2.2.2
                            rcases p4530_3 (m.d 0 2) (by simp) with h4594 | h4594
                            · linarith only [h4594, hlam, p4530_0]
                            · rcases p4530_3 (m.d 1 2) (by simp) with h4596 | h4596
                              · linarith only [h4517, h4596, hlam]
                              · rcases p4530_3 (m.d 2 3) (by simp) with h4598 | h4598
                                · rcases p4530_3 (m.d 2 4) (by simp) with h4599 | h4599
                                  · linarith only [h4524, h4599, hlam]
                                  · rcases p4530_3 (m.d 2 5) (by simp) with h4601 | h4601
                                    · linarith only [h4525, h4601, hlam]
                                    · rcases h4bigk with h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c
                                      · have p4603_0 := h4603c.1
                                        have p4603_1 := h4603c.2.1
                                        have p4603_2 := h4603c.2.2.1
                                        have p4603_3 := h4603c.2.2.2
                                        linarith only [hlam, p4603_0]
                                      · have p4603_0 := h4603c.1
                                        have p4603_1 := h4603c.2.1
                                        have p4603_2 := h4603c.2.2.1
                                        have p4603_3 := h4603c.2.2.2
                                        linarith only [h4281, h4519, h4524, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4530_1, p4603_1]
                                      · have p4603_0 := h4603c.1
                                        have p4603_1 := h4603c.2.1
                                        have p4603_2 := h4603c.2.2.1
                                        have p4603_3 := h4603c.2.2.2
                                        linarith only [h4281, h4524, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4530_1, p4603_1]
                                      · have p4603_0 := h4603c.1
                                        have p4603_1 := h4603c.2.1
                                        have p4603_2 := h4603c.2.2.1
                                        have p4603_3 := h4603c.2.2.2
                                        linarith only [h4282, h4284, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4530_1, p4603_1]
                                      · have p4603_0 := h4603c.1
                                        have p4603_1 := h4603c.2.1
                                        have p4603_2 := h4603c.2.2.1
                                        have p4603_3 := h4603c.2.2.2
                                        linarith only [h4284, hlam, p4603_0]
                                      · have p4603_0 := h4603c.1
                                        have p4603_1 := h4603c.2.1
                                        have p4603_2 := h4603c.2.2.1
                                        have p4603_3 := h4603c.2.2.2
                                        linarith only [h1, hlam, p4603_0]
                                      · have p4603_0 := h4603c.1
                                        have p4603_1 := h4603c.2.1
                                        have p4603_2 := h4603c.2.2.1
                                        have p4603_3 := h4603c.2.2.2
                                        linarith only [hlam, p4603_0]
                                      · have p4603_0 := h4603c.1
                                        have p4603_1 := h4603c.2.1
                                        have p4603_2 := h4603c.2.2.1
                                        have p4603_3 := h4603c.2.2.2
                                        linarith only [h1, h4524, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4603_1]
                                      · have p4603_0 := h4603c.1
                                        have p4603_1 := h4603c.2.1
                                        have p4603_2 := h4603c.2.2.1
                                        have p4603_3 := h4603c.2.2.2
                                        linarith only [h1, h4282, h4284, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4530_1, p4603_1]
                                      · have p4603_0 := h4603c.1
                                        have p4603_1 := h4603c.2.1
                                        have p4603_2 := h4603c.2.2.1
                                        have p4603_3 := h4603c.2.2.2
                                        linarith only [h4522, hlam, p4603_0]
                                      · have p4603_0 := h4603c.1
                                        have p4603_1 := h4603c.2.1
                                        have p4603_2 := h4603c.2.2.1
                                        have p4603_3 := h4603c.2.2.2
                                        linarith only [h4281, hlam, p4603_0]
                                      · have p4603_0 := h4603c.1
                                        have p4603_1 := h4603c.2.1
                                        have p4603_2 := h4603c.2.2.1
                                        have p4603_3 := h4603c.2.2.2
                                        linarith only [h4519, hlam, p4603_0]
                                      · have p4603_0 := h4603c.1
                                        have p4603_1 := h4603c.2.1
                                        have p4603_2 := h4603c.2.2.1
                                        have p4603_3 := h4603c.2.2.2
                                        linarith only [hlam, p4603_0]
                                      · have p4603_0 := h4603c.1
                                        have p4603_1 := h4603c.2.1
                                        have p4603_2 := h4603c.2.2.1
                                        have p4603_3 := h4603c.2.2.2
                                        linarith only [h4281, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4530_1, p4603_1]
                                      · have p4603_0 := h4603c.1
                                        have p4603_1 := h4603c.2.1
                                        have p4603_2 := h4603c.2.2.1
                                        have p4603_3 := h4603c.2.2.2
                                        linarith only [h4526, hlam, p4603_0]
                                      · have p4603_0 := h4603c.1
                                        have p4603_1 := h4603c.2.1
                                        have p4603_2 := h4603c.2.2.1
                                        have p4603_3 := h4603c.2.2.2
                                        linarith only [h4283, hlam, p4603_0]
                                      · have p4603_0 := h4603c.1
                                        have p4603_1 := h4603c.2.1
                                        have p4603_2 := h4603c.2.2.1
                                        have p4603_3 := h4603c.2.2.2
                                        linarith only [h4521, hlam, p4603_0]
                                      · have p4603_0 := h4603c.1
                                        have p4603_1 := h4603c.2.1
                                        have p4603_2 := h4603c.2.2.1
                                        have p4603_3 := h4603c.2.2.2
                                        linarith only [h4524, hlam, p4603_0]
                                      · have p4603_0 := h4603c.1
                                        have p4603_1 := h4603c.2.1
                                        have p4603_2 := h4603c.2.2.1
                                        have p4603_3 := h4603c.2.2.2
                                        linarith only [hlam, p4603_0]
                                      · have p4603_0 := h4603c.1
                                        have p4603_1 := h4603c.2.1
                                        have p4603_2 := h4603c.2.2.1
                                        have p4603_3 := h4603c.2.2.2
                                        linarith only [h4528, hlam, p4603_0]
                                      · have p4603_0 := h4603c.1
                                        have p4603_1 := h4603c.2.1
                                        have p4603_2 := h4603c.2.2.1
                                        have p4603_3 := h4603c.2.2.2
                                        linarith only [hc04, hc45, hlam, hphi, p4603_1]
                                      · have p4603_0 := h4603c.1
                                        have p4603_1 := h4603c.2.1
                                        have p4603_2 := h4603c.2.2.1
                                        have p4603_3 := h4603c.2.2.2
                                        linarith only [hc14, hc45, hlam, hphi, p4603_1]
                                      · have p4603_0 := h4603c.1
                                        have p4603_1 := h4603c.2.1
                                        have p4603_2 := h4603c.2.2.1
                                        have p4603_3 := h4603c.2.2.2
                                        linarith only [h4524, hc34, hc45, hlam, hphi, p4603_1]
                                      · have p4603_0 := h4603c.1
                                        have p4603_1 := h4603c.2.1
                                        have p4603_2 := h4603c.2.2.1
                                        have p4603_3 := h4603c.2.2.2
                                        linarith only [hc34, hc45, hlam, hphi, p4603_1]
                                      · have p4603_0 := h4603c.1
                                        have p4603_1 := h4603c.2.1
                                        have p4603_2 := h4603c.2.2.1
                                        have p4603_3 := h4603c.2.2.2
                                        linarith only [hlam, p4603_0]
                                · linarith only [h4598, hlam, p4530_0]
                          · have p4530_0 := h4530c.1
                            have p4530_1 := h4530c.2.1
                            have p4530_2 := h4530c.2.2.1
                            have p4530_3 := h4530c.2.2.2
                            rcases p4530_3 (m.d 0 2) (by simp) with h4630 | h4630
                            · linarith only [h2, h4630, hlam]
                            · linarith only [h0, h4630, hlam]
                          · have p4530_0 := h4530c.1
                            have p4530_1 := h4530c.2.1
                            have p4530_2 := h4530c.2.2.1
                            have p4530_3 := h4530c.2.2.2
                            linarith only [hlam, p4530_0]
                          · have p4530_0 := h4530c.1
                            have p4530_1 := h4530c.2.1
                            have p4530_2 := h4530c.2.2.1
                            have p4530_3 := h4530c.2.2.2
                            rcases p4530_3 (m.d 0 2) (by simp) with h4634 | h4634
                            · linarith only [h2, h4634, hlam]
                            · linarith only [h4281, h4634, hlam]
                          · have p4530_0 := h4530c.1
                            have p4530_1 := h4530c.2.1
                            have p4530_2 := h4530c.2.2.1
                            have p4530_3 := h4530c.2.2.2
                            rcases p4530_3 (m.d 0 2) (by simp) with h4637 | h4637
                            · linarith only [h2, h4637, hlam]
                            · linarith only [h4282, h4637, hlam]
                          · have p4530_0 := h4530c.1
                            have p4530_1 := h4530c.2.1
                            have p4530_2 := h4530c.2.2.1
                            have p4530_3 := h4530c.2.2.2
                            linarith only [h4281, hlam, p4530_0]
                          · have p4530_0 := h4530c.1
                            have p4530_1 := h4530c.2.1
                            have p4530_2 := h4530c.2.2.1
                            have p4530_3 := h4530c.2.2.2
                            linarith only [h4519, hlam, p4530_0]
                          · have p4530_0 := h4530c.1
                            have p4530_1 := h4530c.2.1
                            have p4530_2 := h4530c.2.2.1
                            have p4530_3 := h4530c.2.2.2
                            linarith only [h4524, hlam, p4530_0]
                          · have p4530_0 := h4530c.1
                            have p4530_1 := h4530c.2.1
                            have p4530_2 := h4530c.2.2.1
                            have p4530_3 := h4530c.2.2.2
                            linarith only [hlam, p4530_0]
                          · have p4530_0 := h4530c.1
                            have p4530_1 := h4530c.2.1
                            have p4530_2 := h4530c.2.2.1
                            have p4530_3 := h4530c.2.2.2
                            linarith only [h4526, hlam, p4530_0]
                          · have p4530_0 := h4530c.1
                            have p4530_1 := h4530c.2.1
                            have p4530_2 := h4530c.2.2.1
                            have p4530_3 := h4530c.2.2.2
                            linarith only [h4282, hlam, p4530_0]
                          · have p4530_0 := h4530c.1
                            have p4530_1 := h4530c.2.1
                            have p4530_2 := h4530c.2.2.1
                            have p4530_3 := h4530c.2.2.2
                            linarith only [h4520, hlam, p4530_0]
                          · have p4530_0 := h4530c.1
                            have p4530_1 := h4530c.2.1
                            have p4530_2 := h4530c.2.2.1
                            have p4530_3 := h4530c.2.2.2
                            linarith only [h4525, hlam, p4530_0]
                          · have p4530_0 := h4530c.1
                            have p4530_1 := h4530c.2.1
                            have p4530_2 := h4530c.2.2.1
                            have p4530_3 := h4530c.2.2.2
                            linarith only [h0, h4520, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p4530_1]
                          · have p4530_0 := h4530c.1
                            have p4530_1 := h4530c.2.1
                            have p4530_2 := h4530c.2.2.1
                            have p4530_3 := h4530c.2.2.2
                            linarith only [hlam, p4530_0]
                    · linarith only [h0, h2, h4520, h4525, hlam]
                  · linarith only [h0, h2, h4283, h4520, h4524, hc03, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h4283, h4284, h4517, h4519, h4521, hc24, hc45, hlam, hphi]
            · linarith only [h2, h4282, h4519, h4520, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
          · linarith only [h2, h4281, h4519, hc12, hc23, hlam, hphi]
    · linarith only [h2, h4281, h4283, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h4656 | h4656
    · rcases m.htr 0 4 5 (by decide) (by decide) with h4657 | h4657
      · linarith only [h4281, h4282, h4657, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4659 | h4659
        · linarith only [h0, h2, h4659, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4661 | h4661
          · rcases m.htr 1 2 5 (by decide) (by decide) with h4662 | h4662
            · linarith only [h0, h4282, h4662, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h4664 | h4664
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4665 | h4665
                · linarith only [h1, h4657, h4665, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4667 | h4667
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4668 | h4668
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4669 | h4669
                      · linarith only [h0, h1, h4282, h4657, h4661, h4668, h4669, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4671 | h4671
                        · linarith only [h0, h4282, h4661, h4667, h4669, h4671, hlam]
                        · rcases h2bigk with h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c | h4673c
                          · have p4673_0 := h4673c.1
                            have p4673_1 := h4673c.2.1
                            have p4673_2 := h4673c.2.2.1
                            have p4673_3 := h4673c.2.2.2
                            linarith only [hlam, p4673_0]
                          · have p4673_0 := h4673c.1
                            have p4673_1 := h4673c.2.1
                            have p4673_2 := h4673c.2.2.1
                            have p4673_3 := h4673c.2.2.2
                            linarith only [h4282, h4669, hc12, hc45, hlam, hphi, ht23, ht34, p4673_1]
                          · have p4673_0 := h4673c.1
                            have p4673_1 := h4673c.2.1
                            have p4673_2 := h4673c.2.2.1
                            have p4673_3 := h4673c.2.2.2
                            linarith only [h2, hlam, p4673_0]
                          · have p4673_0 := h4673c.1
                            have p4673_1 := h4673c.2.1
                            have p4673_2 := h4673c.2.2.1
                            have p4673_3 := h4673c.2.2.2
                            linarith only [h4282, h4667, h4669, hc34, hc45, hlam, hphi, p4673_1]
                          · have p4673_0 := h4673c.1
                            have p4673_1 := h4673c.2.1
                            have p4673_2 := h4673c.2.2.1
                            have p4673_3 := h4673c.2.2.2
                            linarith only [h4282, hlam, p4673_0]
                          · have p4673_0 := h4673c.1
                            have p4673_1 := h4673c.2.1
                            have p4673_2 := h4673c.2.2.1
                            have p4673_3 := h4673c.2.2.2
                            linarith only [h0, hlam, p4673_1]
                          · have p4673_0 := h4673c.1
                            have p4673_1 := h4673c.2.1
                            have p4673_2 := h4673c.2.2.1
                            have p4673_3 := h4673c.2.2.2
                            linarith only [hlam, p4673_0]
                          · have p4673_0 := h4673c.1
                            have p4673_1 := h4673c.2.1
                            have p4673_2 := h4673c.2.2.1
                            have p4673_3 := h4673c.2.2.2
                            linarith only [h4659, hlam, p4673_0]
                          · have p4673_0 := h4673c.1
                            have p4673_1 := h4673c.2.1
                            have p4673_2 := h4673c.2.2.1
                            have p4673_3 := h4673c.2.2.2
                            linarith only [h0, h4282, h4667, h4669, hc34, hc45, hlam, hphi, p4673_1]
                          · have p4673_0 := h4673c.1
                            have p4673_1 := h4673c.2.1
                            have p4673_2 := h4673c.2.2.1
                            have p4673_3 := h4673c.2.2.2
                            linarith only [h4662, hlam, p4673_0]
                          · have p4673_0 := h4673c.1
                            have p4673_1 := h4673c.2.1
                            have p4673_2 := h4673c.2.2.1
                            have p4673_3 := h4673c.2.2.2
                            rcases p4673_3 (m.d 0 2) (by simp) with h4684 | h4684
                            · linarith only [h4684, hlam, p4673_0]
                            · rcases p4673_3 (m.d 1 2) (by simp) with h4686 | h4686
                              · linarith only [h4659, h4686, hlam]
                              · rcases p4673_3 (m.d 2 3) (by simp) with h4688 | h4688
                                · rcases p4673_3 (m.d 2 4) (by simp) with h4689 | h4689
                                  · linarith only [h4667, h4689, hlam]
                                  · rcases p4673_3 (m.d 2 5) (by simp) with h4691 | h4691
                                    · linarith only [h4668, h4691, hlam]
                                    · linarith only [h4282, h4691, hlam]
                                · linarith only [h4688, hlam, p4673_0]
                          · have p4673_0 := h4673c.1
                            have p4673_1 := h4673c.2.1
                            have p4673_2 := h4673c.2.2.1
                            have p4673_3 := h4673c.2.2.2
                            rcases p4673_3 (m.d 0 2) (by simp) with h4695 | h4695
                            · linarith only [h2, h4695, hlam]
                            · linarith only [h0, h4695, hlam]
                          · have p4673_0 := h4673c.1
                            have p4673_1 := h4673c.2.1
                            have p4673_2 := h4673c.2.2.1
                            have p4673_3 := h4673c.2.2.2
                            linarith only [hlam, p4673_0]
                          · have p4673_0 := h4673c.1
                            have p4673_1 := h4673c.2.1
                            have p4673_2 := h4673c.2.2.1
                            have p4673_3 := h4673c.2.2.2
                            rcases p4673_3 (m.d 0 2) (by simp) with h4699 | h4699
                            · linarith only [h2, h4699, hlam]
                            · linarith only [h4281, h4699, hlam]
                          · have p4673_0 := h4673c.1
                            have p4673_1 := h4673c.2.1
                            have p4673_2 := h4673c.2.2.1
                            have p4673_3 := h4673c.2.2.2
                            linarith only [h4282, hc02, hc23, hlam, hphi, p4673_1]
                          · have p4673_0 := h4673c.1
                            have p4673_1 := h4673c.2.1
                            have p4673_2 := h4673c.2.2.1
                            have p4673_3 := h4673c.2.2.2
                            linarith only [h4281, hlam, p4673_0]
                          · have p4673_0 := h4673c.1
                            have p4673_1 := h4673c.2.1
                            have p4673_2 := h4673c.2.2.1
                            have p4673_3 := h4673c.2.2.2
                            linarith only [h4661, hlam, p4673_0]
                          · have p4673_0 := h4673c.1
                            have p4673_1 := h4673c.2.1
                            have p4673_2 := h4673c.2.2.1
                            have p4673_3 := h4673c.2.2.2
                            linarith only [h4667, hlam, p4673_0]
                          · have p4673_0 := h4673c.1
                            have p4673_1 := h4673c.2.1
                            have p4673_2 := h4673c.2.2.1
                            have p4673_3 := h4673c.2.2.2
                            linarith only [hlam, p4673_0]
                          · have p4673_0 := h4673c.1
                            have p4673_1 := h4673c.2.1
                            have p4673_2 := h4673c.2.2.1
                            have p4673_3 := h4673c.2.2.2
                            linarith only [h4669, hlam, p4673_0]
                          · have p4673_0 := h4673c.1
                            have p4673_1 := h4673c.2.1
                            have p4673_2 := h4673c.2.2.1
                            have p4673_3 := h4673c.2.2.2
                            linarith only [h0, h4661, h4669, hc24, hc45, hlam, hphi, p4673_1]
                          · have p4673_0 := h4673c.1
                            have p4673_1 := h4673c.2.1
                            have p4673_2 := h4673c.2.2.1
                            have p4673_3 := h4673c.2.2.2
                            linarith only [h4661, h4669, hc24, hc45, hlam, hphi, p4673_1]
                          · have p4673_0 := h4673c.1
                            have p4673_1 := h4673c.2.1
                            have p4673_2 := h4673c.2.2.1
                            have p4673_3 := h4673c.2.2.2
                            linarith only [h4668, hlam, p4673_0]
                          · have p4673_0 := h4673c.1
                            have p4673_1 := h4673c.2.1
                            have p4673_2 := h4673c.2.2.1
                            have p4673_3 := h4673c.2.2.2
                            rcases p4673_3 (m.d 0 2) (by simp) with h4711 | h4711
                            · linarith only [h4282, h4711, hlam]
                            · linarith only [h4281, h4711, hlam]
                          · have p4673_0 := h4673c.1
                            have p4673_1 := h4673c.2.1
                            have p4673_2 := h4673c.2.2.1
                            have p4673_3 := h4673c.2.2.2
                            linarith only [hlam, p4673_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4715 | h4715
                      · linarith only [h0, h2, h4661, h4668, h4715, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4717 | h4717
                        · linarith only [h0, h2, h4661, h4667, h4668, h4715, h4717, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h0, h2, h4661, h4668, h4717, hc24, hc45, hlam, hphi]
                  · linarith only [h0, h2, h4656, h4661, h4667, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h4656, h4657, h4659, h4661, h4664, hc24, hc45, hlam, hphi]
          · linarith only [h2, h4281, h4661, hc12, hc23, hlam, hphi]
    · linarith only [h2, h4281, h4656, hlam]

end R2N4
