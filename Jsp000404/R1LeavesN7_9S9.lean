import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11440000 in
set_option maxHeartbeats 11440000 in
theorem r1l7_13_24_L_I_H_I_s3_x1_x1_x0_x0_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3688 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h4260 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4261 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h4262 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 1 2 3 (by decide) (by decide) with h4263 | h4263
  · linarith only [h0, h4, h4263, hlam]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h4265 | h4265
    · linarith only [h0, h3688, h4265, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h4267 | h4267
      · rcases m.htr 1 3 5 (by decide) (by decide) with h4268 | h4268
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4269 | h4269
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4270 | h4270
            · rcases m.htr 2 3 5 (by decide) (by decide) with h4271 | h4271
              · rcases m.htr 2 4 5 (by decide) (by decide) with h4272 | h4272
                · rcases m.htr 3 4 5 (by decide) (by decide) with h4273 | h4273
                  · rcases h3bigk with h4274c | h4274c | h4274c | h4274c | h4274c | h4274c | h4274c | h4274c | h4274c | h4274c | h4274c | h4274c | h4274c | h4274c | h4274c | h4274c | h4274c | h4274c | h4274c | h4274c | h4274c | h4274c | h4274c | h4274c | h4274c
                    · have p4274_0 := h4274c.1
                      have p4274_1 := h4274c.2.1
                      have p4274_2 := h4274c.2.2.1
                      have p4274_3 := h4274c.2.2.2
                      linarith only [hlam, p4274_0]
                    · have p4274_0 := h4274c.1
                      have p4274_1 := h4274c.2.1
                      have p4274_2 := h4274c.2.2.1
                      have p4274_3 := h4274c.2.2.2
                      linarith only [h4267, h4273, hc03, hc45, hlam, hphi, ht0b, ht5b, p4274_1]
                    · have p4274_0 := h4274c.1
                      have p4274_1 := h4274c.2.1
                      have p4274_2 := h4274c.2.2.1
                      have p4274_3 := h4274c.2.2.2
                      linarith only [h4, hlam, p4274_1]
                    · have p4274_0 := h4274c.1
                      have p4274_1 := h4274c.2.1
                      have p4274_2 := h4274c.2.2.1
                      have p4274_3 := h4274c.2.2.2
                      rcases p4274_3 (m.d 0 3) (by simp) with h4278 | h4278
                      · rcases p4274_3 (m.d 1 3) (by simp) with h4279 | h4279
                        · linarith only [h1, h4279, hlam]
                        · linarith only [h4267, h4279, hlam]
                      · linarith only [h4278, hlam, p4274_0]
                    · have p4274_0 := h4274c.1
                      have p4274_1 := h4274c.2.1
                      have p4274_2 := h4274c.2.2.1
                      have p4274_3 := h4274c.2.2.2
                      rcases p4274_3 (m.d 0 3) (by simp) with h4283 | h4283
                      · rcases p4274_3 (m.d 1 3) (by simp) with h4284 | h4284
                        · linarith only [h1, h4284, hlam]
                        · linarith only [h4268, h4284, hlam]
                      · linarith only [h4283, hlam, p4274_0]
                    · have p4274_0 := h4274c.1
                      have p4274_1 := h4274c.2.1
                      have p4274_2 := h4274c.2.2.1
                      have p4274_3 := h4274c.2.2.2
                      linarith only [h1, hlam, p4274_0]
                    · have p4274_0 := h4274c.1
                      have p4274_1 := h4274c.2.1
                      have p4274_2 := h4274c.2.2.1
                      have p4274_3 := h4274c.2.2.2
                      linarith only [hlam, p4274_0]
                    · have p4274_0 := h4274c.1
                      have p4274_1 := h4274c.2.1
                      have p4274_2 := h4274c.2.2.1
                      have p4274_3 := h4274c.2.2.2
                      linarith only [h4263, hlam, p4274_1]
                    · have p4274_0 := h4274c.1
                      have p4274_1 := h4274c.2.1
                      have p4274_2 := h4274c.2.2.1
                      have p4274_3 := h4274c.2.2.2
                      linarith only [h1, h4273, hc01, hc45, hlam, hphi, ht0b, ht5b, p4274_1]
                    · have p4274_0 := h4274c.1
                      have p4274_1 := h4274c.2.1
                      have p4274_2 := h4274c.2.2.1
                      have p4274_3 := h4274c.2.2.2
                      rcases p4274_3 (m.d 0 3) (by simp) with h4292 | h4292
                      · rcases p4274_3 (m.d 1 3) (by simp) with h4293 | h4293
                        · rcases p4274_3 (m.d 2 3) (by simp) with h4294 | h4294
                          · rcases p4274_3 (m.d 3 4) (by simp) with h4295 | h4295
                            · linarith only [h4267, h4295, hlam]
                            · linarith only [h4273, h4295, hlam]
                          · linarith only [h4271, h4294, hlam]
                        · linarith only [h4293, hlam, p4274_0]
                      · linarith only [h4261, h4292, hlam]
                    · have p4274_0 := h4274c.1
                      have p4274_1 := h4274c.2.1
                      have p4274_2 := h4274c.2.2.1
                      have p4274_3 := h4274c.2.2.2
                      linarith only [h4260, h4273, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4274_1]
                    · have p4274_0 := h4274c.1
                      have p4274_1 := h4274c.2.1
                      have p4274_2 := h4274c.2.2.1
                      have p4274_3 := h4274c.2.2.2
                      linarith only [h4267, h4273, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4274_1]
                    · have p4274_0 := h4274c.1
                      have p4274_1 := h4274c.2.1
                      have p4274_2 := h4274c.2.2.1
                      have p4274_3 := h4274c.2.2.2
                      linarith only [hlam, p4274_0]
                    · have p4274_0 := h4274c.1
                      have p4274_1 := h4274c.2.1
                      have p4274_2 := h4274c.2.2.1
                      have p4274_3 := h4274c.2.2.2
                      rcases p4274_3 (m.d 0 3) (by simp) with h4304 | h4304
                      · linarith only [h4, h4304, hlam]
                      · linarith only [h4260, h4304, hlam]
                    · have p4274_0 := h4274c.1
                      have p4274_1 := h4274c.2.1
                      have p4274_2 := h4274c.2.2.1
                      have p4274_3 := h4274c.2.2.2
                      rcases p4274_3 (m.d 0 3) (by simp) with h4307 | h4307
                      · linarith only [h4, h4307, hlam]
                      · linarith only [h4261, h4307, hlam]
                    · have p4274_0 := h4274c.1
                      have p4274_1 := h4274c.2.1
                      have p4274_2 := h4274c.2.2.1
                      have p4274_3 := h4274c.2.2.2
                      linarith only [h4260, hlam, p4274_0]
                    · have p4274_0 := h4274c.1
                      have p4274_1 := h4274c.2.1
                      have p4274_2 := h4274c.2.2.1
                      have p4274_3 := h4274c.2.2.2
                      linarith only [h4267, hlam, p4274_0]
                    · have p4274_0 := h4274c.1
                      have p4274_1 := h4274c.2.1
                      have p4274_2 := h4274c.2.2.1
                      have p4274_3 := h4274c.2.2.2
                      linarith only [h4270, hlam, p4274_0]
                    · have p4274_0 := h4274c.1
                      have p4274_1 := h4274c.2.1
                      have p4274_2 := h4274c.2.2.1
                      have p4274_3 := h4274c.2.2.2
                      linarith only [hlam, p4274_0]
                    · have p4274_0 := h4274c.1
                      have p4274_1 := h4274c.2.1
                      have p4274_2 := h4274c.2.2.1
                      have p4274_3 := h4274c.2.2.2
                      linarith only [h1, h4267, hc01, hc35, hlam, hphi, ht0b, ht5b, p4274_1]
                    · have p4274_0 := h4274c.1
                      have p4274_1 := h4274c.2.1
                      have p4274_2 := h4274c.2.2.1
                      have p4274_3 := h4274c.2.2.2
                      linarith only [h4261, hlam, p4274_0]
                    · have p4274_0 := h4274c.1
                      have p4274_1 := h4274c.2.1
                      have p4274_2 := h4274c.2.2.1
                      have p4274_3 := h4274c.2.2.2
                      linarith only [h4268, hlam, p4274_0]
                    · have p4274_0 := h4274c.1
                      have p4274_1 := h4274c.2.1
                      have p4274_2 := h4274c.2.2.1
                      have p4274_3 := h4274c.2.2.2
                      linarith only [h4271, hlam, p4274_0]
                    · have p4274_0 := h4274c.1
                      have p4274_1 := h4274c.2.1
                      have p4274_2 := h4274c.2.2.1
                      have p4274_3 := h4274c.2.2.2
                      linarith only [h4273, hlam, p4274_0]
                    · have p4274_0 := h4274c.1
                      have p4274_1 := h4274c.2.1
                      have p4274_2 := h4274c.2.2.1
                      have p4274_3 := h4274c.2.2.2
                      linarith only [hlam, p4274_0]
                  · rcases h3bigk with h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c
                    · have p4320_0 := h4320c.1
                      have p4320_1 := h4320c.2.1
                      have p4320_2 := h4320c.2.2.1
                      have p4320_3 := h4320c.2.2.2
                      linarith only [hlam, p4320_0]
                    · have p4320_0 := h4320c.1
                      have p4320_1 := h4320c.2.1
                      have p4320_2 := h4320c.2.2.1
                      have p4320_3 := h4320c.2.2.2
                      linarith only [h4267, h4269, h4273, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p4320_1]
                    · have p4320_0 := h4320c.1
                      have p4320_1 := h4320c.2.1
                      have p4320_2 := h4320c.2.2.1
                      have p4320_3 := h4320c.2.2.2
                      linarith only [h4, hlam, p4320_1]
                    · have p4320_0 := h4320c.1
                      have p4320_1 := h4320c.2.1
                      have p4320_2 := h4320c.2.2.1
                      have p4320_3 := h4320c.2.2.2
                      rcases p4320_3 (m.d 0 3) (by simp) with h4324 | h4324
                      · rcases p4320_3 (m.d 1 3) (by simp) with h4325 | h4325
                        · linarith only [h1, h4325, hlam]
                        · linarith only [h4267, h4325, hlam]
                      · linarith only [h4324, hlam, p4320_0]
                    · have p4320_0 := h4320c.1
                      have p4320_1 := h4320c.2.1
                      have p4320_2 := h4320c.2.2.1
                      have p4320_3 := h4320c.2.2.2
                      rcases p4320_3 (m.d 0 3) (by simp) with h4329 | h4329
                      · rcases p4320_3 (m.d 1 3) (by simp) with h4330 | h4330
                        · linarith only [h1, h4330, hlam]
                        · linarith only [h4268, h4330, hlam]
                      · linarith only [h4329, hlam, p4320_0]
                    · have p4320_0 := h4320c.1
                      have p4320_1 := h4320c.2.1
                      have p4320_2 := h4320c.2.2.1
                      have p4320_3 := h4320c.2.2.2
                      linarith only [h1, hlam, p4320_0]
                    · have p4320_0 := h4320c.1
                      have p4320_1 := h4320c.2.1
                      have p4320_2 := h4320c.2.2.1
                      have p4320_3 := h4320c.2.2.2
                      linarith only [hlam, p4320_0]
                    · have p4320_0 := h4320c.1
                      have p4320_1 := h4320c.2.1
                      have p4320_2 := h4320c.2.2.1
                      have p4320_3 := h4320c.2.2.2
                      linarith only [h4263, hlam, p4320_1]
                    · have p4320_0 := h4320c.1
                      have p4320_1 := h4320c.2.1
                      have p4320_2 := h4320c.2.2.1
                      have p4320_3 := h4320c.2.2.2
                      rcases p4320_3 (m.d 0 3) (by simp) with h4337 | h4337
                      · rcases p4320_3 (m.d 1 3) (by simp) with h4338 | h4338
                        · rcases p4320_3 (m.d 2 3) (by simp) with h4339 | h4339
                          · rcases p4320_3 (m.d 3 4) (by simp) with h4340 | h4340
                            · linarith only [h4340, hlam, p4320_0]
                            · rcases p4320_3 (m.d 3 5) (by simp) with h4342 | h4342
                              · linarith only [h4268, h4342, hlam]
                              · linarith only [h4273, h4342, hlam]
                          · linarith only [h4270, h4339, hlam]
                        · linarith only [h4338, hlam, p4320_0]
                      · linarith only [h4260, h4337, hlam]
                    · have p4320_0 := h4320c.1
                      have p4320_1 := h4320c.2.1
                      have p4320_2 := h4320c.2.2.1
                      have p4320_3 := h4320c.2.2.2
                      rcases p4320_3 (m.d 0 3) (by simp) with h4348 | h4348
                      · rcases p4320_3 (m.d 1 3) (by simp) with h4349 | h4349
                        · rcases p4320_3 (m.d 2 3) (by simp) with h4350 | h4350
                          · rcases p4320_3 (m.d 3 4) (by simp) with h4351 | h4351
                            · linarith only [h4267, h4351, hlam]
                            · rcases p4320_3 (m.d 3 5) (by simp) with h4353 | h4353
                              · linarith only [h4353, hlam, p4320_0]
                              · rcases h4bigk with h4355c | h4355c | h4355c | h4355c | h4355c | h4355c | h4355c | h4355c | h4355c | h4355c | h4355c | h4355c | h4355c | h4355c | h4355c | h4355c | h4355c | h4355c | h4355c | h4355c | h4355c | h4355c | h4355c | h4355c | h4355c
                                · have p4355_0 := h4355c.1
                                  have p4355_1 := h4355c.2.1
                                  have p4355_2 := h4355c.2.2.1
                                  have p4355_3 := h4355c.2.2.2
                                  linarith only [hlam, p4355_0]
                                · have p4355_0 := h4355c.1
                                  have p4355_1 := h4355c.2.1
                                  have p4355_2 := h4355c.2.2.1
                                  have p4355_3 := h4355c.2.2.2
                                  linarith only [h4260, h4269, h4273, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p4355_1]
                                · have p4355_0 := h4355c.1
                                  have p4355_1 := h4355c.2.1
                                  have p4355_2 := h4355c.2.2.1
                                  have p4355_3 := h4355c.2.2.2
                                  linarith only [h3688, hlam, p4355_0]
                                · have p4355_0 := h4355c.1
                                  have p4355_1 := h4355c.2.1
                                  have p4355_2 := h4355c.2.2.1
                                  have p4355_3 := h4355c.2.2.2
                                  rcases p4355_3 (m.d 0 4) (by simp) with h4359 | h4359
                                  · rcases p4355_3 (m.d 1 4) (by simp) with h4360 | h4360
                                    · linarith only [h2, h4360, hlam]
                                    · linarith only [h4267, h4360, hlam]
                                  · linarith only [h4260, h4359, hlam]
                                · have p4355_0 := h4355c.1
                                  have p4355_1 := h4355c.2.1
                                  have p4355_2 := h4355c.2.2.1
                                  have p4355_3 := h4355c.2.2.2
                                  linarith only [h4, h4260, h4273, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4355_1]
                                · have p4355_0 := h4355c.1
                                  have p4355_1 := h4355c.2.1
                                  have p4355_2 := h4355c.2.2.1
                                  have p4355_3 := h4355c.2.2.2
                                  linarith only [h2, hlam, p4355_1]
                                · have p4355_0 := h4355c.1
                                  have p4355_1 := h4355c.2.1
                                  have p4355_2 := h4355c.2.2.1
                                  have p4355_3 := h4355c.2.2.2
                                  linarith only [hlam, p4355_0]
                                · have p4355_0 := h4355c.1
                                  have p4355_1 := h4355c.2.1
                                  have p4355_2 := h4355c.2.2.1
                                  have p4355_3 := h4355c.2.2.2
                                  linarith only [h4265, hlam, p4355_0]
                                · have p4355_0 := h4355c.1
                                  have p4355_1 := h4355c.2.1
                                  have p4355_2 := h4355c.2.2.1
                                  have p4355_3 := h4355c.2.2.2
                                  linarith only [h1, h4267, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4355_1]
                                · have p4355_0 := h4355c.1
                                  have p4355_1 := h4355c.2.1
                                  have p4355_2 := h4355c.2.2.1
                                  have p4355_3 := h4355c.2.2.2
                                  linarith only [h1, h4267, h4273, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4355_1]
                                · have p4355_0 := h4355c.1
                                  have p4355_1 := h4355c.2.1
                                  have p4355_2 := h4355c.2.2.1
                                  have p4355_3 := h4355c.2.2.2
                                  linarith only [h3688, hc02, hc24, hlam, hphi, p4355_1]
                                · have p4355_0 := h4355c.1
                                  have p4355_1 := h4355c.2.1
                                  have p4355_2 := h4355c.2.2.1
                                  have p4355_3 := h4355c.2.2.2
                                  linarith only [h4265, hc12, hc24, hlam, hphi, p4355_1]
                                · have p4355_0 := h4355c.1
                                  have p4355_1 := h4355c.2.1
                                  have p4355_2 := h4355c.2.2.1
                                  have p4355_3 := h4355c.2.2.2
                                  linarith only [hlam, p4355_0]
                                · have p4355_0 := h4355c.1
                                  have p4355_1 := h4355c.2.1
                                  have p4355_2 := h4355c.2.2.1
                                  have p4355_3 := h4355c.2.2.2
                                  rcases p4355_3 (m.d 0 4) (by simp) with h4373 | h4373
                                  · linarith only [h3688, h4373, hlam]
                                  · linarith only [h4260, h4373, hlam]
                                · have p4355_0 := h4355c.1
                                  have p4355_1 := h4355c.2.1
                                  have p4355_2 := h4355c.2.2.1
                                  have p4355_3 := h4355c.2.2.2
                                  linarith only [h4270, h4273, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4355_1]
                                · have p4355_0 := h4355c.1
                                  have p4355_1 := h4355c.2.1
                                  have p4355_2 := h4355c.2.2.1
                                  have p4355_3 := h4355c.2.2.2
                                  linarith only [h4260, hlam, p4355_1]
                                · have p4355_0 := h4355c.1
                                  have p4355_1 := h4355c.2.1
                                  have p4355_2 := h4355c.2.2.1
                                  have p4355_3 := h4355c.2.2.2
                                  linarith only [h4267, hlam, p4355_0]
                                · have p4355_0 := h4355c.1
                                  have p4355_1 := h4355c.2.1
                                  have p4355_2 := h4355c.2.2.1
                                  have p4355_3 := h4355c.2.2.2
                                  linarith only [h4270, hlam, p4355_0]
                                · have p4355_0 := h4355c.1
                                  have p4355_1 := h4355c.2.1
                                  have p4355_2 := h4355c.2.2.1
                                  have p4355_3 := h4355c.2.2.2
                                  linarith only [hlam, p4355_0]
                                · have p4355_0 := h4355c.1
                                  have p4355_1 := h4355c.2.1
                                  have p4355_2 := h4355c.2.2.1
                                  have p4355_3 := h4355c.2.2.2
                                  linarith only [h4273, hlam, p4355_0]
                                · have p4355_0 := h4355c.1
                                  have p4355_1 := h4355c.2.1
                                  have p4355_2 := h4355c.2.2.1
                                  have p4355_3 := h4355c.2.2.2
                                  linarith only [h4262, hlam, p4355_0]
                                · have p4355_0 := h4355c.1
                                  have p4355_1 := h4355c.2.1
                                  have p4355_2 := h4355c.2.2.1
                                  have p4355_3 := h4355c.2.2.2
                                  linarith only [h4269, hlam, p4355_0]
                                · have p4355_0 := h4355c.1
                                  have p4355_1 := h4355c.2.1
                                  have p4355_2 := h4355c.2.2.1
                                  have p4355_3 := h4355c.2.2.2
                                  linarith only [h4272, hlam, p4355_0]
                                · have p4355_0 := h4355c.1
                                  have p4355_1 := h4355c.2.1
                                  have p4355_2 := h4355c.2.2.1
                                  have p4355_3 := h4355c.2.2.2
                                  linarith only [h2, h4269, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p4355_1]
                                · have p4355_0 := h4355c.1
                                  have p4355_1 := h4355c.2.1
                                  have p4355_2 := h4355c.2.2.1
                                  have p4355_3 := h4355c.2.2.2
                                  linarith only [hlam, p4355_0]
                          · linarith only [h4271, h4350, hlam]
                        · linarith only [h4349, hlam, p4320_0]
                      · linarith only [h4261, h4348, hlam]
                    · have p4320_0 := h4320c.1
                      have p4320_1 := h4320c.2.1
                      have p4320_2 := h4320c.2.2.1
                      have p4320_3 := h4320c.2.2.2
                      linarith only [h2, h4260, h4269, h4273, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4320_1]
                    · have p4320_0 := h4320c.1
                      have p4320_1 := h4320c.2.1
                      have p4320_2 := h4320c.2.2.1
                      have p4320_3 := h4320c.2.2.2
                      linarith only [h4267, h4269, h4273, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4320_1]
                    · have p4320_0 := h4320c.1
                      have p4320_1 := h4320c.2.1
                      have p4320_2 := h4320c.2.2.1
                      have p4320_3 := h4320c.2.2.2
                      linarith only [hlam, p4320_0]
                    · have p4320_0 := h4320c.1
                      have p4320_1 := h4320c.2.1
                      have p4320_2 := h4320c.2.2.1
                      have p4320_3 := h4320c.2.2.2
                      rcases p4320_3 (m.d 0 3) (by simp) with h4393 | h4393
                      · linarith only [h4, h4393, hlam]
                      · linarith only [h4260, h4393, hlam]
                    · have p4320_0 := h4320c.1
                      have p4320_1 := h4320c.2.1
                      have p4320_2 := h4320c.2.2.1
                      have p4320_3 := h4320c.2.2.2
                      rcases p4320_3 (m.d 0 3) (by simp) with h4396 | h4396
                      · linarith only [h4, h4396, hlam]
                      · linarith only [h4261, h4396, hlam]
                    · have p4320_0 := h4320c.1
                      have p4320_1 := h4320c.2.1
                      have p4320_2 := h4320c.2.2.1
                      have p4320_3 := h4320c.2.2.2
                      linarith only [h4260, hlam, p4320_0]
                    · have p4320_0 := h4320c.1
                      have p4320_1 := h4320c.2.1
                      have p4320_2 := h4320c.2.2.1
                      have p4320_3 := h4320c.2.2.2
                      linarith only [h4267, hlam, p4320_0]
                    · have p4320_0 := h4320c.1
                      have p4320_1 := h4320c.2.1
                      have p4320_2 := h4320c.2.2.1
                      have p4320_3 := h4320c.2.2.2
                      linarith only [h4270, hlam, p4320_0]
                    · have p4320_0 := h4320c.1
                      have p4320_1 := h4320c.2.1
                      have p4320_2 := h4320c.2.2.1
                      have p4320_3 := h4320c.2.2.2
                      linarith only [hlam, p4320_0]
                    · have p4320_0 := h4320c.1
                      have p4320_1 := h4320c.2.1
                      have p4320_2 := h4320c.2.2.1
                      have p4320_3 := h4320c.2.2.2
                      linarith only [h4273, hlam, p4320_1]
                    · have p4320_0 := h4320c.1
                      have p4320_1 := h4320c.2.1
                      have p4320_2 := h4320c.2.2.1
                      have p4320_3 := h4320c.2.2.2
                      linarith only [h4261, hlam, p4320_0]
                    · have p4320_0 := h4320c.1
                      have p4320_1 := h4320c.2.1
                      have p4320_2 := h4320c.2.2.1
                      have p4320_3 := h4320c.2.2.2
                      linarith only [h4268, hlam, p4320_0]
                    · have p4320_0 := h4320c.1
                      have p4320_1 := h4320c.2.1
                      have p4320_2 := h4320c.2.2.1
                      have p4320_3 := h4320c.2.2.2
                      linarith only [h4271, hlam, p4320_0]
                    · have p4320_0 := h4320c.1
                      have p4320_1 := h4320c.2.1
                      have p4320_2 := h4320c.2.2.1
                      have p4320_3 := h4320c.2.2.2
                      linarith only [h1, h4268, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4320_1]
                    · have p4320_0 := h4320c.1
                      have p4320_1 := h4320c.2.1
                      have p4320_2 := h4320c.2.2.1
                      have p4320_3 := h4320c.2.2.2
                      linarith only [hlam, p4320_0]
                · linarith only [h0, h2, h3688, h4269, h4272, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h1, h4, h4268, h4271, hlam]
            · linarith only [h4, h4260, h4270, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4412 | h4412
            · rcases m.htr 2 3 5 (by decide) (by decide) with h4413 | h4413
              · rcases m.htr 2 4 5 (by decide) (by decide) with h4414 | h4414
                · rcases m.htr 3 4 5 (by decide) (by decide) with h4415 | h4415
                  · linarith only [h4267, h4269, h4415, hlam]
                  · rcases h3bigk with h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c | h4417c
                    · have p4417_0 := h4417c.1
                      have p4417_1 := h4417c.2.1
                      have p4417_2 := h4417c.2.2.1
                      have p4417_3 := h4417c.2.2.2
                      linarith only [hlam, p4417_0]
                    · have p4417_0 := h4417c.1
                      have p4417_1 := h4417c.2.1
                      have p4417_2 := h4417c.2.2.1
                      have p4417_3 := h4417c.2.2.2
                      rcases p4417_3 (m.d 0 3) (by simp) with h4419 | h4419
                      · rcases p4417_3 (m.d 1 3) (by simp) with h4420 | h4420
                        · linarith only [h1, h4420, hlam]
                        · rcases p4417_3 (m.d 2 3) (by simp) with h4422 | h4422
                          · rcases p4417_3 (m.d 3 4) (by simp) with h4423 | h4423
                            · linarith only [h4260, h4423, hlam]
                            · rcases p4417_3 (m.d 3 5) (by simp) with h4425 | h4425
                              · linarith only [h4261, h4425, hlam]
                              · rcases h4bigk with h4427c | h4427c | h4427c | h4427c | h4427c | h4427c | h4427c | h4427c | h4427c | h4427c | h4427c | h4427c | h4427c | h4427c | h4427c | h4427c | h4427c | h4427c | h4427c | h4427c | h4427c | h4427c | h4427c | h4427c | h4427c
                                · have p4427_0 := h4427c.1
                                  have p4427_1 := h4427c.2.1
                                  have p4427_2 := h4427c.2.2.1
                                  have p4427_3 := h4427c.2.2.2
                                  linarith only [hlam, p4427_0]
                                · have p4427_0 := h4427c.1
                                  have p4427_1 := h4427c.2.1
                                  have p4427_2 := h4427c.2.2.1
                                  have p4427_3 := h4427c.2.2.2
                                  linarith only [h4, h4260, h4265, hc12, hc23, hlam, hphi, p4427_1]
                                · have p4427_0 := h4427c.1
                                  have p4427_1 := h4427c.2.1
                                  have p4427_2 := h4427c.2.2.1
                                  have p4427_3 := h4427c.2.2.2
                                  linarith only [h3688, hlam, p4427_0]
                                · have p4427_0 := h4427c.1
                                  have p4427_1 := h4427c.2.1
                                  have p4427_2 := h4427c.2.2.1
                                  have p4427_3 := h4427c.2.2.2
                                  rcases p4427_3 (m.d 0 4) (by simp) with h4431 | h4431
                                  · rcases p4427_3 (m.d 1 4) (by simp) with h4432 | h4432
                                    · linarith only [h2, h4432, hlam]
                                    · linarith only [h4267, h4432, hlam]
                                  · linarith only [h4260, h4431, hlam]
                                · have p4427_0 := h4427c.1
                                  have p4427_1 := h4427c.2.1
                                  have p4427_2 := h4427c.2.2.1
                                  have p4427_3 := h4427c.2.2.2
                                  linarith only [h4, h4260, h4265, h4269, hc12, hc23, hlam, hphi, p4427_1]
                                · have p4427_0 := h4427c.1
                                  have p4427_1 := h4427c.2.1
                                  have p4427_2 := h4427c.2.2.1
                                  have p4427_3 := h4427c.2.2.2
                                  linarith only [h2, hlam, p4427_1]
                                · have p4427_0 := h4427c.1
                                  have p4427_1 := h4427c.2.1
                                  have p4427_2 := h4427c.2.2.1
                                  have p4427_3 := h4427c.2.2.2
                                  linarith only [hlam, p4427_0]
                                · have p4427_0 := h4427c.1
                                  have p4427_1 := h4427c.2.1
                                  have p4427_2 := h4427c.2.2.1
                                  have p4427_3 := h4427c.2.2.2
                                  linarith only [h4265, hlam, p4427_0]
                                · have p4427_0 := h4427c.1
                                  have p4427_1 := h4427c.2.1
                                  have p4427_2 := h4427c.2.2.1
                                  have p4427_3 := h4427c.2.2.2
                                  linarith only [h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4427_1]
                                · have p4427_0 := h4427c.1
                                  have p4427_1 := h4427c.2.1
                                  have p4427_2 := h4427c.2.2.1
                                  have p4427_3 := h4427c.2.2.2
                                  linarith only [h4269, hlam, p4427_0]
                                · have p4427_0 := h4427c.1
                                  have p4427_1 := h4427c.2.1
                                  have p4427_2 := h4427c.2.2.1
                                  have p4427_3 := h4427c.2.2.2
                                  linarith only [h0, h3688, h4412, hc12, hc23, hlam, hphi, p4427_1]
                                · have p4427_0 := h4427c.1
                                  have p4427_1 := h4427c.2.1
                                  have p4427_2 := h4427c.2.2.1
                                  have p4427_3 := h4427c.2.2.2
                                  linarith only [h4265, h4412, hc12, hc23, hlam, hphi, p4427_1]
                                · have p4427_0 := h4427c.1
                                  have p4427_1 := h4427c.2.1
                                  have p4427_2 := h4427c.2.2.1
                                  have p4427_3 := h4427c.2.2.2
                                  linarith only [hlam, p4427_0]
                                · have p4427_0 := h4427c.1
                                  have p4427_1 := h4427c.2.1
                                  have p4427_2 := h4427c.2.2.1
                                  have p4427_3 := h4427c.2.2.2
                                  rcases p4427_3 (m.d 0 4) (by simp) with h4445 | h4445
                                  · linarith only [h3688, h4445, hlam]
                                  · linarith only [h4260, h4445, hlam]
                                · have p4427_0 := h4427c.1
                                  have p4427_1 := h4427c.2.1
                                  have p4427_2 := h4427c.2.2.1
                                  have p4427_3 := h4427c.2.2.2
                                  linarith only [h4265, h4269, h4412, hc12, hc23, hlam, hphi, p4427_1]
                                · have p4427_0 := h4427c.1
                                  have p4427_1 := h4427c.2.1
                                  have p4427_2 := h4427c.2.2.1
                                  have p4427_3 := h4427c.2.2.2
                                  linarith only [h4260, hlam, p4427_1]
                                · have p4427_0 := h4427c.1
                                  have p4427_1 := h4427c.2.1
                                  have p4427_2 := h4427c.2.2.1
                                  have p4427_3 := h4427c.2.2.2
                                  linarith only [h4267, hlam, p4427_0]
                                · have p4427_0 := h4427c.1
                                  have p4427_1 := h4427c.2.1
                                  have p4427_2 := h4427c.2.2.1
                                  have p4427_3 := h4427c.2.2.2
                                  linarith only [h4412, hlam, p4427_0]
                                · have p4427_0 := h4427c.1
                                  have p4427_1 := h4427c.2.1
                                  have p4427_2 := h4427c.2.2.1
                                  have p4427_3 := h4427c.2.2.2
                                  linarith only [hlam, p4427_0]
                                · have p4427_0 := h4427c.1
                                  have p4427_1 := h4427c.2.1
                                  have p4427_2 := h4427c.2.2.1
                                  have p4427_3 := h4427c.2.2.2
                                  linarith only [h4415, hlam, p4427_0]
                                · have p4427_0 := h4427c.1
                                  have p4427_1 := h4427c.2.1
                                  have p4427_2 := h4427c.2.2.1
                                  have p4427_3 := h4427c.2.2.2
                                  linarith only [h4262, hlam, p4427_0]
                                · have p4427_0 := h4427c.1
                                  have p4427_1 := h4427c.2.1
                                  have p4427_2 := h4427c.2.2.1
                                  have p4427_3 := h4427c.2.2.2
                                  linarith only [h4, h4262, h4265, h4268, h4415, hc04, hc12, hc23, hc34, hlam, hphi, ht0b, ht45, ht5b, p4417_1, p4427_1]
                                · have p4427_0 := h4427c.1
                                  have p4427_1 := h4427c.2.1
                                  have p4427_2 := h4427c.2.2.1
                                  have p4427_3 := h4427c.2.2.2
                                  linarith only [h4414, hlam, p4427_0]
                                · have p4427_0 := h4427c.1
                                  have p4427_1 := h4427c.2.1
                                  have p4427_2 := h4427c.2.2.1
                                  have p4427_3 := h4427c.2.2.2
                                  linarith only [h3688, h4262, h4412, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4427_1]
                                · have p4427_0 := h4427c.1
                                  have p4427_1 := h4427c.2.1
                                  have p4427_2 := h4427c.2.2.1
                                  have p4427_3 := h4427c.2.2.2
                                  linarith only [hlam, p4427_0]
                          · linarith only [h4263, h4422, hlam]
                      · linarith only [h1, h4419, hlam]
                    · have p4417_0 := h4417c.1
                      have p4417_1 := h4417c.2.1
                      have p4417_2 := h4417c.2.2.1
                      have p4417_3 := h4417c.2.2.2
                      linarith only [h4, hlam, p4417_1]
                    · have p4417_0 := h4417c.1
                      have p4417_1 := h4417c.2.1
                      have p4417_2 := h4417c.2.2.1
                      have p4417_3 := h4417c.2.2.2
                      rcases p4417_3 (m.d 0 3) (by simp) with h4462 | h4462
                      · rcases p4417_3 (m.d 1 3) (by simp) with h4463 | h4463
                        · linarith only [h1, h4463, hlam]
                        · linarith only [h4267, h4463, hlam]
                      · linarith only [h4462, hlam, p4417_0]
                    · have p4417_0 := h4417c.1
                      have p4417_1 := h4417c.2.1
                      have p4417_2 := h4417c.2.2.1
                      have p4417_3 := h4417c.2.2.2
                      rcases p4417_3 (m.d 0 3) (by simp) with h4467 | h4467
                      · rcases p4417_3 (m.d 1 3) (by simp) with h4468 | h4468
                        · linarith only [h1, h4468, hlam]
                        · linarith only [h4268, h4468, hlam]
                      · linarith only [h4467, hlam, p4417_0]
                    · have p4417_0 := h4417c.1
                      have p4417_1 := h4417c.2.1
                      have p4417_2 := h4417c.2.2.1
                      have p4417_3 := h4417c.2.2.2
                      linarith only [h1, hlam, p4417_0]
                    · have p4417_0 := h4417c.1
                      have p4417_1 := h4417c.2.1
                      have p4417_2 := h4417c.2.2.1
                      have p4417_3 := h4417c.2.2.2
                      linarith only [hlam, p4417_0]
                    · have p4417_0 := h4417c.1
                      have p4417_1 := h4417c.2.1
                      have p4417_2 := h4417c.2.2.1
                      have p4417_3 := h4417c.2.2.2
                      linarith only [h4263, hlam, p4417_1]
                    · have p4417_0 := h4417c.1
                      have p4417_1 := h4417c.2.1
                      have p4417_2 := h4417c.2.2.1
                      have p4417_3 := h4417c.2.2.2
                      rcases p4417_3 (m.d 0 3) (by simp) with h4475 | h4475
                      · rcases p4417_3 (m.d 1 3) (by simp) with h4476 | h4476
                        · rcases p4417_3 (m.d 2 3) (by simp) with h4477 | h4477
                          · rcases p4417_3 (m.d 3 4) (by simp) with h4478 | h4478
                            · linarith only [h4478, hlam, p4417_0]
                            · rcases p4417_3 (m.d 3 5) (by simp) with h4480 | h4480
                              · linarith only [h4268, h4480, hlam]
                              · linarith only [h4415, h4480, hlam]
                          · linarith only [h4412, h4477, hlam]
                        · linarith only [h4476, hlam, p4417_0]
                      · linarith only [h4260, h4475, hlam]
                    · have p4417_0 := h4417c.1
                      have p4417_1 := h4417c.2.1
                      have p4417_2 := h4417c.2.2.1
                      have p4417_3 := h4417c.2.2.2
                      rcases p4417_3 (m.d 0 3) (by simp) with h4486 | h4486
                      · rcases p4417_3 (m.d 1 3) (by simp) with h4487 | h4487
                        · rcases p4417_3 (m.d 2 3) (by simp) with h4488 | h4488
                          · rcases p4417_3 (m.d 3 4) (by simp) with h4489 | h4489
                            · linarith only [h4267, h4489, hlam]
                            · rcases p4417_3 (m.d 3 5) (by simp) with h4491 | h4491
                              · linarith only [h4491, hlam, p4417_0]
                              · rcases h4bigk with h4493c | h4493c | h4493c | h4493c | h4493c | h4493c | h4493c | h4493c | h4493c | h4493c | h4493c | h4493c | h4493c | h4493c | h4493c | h4493c | h4493c | h4493c | h4493c | h4493c | h4493c | h4493c | h4493c | h4493c | h4493c
                                · have p4493_0 := h4493c.1
                                  have p4493_1 := h4493c.2.1
                                  have p4493_2 := h4493c.2.2.1
                                  have p4493_3 := h4493c.2.2.2
                                  linarith only [hlam, p4493_0]
                                · have p4493_0 := h4493c.1
                                  have p4493_1 := h4493c.2.1
                                  have p4493_2 := h4493c.2.2.1
                                  have p4493_3 := h4493c.2.2.2
                                  linarith only [h3688, h4265, h4412, hc12, hc23, hlam, hphi, p4493_1]
                                · have p4493_0 := h4493c.1
                                  have p4493_1 := h4493c.2.1
                                  have p4493_2 := h4493c.2.2.1
                                  have p4493_3 := h4493c.2.2.2
                                  linarith only [h3688, hlam, p4493_0]
                                · have p4493_0 := h4493c.1
                                  have p4493_1 := h4493c.2.1
                                  have p4493_2 := h4493c.2.2.1
                                  have p4493_3 := h4493c.2.2.2
                                  rcases p4493_3 (m.d 0 4) (by simp) with h4497 | h4497
                                  · rcases p4493_3 (m.d 1 4) (by simp) with h4498 | h4498
                                    · linarith only [h2, h4498, hlam]
                                    · linarith only [h4267, h4498, hlam]
                                  · linarith only [h4260, h4497, hlam]
                                · have p4493_0 := h4493c.1
                                  have p4493_1 := h4493c.2.1
                                  have p4493_2 := h4493c.2.2.1
                                  have p4493_3 := h4493c.2.2.2
                                  linarith only [h3688, h4265, h4269, h4412, hc12, hc23, hlam, hphi, p4493_1]
                                · have p4493_0 := h4493c.1
                                  have p4493_1 := h4493c.2.1
                                  have p4493_2 := h4493c.2.2.1
                                  have p4493_3 := h4493c.2.2.2
                                  linarith only [h2, hlam, p4493_1]
                                · have p4493_0 := h4493c.1
                                  have p4493_1 := h4493c.2.1
                                  have p4493_2 := h4493c.2.2.1
                                  have p4493_3 := h4493c.2.2.2
                                  linarith only [hlam, p4493_0]
                                · have p4493_0 := h4493c.1
                                  have p4493_1 := h4493c.2.1
                                  have p4493_2 := h4493c.2.2.1
                                  have p4493_3 := h4493c.2.2.2
                                  linarith only [h4265, hlam, p4493_0]
                                · have p4493_0 := h4493c.1
                                  have p4493_1 := h4493c.2.1
                                  have p4493_2 := h4493c.2.2.1
                                  have p4493_3 := h4493c.2.2.2
                                  linarith only [h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4493_1]
                                · have p4493_0 := h4493c.1
                                  have p4493_1 := h4493c.2.1
                                  have p4493_2 := h4493c.2.2.1
                                  have p4493_3 := h4493c.2.2.2
                                  linarith only [h4269, hlam, p4493_0]
                                · have p4493_0 := h4493c.1
                                  have p4493_1 := h4493c.2.1
                                  have p4493_2 := h4493c.2.2.1
                                  have p4493_3 := h4493c.2.2.2
                                  linarith only [h0, h3688, h4412, hc12, hc23, hlam, hphi, p4493_1]
                                · have p4493_0 := h4493c.1
                                  have p4493_1 := h4493c.2.1
                                  have p4493_2 := h4493c.2.2.1
                                  have p4493_3 := h4493c.2.2.2
                                  linarith only [h4265, h4412, hc12, hc23, hlam, hphi, p4493_1]
                                · have p4493_0 := h4493c.1
                                  have p4493_1 := h4493c.2.1
                                  have p4493_2 := h4493c.2.2.1
                                  have p4493_3 := h4493c.2.2.2
                                  linarith only [hlam, p4493_0]
                                · have p4493_0 := h4493c.1
                                  have p4493_1 := h4493c.2.1
                                  have p4493_2 := h4493c.2.2.1
                                  have p4493_3 := h4493c.2.2.2
                                  rcases p4493_3 (m.d 0 4) (by simp) with h4511 | h4511
                                  · linarith only [h3688, h4511, hlam]
                                  · linarith only [h4260, h4511, hlam]
                                · have p4493_0 := h4493c.1
                                  have p4493_1 := h4493c.2.1
                                  have p4493_2 := h4493c.2.2.1
                                  have p4493_3 := h4493c.2.2.2
                                  linarith only [h4265, h4269, h4412, hc12, hc23, hlam, hphi, p4493_1]
                                · have p4493_0 := h4493c.1
                                  have p4493_1 := h4493c.2.1
                                  have p4493_2 := h4493c.2.2.1
                                  have p4493_3 := h4493c.2.2.2
                                  linarith only [h4260, hlam, p4493_1]
                                · have p4493_0 := h4493c.1
                                  have p4493_1 := h4493c.2.1
                                  have p4493_2 := h4493c.2.2.1
                                  have p4493_3 := h4493c.2.2.2
                                  linarith only [h4267, hlam, p4493_0]
                                · have p4493_0 := h4493c.1
                                  have p4493_1 := h4493c.2.1
                                  have p4493_2 := h4493c.2.2.1
                                  have p4493_3 := h4493c.2.2.2
                                  linarith only [h4412, hlam, p4493_0]
                                · have p4493_0 := h4493c.1
                                  have p4493_1 := h4493c.2.1
                                  have p4493_2 := h4493c.2.2.1
                                  have p4493_3 := h4493c.2.2.2
                                  linarith only [hlam, p4493_0]
                                · have p4493_0 := h4493c.1
                                  have p4493_1 := h4493c.2.1
                                  have p4493_2 := h4493c.2.2.1
                                  have p4493_3 := h4493c.2.2.2
                                  linarith only [h4415, hlam, p4493_0]
                                · have p4493_0 := h4493c.1
                                  have p4493_1 := h4493c.2.1
                                  have p4493_2 := h4493c.2.2.1
                                  have p4493_3 := h4493c.2.2.2
                                  linarith only [h4262, hlam, p4493_0]
                                · have p4493_0 := h4493c.1
                                  have p4493_1 := h4493c.2.1
                                  have p4493_2 := h4493c.2.2.1
                                  have p4493_3 := h4493c.2.2.2
                                  linarith only [h4262, h4265, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4493_1]
                                · have p4493_0 := h4493c.1
                                  have p4493_1 := h4493c.2.1
                                  have p4493_2 := h4493c.2.2.1
                                  have p4493_3 := h4493c.2.2.2
                                  linarith only [h4414, hlam, p4493_0]
                                · have p4493_0 := h4493c.1
                                  have p4493_1 := h4493c.2.1
                                  have p4493_2 := h4493c.2.2.1
                                  have p4493_3 := h4493c.2.2.2
                                  linarith only [h3688, h4262, h4412, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4493_1]
                                · have p4493_0 := h4493c.1
                                  have p4493_1 := h4493c.2.1
                                  have p4493_2 := h4493c.2.2.1
                                  have p4493_3 := h4493c.2.2.2
                                  linarith only [hlam, p4493_0]
                          · linarith only [h4413, h4488, hlam]
                        · linarith only [h4487, hlam, p4417_0]
                      · linarith only [h4261, h4486, hlam]
                    · have p4417_0 := h4417c.1
                      have p4417_1 := h4417c.2.1
                      have p4417_2 := h4417c.2.2.1
                      have p4417_3 := h4417c.2.2.2
                      linarith only [h4260, h4262, h4265, h4269, hc12, hc23, hlam, hphi, p4417_1]
                    · have p4417_0 := h4417c.1
                      have p4417_1 := h4417c.2.1
                      have p4417_2 := h4417c.2.2.1
                      have p4417_3 := h4417c.2.2.2
                      rcases p4417_3 (m.d 0 3) (by simp) with h4529 | h4529
                      · linarith only [h4, h4529, hlam]
                      · linarith only [h1, h4529, hlam]
                    · have p4417_0 := h4417c.1
                      have p4417_1 := h4417c.2.1
                      have p4417_2 := h4417c.2.2.1
                      have p4417_3 := h4417c.2.2.2
                      linarith only [hlam, p4417_0]
                    · have p4417_0 := h4417c.1
                      have p4417_1 := h4417c.2.1
                      have p4417_2 := h4417c.2.2.1
                      have p4417_3 := h4417c.2.2.2
                      rcases p4417_3 (m.d 0 3) (by simp) with h4533 | h4533
                      · linarith only [h4, h4533, hlam]
                      · linarith only [h4260, h4533, hlam]
                    · have p4417_0 := h4417c.1
                      have p4417_1 := h4417c.2.1
                      have p4417_2 := h4417c.2.2.1
                      have p4417_3 := h4417c.2.2.2
                      rcases p4417_3 (m.d 0 3) (by simp) with h4536 | h4536
                      · linarith only [h4, h4536, hlam]
                      · linarith only [h4261, h4536, hlam]
                    · have p4417_0 := h4417c.1
                      have p4417_1 := h4417c.2.1
                      have p4417_2 := h4417c.2.2.1
                      have p4417_3 := h4417c.2.2.2
                      linarith only [h4260, hlam, p4417_0]
                    · have p4417_0 := h4417c.1
                      have p4417_1 := h4417c.2.1
                      have p4417_2 := h4417c.2.2.1
                      have p4417_3 := h4417c.2.2.2
                      linarith only [h4267, hlam, p4417_0]
                    · have p4417_0 := h4417c.1
                      have p4417_1 := h4417c.2.1
                      have p4417_2 := h4417c.2.2.1
                      have p4417_3 := h4417c.2.2.2
                      linarith only [h4412, hlam, p4417_0]
                    · have p4417_0 := h4417c.1
                      have p4417_1 := h4417c.2.1
                      have p4417_2 := h4417c.2.2.1
                      have p4417_3 := h4417c.2.2.2
                      linarith only [hlam, p4417_0]
                    · have p4417_0 := h4417c.1
                      have p4417_1 := h4417c.2.1
                      have p4417_2 := h4417c.2.2.1
                      have p4417_3 := h4417c.2.2.2
                      linarith only [h4415, hlam, p4417_1]
                    · have p4417_0 := h4417c.1
                      have p4417_1 := h4417c.2.1
                      have p4417_2 := h4417c.2.2.1
                      have p4417_3 := h4417c.2.2.2
                      linarith only [h4261, hlam, p4417_0]
                    · have p4417_0 := h4417c.1
                      have p4417_1 := h4417c.2.1
                      have p4417_2 := h4417c.2.2.1
                      have p4417_3 := h4417c.2.2.2
                      linarith only [h4268, hlam, p4417_0]
                    · have p4417_0 := h4417c.1
                      have p4417_1 := h4417c.2.1
                      have p4417_2 := h4417c.2.2.1
                      have p4417_3 := h4417c.2.2.2
                      linarith only [h4413, hlam, p4417_0]
                    · have p4417_0 := h4417c.1
                      have p4417_1 := h4417c.2.1
                      have p4417_2 := h4417c.2.2.1
                      have p4417_3 := h4417c.2.2.2
                      linarith only [h1, h4268, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4417_1]
                    · have p4417_0 := h4417c.1
                      have p4417_1 := h4417c.2.1
                      have p4417_2 := h4417c.2.2.1
                      have p4417_3 := h4417c.2.2.2
                      linarith only [hlam, p4417_0]
                · linarith only [h0, h3688, h4, h4260, h4262, h4414, hc12, hc23, hlam, hphi]
              · linarith only [h4, h4261, h4413, hlam]
            · linarith only [h4, h4260, h4262, h4265, h4269, h4412, hc12, hc34, hlam, hphi, ht23]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4552 | h4552
          · linarith only [h4267, h4268, h4552, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4554 | h4554
            · rcases m.htr 2 3 5 (by decide) (by decide) with h4555 | h4555
              · rcases m.htr 2 4 5 (by decide) (by decide) with h4556 | h4556
                · rcases m.htr 3 4 5 (by decide) (by decide) with h4557 | h4557
                  · linarith only [h4261, h4265, h4267, h4268, h4552, h4557, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases h3bigk with h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c
                    · have p4559_0 := h4559c.1
                      have p4559_1 := h4559c.2.1
                      have p4559_2 := h4559c.2.2.1
                      have p4559_3 := h4559c.2.2.2
                      linarith only [hlam, p4559_0]
                    · have p4559_0 := h4559c.1
                      have p4559_1 := h4559c.2.1
                      have p4559_2 := h4559c.2.2.1
                      have p4559_3 := h4559c.2.2.2
                      rcases p4559_3 (m.d 0 3) (by simp) with h4561 | h4561
                      · rcases p4559_3 (m.d 1 3) (by simp) with h4562 | h4562
                        · linarith only [h1, h4562, hlam]
                        · rcases p4559_3 (m.d 2 3) (by simp) with h4564 | h4564
                          · rcases p4559_3 (m.d 3 4) (by simp) with h4565 | h4565
                            · linarith only [h4260, h4565, hlam]
                            · rcases p4559_3 (m.d 3 5) (by simp) with h4567 | h4567
                              · linarith only [h4261, h4567, hlam]
                              · linarith only [h4268, h4567, hlam]
                          · linarith only [h4263, h4564, hlam]
                      · linarith only [h1, h4561, hlam]
                    · have p4559_0 := h4559c.1
                      have p4559_1 := h4559c.2.1
                      have p4559_2 := h4559c.2.2.1
                      have p4559_3 := h4559c.2.2.2
                      linarith only [h4, hlam, p4559_1]
                    · have p4559_0 := h4559c.1
                      have p4559_1 := h4559c.2.1
                      have p4559_2 := h4559c.2.2.1
                      have p4559_3 := h4559c.2.2.2
                      linarith only [h4260, h4262, h4267, h4268, h4557, hlam, p4559_2]
                    · have p4559_0 := h4559c.1
                      have p4559_1 := h4559c.2.1
                      have p4559_2 := h4559c.2.2.1
                      have p4559_3 := h4559c.2.2.2
                      linarith only [h4, h4267, h4268, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4559_1]
                    · have p4559_0 := h4559c.1
                      have p4559_1 := h4559c.2.1
                      have p4559_2 := h4559c.2.2.1
                      have p4559_3 := h4559c.2.2.2
                      linarith only [h1, hlam, p4559_0]
                    · have p4559_0 := h4559c.1
                      have p4559_1 := h4559c.2.1
                      have p4559_2 := h4559c.2.2.1
                      have p4559_3 := h4559c.2.2.2
                      linarith only [hlam, p4559_0]
                    · have p4559_0 := h4559c.1
                      have p4559_1 := h4559c.2.1
                      have p4559_2 := h4559c.2.2.1
                      have p4559_3 := h4559c.2.2.2
                      linarith only [h4263, hlam, p4559_1]
                    · have p4559_0 := h4559c.1
                      have p4559_1 := h4559c.2.1
                      have p4559_2 := h4559c.2.2.1
                      have p4559_3 := h4559c.2.2.2
                      linarith only [h4262, h4268, h4557, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p4559_1]
                    · have p4559_0 := h4559c.1
                      have p4559_1 := h4559c.2.1
                      have p4559_2 := h4559c.2.2.1
                      have p4559_3 := h4559c.2.2.2
                      linarith only [h4268, hlam, p4559_0]
                    · have p4559_0 := h4559c.1
                      have p4559_1 := h4559c.2.1
                      have p4559_2 := h4559c.2.2.1
                      have p4559_3 := h4559c.2.2.2
                      linarith only [h4260, h4262, h4268, h4557, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4559_1]
                    · have p4559_0 := h4559c.1
                      have p4559_1 := h4559c.2.1
                      have p4559_2 := h4559c.2.2.1
                      have p4559_3 := h4559c.2.2.2
                      rcases p4559_3 (m.d 0 3) (by simp) with h4581 | h4581
                      · linarith only [h4, h4581, hlam]
                      · linarith only [h1, h4581, hlam]
                    · have p4559_0 := h4559c.1
                      have p4559_1 := h4559c.2.1
                      have p4559_2 := h4559c.2.2.1
                      have p4559_3 := h4559c.2.2.2
                      linarith only [hlam, p4559_0]
                    · have p4559_0 := h4559c.1
                      have p4559_1 := h4559c.2.1
                      have p4559_2 := h4559c.2.2.1
                      have p4559_3 := h4559c.2.2.2
                      linarith only [h4, h4260, h4262, h4267, h4268, h4557, hlam, p4559_2]
                    · have p4559_0 := h4559c.1
                      have p4559_1 := h4559c.2.1
                      have p4559_2 := h4559c.2.2.1
                      have p4559_3 := h4559c.2.2.2
                      linarith only [h4267, h4268, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4559_1]
                    · have p4559_0 := h4559c.1
                      have p4559_1 := h4559c.2.1
                      have p4559_2 := h4559c.2.2.1
                      have p4559_3 := h4559c.2.2.2
                      linarith only [h4260, hlam, p4559_0]
                    · have p4559_0 := h4559c.1
                      have p4559_1 := h4559c.2.1
                      have p4559_2 := h4559c.2.2.1
                      have p4559_3 := h4559c.2.2.2
                      linarith only [h4267, hlam, p4559_0]
                    · have p4559_0 := h4559c.1
                      have p4559_1 := h4559c.2.1
                      have p4559_2 := h4559c.2.2.1
                      have p4559_3 := h4559c.2.2.2
                      linarith only [h4554, hlam, p4559_0]
                    · have p4559_0 := h4559c.1
                      have p4559_1 := h4559c.2.1
                      have p4559_2 := h4559c.2.2.1
                      have p4559_3 := h4559c.2.2.2
                      linarith only [hlam, p4559_0]
                    · have p4559_0 := h4559c.1
                      have p4559_1 := h4559c.2.1
                      have p4559_2 := h4559c.2.2.1
                      have p4559_3 := h4559c.2.2.2
                      linarith only [h4557, hlam, p4559_1]
                    · have p4559_0 := h4559c.1
                      have p4559_1 := h4559c.2.1
                      have p4559_2 := h4559c.2.2.1
                      have p4559_3 := h4559c.2.2.2
                      linarith only [h4261, hlam, p4559_0]
                    · have p4559_0 := h4559c.1
                      have p4559_1 := h4559c.2.1
                      have p4559_2 := h4559c.2.2.1
                      have p4559_3 := h4559c.2.2.2
                      linarith only [h4260, h4262, h4267, h4557, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p4559_1]
                    · have p4559_0 := h4559c.1
                      have p4559_1 := h4559c.2.1
                      have p4559_2 := h4559c.2.2.1
                      have p4559_3 := h4559c.2.2.2
                      linarith only [h4555, hlam, p4559_0]
                    · have p4559_0 := h4559c.1
                      have p4559_1 := h4559c.2.1
                      have p4559_2 := h4559c.2.2.1
                      have p4559_3 := h4559c.2.2.2
                      rcases p4559_3 (m.d 0 3) (by simp) with h4595 | h4595
                      · rcases p4559_3 (m.d 1 3) (by simp) with h4596 | h4596
                        · linarith only [h4268, h4596, hlam]
                        · linarith only [h4267, h4596, hlam]
                      · linarith only [h4260, h4595, hlam]
                    · have p4559_0 := h4559c.1
                      have p4559_1 := h4559c.2.1
                      have p4559_2 := h4559c.2.2.1
                      have p4559_3 := h4559c.2.2.2
                      linarith only [hlam, p4559_0]
                · linarith only [h3688, h4, h4260, h4262, h4556, hc02, hc23, hlam, hphi]
              · linarith only [h4, h4261, h4555, hlam]
            · linarith only [h1, h4, h4260, h4262, h4267, h4554, hc01, hc45, hlam, hphi, ht0b, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h4604 | h4604
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4605 | h4605
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4606 | h4606
            · rcases m.htr 2 3 5 (by decide) (by decide) with h4607 | h4607
              · rcases m.htr 2 4 5 (by decide) (by decide) with h4608 | h4608
                · rcases m.htr 3 4 5 (by decide) (by decide) with h4609 | h4609
                  · rcases h3bigk with h4610c | h4610c | h4610c | h4610c | h4610c | h4610c | h4610c | h4610c | h4610c | h4610c | h4610c | h4610c | h4610c | h4610c | h4610c | h4610c | h4610c | h4610c | h4610c | h4610c | h4610c | h4610c | h4610c | h4610c | h4610c
                    · have p4610_0 := h4610c.1
                      have p4610_1 := h4610c.2.1
                      have p4610_2 := h4610c.2.2.1
                      have p4610_3 := h4610c.2.2.2
                      linarith only [hlam, p4610_0]
                    · have p4610_0 := h4610c.1
                      have p4610_1 := h4610c.2.1
                      have p4610_2 := h4610c.2.2.1
                      have p4610_3 := h4610c.2.2.2
                      rcases p4610_3 (m.d 0 3) (by simp) with h4612 | h4612
                      · rcases p4610_3 (m.d 1 3) (by simp) with h4613 | h4613
                        · linarith only [h1, h4613, hlam]
                        · rcases p4610_3 (m.d 2 3) (by simp) with h4615 | h4615
                          · rcases p4610_3 (m.d 3 4) (by simp) with h4616 | h4616
                            · linarith only [h4260, h4616, hlam]
                            · linarith only [h4267, h4616, hlam]
                          · linarith only [h4263, h4615, hlam]
                      · linarith only [h1, h4612, hlam]
                    · have p4610_0 := h4610c.1
                      have p4610_1 := h4610c.2.1
                      have p4610_2 := h4610c.2.2.1
                      have p4610_3 := h4610c.2.2.2
                      linarith only [h4, hlam, p4610_1]
                    · have p4610_0 := h4610c.1
                      have p4610_1 := h4610c.2.1
                      have p4610_2 := h4610c.2.2.1
                      have p4610_3 := h4610c.2.2.2
                      linarith only [h4267, h4604, h4609, hc03, hc45, hlam, hphi, ht0b, ht5b, p4610_1]
                    · have p4610_0 := h4610c.1
                      have p4610_1 := h4610c.2.1
                      have p4610_2 := h4610c.2.2.1
                      have p4610_3 := h4610c.2.2.2
                      linarith only [h4260, h4267, h4604, hlam, p4610_2]
                    · have p4610_0 := h4610c.1
                      have p4610_1 := h4610c.2.1
                      have p4610_2 := h4610c.2.2.1
                      have p4610_3 := h4610c.2.2.2
                      linarith only [h1, hlam, p4610_0]
                    · have p4610_0 := h4610c.1
                      have p4610_1 := h4610c.2.1
                      have p4610_2 := h4610c.2.2.1
                      have p4610_3 := h4610c.2.2.2
                      linarith only [hlam, p4610_0]
                    · have p4610_0 := h4610c.1
                      have p4610_1 := h4610c.2.1
                      have p4610_2 := h4610c.2.2.1
                      have p4610_3 := h4610c.2.2.2
                      linarith only [h4263, hlam, p4610_1]
                    · have p4610_0 := h4610c.1
                      have p4610_1 := h4610c.2.1
                      have p4610_2 := h4610c.2.2.1
                      have p4610_3 := h4610c.2.2.2
                      linarith only [h4267, hlam, p4610_0]
                    · have p4610_0 := h4610c.1
                      have p4610_1 := h4610c.2.1
                      have p4610_2 := h4610c.2.2.1
                      have p4610_3 := h4610c.2.2.2
                      linarith only [h4260, h4267, h4609, hc03, hc45, hlam, hphi, ht0b, ht5b, p4610_1]
                    · have p4610_0 := h4610c.1
                      have p4610_1 := h4610c.2.1
                      have p4610_2 := h4610c.2.2.1
                      have p4610_3 := h4610c.2.2.2
                      linarith only [h4260, h4267, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4610_1]
                    · have p4610_0 := h4610c.1
                      have p4610_1 := h4610c.2.1
                      have p4610_2 := h4610c.2.2.1
                      have p4610_3 := h4610c.2.2.2
                      rcases p4610_3 (m.d 0 3) (by simp) with h4630 | h4630
                      · linarith only [h4, h4630, hlam]
                      · linarith only [h1, h4630, hlam]
                    · have p4610_0 := h4610c.1
                      have p4610_1 := h4610c.2.1
                      have p4610_2 := h4610c.2.2.1
                      have p4610_3 := h4610c.2.2.2
                      linarith only [hlam, p4610_0]
                    · have p4610_0 := h4610c.1
                      have p4610_1 := h4610c.2.1
                      have p4610_2 := h4610c.2.2.1
                      have p4610_3 := h4610c.2.2.2
                      linarith only [h4267, h4604, h4609, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4610_1]
                    · have p4610_0 := h4610c.1
                      have p4610_1 := h4610c.2.1
                      have p4610_2 := h4610c.2.2.1
                      have p4610_3 := h4610c.2.2.2
                      linarith only [h4, h4260, h4267, h4604, hlam, p4610_2]
                    · have p4610_0 := h4610c.1
                      have p4610_1 := h4610c.2.1
                      have p4610_2 := h4610c.2.2.1
                      have p4610_3 := h4610c.2.2.2
                      linarith only [h4260, hlam, p4610_0]
                    · have p4610_0 := h4610c.1
                      have p4610_1 := h4610c.2.1
                      have p4610_2 := h4610c.2.2.1
                      have p4610_3 := h4610c.2.2.2
                      linarith only [h4260, h4604, h4609, hc03, hc45, hlam, hphi, ht0b, ht5b, p4610_1]
                    · have p4610_0 := h4610c.1
                      have p4610_1 := h4610c.2.1
                      have p4610_2 := h4610c.2.2.1
                      have p4610_3 := h4610c.2.2.2
                      linarith only [h4606, hlam, p4610_0]
                    · have p4610_0 := h4610c.1
                      have p4610_1 := h4610c.2.1
                      have p4610_2 := h4610c.2.2.1
                      have p4610_3 := h4610c.2.2.2
                      linarith only [hlam, p4610_0]
                    · have p4610_0 := h4610c.1
                      have p4610_1 := h4610c.2.1
                      have p4610_2 := h4610c.2.2.1
                      have p4610_3 := h4610c.2.2.2
                      rcases p4610_3 (m.d 0 3) (by simp) with h4640 | h4640
                      · rcases p4610_3 (m.d 1 3) (by simp) with h4641 | h4641
                        · linarith only [h4267, h4641, hlam]
                        · linarith only [h4604, h4641, hlam]
                      · linarith only [h4261, h4640, hlam]
                    · have p4610_0 := h4610c.1
                      have p4610_1 := h4610c.2.1
                      have p4610_2 := h4610c.2.2.1
                      have p4610_3 := h4610c.2.2.2
                      linarith only [h4261, hlam, p4610_0]
                    · have p4610_0 := h4610c.1
                      have p4610_1 := h4610c.2.1
                      have p4610_2 := h4610c.2.2.1
                      have p4610_3 := h4610c.2.2.2
                      linarith only [h4604, hlam, p4610_0]
                    · have p4610_0 := h4610c.1
                      have p4610_1 := h4610c.2.1
                      have p4610_2 := h4610c.2.2.1
                      have p4610_3 := h4610c.2.2.2
                      linarith only [h4607, hlam, p4610_0]
                    · have p4610_0 := h4610c.1
                      have p4610_1 := h4610c.2.1
                      have p4610_2 := h4610c.2.2.1
                      have p4610_3 := h4610c.2.2.2
                      linarith only [h4609, hlam, p4610_0]
                    · have p4610_0 := h4610c.1
                      have p4610_1 := h4610c.2.1
                      have p4610_2 := h4610c.2.2.1
                      have p4610_3 := h4610c.2.2.2
                      linarith only [hlam, p4610_0]
                  · linarith only [h4262, h4267, h4604, h4609, hc04, hc35, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h3688, h4260, h4267, h4604, h4605, h4608, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h4, h4260, h4267, h4604, h4607, hlam]
            · linarith only [h4, h4260, h4606, hlam]
          · linarith only [h4267, h4604, h4605, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4655 | h4655
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4656 | h4656
            · rcases m.htr 2 3 5 (by decide) (by decide) with h4657 | h4657
              · rcases m.htr 2 4 5 (by decide) (by decide) with h4658 | h4658
                · rcases m.htr 3 4 5 (by decide) (by decide) with h4659 | h4659
                  · rcases h3bigk with h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c | h4660c
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [hlam, p4660_0]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      rcases p4660_3 (m.d 0 3) (by simp) with h4662 | h4662
                      · rcases p4660_3 (m.d 1 3) (by simp) with h4663 | h4663
                        · linarith only [h1, h4663, hlam]
                        · rcases p4660_3 (m.d 2 3) (by simp) with h4665 | h4665
                          · rcases p4660_3 (m.d 3 4) (by simp) with h4666 | h4666
                            · linarith only [h4260, h4666, hlam]
                            · linarith only [h4267, h4666, hlam]
                          · linarith only [h4263, h4665, hlam]
                      · linarith only [h1, h4662, hlam]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [h4, hlam, p4660_1]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [h4, h4263, h4267, hc12, hc23, hlam, hphi, p4660_1]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [h4, h4263, h4604, hc12, hc23, hlam, hphi, p4660_1]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [h1, hlam, p4660_0]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [hlam, p4660_0]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [h4263, hlam, p4660_1]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [h4267, hlam, p4660_0]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [h4604, hlam, p4660_0]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [h4260, h4263, h4267, hc12, hc23, hlam, hphi, p4660_1]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      rcases p4660_3 (m.d 0 3) (by simp) with h4680 | h4680
                      · linarith only [h4, h4680, hlam]
                      · linarith only [h1, h4680, hlam]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [hlam, p4660_0]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [h4263, h4604, h4659, hc12, hc23, hlam, hphi, p4660_1]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [h4263, h4604, hc12, hc23, hlam, hphi, p4660_1]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [h4260, hlam, p4660_0]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [h4, h4260, h4263, hc12, hc23, hlam, hphi, p4660_1]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [h4656, hlam, p4660_0]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [hlam, p4660_0]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [h4, h4260, h4263, h4604, hc12, hc23, hlam, hphi, p4660_1]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [h4261, hlam, p4660_0]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [h4, h4261, h4263, hc12, hc23, hlam, hphi, p4660_1]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [h4657, hlam, p4660_0]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [h4659, hlam, p4660_0]
                    · have p4660_0 := h4660c.1
                      have p4660_1 := h4660c.2.1
                      have p4660_2 := h4660c.2.2.1
                      have p4660_3 := h4660c.2.2.2
                      linarith only [hlam, p4660_0]
                  · linarith only [h2, h4263, h4267, h4655, h4659, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h0, h3688, h4, h4260, h4267, h4655, h4658, hc12, hc23, hlam, hphi]
              · linarith only [h4, h4261, h4657, hlam]
            · linarith only [h4, h4260, h4656, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4700 | h4700
            · rcases m.htr 2 3 5 (by decide) (by decide) with h4701 | h4701
              · rcases m.htr 2 4 5 (by decide) (by decide) with h4702 | h4702
                · rcases m.htr 3 4 5 (by decide) (by decide) with h4703 | h4703
                  · linarith only [h4, h4260, h4265, h4655, h4703, hc12, hc23, hlam, hphi]
                  · linarith only [h4, h4260, h4262, h4263, h4267, h4703, hc12, hc23, hlam, hphi]
                · linarith only [h3688, h4262, h4702, hlam]
              · linarith only [h4, h4261, h4701, hlam]
            · linarith only [h4, h4260, h4700, hlam]

end R2N4
