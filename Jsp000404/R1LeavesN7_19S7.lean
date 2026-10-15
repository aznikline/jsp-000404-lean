import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_19S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8830000 in
set_option maxHeartbeats 8830000 in
theorem r1l7_21_14_H_I_L_I_s2 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_21_14_H_I_L_I_s3 m hb1 hb4 h0 h1 h2 h3
  · rcases m.htr 0 2 4 (by decide) (by decide) with h4286 | h4286
    · rcases m.htr 0 3 4 (by decide) (by decide) with h4287 | h4287
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4288 | h4288
        · linarith only [h0, h3, h4286, h4288, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4290 | h4290
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4291 | h4291
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4292 | h4292
              · linarith only [h0, h3, h4292, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4294 | h4294
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4295 | h4295
                  · linarith only [h0, h3, h4290, h4295, hlam]
                  · linarith only [h0, h3, h4290, h4295, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4298 | h4298
                  · linarith only [h1, h3, h4287, h4292, h4294, h4298, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h1, h3, h4287, h4290, h4294, h4298, hc23, hc35, hlam, hphi]
            · linarith only [h0, h3, h4286, h4290, h4291, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4302 | h4302
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4303 | h4303
              · linarith only [h0, h3, h4303, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4305 | h4305
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4306 | h4306
                  · linarith only [h1, h3, h4306, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4308 | h4308
                    · linarith only [h2, h3, h4288, h4308, hlam]
                    · linarith only [h1, h3, h4290, h4302, h4308, hc24, hc45, hlam, hphi]
                · linarith only [h1, h3, h4287, h4290, h4302, h4305, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4312 | h4312
              · linarith only [h0, h3, h4286, h4302, h4312, hc15, hc25, hlam, hphi, ht01, ht0b, ht5b]
              · linarith only [h0, h3, h4286, h4302, h4312, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4315 | h4315
        · linarith only [h2, h3, h4315, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4317 | h4317
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4318 | h4318
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4319 | h4319
              · linarith only [h0, h3, h4319, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4321 | h4321
                · linarith only [h1, h3, h4287, h4319, h4321, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4323 | h4323
                  · linarith only [h1, h3, h4323, hlam]
                  · linarith only [h0, h3, h4317, h4323, hc23, hc35, hlam, hphi]
            · linarith only [h0, h3, h4286, h4317, h4318, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4327 | h4327
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4328 | h4328
              · linarith only [h0, h3, h4328, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4330 | h4330
                · linarith only [h1, h4287, h4330, hlam]
                · linarith only [h4317, h4327, h4330, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4333 | h4333
              · linarith only [h0, h3, h4286, h4327, h4333, hc15, hc25, hlam, hphi, ht01, ht0b, ht5b]
              · linarith only [h0, h3, h4286, h4327, h4333, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h4336 | h4336
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4337 | h4337
        · linarith only [h1, h3, h4336, h4337, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4339 | h4339
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4340 | h4340
            · linarith only [h0, h3, h4286, h4340, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4342 | h4342
              · linarith only [h2, h3, h4340, h4342, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4344 | h4344
                · linarith only [h4339, h4340, h4344, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4346 | h4346
                  · linarith only [h1, h3, h4336, h4342, h4344, h4346, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h1, h3, h4336, h4344, h4346, hc13, hc35, hlam, hphi]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4349 | h4349
            · linarith only [h0, h4286, h4349, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4351 | h4351
              · linarith only [h0, h3, h4351, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4353 | h4353
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4354 | h4354
                  · linarith only [h1, h3, h4354, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4356 | h4356
                    · linarith only [h1, h3, h4337, h4353, h4354, h4356, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h1, h3, h4353, h4356, hc34, hc45, hlam, hphi]
                · linarith only [h1, h3, h4336, h4339, h4351, h4353, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4360 | h4360
        · linarith only [h2, h3, h4360, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4362 | h4362
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4363 | h4363
            · linarith only [h0, h4286, h4363, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4365 | h4365
              · linarith only [h0, h3, h4365, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4367 | h4367
                · linarith only [h1, h3, h4336, h4367, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4369 | h4369
                  · linarith only [h1, h3, h4369, hlam]
                  · linarith only [h0, h3, h4362, h4369, hc23, hc35, hlam, hphi]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4372 | h4372
            · linarith only [h1, h3, h4286, h4362, h4372, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4374 | h4374
              · linarith only [h0, h3, h4374, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4376 | h4376
                · linarith only [h1, h3, h4336, h4376, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4378 | h4378
                  · linarith only [h2, h3, h4376, h4378, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4380 | h4380
                    · linarith only [h2, h3, h4360, h4380, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4382 | h4382
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4383 | h4383
                        · linarith only [h2, h3, h4362, h4376, h4380, h4383, hc12, hc24, hlam, hphi]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4385 | h4385
                          · linarith only [h0, h4286, h4383, h4385, hc12, hc34, hlam, hphi, ht23]
                          · rcases h1bigk with h4387c | h4387c | h4387c | h4387c | h4387c | h4387c | h4387c | h4387c | h4387c | h4387c | h4387c | h4387c | h4387c | h4387c | h4387c | h4387c | h4387c | h4387c | h4387c | h4387c | h4387c | h4387c | h4387c | h4387c | h4387c
                            · have p4387_0 := h4387c.1
                              have p4387_1 := h4387c.2.1
                              have p4387_2 := h4387c.2.2.1
                              have p4387_3 := h4387c.2.2.2
                              linarith only [hlam, p4387_0]
                            · have p4387_0 := h4387c.1
                              have p4387_1 := h4387c.2.1
                              have p4387_2 := h4387c.2.2.1
                              have p4387_3 := h4387c.2.2.2
                              linarith only [h3, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4387_1]
                            · have p4387_0 := h4387c.1
                              have p4387_1 := h4387c.2.1
                              have p4387_2 := h4387c.2.2.1
                              have p4387_3 := h4387c.2.2.2
                              linarith only [h3, h4362, h4374, hc12, hc25, hlam, hphi, p4387_1]
                            · have p4387_0 := h4387c.1
                              have p4387_1 := h4387c.2.1
                              have p4387_2 := h4387c.2.2.1
                              have p4387_3 := h4387c.2.2.2
                              linarith only [h3, h4362, h4374, h4376, hc12, hc25, hlam, hphi, p4387_1]
                            · have p4387_0 := h4387c.1
                              have p4387_1 := h4387c.2.1
                              have p4387_2 := h4387c.2.2.1
                              have p4387_3 := h4387c.2.2.2
                              linarith only [h3, hlam, p4387_0]
                            · have p4387_0 := h4387c.1
                              have p4387_1 := h4387c.2.1
                              have p4387_2 := h4387c.2.2.1
                              have p4387_3 := h4387c.2.2.2
                              linarith only [h0, hlam, p4387_0]
                            · have p4387_0 := h4387c.1
                              have p4387_1 := h4387c.2.1
                              have p4387_2 := h4387c.2.2.1
                              have p4387_3 := h4387c.2.2.2
                              linarith only [hlam, p4387_0]
                            · have p4387_0 := h4387c.1
                              have p4387_1 := h4387c.2.1
                              have p4387_2 := h4387c.2.2.1
                              have p4387_3 := h4387c.2.2.2
                              linarith only [h4362, hlam, p4387_1]
                            · have p4387_0 := h4387c.1
                              have p4387_1 := h4387c.2.1
                              have p4387_2 := h4387c.2.2.1
                              have p4387_3 := h4387c.2.2.2
                              linarith only [h4372, hlam, p4387_1]
                            · have p4387_0 := h4387c.1
                              have p4387_1 := h4387c.2.1
                              have p4387_2 := h4387c.2.2.1
                              have p4387_3 := h4387c.2.2.2
                              linarith only [h4374, hlam, p4387_1]
                            · have p4387_0 := h4387c.1
                              have p4387_1 := h4387c.2.1
                              have p4387_2 := h4387c.2.2.1
                              have p4387_3 := h4387c.2.2.2
                              linarith only [h1, hlam, p4387_0]
                            · have p4387_0 := h4387c.1
                              have p4387_1 := h4387c.2.1
                              have p4387_2 := h4387c.2.2.1
                              have p4387_3 := h4387c.2.2.2
                              linarith only [h1, h3, h4374, hc12, hc25, hlam, hphi, p4387_1]
                            · have p4387_0 := h4387c.1
                              have p4387_1 := h4387c.2.1
                              have p4387_2 := h4387c.2.2.1
                              have p4387_3 := h4387c.2.2.2
                              linarith only [hlam, p4387_0]
                            · have p4387_0 := h4387c.1
                              have p4387_1 := h4387c.2.1
                              have p4387_2 := h4387c.2.2.1
                              have p4387_3 := h4387c.2.2.2
                              linarith only [h4376, hlam, p4387_0]
                            · have p4387_0 := h4387c.1
                              have p4387_1 := h4387c.2.1
                              have p4387_2 := h4387c.2.2.1
                              have p4387_3 := h4387c.2.2.2
                              linarith only [h4378, hlam, p4387_1]
                            · have p4387_0 := h4387c.1
                              have p4387_1 := h4387c.2.1
                              have p4387_2 := h4387c.2.2.1
                              have p4387_3 := h4387c.2.2.2
                              linarith only [h2, hlam, p4387_0]
                            · have p4387_0 := h4387c.1
                              have p4387_1 := h4387c.2.1
                              have p4387_2 := h4387c.2.2.1
                              have p4387_3 := h4387c.2.2.2
                              linarith only [h2, h3, h4374, hc12, hc25, hlam, hphi, p4387_1]
                            · have p4387_0 := h4387c.1
                              have p4387_1 := h4387c.2.1
                              have p4387_2 := h4387c.2.2.1
                              have p4387_3 := h4387c.2.2.2
                              linarith only [h2, h3, h4374, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4387_1]
                            · have p4387_0 := h4387c.1
                              have p4387_1 := h4387c.2.1
                              have p4387_2 := h4387c.2.2.1
                              have p4387_3 := h4387c.2.2.2
                              linarith only [hlam, p4387_0]
                            · have p4387_0 := h4387c.1
                              have p4387_1 := h4387c.2.1
                              have p4387_2 := h4387c.2.2.1
                              have p4387_3 := h4387c.2.2.2
                              linarith only [h4380, hlam, p4387_1]
                            · have p4387_0 := h4387c.1
                              have p4387_1 := h4387c.2.1
                              have p4387_2 := h4387c.2.2.1
                              have p4387_3 := h4387c.2.2.2
                              linarith only [h4374, hc01, hc25, hlam, hphi, ht12, p4387_1]
                            · have p4387_0 := h4387c.1
                              have p4387_1 := h4387c.2.1
                              have p4387_2 := h4387c.2.2.1
                              have p4387_3 := h4387c.2.2.2
                              linarith only [h4374, hc12, hc25, hlam, hphi, p4387_1]
                            · have p4387_0 := h4387c.1
                              have p4387_1 := h4387c.2.1
                              have p4387_2 := h4387c.2.2.1
                              have p4387_3 := h4387c.2.2.2
                              linarith only [h4362, h4378, h4385, hc12, hc45, hlam, hphi, ht23, ht34, p4387_1]
                            · have p4387_0 := h4387c.1
                              have p4387_1 := h4387c.2.1
                              have p4387_2 := h4387c.2.2.1
                              have p4387_3 := h4387c.2.2.2
                              linarith only [h4362, h4376, h4378, h4385, hc12, hc45, hlam, hphi, ht23, ht34, p4387_1]
                            · have p4387_0 := h4387c.1
                              have p4387_1 := h4387c.2.1
                              have p4387_2 := h4387c.2.2.1
                              have p4387_3 := h4387c.2.2.2
                              linarith only [hlam, p4387_0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4413 | h4413
                        · linarith only [h2, h3, h4362, h4376, h4380, h4413, hc12, hc24, hlam, hphi]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4415 | h4415
                          · linarith only [h0, h4286, h4413, h4415, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h4362, h4382, h4415, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 9230000 in
set_option maxHeartbeats 9230000 in
theorem r1l7_21_14_H_I_L_I_s1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_21_14_H_I_L_I_s2 m hb1 hb4 h0 h1 h2
  · rcases m.htr 0 1 5 (by decide) (by decide) with h4418 | h4418
    · rcases m.htr 0 2 4 (by decide) (by decide) with h4419 | h4419
      · linarith only [h0, h2, h4419, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h4421 | h4421
        · linarith only [h1, h2, h4421, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4423 | h4423
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4424 | h4424
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4425 | h4425
              · linarith only [h0, h2, h4419, h4425, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4427 | h4427
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4428 | h4428
                  · linarith only [h0, h2, h4421, h4424, h4425, h4428, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h0, h2, h4424, h4428, hc23, hc34, hlam, hphi]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4431 | h4431
                  · linarith only [h1, h4421, h4431, hlam]
                  · linarith only [h2, h4418, h4424, h4427, h4431, hc23, hc34, hlam, hphi]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4434 | h4434
              · linarith only [h0, h4419, h4434, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4436 | h4436
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4437 | h4437
                  · linarith only [h1, h2, h4421, h4437, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4439 | h4439
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4440 | h4440
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4441 | h4441
                        · linarith only [h0, h2, h4437, h4441, hc12, hc23, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4443 | h4443
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4444 | h4444
                            · rcases h1bigk with h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c
                              · have p4445_0 := h4445c.1
                                have p4445_1 := h4445c.2.1
                                have p4445_2 := h4445c.2.2.1
                                have p4445_3 := h4445c.2.2.2
                                linarith only [hlam, p4445_0]
                              · have p4445_0 := h4445c.1
                                have p4445_1 := h4445c.2.1
                                have p4445_2 := h4445c.2.2.1
                                have p4445_3 := h4445c.2.2.2
                                linarith only [h4436, h4443, hc01, hc45, hlam, hphi, ht0b, ht5b, p4445_1]
                              · have p4445_0 := h4445c.1
                                have p4445_1 := h4445c.2.1
                                have p4445_2 := h4445c.2.2.1
                                have p4445_3 := h4445c.2.2.2
                                linarith only [h2, h4424, h4434, h4436, h4441, h4443, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4445_1]
                              · have p4445_0 := h4445c.1
                                have p4445_1 := h4445c.2.1
                                have p4445_2 := h4445c.2.2.1
                                have p4445_3 := h4445c.2.2.2
                                linarith only [h2, hlam, p4445_0]
                              · have p4445_0 := h4445c.1
                                have p4445_1 := h4445c.2.1
                                have p4445_2 := h4445c.2.2.1
                                have p4445_3 := h4445c.2.2.2
                                linarith only [h2, h4434, h4436, h4441, h4443, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4445_1]
                              · have p4445_0 := h4445c.1
                                have p4445_1 := h4445c.2.1
                                have p4445_2 := h4445c.2.2.1
                                have p4445_3 := h4445c.2.2.2
                                linarith only [h0, hlam, p4445_0]
                              · have p4445_0 := h4445c.1
                                have p4445_1 := h4445c.2.1
                                have p4445_2 := h4445c.2.2.1
                                have p4445_3 := h4445c.2.2.2
                                linarith only [hlam, p4445_0]
                              · have p4445_0 := h4445c.1
                                have p4445_1 := h4445c.2.1
                                have p4445_2 := h4445c.2.2.1
                                have p4445_3 := h4445c.2.2.2
                                linarith only [h4424, hlam, p4445_1]
                              · have p4445_0 := h4445c.1
                                have p4445_1 := h4445c.2.1
                                have p4445_2 := h4445c.2.2.1
                                have p4445_3 := h4445c.2.2.2
                                linarith only [h4434, hlam, p4445_1]
                              · have p4445_0 := h4445c.1
                                have p4445_1 := h4445c.2.1
                                have p4445_2 := h4445c.2.2.1
                                have p4445_3 := h4445c.2.2.2
                                linarith only [h0, h2, h4434, h4436, h4441, h4443, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4445_1]
                              · have p4445_0 := h4445c.1
                                have p4445_1 := h4445c.2.1
                                have p4445_2 := h4445c.2.2.1
                                have p4445_3 := h4445c.2.2.2
                                linarith only [h1, hlam, p4445_0]
                              · have p4445_0 := h4445c.1
                                have p4445_1 := h4445c.2.1
                                have p4445_2 := h4445c.2.2.1
                                have p4445_3 := h4445c.2.2.2
                                linarith only [h1, h2, h4434, h4441, hc12, hc34, hlam, hphi, ht23, p4445_1]
                              · have p4445_0 := h4445c.1
                                have p4445_1 := h4445c.2.1
                                have p4445_2 := h4445c.2.2.1
                                have p4445_3 := h4445c.2.2.2
                                linarith only [hlam, p4445_0]
                              · have p4445_0 := h4445c.1
                                have p4445_1 := h4445c.2.1
                                have p4445_2 := h4445c.2.2.1
                                have p4445_3 := h4445c.2.2.2
                                linarith only [h4437, hlam, p4445_0]
                              · have p4445_0 := h4445c.1
                                have p4445_1 := h4445c.2.1
                                have p4445_2 := h4445c.2.2.1
                                have p4445_3 := h4445c.2.2.2
                                linarith only [h1, h2, h4434, h4436, h4441, h4443, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4445_1]
                              · have p4445_0 := h4445c.1
                                have p4445_1 := h4445c.2.1
                                have p4445_2 := h4445c.2.2.1
                                have p4445_3 := h4445c.2.2.2
                                linarith only [h4434, h4441, hc01, hc34, hlam, hphi, ht12, ht23, p4445_1]
                              · have p4445_0 := h4445c.1
                                have p4445_1 := h4445c.2.1
                                have p4445_2 := h4445c.2.2.1
                                have p4445_3 := h4445c.2.2.2
                                linarith only [h4434, h4436, h4441, h4443, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4445_1]
                              · have p4445_0 := h4445c.1
                                have p4445_1 := h4445c.2.1
                                have p4445_2 := h4445c.2.2.1
                                have p4445_3 := h4445c.2.2.2
                                linarith only [h4424, h4434, h4436, h4441, h4443, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4445_1]
                              · have p4445_0 := h4445c.1
                                have p4445_1 := h4445c.2.1
                                have p4445_2 := h4445c.2.2.1
                                have p4445_3 := h4445c.2.2.2
                                linarith only [hlam, p4445_0]
                              · have p4445_0 := h4445c.1
                                have p4445_1 := h4445c.2.1
                                have p4445_2 := h4445c.2.2.1
                                have p4445_3 := h4445c.2.2.2
                                rcases p4445_3 (m.d 0 1) (by simp) with h4465 | h4465
                                · linarith only [h2, h4465, hlam]
                                · linarith only [h4418, h4465, hlam]
                              · have p4445_0 := h4445c.1
                                have p4445_1 := h4445c.2.1
                                have p4445_2 := h4445c.2.2.1
                                have p4445_3 := h4445c.2.2.2
                                linarith only [h4418, hlam, p4445_0]
                              · have p4445_0 := h4445c.1
                                have p4445_1 := h4445c.2.1
                                have p4445_2 := h4445c.2.2.1
                                have p4445_3 := h4445c.2.2.2
                                linarith only [h4436, hlam, p4445_0]
                              · have p4445_0 := h4445c.1
                                have p4445_1 := h4445c.2.1
                                have p4445_2 := h4445c.2.2.1
                                have p4445_3 := h4445c.2.2.2
                                linarith only [h4439, hlam, p4445_0]
                              · have p4445_0 := h4445c.1
                                have p4445_1 := h4445c.2.1
                                have p4445_2 := h4445c.2.2.1
                                have p4445_3 := h4445c.2.2.2
                                linarith only [h4440, hlam, p4445_0]
                              · have p4445_0 := h4445c.1
                                have p4445_1 := h4445c.2.1
                                have p4445_2 := h4445c.2.2.1
                                have p4445_3 := h4445c.2.2.2
                                linarith only [hlam, p4445_0]
                            · linarith only [h1, h4424, h4436, h4441, h4443, h4444, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · linarith only [h1, h2, h4424, h4434, h4443, hc12, hc45, hlam, hphi, ht23, ht34]
                      · linarith only [h2, h4418, h4423, h4440, hlam]
                    · linarith only [h4424, h4436, h4439, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4477 | h4477
                  · linarith only [h1, h4421, h4477, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4479 | h4479
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4480 | h4480
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4481 | h4481
                        · linarith only [h1, h2, h4436, h4477, h4479, h4481, hc12, hc23, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4483 | h4483
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4484 | h4484
                            · rcases h1bigk with h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c
                              · have p4485_0 := h4485c.1
                                have p4485_1 := h4485c.2.1
                                have p4485_2 := h4485c.2.2.1
                                have p4485_3 := h4485c.2.2.2
                                linarith only [hlam, p4485_0]
                              · have p4485_0 := h4485c.1
                                have p4485_1 := h4485c.2.1
                                have p4485_2 := h4485c.2.2.1
                                have p4485_3 := h4485c.2.2.2
                                linarith only [h2, h4434, h4481, hc12, hc34, hlam, hphi, ht23, p4485_1]
                              · have p4485_0 := h4485c.1
                                have p4485_1 := h4485c.2.1
                                have p4485_2 := h4485c.2.2.1
                                have p4485_3 := h4485c.2.2.2
                                linarith only [h2, h4434, h4479, h4481, h4484, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4485_1]
                              · have p4485_0 := h4485c.1
                                have p4485_1 := h4485c.2.1
                                have p4485_2 := h4485c.2.2.1
                                have p4485_3 := h4485c.2.2.2
                                linarith only [h2, hlam, p4485_0]
                              · have p4485_0 := h4485c.1
                                have p4485_1 := h4485c.2.1
                                have p4485_2 := h4485c.2.2.1
                                have p4485_3 := h4485c.2.2.2
                                linarith only [h2, h4434, h4481, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4485_1]
                              · have p4485_0 := h4485c.1
                                have p4485_1 := h4485c.2.1
                                have p4485_2 := h4485c.2.2.1
                                have p4485_3 := h4485c.2.2.2
                                linarith only [h0, hlam, p4485_0]
                              · have p4485_0 := h4485c.1
                                have p4485_1 := h4485c.2.1
                                have p4485_2 := h4485c.2.2.1
                                have p4485_3 := h4485c.2.2.2
                                linarith only [hlam, p4485_0]
                              · have p4485_0 := h4485c.1
                                have p4485_1 := h4485c.2.1
                                have p4485_2 := h4485c.2.2.1
                                have p4485_3 := h4485c.2.2.2
                                linarith only [h4424, hlam, p4485_1]
                              · have p4485_0 := h4485c.1
                                have p4485_1 := h4485c.2.1
                                have p4485_2 := h4485c.2.2.1
                                have p4485_3 := h4485c.2.2.2
                                linarith only [h4434, hlam, p4485_1]
                              · have p4485_0 := h4485c.1
                                have p4485_1 := h4485c.2.1
                                have p4485_2 := h4485c.2.2.1
                                have p4485_3 := h4485c.2.2.2
                                linarith only [h4436, hlam, p4485_1]
                              · have p4485_0 := h4485c.1
                                have p4485_1 := h4485c.2.1
                                have p4485_2 := h4485c.2.2.1
                                have p4485_3 := h4485c.2.2.2
                                linarith only [h1, hlam, p4485_0]
                              · have p4485_0 := h4485c.1
                                have p4485_1 := h4485c.2.1
                                have p4485_2 := h4485c.2.2.1
                                have p4485_3 := h4485c.2.2.2
                                linarith only [h1, h2, h4434, h4481, hc12, hc34, hlam, hphi, ht23, p4485_1]
                              · have p4485_0 := h4485c.1
                                have p4485_1 := h4485c.2.1
                                have p4485_2 := h4485c.2.2.1
                                have p4485_3 := h4485c.2.2.2
                                linarith only [hlam, p4485_0]
                              · have p4485_0 := h4485c.1
                                have p4485_1 := h4485c.2.1
                                have p4485_2 := h4485c.2.2.1
                                have p4485_3 := h4485c.2.2.2
                                linarith only [h4477, hlam, p4485_0]
                              · have p4485_0 := h4485c.1
                                have p4485_1 := h4485c.2.1
                                have p4485_2 := h4485c.2.2.1
                                have p4485_3 := h4485c.2.2.2
                                linarith only [h1, h2, h4434, h4436, h4481, hc12, hc34, hlam, hphi, ht23, p4485_1]
                              · have p4485_0 := h4485c.1
                                have p4485_1 := h4485c.2.1
                                have p4485_2 := h4485c.2.2.1
                                have p4485_3 := h4485c.2.2.2
                                linarith only [h4434, h4481, hc01, hc34, hlam, hphi, ht12, ht23, p4485_1]
                              · have p4485_0 := h4485c.1
                                have p4485_1 := h4485c.2.1
                                have p4485_2 := h4485c.2.2.1
                                have p4485_3 := h4485c.2.2.2
                                linarith only [h4434, h4481, hc12, hc34, hlam, hphi, ht23, p4485_1]
                              · have p4485_0 := h4485c.1
                                have p4485_1 := h4485c.2.1
                                have p4485_2 := h4485c.2.2.1
                                have p4485_3 := h4485c.2.2.2
                                linarith only [h4424, h4434, h4481, hc12, hc34, hlam, hphi, ht23, p4485_1]
                              · have p4485_0 := h4485c.1
                                have p4485_1 := h4485c.2.1
                                have p4485_2 := h4485c.2.2.1
                                have p4485_3 := h4485c.2.2.2
                                linarith only [hlam, p4485_0]
                              · have p4485_0 := h4485c.1
                                have p4485_1 := h4485c.2.1
                                have p4485_2 := h4485c.2.2.1
                                have p4485_3 := h4485c.2.2.2
                                linarith only [h4434, h4436, h4481, hc12, hc34, hlam, hphi, ht23, p4485_1]
                              · have p4485_0 := h4485c.1
                                have p4485_1 := h4485c.2.1
                                have p4485_2 := h4485c.2.2.1
                                have p4485_3 := h4485c.2.2.2
                                linarith only [h4418, hlam, p4485_0]
                              · have p4485_0 := h4485c.1
                                have p4485_1 := h4485c.2.1
                                have p4485_2 := h4485c.2.2.1
                                have p4485_3 := h4485c.2.2.2
                                linarith only [h4418, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4485_1]
                              · have p4485_0 := h4485c.1
                                have p4485_1 := h4485c.2.1
                                have p4485_2 := h4485c.2.2.1
                                have p4485_3 := h4485c.2.2.2
                                linarith only [h4479, hlam, p4485_0]
                              · have p4485_0 := h4485c.1
                                have p4485_1 := h4485c.2.1
                                have p4485_2 := h4485c.2.2.1
                                have p4485_3 := h4485c.2.2.2
                                linarith only [h4480, hlam, p4485_0]
                              · have p4485_0 := h4485c.1
                                have p4485_1 := h4485c.2.1
                                have p4485_2 := h4485c.2.2.1
                                have p4485_3 := h4485c.2.2.2
                                linarith only [hlam, p4485_0]
                            · linarith only [h1, h2, h4434, h4479, h4481, h4484, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h1, h2, h4434, h4479, h4480, h4483, hlam]
                      · linarith only [h1, h2, h4479, h4480, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4514 | h4514
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4515 | h4515
                        · linarith only [h0, h2, h4477, h4515, hc12, hc23, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4517 | h4517
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4518 | h4518
                            · rcases h1bigk with h4519c | h4519c | h4519c | h4519c | h4519c | h4519c | h4519c | h4519c | h4519c | h4519c | h4519c | h4519c | h4519c | h4519c | h4519c | h4519c | h4519c | h4519c | h4519c | h4519c | h4519c | h4519c | h4519c | h4519c | h4519c
                              · have p4519_0 := h4519c.1
                                have p4519_1 := h4519c.2.1
                                have p4519_2 := h4519c.2.2.1
                                have p4519_3 := h4519c.2.2.2
                                linarith only [hlam, p4519_0]
                              · have p4519_0 := h4519c.1
                                have p4519_1 := h4519c.2.1
                                have p4519_2 := h4519c.2.2.1
                                have p4519_3 := h4519c.2.2.2
                                linarith only [h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4519_1]
                              · have p4519_0 := h4519c.1
                                have p4519_1 := h4519c.2.1
                                have p4519_2 := h4519c.2.2.1
                                have p4519_3 := h4519c.2.2.2
                                linarith only [h2, h4434, h4515, hc13, hc34, hlam, hphi, p4519_1]
                              · have p4519_0 := h4519c.1
                                have p4519_1 := h4519c.2.1
                                have p4519_2 := h4519c.2.2.1
                                have p4519_3 := h4519c.2.2.2
                                linarith only [h2, hlam, p4519_0]
                              · have p4519_0 := h4519c.1
                                have p4519_1 := h4519c.2.1
                                have p4519_2 := h4519c.2.2.1
                                have p4519_3 := h4519c.2.2.2
                                linarith only [h2, h4434, h4515, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4519_1]
                              · have p4519_0 := h4519c.1
                                have p4519_1 := h4519c.2.1
                                have p4519_2 := h4519c.2.2.1
                                have p4519_3 := h4519c.2.2.2
                                linarith only [h0, hlam, p4519_0]
                              · have p4519_0 := h4519c.1
                                have p4519_1 := h4519c.2.1
                                have p4519_2 := h4519c.2.2.1
                                have p4519_3 := h4519c.2.2.2
                                linarith only [hlam, p4519_0]
                              · have p4519_0 := h4519c.1
                                have p4519_1 := h4519c.2.1
                                have p4519_2 := h4519c.2.2.1
                                have p4519_3 := h4519c.2.2.2
                                linarith only [h4424, hlam, p4519_1]
                              · have p4519_0 := h4519c.1
                                have p4519_1 := h4519c.2.1
                                have p4519_2 := h4519c.2.2.1
                                have p4519_3 := h4519c.2.2.2
                                linarith only [h4434, hlam, p4519_1]
                              · have p4519_0 := h4519c.1
                                have p4519_1 := h4519c.2.1
                                have p4519_2 := h4519c.2.2.1
                                have p4519_3 := h4519c.2.2.2
                                linarith only [h4436, hlam, p4519_1]
                              · have p4519_0 := h4519c.1
                                have p4519_1 := h4519c.2.1
                                have p4519_2 := h4519c.2.2.1
                                have p4519_3 := h4519c.2.2.2
                                linarith only [h1, hlam, p4519_0]
                              · have p4519_0 := h4519c.1
                                have p4519_1 := h4519c.2.1
                                have p4519_2 := h4519c.2.2.1
                                have p4519_3 := h4519c.2.2.2
                                linarith only [h4479, hc12, hc35, hlam, hphi, ht23, p4519_1]
                              · have p4519_0 := h4519c.1
                                have p4519_1 := h4519c.2.1
                                have p4519_2 := h4519c.2.2.1
                                have p4519_3 := h4519c.2.2.2
                                linarith only [hlam, p4519_0]
                              · have p4519_0 := h4519c.1
                                have p4519_1 := h4519c.2.1
                                have p4519_2 := h4519c.2.2.1
                                have p4519_3 := h4519c.2.2.2
                                linarith only [h4477, hlam, p4519_0]
                              · have p4519_0 := h4519c.1
                                have p4519_1 := h4519c.2.1
                                have p4519_2 := h4519c.2.2.1
                                have p4519_3 := h4519c.2.2.2
                                linarith only [h4479, hlam, p4519_1]
                              · have p4519_0 := h4519c.1
                                have p4519_1 := h4519c.2.1
                                have p4519_2 := h4519c.2.2.1
                                have p4519_3 := h4519c.2.2.2
                                linarith only [h4434, h4515, hc01, hc34, hlam, hphi, ht12, ht23, p4519_1]
                              · have p4519_0 := h4519c.1
                                have p4519_1 := h4519c.2.1
                                have p4519_2 := h4519c.2.2.1
                                have p4519_3 := h4519c.2.2.2
                                linarith only [h4434, h4515, hc12, hc34, hlam, hphi, ht23, p4519_1]
                              · have p4519_0 := h4519c.1
                                have p4519_1 := h4519c.2.1
                                have p4519_2 := h4519c.2.2.1
                                have p4519_3 := h4519c.2.2.2
                                linarith only [h4424, h4434, h4515, hc12, hc34, hlam, hphi, ht23, p4519_1]
                              · have p4519_0 := h4519c.1
                                have p4519_1 := h4519c.2.1
                                have p4519_2 := h4519c.2.2.1
                                have p4519_3 := h4519c.2.2.2
                                linarith only [hlam, p4519_0]
                              · have p4519_0 := h4519c.1
                                have p4519_1 := h4519c.2.1
                                have p4519_2 := h4519c.2.2.1
                                have p4519_3 := h4519c.2.2.2
                                linarith only [h4424, h4434, h4479, h4515, hc12, hc34, hlam, hphi, ht23, p4519_1]
                              · have p4519_0 := h4519c.1
                                have p4519_1 := h4519c.2.1
                                have p4519_2 := h4519c.2.2.1
                                have p4519_3 := h4519c.2.2.2
                                linarith only [h4418, hlam, p4519_0]
                              · have p4519_0 := h4519c.1
                                have p4519_1 := h4519c.2.1
                                have p4519_2 := h4519c.2.2.1
                                have p4519_3 := h4519c.2.2.2
                                linarith only [h4418, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4519_1]
                              · have p4519_0 := h4519c.1
                                have p4519_1 := h4519c.2.1
                                have p4519_2 := h4519c.2.2.1
                                have p4519_3 := h4519c.2.2.2
                                linarith only [h2, h4418, h4424, h4434, h4515, hc12, hc34, hlam, hphi, ht23, p4519_1]
                              · have p4519_0 := h4519c.1
                                have p4519_1 := h4519c.2.1
                                have p4519_2 := h4519c.2.2.1
                                have p4519_3 := h4519c.2.2.2
                                linarith only [h4514, hlam, p4519_0]
                              · have p4519_0 := h4519c.1
                                have p4519_1 := h4519c.2.1
                                have p4519_2 := h4519c.2.2.1
                                have p4519_3 := h4519c.2.2.2
                                linarith only [hlam, p4519_0]
                            · linarith only [h0, h2, h4434, h4515, h4518, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h2, h4418, h4434, h4514, h4517, hlam]
                      · linarith only [h2, h4418, h4424, h4479, h4514, hc12, hc45, hlam, hphi, ht23, ht34]
          · linarith only [h2, h4418, h4423, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h4549 | h4549
      · linarith only [h0, h2, h4549, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h4551 | h4551
        · linarith only [h1, h2, h4551, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4553 | h4553
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4554 | h4554
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4555 | h4555
              · linarith only [h0, h2, h4549, h4555, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4557 | h4557
                · linarith only [h0, h4418, h4557, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4559 | h4559
                  · linarith only [h0, h2, h4551, h4554, h4555, h4559, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h0, h2, h4554, h4559, hc23, hc34, hlam, hphi]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4562 | h4562
              · linarith only [h0, h4549, h4562, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4564 | h4564
                · linarith only [h1, h4418, h4554, h4564, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4566 | h4566
                  · linarith only [h1, h4551, h4566, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4568 | h4568
                    · linarith only [h1, h4418, h4568, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4570 | h4570
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4571 | h4571
                        · linarith only [h1, h4418, h4554, h4566, h4570, h4571, hc12, hc23, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4573 | h4573
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4574 | h4574
                            · rcases h1bigk with h4575c | h4575c | h4575c | h4575c | h4575c | h4575c | h4575c | h4575c | h4575c | h4575c | h4575c | h4575c | h4575c | h4575c | h4575c | h4575c | h4575c | h4575c | h4575c | h4575c | h4575c | h4575c | h4575c | h4575c | h4575c
                              · have p4575_0 := h4575c.1
                                have p4575_1 := h4575c.2.1
                                have p4575_2 := h4575c.2.2.1
                                have p4575_3 := h4575c.2.2.2
                                linarith only [hlam, p4575_0]
                              · have p4575_0 := h4575c.1
                                have p4575_1 := h4575c.2.1
                                have p4575_2 := h4575c.2.2.1
                                have p4575_3 := h4575c.2.2.2
                                linarith only [h4418, h4570, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4575_1]
                              · have p4575_0 := h4575c.1
                                have p4575_1 := h4575c.2.1
                                have p4575_2 := h4575c.2.2.1
                                have p4575_3 := h4575c.2.2.2
                                linarith only [h4418, h4570, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4575_1]
                              · have p4575_0 := h4575c.1
                                have p4575_1 := h4575c.2.1
                                have p4575_2 := h4575c.2.2.1
                                have p4575_3 := h4575c.2.2.2
                                linarith only [h2, hlam, p4575_0]
                              · have p4575_0 := h4575c.1
                                have p4575_1 := h4575c.2.1
                                have p4575_2 := h4575c.2.2.1
                                have p4575_3 := h4575c.2.2.2
                                linarith only [h4418, hlam, p4575_0]
                              · have p4575_0 := h4575c.1
                                have p4575_1 := h4575c.2.1
                                have p4575_2 := h4575c.2.2.1
                                have p4575_3 := h4575c.2.2.2
                                linarith only [h0, hlam, p4575_0]
                              · have p4575_0 := h4575c.1
                                have p4575_1 := h4575c.2.1
                                have p4575_2 := h4575c.2.2.1
                                have p4575_3 := h4575c.2.2.2
                                linarith only [hlam, p4575_0]
                              · have p4575_0 := h4575c.1
                                have p4575_1 := h4575c.2.1
                                have p4575_2 := h4575c.2.2.1
                                have p4575_3 := h4575c.2.2.2
                                linarith only [h4554, hlam, p4575_1]
                              · have p4575_0 := h4575c.1
                                have p4575_1 := h4575c.2.1
                                have p4575_2 := h4575c.2.2.1
                                have p4575_3 := h4575c.2.2.2
                                linarith only [h4562, hlam, p4575_1]
                              · have p4575_0 := h4575c.1
                                have p4575_1 := h4575c.2.1
                                have p4575_2 := h4575c.2.2.1
                                have p4575_3 := h4575c.2.2.2
                                linarith only [h4564, hlam, p4575_1]
                              · have p4575_0 := h4575c.1
                                have p4575_1 := h4575c.2.1
                                have p4575_2 := h4575c.2.2.1
                                have p4575_3 := h4575c.2.2.2
                                linarith only [h1, hlam, p4575_0]
                              · have p4575_0 := h4575c.1
                                have p4575_1 := h4575c.2.1
                                have p4575_2 := h4575c.2.2.1
                                have p4575_3 := h4575c.2.2.2
                                linarith only [h1, h4418, h4562, h4570, h4571, hc12, hc34, hlam, hphi, ht23, p4575_1]
                              · have p4575_0 := h4575c.1
                                have p4575_1 := h4575c.2.1
                                have p4575_2 := h4575c.2.2.1
                                have p4575_3 := h4575c.2.2.2
                                linarith only [hlam, p4575_0]
                              · have p4575_0 := h4575c.1
                                have p4575_1 := h4575c.2.1
                                have p4575_2 := h4575c.2.2.1
                                have p4575_3 := h4575c.2.2.2
                                linarith only [h4566, hlam, p4575_0]
                              · have p4575_0 := h4575c.1
                                have p4575_1 := h4575c.2.1
                                have p4575_2 := h4575c.2.2.1
                                have p4575_3 := h4575c.2.2.2
                                linarith only [h4568, hlam, p4575_1]
                              · have p4575_0 := h4575c.1
                                have p4575_1 := h4575c.2.1
                                have p4575_2 := h4575c.2.2.1
                                have p4575_3 := h4575c.2.2.2
                                linarith only [h4562, h4571, hc01, hc34, hlam, hphi, ht12, ht23, p4575_1]
                              · have p4575_0 := h4575c.1
                                have p4575_1 := h4575c.2.1
                                have p4575_2 := h4575c.2.2.1
                                have p4575_3 := h4575c.2.2.2
                                linarith only [h4562, h4571, hc12, hc34, hlam, hphi, ht23, p4575_1]
                              · have p4575_0 := h4575c.1
                                have p4575_1 := h4575c.2.1
                                have p4575_2 := h4575c.2.2.1
                                have p4575_3 := h4575c.2.2.2
                                linarith only [h4554, h4562, h4571, hc12, hc34, hlam, hphi, ht23, p4575_1]
                              · have p4575_0 := h4575c.1
                                have p4575_1 := h4575c.2.1
                                have p4575_2 := h4575c.2.2.1
                                have p4575_3 := h4575c.2.2.2
                                linarith only [hlam, p4575_0]
                              · have p4575_0 := h4575c.1
                                have p4575_1 := h4575c.2.1
                                have p4575_2 := h4575c.2.2.1
                                have p4575_3 := h4575c.2.2.2
                                linarith only [h1, h4418, h4554, h4562, h4571, hc12, hc34, hlam, hphi, ht23, p4575_1]
                              · have p4575_0 := h4575c.1
                                have p4575_1 := h4575c.2.1
                                have p4575_2 := h4575c.2.2.1
                                have p4575_3 := h4575c.2.2.2
                                linarith only [h1, h4554, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4575_1]
                              · have p4575_0 := h4575c.1
                                have p4575_1 := h4575c.2.1
                                have p4575_2 := h4575c.2.2.1
                                have p4575_3 := h4575c.2.2.2
                                linarith only [h4568, hc12, hc35, hlam, hphi, ht23, p4575_1]
                              · have p4575_0 := h4575c.1
                                have p4575_1 := h4575c.2.1
                                have p4575_2 := h4575c.2.2.1
                                have p4575_3 := h4575c.2.2.2
                                linarith only [h4554, h4568, hc12, hc35, hlam, hphi, ht23, p4575_1]
                              · have p4575_0 := h4575c.1
                                have p4575_1 := h4575c.2.1
                                have p4575_2 := h4575c.2.2.1
                                have p4575_3 := h4575c.2.2.2
                                linarith only [h4570, hlam, p4575_0]
                              · have p4575_0 := h4575c.1
                                have p4575_1 := h4575c.2.1
                                have p4575_2 := h4575c.2.2.1
                                have p4575_3 := h4575c.2.2.2
                                linarith only [hlam, p4575_0]
                            · linarith only [h1, h2, h4553, h4554, h4562, h4571, h4574, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                          · linarith only [h2, h4553, h4562, h4573, hlam]
                      · linarith only [h2, h4553, h4570, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4604 | h4604
            · linarith only [h0, h2, h4553, h4604, hc23, hc45, hlam, hphi, ht34]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4606 | h4606
              · linarith only [h1, h2, h4553, h4604, h4606, hc24, hc45, hlam, hphi]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4608 | h4608
                · linarith only [h1, h4418, h4604, h4608, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4610 | h4610
                  · linarith only [h1, h2, h4553, h4610, hc34, hc45, hlam, hphi]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4612 | h4612
                    · linarith only [h1, h4418, h4612, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4614 | h4614
                      · linarith only [h1, h2, h4553, h4604, h4606, h4614, hc12, hc24, hlam, hphi]
                      · linarith only [h1, h2, h4604, h4614, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
