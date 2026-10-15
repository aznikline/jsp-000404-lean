import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5244000 in
set_option maxHeartbeats 5244000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s7_x0_x0_x0_x0_x0 (m : N7Model)
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
    (h4338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h4339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  rcases m.htr 1 2 3 (by decide) (by decide) with h4340 | h4340
  · rcases m.htr 1 2 4 (by decide) (by decide) with h4341 | h4341
    · rcases m.htr 1 2 5 (by decide) (by decide) with h4342 | h4342
      · rcases m.htr 1 3 4 (by decide) (by decide) with h4343 | h4343
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4344 | h4344
          · rcases m.htr 1 4 5 (by decide) (by decide) with h4345 | h4345
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4346 | h4346
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4347 | h4347
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4348 | h4348
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4349 | h4349
                    · linarith only [h4335, h4346, h4349, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h0, h4336, h4348, h4349, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4352 | h4352
                    · linarith only [h4346, h4348, h4352, hlam]
                    · rcases h1bigk with h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c | h4354c
                      · have p4354_0 := h4354c.1
                        have p4354_1 := h4354c.2.1
                        have p4354_2 := h4354c.2.2.1
                        have p4354_3 := h4354c.2.2.2
                        linarith only [hlam, p4354_0]
                      · have p4354_0 := h4354c.1
                        have p4354_1 := h4354c.2.1
                        have p4354_2 := h4354c.2.2.1
                        have p4354_3 := h4354c.2.2.2
                        linarith only [h0, hlam, p4354_0]
                      · have p4354_0 := h4354c.1
                        have p4354_1 := h4354c.2.1
                        have p4354_2 := h4354c.2.2.1
                        have p4354_3 := h4354c.2.2.2
                        linarith only [h3473, hlam, p4354_0]
                      · have p4354_0 := h4354c.1
                        have p4354_1 := h4354c.2.1
                        have p4354_2 := h4354c.2.2.1
                        have p4354_3 := h4354c.2.2.2
                        linarith only [h4044, hlam, p4354_0]
                      · have p4354_0 := h4354c.1
                        have p4354_1 := h4354c.2.1
                        have p4354_2 := h4354c.2.2.1
                        have p4354_3 := h4354c.2.2.2
                        linarith only [h4238, hlam, p4354_0]
                      · have p4354_0 := h4354c.1
                        have p4354_1 := h4354c.2.1
                        have p4354_2 := h4354c.2.2.1
                        have p4354_3 := h4354c.2.2.2
                        rcases p4354_3 (m.d 0 1) (by simp) with h4360 | h4360
                        · linarith only [h4360, hlam, p4354_0]
                        · rcases p4354_3 (m.d 1 2) (by simp) with h4362 | h4362
                          · rcases p4354_3 (m.d 1 3) (by simp) with h4363 | h4363
                            · linarith only [h4340, h4363, hlam]
                            · linarith only [h3473, h4363, hlam]
                          · linarith only [h4362, hlam, p4354_0]
                      · have p4354_0 := h4354c.1
                        have p4354_1 := h4354c.2.1
                        have p4354_2 := h4354c.2.2.1
                        have p4354_3 := h4354c.2.2.2
                        linarith only [hlam, p4354_0]
                      · have p4354_0 := h4354c.1
                        have p4354_1 := h4354c.2.1
                        have p4354_2 := h4354c.2.2.1
                        have p4354_3 := h4354c.2.2.2
                        linarith only [h3473, hc01, hc12, hlam, hphi, p4354_1]
                      · have p4354_0 := h4354c.1
                        have p4354_1 := h4354c.2.1
                        have p4354_2 := h4354c.2.2.1
                        have p4354_3 := h4354c.2.2.2
                        linarith only [h4044, h4339, h4346, h4348, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4354_1, u4ehi3]
                      · have p4354_0 := h4354c.1
                        have p4354_1 := h4354c.2.1
                        have p4354_2 := h4354c.2.2.1
                        have p4354_3 := h4354c.2.2.2
                        linarith only [h4238, hc01, hc12, hlam, hphi, p4354_1]
                      · have p4354_0 := h4354c.1
                        have p4354_1 := h4354c.2.1
                        have p4354_2 := h4354c.2.2.1
                        have p4354_3 := h4354c.2.2.2
                        rcases p4354_3 (m.d 0 1) (by simp) with h4371 | h4371
                        · linarith only [h4371, hlam, p4354_0]
                        · rcases p4354_3 (m.d 1 2) (by simp) with h4373 | h4373
                          · rcases p4354_3 (m.d 1 3) (by simp) with h4374 | h4374
                            · rcases p4354_3 (m.d 1 4) (by simp) with h4375 | h4375
                              · linarith only [h4343, h4375, hlam]
                              · linarith only [h4044, h4375, hlam]
                            · linarith only [h4374, hlam, p4354_0]
                          · linarith only [h0, h4373, hlam]
                      · have p4354_0 := h4354c.1
                        have p4354_1 := h4354c.2.1
                        have p4354_2 := h4354c.2.2.1
                        have p4354_3 := h4354c.2.2.2
                        linarith only [h4340, hlam, p4354_0]
                      · have p4354_0 := h4354c.1
                        have p4354_1 := h4354c.2.1
                        have p4354_2 := h4354c.2.2.1
                        have p4354_3 := h4354c.2.2.2
                        linarith only [hlam, p4354_0]
                      · have p4354_0 := h4354c.1
                        have p4354_1 := h4354c.2.1
                        have p4354_2 := h4354c.2.2.1
                        have p4354_3 := h4354c.2.2.2
                        linarith only [h4044, h4339, h4346, h4348, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p4354_1, u4ehi3]
                      · have p4354_0 := h4354c.1
                        have p4354_1 := h4354c.2.1
                        have p4354_2 := h4354c.2.2.1
                        have p4354_3 := h4354c.2.2.2
                        linarith only [h4238, h4339, h4340, h4346, h4348, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4354_1, u4ehi3]
                      · have p4354_0 := h4354c.1
                        have p4354_1 := h4354c.2.1
                        have p4354_2 := h4354c.2.2.1
                        have p4354_3 := h4354c.2.2.2
                        rcases p4354_3 (m.d 0 1) (by simp) with h4384 | h4384
                        · linarith only [h4384, hlam, p4354_0]
                        · rcases p4354_3 (m.d 1 2) (by simp) with h4386 | h4386
                          · rcases p4354_3 (m.d 1 3) (by simp) with h4387 | h4387
                            · rcases p4354_3 (m.d 1 4) (by simp) with h4388 | h4388
                              · rcases p4354_3 (m.d 1 5) (by simp) with h4389 | h4389
                                · linarith only [h4345, h4389, hlam]
                                · linarith only [h4238, h4389, hlam]
                              · linarith only [h4388, hlam, p4354_0]
                            · linarith only [h3473, h4387, hlam]
                          · linarith only [h0, h4386, hlam]
                      · have p4354_0 := h4354c.1
                        have p4354_1 := h4354c.2.1
                        have p4354_2 := h4354c.2.2.1
                        have p4354_3 := h4354c.2.2.2
                        linarith only [h4341, hlam, p4354_0]
                      · have p4354_0 := h4354c.1
                        have p4354_1 := h4354c.2.1
                        have p4354_2 := h4354c.2.2.1
                        have p4354_3 := h4354c.2.2.2
                        linarith only [h4343, hlam, p4354_1]
                      · have p4354_0 := h4354c.1
                        have p4354_1 := h4354c.2.1
                        have p4354_2 := h4354c.2.2.1
                        have p4354_3 := h4354c.2.2.2
                        linarith only [hlam, p4354_0]
                      · have p4354_0 := h4354c.1
                        have p4354_1 := h4354c.2.1
                        have p4354_2 := h4354c.2.2.1
                        have p4354_3 := h4354c.2.2.2
                        linarith only [h4238, h4339, h4346, h4348, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p4354_1, u4ehi3]
                      · have p4354_0 := h4354c.1
                        have p4354_1 := h4354c.2.1
                        have p4354_2 := h4354c.2.2.1
                        have p4354_3 := h4354c.2.2.2
                        rcases p4354_3 (m.d 0 1) (by simp) with h4399 | h4399
                        · linarith only [h4399, hlam, p4354_0]
                        · rcases p4354_3 (m.d 1 2) (by simp) with h4401 | h4401
                          · rcases p4354_3 (m.d 1 3) (by simp) with h4402 | h4402
                            · rcases p4354_3 (m.d 1 4) (by simp) with h4403 | h4403
                              · rcases p4354_3 (m.d 1 5) (by simp) with h4404 | h4404
                                · rcases h2bigk with h4405c | h4405c | h4405c | h4405c | h4405c | h4405c | h4405c | h4405c | h4405c | h4405c | h4405c | h4405c | h4405c | h4405c | h4405c | h4405c | h4405c | h4405c | h4405c | h4405c | h4405c | h4405c | h4405c | h4405c | h4405c
                                  · have p4405_0 := h4405c.1
                                    have p4405_1 := h4405c.2.1
                                    have p4405_2 := h4405c.2.2.1
                                    have p4405_3 := h4405c.2.2.2
                                    linarith only [hlam, p4405_0]
                                  · have p4405_0 := h4405c.1
                                    have p4405_1 := h4405c.2.1
                                    have p4405_2 := h4405c.2.2.1
                                    have p4405_3 := h4405c.2.2.2
                                    linarith only [h0, hlam, p4405_0]
                                  · have p4405_0 := h4405c.1
                                    have p4405_1 := h4405c.2.1
                                    have p4405_2 := h4405c.2.2.1
                                    have p4405_3 := h4405c.2.2.2
                                    linarith only [h0, h4347, h4352, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4405_1, u4ehi3]
                                  · have p4405_0 := h4405c.1
                                    have p4405_1 := h4405c.2.1
                                    have p4405_2 := h4405c.2.2.1
                                    have p4405_3 := h4405c.2.2.2
                                    rcases p4405_3 (m.d 0 2) (by simp) with h4409 | h4409
                                    · rcases p4405_3 (m.d 1 2) (by simp) with h4410 | h4410
                                      · rcases p4405_3 (m.d 2 3) (by simp) with h4411 | h4411
                                        · linarith only [h4335, h4411, hlam]
                                        · linarith only [h4346, h4411, hlam]
                                      · linarith only [h4341, h4410, hlam]
                                    · linarith only [h4409, hlam, p4405_0]
                                  · have p4405_0 := h4405c.1
                                    have p4405_1 := h4405c.2.1
                                    have p4405_2 := h4405c.2.2.1
                                    have p4405_3 := h4405c.2.2.2
                                    rcases p4405_3 (m.d 0 2) (by simp) with h4416 | h4416
                                    · rcases p4405_3 (m.d 1 2) (by simp) with h4417 | h4417
                                      · rcases p4405_3 (m.d 2 3) (by simp) with h4418 | h4418
                                        · linarith only [h4335, h4418, hlam]
                                        · linarith only [h4347, h4418, hlam]
                                      · linarith only [h4342, h4417, hlam]
                                    · linarith only [h4416, hlam, p4405_0]
                                  · have p4405_0 := h4405c.1
                                    have p4405_1 := h4405c.2.1
                                    have p4405_2 := h4405c.2.2.1
                                    have p4405_3 := h4405c.2.2.2
                                    linarith only [h4335, h4347, h4352, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4405_1, u4ehi3]
                                  · have p4405_0 := h4405c.1
                                    have p4405_1 := h4405c.2.1
                                    have p4405_2 := h4405c.2.2.1
                                    have p4405_3 := h4405c.2.2.2
                                    linarith only [hlam, p4405_0]
                                  · have p4405_0 := h4405c.1
                                    have p4405_1 := h4405c.2.1
                                    have p4405_2 := h4405c.2.2.1
                                    have p4405_3 := h4405c.2.2.2
                                    linarith only [h4347, h4352, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4405_1, u4ehi3]
                                  · have p4405_0 := h4405c.1
                                    have p4405_1 := h4405c.2.1
                                    have p4405_2 := h4405c.2.2.1
                                    have p4405_3 := h4405c.2.2.2
                                    rcases p4405_3 (m.d 0 2) (by simp) with h4426 | h4426
                                    · linarith only [h0, h4426, hlam]
                                    · linarith only [h4336, h4426, hlam]
                                  · have p4405_0 := h4405c.1
                                    have p4405_1 := h4405c.2.1
                                    have p4405_2 := h4405c.2.2.1
                                    have p4405_3 := h4405c.2.2.2
                                    rcases p4405_3 (m.d 0 2) (by simp) with h4429 | h4429
                                    · linarith only [h0, h4429, hlam]
                                    · linarith only [h4337, h4429, hlam]
                                  · have p4405_0 := h4405c.1
                                    have p4405_1 := h4405c.2.1
                                    have p4405_2 := h4405c.2.2.1
                                    have p4405_3 := h4405c.2.2.2
                                    linarith only [h4335, hlam, p4405_0]
                                  · have p4405_0 := h4405c.1
                                    have p4405_1 := h4405c.2.1
                                    have p4405_2 := h4405c.2.2.1
                                    have p4405_3 := h4405c.2.2.2
                                    linarith only [h4340, hlam, p4405_0]
                                  · have p4405_0 := h4405c.1
                                    have p4405_1 := h4405c.2.1
                                    have p4405_2 := h4405c.2.2.1
                                    have p4405_3 := h4405c.2.2.2
                                    linarith only [hlam, p4405_0]
                                  · have p4405_0 := h4405c.1
                                    have p4405_1 := h4405c.2.1
                                    have p4405_2 := h4405c.2.2.1
                                    have p4405_3 := h4405c.2.2.2
                                    linarith only [h4335, h4346, hc02, hlam, hphi, ht0b, ht45, ht5b, p4405_1, u4ehi3]
                                  · have p4405_0 := h4405c.1
                                    have p4405_1 := h4405c.2.1
                                    have p4405_2 := h4405c.2.2.1
                                    have p4405_3 := h4405c.2.2.2
                                    linarith only [h0, h4335, h4347, h4352, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4405_1, u4ehi3]
                                  · have p4405_0 := h4405c.1
                                    have p4405_1 := h4405c.2.1
                                    have p4405_2 := h4405c.2.2.1
                                    have p4405_3 := h4405c.2.2.2
                                    linarith only [h4336, hlam, p4405_0]
                                  · have p4405_0 := h4405c.1
                                    have p4405_1 := h4405c.2.1
                                    have p4405_2 := h4405c.2.2.1
                                    have p4405_3 := h4405c.2.2.2
                                    linarith only [h4341, hlam, p4405_0]
                                  · have p4405_0 := h4405c.1
                                    have p4405_1 := h4405c.2.1
                                    have p4405_2 := h4405c.2.2.1
                                    have p4405_3 := h4405c.2.2.2
                                    linarith only [h4346, hlam, p4405_0]
                                  · have p4405_0 := h4405c.1
                                    have p4405_1 := h4405c.2.1
                                    have p4405_2 := h4405c.2.2.1
                                    have p4405_3 := h4405c.2.2.2
                                    linarith only [hlam, p4405_0]
                                  · have p4405_0 := h4405c.1
                                    have p4405_1 := h4405c.2.1
                                    have p4405_2 := h4405c.2.2.1
                                    have p4405_3 := h4405c.2.2.2
                                    linarith only [h4348, hlam, p4405_0]
                                  · have p4405_0 := h4405c.1
                                    have p4405_1 := h4405c.2.1
                                    have p4405_2 := h4405c.2.2.1
                                    have p4405_3 := h4405c.2.2.2
                                    linarith only [h4337, hlam, p4405_0]
                                  · have p4405_0 := h4405c.1
                                    have p4405_1 := h4405c.2.1
                                    have p4405_2 := h4405c.2.2.1
                                    have p4405_3 := h4405c.2.2.2
                                    linarith only [h4342, hlam, p4405_0]
                                  · have p4405_0 := h4405c.1
                                    have p4405_1 := h4405c.2.1
                                    have p4405_2 := h4405c.2.2.1
                                    have p4405_3 := h4405c.2.2.2
                                    linarith only [h4347, hlam, p4405_0]
                                  · have p4405_0 := h4405c.1
                                    have p4405_1 := h4405c.2.1
                                    have p4405_2 := h4405c.2.2.1
                                    have p4405_3 := h4405c.2.2.2
                                    linarith only [h0, h4337, h4346, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4405_1, u4ehi3]
                                  · have p4405_0 := h4405c.1
                                    have p4405_1 := h4405c.2.1
                                    have p4405_2 := h4405c.2.2.1
                                    have p4405_3 := h4405c.2.2.2
                                    linarith only [hlam, p4405_0]
                                · linarith only [h4404, hlam, p4354_0]
                              · linarith only [h4044, h4403, hlam]
                            · linarith only [h3473, h4402, hlam]
                          · linarith only [h0, h4401, hlam]
                      · have p4354_0 := h4354c.1
                        have p4354_1 := h4354c.2.1
                        have p4354_2 := h4354c.2.2.1
                        have p4354_3 := h4354c.2.2.2
                        linarith only [h4342, hlam, p4354_0]
                      · have p4354_0 := h4354c.1
                        have p4354_1 := h4354c.2.1
                        have p4354_2 := h4354c.2.2.1
                        have p4354_3 := h4354c.2.2.2
                        linarith only [h4344, hlam, p4354_0]
                      · have p4354_0 := h4354c.1
                        have p4354_1 := h4354c.2.1
                        have p4354_2 := h4354c.2.2.1
                        have p4354_3 := h4354c.2.2.2
                        linarith only [h4345, hlam, p4354_0]
                      · have p4354_0 := h4354c.1
                        have p4354_1 := h4354c.2.1
                        have p4354_2 := h4354c.2.2.1
                        have p4354_3 := h4354c.2.2.2
                        linarith only [hlam, p4354_0]
                · linarith only [h3473, h4338, h4340, h4346, h4347, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4456 | h4456
                · linarith only [h4340, h4343, h4346, h4456, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4458 | h4458
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4459 | h4459
                    · rcases h1bigk with h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c
                      · have p4460_0 := h4460c.1
                        have p4460_1 := h4460c.2.1
                        have p4460_2 := h4460c.2.2.1
                        have p4460_3 := h4460c.2.2.2
                        linarith only [hlam, p4460_0]
                      · have p4460_0 := h4460c.1
                        have p4460_1 := h4460c.2.1
                        have p4460_2 := h4460c.2.2.1
                        have p4460_3 := h4460c.2.2.2
                        linarith only [h0, hlam, p4460_0]
                      · have p4460_0 := h4460c.1
                        have p4460_1 := h4460c.2.1
                        have p4460_2 := h4460c.2.2.1
                        have p4460_3 := h4460c.2.2.2
                        linarith only [h3473, hlam, p4460_0]
                      · have p4460_0 := h4460c.1
                        have p4460_1 := h4460c.2.1
                        have p4460_2 := h4460c.2.2.1
                        have p4460_3 := h4460c.2.2.2
                        linarith only [h4044, hlam, p4460_0]
                      · have p4460_0 := h4460c.1
                        have p4460_1 := h4460c.2.1
                        have p4460_2 := h4460c.2.2.1
                        have p4460_3 := h4460c.2.2.2
                        linarith only [h4238, hlam, p4460_0]
                      · have p4460_0 := h4460c.1
                        have p4460_1 := h4460c.2.1
                        have p4460_2 := h4460c.2.2.1
                        have p4460_3 := h4460c.2.2.2
                        rcases p4460_3 (m.d 0 1) (by simp) with h4466 | h4466
                        · linarith only [h4466, hlam, p4460_0]
                        · rcases p4460_3 (m.d 1 2) (by simp) with h4468 | h4468
                          · rcases p4460_3 (m.d 1 3) (by simp) with h4469 | h4469
                            · linarith only [h4340, h4469, hlam]
                            · linarith only [h3473, h4469, hlam]
                          · linarith only [h4468, hlam, p4460_0]
                      · have p4460_0 := h4460c.1
                        have p4460_1 := h4460c.2.1
                        have p4460_2 := h4460c.2.2.1
                        have p4460_3 := h4460c.2.2.2
                        linarith only [hlam, p4460_0]
                      · have p4460_0 := h4460c.1
                        have p4460_1 := h4460c.2.1
                        have p4460_2 := h4460c.2.2.1
                        have p4460_3 := h4460c.2.2.2
                        linarith only [h3473, h4338, h4456, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4460_1]
                      · have p4460_0 := h4460c.1
                        have p4460_1 := h4460c.2.1
                        have p4460_2 := h4460c.2.2.1
                        have p4460_3 := h4460c.2.2.2
                        linarith only [h4044, h4336, h4458, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4460_1, u4ehi4]
                      · have p4460_0 := h4460c.1
                        have p4460_1 := h4460c.2.1
                        have p4460_2 := h4460c.2.2.1
                        have p4460_3 := h4460c.2.2.2
                        linarith only [h4238, hc01, hc12, hlam, hphi, p4460_1]
                      · have p4460_0 := h4460c.1
                        have p4460_1 := h4460c.2.1
                        have p4460_2 := h4460c.2.2.1
                        have p4460_3 := h4460c.2.2.2
                        rcases p4460_3 (m.d 0 1) (by simp) with h4477 | h4477
                        · linarith only [h4477, hlam, p4460_0]
                        · rcases p4460_3 (m.d 1 2) (by simp) with h4479 | h4479
                          · rcases p4460_3 (m.d 1 3) (by simp) with h4480 | h4480
                            · rcases p4460_3 (m.d 1 4) (by simp) with h4481 | h4481
                              · linarith only [h4343, h4481, hlam]
                              · linarith only [h4044, h4481, hlam]
                            · linarith only [h4480, hlam, p4460_0]
                          · linarith only [h0, h4479, hlam]
                      · have p4460_0 := h4460c.1
                        have p4460_1 := h4460c.2.1
                        have p4460_2 := h4460c.2.2.1
                        have p4460_3 := h4460c.2.2.2
                        linarith only [h4340, hlam, p4460_0]
                      · have p4460_0 := h4460c.1
                        have p4460_1 := h4460c.2.1
                        have p4460_2 := h4460c.2.2.1
                        have p4460_3 := h4460c.2.2.2
                        linarith only [hlam, p4460_0]
                      · have p4460_0 := h4460c.1
                        have p4460_1 := h4460c.2.1
                        have p4460_2 := h4460c.2.2.1
                        have p4460_3 := h4460c.2.2.2
                        linarith only [h4044, h4336, h4458, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p4460_1, u4ehi4]
                      · have p4460_0 := h4460c.1
                        have p4460_1 := h4460c.2.1
                        have p4460_2 := h4460c.2.2.1
                        have p4460_3 := h4460c.2.2.2
                        linarith only [h4238, h4340, hc01, hc12, hlam, hphi, p4460_1]
                      · have p4460_0 := h4460c.1
                        have p4460_1 := h4460c.2.1
                        have p4460_2 := h4460c.2.2.1
                        have p4460_3 := h4460c.2.2.2
                        rcases p4460_3 (m.d 0 1) (by simp) with h4490 | h4490
                        · linarith only [h4490, hlam, p4460_0]
                        · rcases p4460_3 (m.d 1 2) (by simp) with h4492 | h4492
                          · rcases p4460_3 (m.d 1 3) (by simp) with h4493 | h4493
                            · rcases p4460_3 (m.d 1 4) (by simp) with h4494 | h4494
                              · rcases p4460_3 (m.d 1 5) (by simp) with h4495 | h4495
                                · linarith only [h4345, h4495, hlam]
                                · linarith only [h4238, h4495, hlam]
                              · linarith only [h4494, hlam, p4460_0]
                            · linarith only [h3473, h4493, hlam]
                          · linarith only [h0, h4492, hlam]
                      · have p4460_0 := h4460c.1
                        have p4460_1 := h4460c.2.1
                        have p4460_2 := h4460c.2.2.1
                        have p4460_3 := h4460c.2.2.2
                        linarith only [h4341, hlam, p4460_0]
                      · have p4460_0 := h4460c.1
                        have p4460_1 := h4460c.2.1
                        have p4460_2 := h4460c.2.2.1
                        have p4460_3 := h4460c.2.2.2
                        linarith only [h4343, hlam, p4460_1]
                      · have p4460_0 := h4460c.1
                        have p4460_1 := h4460c.2.1
                        have p4460_2 := h4460c.2.2.1
                        have p4460_3 := h4460c.2.2.2
                        linarith only [hlam, p4460_0]
                      · have p4460_0 := h4460c.1
                        have p4460_1 := h4460c.2.1
                        have p4460_2 := h4460c.2.2.1
                        have p4460_3 := h4460c.2.2.2
                        linarith only [h4238, hc01, hc14, hlam, hphi, p4460_1]
                      · have p4460_0 := h4460c.1
                        have p4460_1 := h4460c.2.1
                        have p4460_2 := h4460c.2.2.1
                        have p4460_3 := h4460c.2.2.2
                        rcases p4460_3 (m.d 0 1) (by simp) with h4505 | h4505
                        · linarith only [h4505, hlam, p4460_0]
                        · rcases p4460_3 (m.d 1 2) (by simp) with h4507 | h4507
                          · rcases p4460_3 (m.d 1 3) (by simp) with h4508 | h4508
                            · rcases p4460_3 (m.d 1 4) (by simp) with h4509 | h4509
                              · rcases p4460_3 (m.d 1 5) (by simp) with h4510 | h4510
                                · rcases h2bigk with h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c | h4511c
                                  · have p4511_0 := h4511c.1
                                    have p4511_1 := h4511c.2.1
                                    have p4511_2 := h4511c.2.2.1
                                    have p4511_3 := h4511c.2.2.2
                                    linarith only [hlam, p4511_0]
                                  · have p4511_0 := h4511c.1
                                    have p4511_1 := h4511c.2.1
                                    have p4511_2 := h4511c.2.2.1
                                    have p4511_3 := h4511c.2.2.2
                                    linarith only [h0, hlam, p4511_0]
                                  · have p4511_0 := h4511c.1
                                    have p4511_1 := h4511c.2.1
                                    have p4511_2 := h4511c.2.2.1
                                    have p4511_3 := h4511c.2.2.2
                                    rcases p4511_3 (m.d 0 2) (by simp) with h4514 | h4514
                                    · rcases p4511_3 (m.d 1 2) (by simp) with h4515 | h4515
                                      · rcases p4511_3 (m.d 2 3) (by simp) with h4516 | h4516
                                        · linarith only [h4516, hlam, p4511_0]
                                        · rcases p4511_3 (m.d 2 4) (by simp) with h4518 | h4518
                                          · linarith only [h4336, h4518, hlam]
                                          · linarith only [h4346, h4518, hlam]
                                      · linarith only [h4340, h4515, hlam]
                                    · linarith only [h4514, hlam, p4511_0]
                                  · have p4511_0 := h4511c.1
                                    have p4511_1 := h4511c.2.1
                                    have p4511_2 := h4511c.2.2.1
                                    have p4511_3 := h4511c.2.2.2
                                    linarith only [h0, h4458, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4511_1, u4ehi4]
                                  · have p4511_0 := h4511c.1
                                    have p4511_1 := h4511c.2.1
                                    have p4511_2 := h4511c.2.2.1
                                    have p4511_3 := h4511c.2.2.2
                                    rcases p4511_3 (m.d 0 2) (by simp) with h4524 | h4524
                                    · rcases p4511_3 (m.d 1 2) (by simp) with h4525 | h4525
                                      · rcases p4511_3 (m.d 2 3) (by simp) with h4526 | h4526
                                        · linarith only [h4335, h4526, hlam]
                                        · rcases p4511_3 (m.d 2 4) (by simp) with h4528 | h4528
                                          · linarith only [h4336, h4528, hlam]
                                          · linarith only [h4458, h4528, hlam]
                                      · linarith only [h4342, h4525, hlam]
                                    · linarith only [h4524, hlam, p4511_0]
                                  · have p4511_0 := h4511c.1
                                    have p4511_1 := h4511c.2.1
                                    have p4511_2 := h4511c.2.2.1
                                    have p4511_3 := h4511c.2.2.2
                                    linarith only [h4335, h4338, hc12, hlam, hphi, ht01, ht0b, ht5b, p4511_1, u5ehi3]
                                  · have p4511_0 := h4511c.1
                                    have p4511_1 := h4511c.2.1
                                    have p4511_2 := h4511c.2.2.1
                                    have p4511_3 := h4511c.2.2.2
                                    linarith only [hlam, p4511_0]
                                  · have p4511_0 := h4511c.1
                                    have p4511_1 := h4511c.2.1
                                    have p4511_2 := h4511c.2.2.1
                                    have p4511_3 := h4511c.2.2.2
                                    rcases p4511_3 (m.d 0 2) (by simp) with h4535 | h4535
                                    · linarith only [h0, h4535, hlam]
                                    · linarith only [h4335, h4535, hlam]
                                  · have p4511_0 := h4511c.1
                                    have p4511_1 := h4511c.2.1
                                    have p4511_2 := h4511c.2.2.1
                                    have p4511_3 := h4511c.2.2.2
                                    linarith only [h4458, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4511_1, u4ehi4]
                                  · have p4511_0 := h4511c.1
                                    have p4511_1 := h4511c.2.1
                                    have p4511_2 := h4511c.2.2.1
                                    have p4511_3 := h4511c.2.2.2
                                    rcases p4511_3 (m.d 0 2) (by simp) with h4539 | h4539
                                    · linarith only [h0, h4539, hlam]
                                    · linarith only [h4337, h4539, hlam]
                                  · have p4511_0 := h4511c.1
                                    have p4511_1 := h4511c.2.1
                                    have p4511_2 := h4511c.2.2.1
                                    have p4511_3 := h4511c.2.2.2
                                    linarith only [h4335, hlam, p4511_0]
                                  · have p4511_0 := h4511c.1
                                    have p4511_1 := h4511c.2.1
                                    have p4511_2 := h4511c.2.2.1
                                    have p4511_3 := h4511c.2.2.2
                                    linarith only [h4340, hlam, p4511_0]
                                  · have p4511_0 := h4511c.1
                                    have p4511_1 := h4511c.2.1
                                    have p4511_2 := h4511c.2.2.1
                                    have p4511_3 := h4511c.2.2.2
                                    linarith only [hlam, p4511_0]
                                  · have p4511_0 := h4511c.1
                                    have p4511_1 := h4511c.2.1
                                    have p4511_2 := h4511c.2.2.1
                                    have p4511_3 := h4511c.2.2.2
                                    linarith only [h4346, hlam, p4511_1]
                                  · have p4511_0 := h4511c.1
                                    have p4511_1 := h4511c.2.1
                                    have p4511_2 := h4511c.2.2.1
                                    have p4511_3 := h4511c.2.2.2
                                    linarith only [h4456, hlam, p4511_1]
                                  · have p4511_0 := h4511c.1
                                    have p4511_1 := h4511c.2.1
                                    have p4511_2 := h4511c.2.2.1
                                    have p4511_3 := h4511c.2.2.2
                                    linarith only [h4336, hlam, p4511_0]
                                  · have p4511_0 := h4511c.1
                                    have p4511_1 := h4511c.2.1
                                    have p4511_2 := h4511c.2.2.1
                                    have p4511_3 := h4511c.2.2.2
                                    linarith only [h4341, hlam, p4511_0]
                                  · have p4511_0 := h4511c.1
                                    have p4511_1 := h4511c.2.1
                                    have p4511_2 := h4511c.2.2.1
                                    have p4511_3 := h4511c.2.2.2
                                    rcases p4511_3 (m.d 0 2) (by simp) with h4549 | h4549
                                    · rcases p4511_3 (m.d 1 2) (by simp) with h4550 | h4550
                                      · rcases p4511_3 (m.d 2 3) (by simp) with h4551 | h4551
                                        · linarith only [h4346, h4551, hlam]
                                        · rcases p4511_3 (m.d 2 4) (by simp) with h4553 | h4553
                                          · rcases p4511_3 (m.d 2 5) (by simp) with h4554 | h4554
                                            · linarith only [h4458, h4554, hlam]
                                            · linarith only [h4456, h4554, hlam]
                                          · linarith only [h4346, h4553, hlam]
                                      · linarith only [h4340, h4550, hlam]
                                    · linarith only [h4335, h4549, hlam]
                                  · have p4511_0 := h4511c.1
                                    have p4511_1 := h4511c.2.1
                                    have p4511_2 := h4511c.2.2.1
                                    have p4511_3 := h4511c.2.2.2
                                    linarith only [hlam, p4511_0]
                                  · have p4511_0 := h4511c.1
                                    have p4511_1 := h4511c.2.1
                                    have p4511_2 := h4511c.2.2.1
                                    have p4511_3 := h4511c.2.2.2
                                    linarith only [h4336, h4458, hc02, hlam, hphi, ht0b, ht45, ht5b, p4511_1, u4ehi4]
                                  · have p4511_0 := h4511c.1
                                    have p4511_1 := h4511c.2.1
                                    have p4511_2 := h4511c.2.2.1
                                    have p4511_3 := h4511c.2.2.2
                                    linarith only [h4337, hlam, p4511_0]
                                  · have p4511_0 := h4511c.1
                                    have p4511_1 := h4511c.2.1
                                    have p4511_2 := h4511c.2.2.1
                                    have p4511_3 := h4511c.2.2.2
                                    linarith only [h4342, hlam, p4511_0]
                                  · have p4511_0 := h4511c.1
                                    have p4511_1 := h4511c.2.1
                                    have p4511_2 := h4511c.2.2.1
                                    have p4511_3 := h4511c.2.2.2
                                    rcases p4511_3 (m.d 0 2) (by simp) with h4564 | h4564
                                    · rcases p4511_3 (m.d 1 2) (by simp) with h4565 | h4565
                                      · rcases p4511_3 (m.d 2 3) (by simp) with h4566 | h4566
                                        · linarith only [h4456, h4566, hlam]
                                        · rcases p4511_3 (m.d 2 4) (by simp) with h4568 | h4568
                                          · rcases p4511_3 (m.d 2 5) (by simp) with h4569 | h4569
                                            · rcases h5bigk with h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c | h4570c
                                              · have p4570_0 := h4570c.1
                                                have p4570_1 := h4570c.2.1
                                                have p4570_2 := h4570c.2.2.1
                                                have p4570_3 := h4570c.2.2.2
                                                linarith only [hlam, p4570_0]
                                              · have p4570_0 := h4570c.1
                                                have p4570_1 := h4570c.2.1
                                                have p4570_2 := h4570c.2.2.1
                                                have p4570_3 := h4570c.2.2.2
                                                linarith only [h4238, hlam, p4570_1]
                                              · have p4570_0 := h4570c.1
                                                have p4570_1 := h4570c.2.1
                                                have p4570_2 := h4570c.2.2.1
                                                have p4570_3 := h4570c.2.2.2
                                                linarith only [h4339, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4511_1, p4570_1]
                                              · have p4570_0 := h4570c.1
                                                have p4570_1 := h4570c.2.1
                                                have p4570_2 := h4570c.2.2.1
                                                have p4570_3 := h4570c.2.2.2
                                                linarith only [h3473, h4338, h4340, h4456, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4511_1, p4570_1]
                                              · have p4570_0 := h4570c.1
                                                have p4570_1 := h4570c.2.1
                                                have p4570_2 := h4570c.2.2.1
                                                have p4570_3 := h4570c.2.2.2
                                                rcases p4570_3 (m.d 0 5) (by simp) with h4575 | h4575
                                                · rcases p4570_3 (m.d 1 5) (by simp) with h4576 | h4576
                                                  · rcases p4570_3 (m.d 2 5) (by simp) with h4577 | h4577
                                                    · linarith only [h4337, h4577, hlam]
                                                    · linarith only [h4458, h4577, hlam]
                                                  · linarith only [h4345, h4576, hlam]
                                                · linarith only [h4339, h4575, hlam]
                                              · have p4570_0 := h4570c.1
                                                have p4570_1 := h4570c.2.1
                                                have p4570_2 := h4570c.2.2.1
                                                have p4570_3 := h4570c.2.2.2
                                                linarith only [h4337, h4340, h4343, h4345, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4511_1, p4570_1]
                                              · have p4570_0 := h4570c.1
                                                have p4570_1 := h4570c.2.1
                                                have p4570_2 := h4570c.2.2.1
                                                have p4570_3 := h4570c.2.2.2
                                                linarith only [hlam, p4570_0]
                                              · have p4570_0 := h4570c.1
                                                have p4570_1 := h4570c.2.1
                                                have p4570_2 := h4570c.2.2.1
                                                have p4570_3 := h4570c.2.2.2
                                                linarith only [h4340, h4343, h4345, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4511_1, p4570_1]
                                              · have p4570_0 := h4570c.1
                                                have p4570_1 := h4570c.2.1
                                                have p4570_2 := h4570c.2.2.1
                                                have p4570_3 := h4570c.2.2.2
                                                linarith only [h4340, h4343, h4345, h4456, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4511_1, p4570_1]
                                              · have p4570_0 := h4570c.1
                                                have p4570_1 := h4570c.2.1
                                                have p4570_2 := h4570c.2.2.1
                                                have p4570_3 := h4570c.2.2.2
                                                rcases p4570_3 (m.d 0 5) (by simp) with h4586 | h4586
                                                · linarith only [h4238, h4586, hlam]
                                                · linarith only [h4339, h4586, hlam]
                                              · have p4570_0 := h4570c.1
                                                have p4570_1 := h4570c.2.1
                                                have p4570_2 := h4570c.2.2.1
                                                have p4570_3 := h4570c.2.2.2
                                                linarith only [h4337, hlam, p4570_1]
                                              · have p4570_0 := h4570c.1
                                                have p4570_1 := h4570c.2.1
                                                have p4570_2 := h4570c.2.2.1
                                                have p4570_3 := h4570c.2.2.2
                                                linarith only [h4342, hlam, p4570_1]
                                              · have p4570_0 := h4570c.1
                                                have p4570_1 := h4570c.2.1
                                                have p4570_2 := h4570c.2.2.1
                                                have p4570_3 := h4570c.2.2.2
                                                linarith only [hlam, p4570_0]
                                              · have p4570_0 := h4570c.1
                                                have p4570_1 := h4570c.2.1
                                                have p4570_2 := h4570c.2.2.1
                                                have p4570_3 := h4570c.2.2.2
                                                linarith only [h4456, hlam, p4570_1]
                                              · have p4570_0 := h4570c.1
                                                have p4570_1 := h4570c.2.1
                                                have p4570_2 := h4570c.2.2.1
                                                have p4570_3 := h4570c.2.2.2
                                                linarith only [h0, h4337, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4570_1, u4ehi4]
                                              · have p4570_0 := h4570c.1
                                                have p4570_1 := h4570c.2.1
                                                have p4570_2 := h4570c.2.2.1
                                                have p4570_3 := h4570c.2.2.2
                                                linarith only [h4338, hlam, p4570_1]
                                              · have p4570_0 := h4570c.1
                                                have p4570_1 := h4570c.2.1
                                                have p4570_2 := h4570c.2.2.1
                                                have p4570_3 := h4570c.2.2.2
                                                linarith only [h4344, hlam, p4570_1]
                                              · have p4570_0 := h4570c.1
                                                have p4570_1 := h4570c.2.1
                                                have p4570_2 := h4570c.2.2.1
                                                have p4570_3 := h4570c.2.2.2
                                                linarith only [h3473, h4338, h4340, hc12, hlam, hphi, ht01, ht0b, ht5b, p4570_1, u5ehi2]
                                              · have p4570_0 := h4570c.1
                                                have p4570_1 := h4570c.2.1
                                                have p4570_2 := h4570c.2.2.1
                                                have p4570_3 := h4570c.2.2.2
                                                linarith only [hlam, p4570_0]
                                              · have p4570_0 := h4570c.1
                                                have p4570_1 := h4570c.2.1
                                                have p4570_2 := h4570c.2.2.1
                                                have p4570_3 := h4570c.2.2.2
                                                linarith only [h3473, h4338, h4340, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4570_1, u4ehi4]
                                              · have p4570_0 := h4570c.1
                                                have p4570_1 := h4570c.2.1
                                                have p4570_2 := h4570c.2.2.1
                                                have p4570_3 := h4570c.2.2.2
                                                linarith only [h4339, hlam, p4570_1]
                                              · have p4570_0 := h4570c.1
                                                have p4570_1 := h4570c.2.1
                                                have p4570_2 := h4570c.2.2.1
                                                have p4570_3 := h4570c.2.2.2
                                                linarith only [h4345, hlam, p4570_1]
                                              · have p4570_0 := h4570c.1
                                                have p4570_1 := h4570c.2.1
                                                have p4570_2 := h4570c.2.2.1
                                                have p4570_3 := h4570c.2.2.2
                                                linarith only [h4458, hlam, p4570_1]
                                              · have p4570_0 := h4570c.1
                                                have p4570_1 := h4570c.2.1
                                                have p4570_2 := h4570c.2.2.1
                                                have p4570_3 := h4570c.2.2.2
                                                linarith only [h4459, hlam, p4570_1]
                                              · have p4570_0 := h4570c.1
                                                have p4570_1 := h4570c.2.1
                                                have p4570_2 := h4570c.2.2.1
                                                have p4570_3 := h4570c.2.2.2
                                                linarith only [hlam, p4570_0]
                                            · linarith only [h4456, h4569, hlam]
                                          · linarith only [h4346, h4568, hlam]
                                      · linarith only [h4340, h4565, hlam]
                                    · linarith only [h4335, h4564, hlam]
                                  · have p4511_0 := h4511c.1
                                    have p4511_1 := h4511c.2.1
                                    have p4511_2 := h4511c.2.2.1
                                    have p4511_3 := h4511c.2.2.2
                                    linarith only [h4458, hlam, p4511_1]
                                  · have p4511_0 := h4511c.1
                                    have p4511_1 := h4511c.2.1
                                    have p4511_2 := h4511c.2.2.1
                                    have p4511_3 := h4511c.2.2.2
                                    linarith only [hlam, p4511_0]
                                · linarith only [h4510, hlam, p4460_0]
                              · linarith only [h4044, h4509, hlam]
                            · linarith only [h3473, h4508, hlam]
                          · linarith only [h0, h4507, hlam]
                      · have p4460_0 := h4460c.1
                        have p4460_1 := h4460c.2.1
                        have p4460_2 := h4460c.2.2.1
                        have p4460_3 := h4460c.2.2.2
                        linarith only [h4342, hlam, p4460_0]
                      · have p4460_0 := h4460c.1
                        have p4460_1 := h4460c.2.1
                        have p4460_2 := h4460c.2.2.1
                        have p4460_3 := h4460c.2.2.2
                        linarith only [h4344, hlam, p4460_0]
                      · have p4460_0 := h4460c.1
                        have p4460_1 := h4460c.2.1
                        have p4460_2 := h4460c.2.2.1
                        have p4460_3 := h4460c.2.2.2
                        linarith only [h4345, hlam, p4460_0]
                      · have p4460_0 := h4460c.1
                        have p4460_1 := h4460c.2.1
                        have p4460_2 := h4460c.2.2.1
                        have p4460_3 := h4460c.2.2.2
                        linarith only [hlam, p4460_0]
                    · linarith only [h4346, h4458, h4459, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4619 | h4619
                    · linarith only [h4340, h4343, h4458, h4619, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                    · rcases h1bigk with h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c | h4621c
                      · have p4621_0 := h4621c.1
                        have p4621_1 := h4621c.2.1
                        have p4621_2 := h4621c.2.2.1
                        have p4621_3 := h4621c.2.2.2
                        linarith only [hlam, p4621_0]
                      · have p4621_0 := h4621c.1
                        have p4621_1 := h4621c.2.1
                        have p4621_2 := h4621c.2.2.1
                        have p4621_3 := h4621c.2.2.2
                        linarith only [h0, hlam, p4621_0]
                      · have p4621_0 := h4621c.1
                        have p4621_1 := h4621c.2.1
                        have p4621_2 := h4621c.2.2.1
                        have p4621_3 := h4621c.2.2.2
                        linarith only [h3473, hlam, p4621_0]
                      · have p4621_0 := h4621c.1
                        have p4621_1 := h4621c.2.1
                        have p4621_2 := h4621c.2.2.1
                        have p4621_3 := h4621c.2.2.2
                        linarith only [h4044, hlam, p4621_0]
                      · have p4621_0 := h4621c.1
                        have p4621_1 := h4621c.2.1
                        have p4621_2 := h4621c.2.2.1
                        have p4621_3 := h4621c.2.2.2
                        linarith only [h4238, hlam, p4621_0]
                      · have p4621_0 := h4621c.1
                        have p4621_1 := h4621c.2.1
                        have p4621_2 := h4621c.2.2.1
                        have p4621_3 := h4621c.2.2.2
                        rcases p4621_3 (m.d 0 1) (by simp) with h4627 | h4627
                        · linarith only [h4627, hlam, p4621_0]
                        · rcases p4621_3 (m.d 1 2) (by simp) with h4629 | h4629
                          · rcases p4621_3 (m.d 1 3) (by simp) with h4630 | h4630
                            · linarith only [h4340, h4630, hlam]
                            · linarith only [h3473, h4630, hlam]
                          · linarith only [h4629, hlam, p4621_0]
                      · have p4621_0 := h4621c.1
                        have p4621_1 := h4621c.2.1
                        have p4621_2 := h4621c.2.2.1
                        have p4621_3 := h4621c.2.2.2
                        linarith only [hlam, p4621_0]
                      · have p4621_0 := h4621c.1
                        have p4621_1 := h4621c.2.1
                        have p4621_2 := h4621c.2.2.1
                        have p4621_3 := h4621c.2.2.2
                        linarith only [h3473, hc01, hc12, hlam, hphi, p4621_1]
                      · have p4621_0 := h4621c.1
                        have p4621_1 := h4621c.2.1
                        have p4621_2 := h4621c.2.2.1
                        have p4621_3 := h4621c.2.2.2
                        linarith only [h4044, h4339, h4346, h4619, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4621_1]
                      · have p4621_0 := h4621c.1
                        have p4621_1 := h4621c.2.1
                        have p4621_2 := h4621c.2.2.1
                        have p4621_3 := h4621c.2.2.2
                        linarith only [h4238, h4339, h4346, h4619, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4621_1]
                      · have p4621_0 := h4621c.1
                        have p4621_1 := h4621c.2.1
                        have p4621_2 := h4621c.2.2.1
                        have p4621_3 := h4621c.2.2.2
                        rcases p4621_3 (m.d 0 1) (by simp) with h4638 | h4638
                        · linarith only [h4638, hlam, p4621_0]
                        · rcases p4621_3 (m.d 1 2) (by simp) with h4640 | h4640
                          · rcases p4621_3 (m.d 1 3) (by simp) with h4641 | h4641
                            · rcases p4621_3 (m.d 1 4) (by simp) with h4642 | h4642
                              · linarith only [h4343, h4642, hlam]
                              · linarith only [h4044, h4642, hlam]
                            · linarith only [h4641, hlam, p4621_0]
                          · linarith only [h0, h4640, hlam]
                      · have p4621_0 := h4621c.1
                        have p4621_1 := h4621c.2.1
                        have p4621_2 := h4621c.2.2.1
                        have p4621_3 := h4621c.2.2.2
                        linarith only [h4340, hlam, p4621_0]
                      · have p4621_0 := h4621c.1
                        have p4621_1 := h4621c.2.1
                        have p4621_2 := h4621c.2.2.1
                        have p4621_3 := h4621c.2.2.2
                        linarith only [hlam, p4621_0]
                      · have p4621_0 := h4621c.1
                        have p4621_1 := h4621c.2.1
                        have p4621_2 := h4621c.2.2.1
                        have p4621_3 := h4621c.2.2.2
                        linarith only [h4044, h4339, h4346, h4619, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4621_1]
                      · have p4621_0 := h4621c.1
                        have p4621_1 := h4621c.2.1
                        have p4621_2 := h4621c.2.2.1
                        have p4621_3 := h4621c.2.2.2
                        linarith only [h4238, h4339, h4340, h4346, h4619, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4621_1]
                      · have p4621_0 := h4621c.1
                        have p4621_1 := h4621c.2.1
                        have p4621_2 := h4621c.2.2.1
                        have p4621_3 := h4621c.2.2.2
                        rcases p4621_3 (m.d 0 1) (by simp) with h4651 | h4651
                        · linarith only [h4651, hlam, p4621_0]
                        · rcases p4621_3 (m.d 1 2) (by simp) with h4653 | h4653
                          · rcases p4621_3 (m.d 1 3) (by simp) with h4654 | h4654
                            · rcases p4621_3 (m.d 1 4) (by simp) with h4655 | h4655
                              · rcases p4621_3 (m.d 1 5) (by simp) with h4656 | h4656
                                · linarith only [h4345, h4656, hlam]
                                · linarith only [h4238, h4656, hlam]
                              · linarith only [h4655, hlam, p4621_0]
                            · linarith only [h3473, h4654, hlam]
                          · linarith only [h0, h4653, hlam]
                      · have p4621_0 := h4621c.1
                        have p4621_1 := h4621c.2.1
                        have p4621_2 := h4621c.2.2.1
                        have p4621_3 := h4621c.2.2.2
                        linarith only [h4341, hlam, p4621_0]
                      · have p4621_0 := h4621c.1
                        have p4621_1 := h4621c.2.1
                        have p4621_2 := h4621c.2.2.1
                        have p4621_3 := h4621c.2.2.2
                        linarith only [h4343, hlam, p4621_1]
                      · have p4621_0 := h4621c.1
                        have p4621_1 := h4621c.2.1
                        have p4621_2 := h4621c.2.2.1
                        have p4621_3 := h4621c.2.2.2
                        linarith only [hlam, p4621_0]
                      · have p4621_0 := h4621c.1
                        have p4621_1 := h4621c.2.1
                        have p4621_2 := h4621c.2.2.1
                        have p4621_3 := h4621c.2.2.2
                        linarith only [h4238, h4339, h4346, h4619, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4621_1]
                      · have p4621_0 := h4621c.1
                        have p4621_1 := h4621c.2.1
                        have p4621_2 := h4621c.2.2.1
                        have p4621_3 := h4621c.2.2.2
                        rcases p4621_3 (m.d 0 1) (by simp) with h4666 | h4666
                        · linarith only [h4666, hlam, p4621_0]
                        · rcases p4621_3 (m.d 1 2) (by simp) with h4668 | h4668
                          · rcases p4621_3 (m.d 1 3) (by simp) with h4669 | h4669
                            · rcases p4621_3 (m.d 1 4) (by simp) with h4670 | h4670
                              · rcases p4621_3 (m.d 1 5) (by simp) with h4671 | h4671
                                · rcases h2bigk with h4672c | h4672c | h4672c | h4672c | h4672c | h4672c | h4672c | h4672c | h4672c | h4672c | h4672c | h4672c | h4672c | h4672c | h4672c | h4672c | h4672c | h4672c | h4672c | h4672c | h4672c | h4672c | h4672c | h4672c | h4672c
                                  · have p4672_0 := h4672c.1
                                    have p4672_1 := h4672c.2.1
                                    have p4672_2 := h4672c.2.2.1
                                    have p4672_3 := h4672c.2.2.2
                                    linarith only [hlam, p4672_0]
                                  · have p4672_0 := h4672c.1
                                    have p4672_1 := h4672c.2.1
                                    have p4672_2 := h4672c.2.2.1
                                    have p4672_3 := h4672c.2.2.2
                                    linarith only [h0, hlam, p4672_0]
                                  · have p4672_0 := h4672c.1
                                    have p4672_1 := h4672c.2.1
                                    have p4672_2 := h4672c.2.2.1
                                    have p4672_3 := h4672c.2.2.2
                                    linarith only [h4336, h4339, h4346, h4619, hlam, p4672_2]
                                  · have p4672_0 := h4672c.1
                                    have p4672_1 := h4672c.2.1
                                    have p4672_2 := h4672c.2.2.1
                                    have p4672_3 := h4672c.2.2.2
                                    rcases p4672_3 (m.d 0 2) (by simp) with h4676 | h4676
                                    · rcases p4672_3 (m.d 1 2) (by simp) with h4677 | h4677
                                      · rcases p4672_3 (m.d 2 3) (by simp) with h4678 | h4678
                                        · linarith only [h4335, h4678, hlam]
                                        · rcases p4672_3 (m.d 2 4) (by simp) with h4680 | h4680
                                          · linarith only [h4680, hlam, p4672_0]
                                          · rcases p4672_3 (m.d 2 5) (by simp) with h4682 | h4682
                                            · linarith only [h4337, h4682, hlam]
                                            · linarith only [h4458, h4682, hlam]
                                      · linarith only [h4341, h4677, hlam]
                                    · linarith only [h4676, hlam, p4672_0]
                                  · have p4672_0 := h4672c.1
                                    have p4672_1 := h4672c.2.1
                                    have p4672_2 := h4672c.2.2.1
                                    have p4672_3 := h4672c.2.2.2
                                    rcases p4672_3 (m.d 0 2) (by simp) with h4687 | h4687
                                    · rcases p4672_3 (m.d 1 2) (by simp) with h4688 | h4688
                                      · rcases p4672_3 (m.d 2 3) (by simp) with h4689 | h4689
                                        · linarith only [h4335, h4689, hlam]
                                        · rcases p4672_3 (m.d 2 4) (by simp) with h4691 | h4691
                                          · linarith only [h4336, h4691, hlam]
                                          · rcases p4672_3 (m.d 2 5) (by simp) with h4693 | h4693
                                            · linarith only [h4693, hlam, p4672_0]
                                            · rcases h5bigk with h4695c | h4695c | h4695c | h4695c | h4695c | h4695c | h4695c | h4695c | h4695c | h4695c | h4695c | h4695c | h4695c | h4695c | h4695c | h4695c | h4695c | h4695c | h4695c | h4695c | h4695c | h4695c | h4695c | h4695c | h4695c
                                              · have p4695_0 := h4695c.1
                                                have p4695_1 := h4695c.2.1
                                                have p4695_2 := h4695c.2.2.1
                                                have p4695_3 := h4695c.2.2.2
                                                linarith only [hlam, p4695_0]
                                              · have p4695_0 := h4695c.1
                                                have p4695_1 := h4695c.2.1
                                                have p4695_2 := h4695c.2.2.1
                                                have p4695_3 := h4695c.2.2.2
                                                linarith only [h4238, hlam, p4695_1]
                                              · have p4695_0 := h4695c.1
                                                have p4695_1 := h4695c.2.1
                                                have p4695_2 := h4695c.2.2.1
                                                have p4695_3 := h4695c.2.2.2
                                                rcases p4695_3 (m.d 0 5) (by simp) with h4698 | h4698
                                                · rcases p4695_3 (m.d 1 5) (by simp) with h4699 | h4699
                                                  · rcases p4695_3 (m.d 2 5) (by simp) with h4700 | h4700
                                                    · linarith only [h4337, h4700, hlam]
                                                    · rcases p4695_3 (m.d 3 5) (by simp) with h4702 | h4702
                                                      · linarith only [h4338, h4702, hlam]
                                                      · linarith only [h4456, h4702, hlam]
                                                  · linarith only [h4342, h4699, hlam]
                                                · linarith only [h4337, h4698, hlam]
                                              · have p4695_0 := h4695c.1
                                                have p4695_1 := h4695c.2.1
                                                have p4695_2 := h4695c.2.2.1
                                                have p4695_3 := h4695c.2.2.2
                                                rcases p4695_3 (m.d 0 5) (by simp) with h4707 | h4707
                                                · rcases p4695_3 (m.d 1 5) (by simp) with h4708 | h4708
                                                  · rcases p4695_3 (m.d 2 5) (by simp) with h4709 | h4709
                                                    · linarith only [h4337, h4709, hlam]
                                                    · rcases p4695_3 (m.d 3 5) (by simp) with h4711 | h4711
                                                      · linarith only [h4338, h4711, hlam]
                                                      · rcases p4695_3 (m.d 4 5) (by simp) with h4713 | h4713
                                                        · linarith only [h4339, h4713, hlam]
                                                        · linarith only [h4619, h4713, hlam]
                                                  · linarith only [h4344, h4708, hlam]
                                                · linarith only [h4338, h4707, hlam]
                                              · have p4695_0 := h4695c.1
                                                have p4695_1 := h4695c.2.1
                                                have p4695_2 := h4695c.2.2.1
                                                have p4695_3 := h4695c.2.2.2
                                                linarith only [h4335, h4338, h4346, h4619, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4695_1]
                                              · have p4695_0 := h4695c.1
                                                have p4695_1 := h4695c.2.1
                                                have p4695_2 := h4695c.2.2.1
                                                have p4695_3 := h4695c.2.2.2
                                                linarith only [h4339, h4346, h4619, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4695_1]
                                              · have p4695_0 := h4695c.1
                                                have p4695_1 := h4695c.2.1
                                                have p4695_2 := h4695c.2.2.1
                                                have p4695_3 := h4695c.2.2.2
                                                linarith only [hlam, p4695_0]
                                              · have p4695_0 := h4695c.1
                                                have p4695_1 := h4695c.2.1
                                                have p4695_2 := h4695c.2.2.1
                                                have p4695_3 := h4695c.2.2.2
                                                rcases p4695_3 (m.d 0 5) (by simp) with h4721 | h4721
                                                · linarith only [h4238, h4721, hlam]
                                                · linarith only [h4337, h4721, hlam]
                                              · have p4695_0 := h4695c.1
                                                have p4695_1 := h4695c.2.1
                                                have p4695_2 := h4695c.2.2.1
                                                have p4695_3 := h4695c.2.2.2
                                                rcases p4695_3 (m.d 0 5) (by simp) with h4724 | h4724
                                                · linarith only [h4238, h4724, hlam]
                                                · linarith only [h4338, h4724, hlam]
                                              · have p4695_0 := h4695c.1
                                                have p4695_1 := h4695c.2.1
                                                have p4695_2 := h4695c.2.2.1
                                                have p4695_3 := h4695c.2.2.2
                                                linarith only [h4340, h4343, h4345, h4346, h4619, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4695_1]
                                              · have p4695_0 := h4695c.1
                                                have p4695_1 := h4695c.2.1
                                                have p4695_2 := h4695c.2.2.1
                                                have p4695_3 := h4695c.2.2.2
                                                linarith only [h4337, hlam, p4695_1]
                                              · have p4695_0 := h4695c.1
                                                have p4695_1 := h4695c.2.1
                                                have p4695_2 := h4695c.2.2.1
                                                have p4695_3 := h4695c.2.2.2
                                                linarith only [h4342, hlam, p4695_1]
                                              · have p4695_0 := h4695c.1
                                                have p4695_1 := h4695c.2.1
                                                have p4695_2 := h4695c.2.2.1
                                                have p4695_3 := h4695c.2.2.2
                                                linarith only [hlam, p4695_0]
                                              · have p4695_0 := h4695c.1
                                                have p4695_1 := h4695c.2.1
                                                have p4695_2 := h4695c.2.2.1
                                                have p4695_3 := h4695c.2.2.2
                                                linarith only [h4456, hlam, p4695_1]
                                              · have p4695_0 := h4695c.1
                                                have p4695_1 := h4695c.2.1
                                                have p4695_2 := h4695c.2.2.1
                                                have p4695_3 := h4695c.2.2.2
                                                linarith only [h4458, hlam, p4695_0]
                                              · have p4695_0 := h4695c.1
                                                have p4695_1 := h4695c.2.1
                                                have p4695_2 := h4695c.2.2.1
                                                have p4695_3 := h4695c.2.2.2
                                                linarith only [h4338, hlam, p4695_1]
                                              · have p4695_0 := h4695c.1
                                                have p4695_1 := h4695c.2.1
                                                have p4695_2 := h4695c.2.2.1
                                                have p4695_3 := h4695c.2.2.2
                                                linarith only [h4344, hlam, p4695_1]
                                              · have p4695_0 := h4695c.1
                                                have p4695_1 := h4695c.2.1
                                                have p4695_2 := h4695c.2.2.1
                                                have p4695_3 := h4695c.2.2.2
                                                linarith only [h0, h4335, h4338, h4458, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4695_1, u4ehi2]
                                              · have p4695_0 := h4695c.1
                                                have p4695_1 := h4695c.2.1
                                                have p4695_2 := h4695c.2.2.1
                                                have p4695_3 := h4695c.2.2.2
                                                linarith only [hlam, p4695_0]
                                              · have p4695_0 := h4695c.1
                                                have p4695_1 := h4695c.2.1
                                                have p4695_2 := h4695c.2.2.1
                                                have p4695_3 := h4695c.2.2.2
                                                linarith only [h4619, hlam, p4695_0]
                                              · have p4695_0 := h4695c.1
                                                have p4695_1 := h4695c.2.1
                                                have p4695_2 := h4695c.2.2.1
                                                have p4695_3 := h4695c.2.2.2
                                                linarith only [h4339, hlam, p4695_1]
                                              · have p4695_0 := h4695c.1
                                                have p4695_1 := h4695c.2.1
                                                have p4695_2 := h4695c.2.2.1
                                                have p4695_3 := h4695c.2.2.2
                                                linarith only [h4345, hlam, p4695_1]
                                              · have p4695_0 := h4695c.1
                                                have p4695_1 := h4695c.2.1
                                                have p4695_2 := h4695c.2.2.1
                                                have p4695_3 := h4695c.2.2.2
                                                linarith only [h4339, h4458, hc04, hlam, hphi, ht0b, ht45, ht5b, p4695_1, u4ehi2]
                                              · have p4695_0 := h4695c.1
                                                have p4695_1 := h4695c.2.1
                                                have p4695_2 := h4695c.2.2.1
                                                have p4695_3 := h4695c.2.2.2
                                                linarith only [h4044, h4339, h4340, h4343, hc12, hlam, hphi, ht01, ht0b, ht5b, p4695_1, u5ehi3]
                                              · have p4695_0 := h4695c.1
                                                have p4695_1 := h4695c.2.1
                                                have p4695_2 := h4695c.2.2.1
                                                have p4695_3 := h4695c.2.2.2
                                                linarith only [hlam, p4695_0]
                                      · linarith only [h4342, h4688, hlam]
                                    · linarith only [h4687, hlam, p4672_0]
                                  · have p4672_0 := h4672c.1
                                    have p4672_1 := h4672c.2.1
                                    have p4672_2 := h4672c.2.2.1
                                    have p4672_3 := h4672c.2.2.2
                                    linarith only [h4336, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4672_1, u4ehi2]
                                  · have p4672_0 := h4672c.1
                                    have p4672_1 := h4672c.2.1
                                    have p4672_2 := h4672c.2.2.1
                                    have p4672_3 := h4672c.2.2.2
                                    linarith only [hlam, p4672_0]
                                  · have p4672_0 := h4672c.1
                                    have p4672_1 := h4672c.2.1
                                    have p4672_2 := h4672c.2.2.1
                                    have p4672_3 := h4672c.2.2.2
                                    linarith only [h4044, h4339, h4340, h4343, h4346, h4619, hlam, p4672_2]
                                  · have p4672_0 := h4672c.1
                                    have p4672_1 := h4672c.2.1
                                    have p4672_2 := h4672c.2.2.1
                                    have p4672_3 := h4672c.2.2.2
                                    rcases p4672_3 (m.d 0 2) (by simp) with h4748 | h4748
                                    · linarith only [h0, h4748, hlam]
                                    · linarith only [h4336, h4748, hlam]
                                  · have p4672_0 := h4672c.1
                                    have p4672_1 := h4672c.2.1
                                    have p4672_2 := h4672c.2.2.1
                                    have p4672_3 := h4672c.2.2.2
                                    rcases p4672_3 (m.d 0 2) (by simp) with h4751 | h4751
                                    · linarith only [h0, h4751, hlam]
                                    · linarith only [h4337, h4751, hlam]
                                  · have p4672_0 := h4672c.1
                                    have p4672_1 := h4672c.2.1
                                    have p4672_2 := h4672c.2.2.1
                                    have p4672_3 := h4672c.2.2.2
                                    linarith only [h4335, hlam, p4672_0]
                                  · have p4672_0 := h4672c.1
                                    have p4672_1 := h4672c.2.1
                                    have p4672_2 := h4672c.2.2.1
                                    have p4672_3 := h4672c.2.2.2
                                    linarith only [h4340, hlam, p4672_0]
                                  · have p4672_0 := h4672c.1
                                    have p4672_1 := h4672c.2.1
                                    have p4672_2 := h4672c.2.2.1
                                    have p4672_3 := h4672c.2.2.2
                                    linarith only [hlam, p4672_0]
                                  · have p4672_0 := h4672c.1
                                    have p4672_1 := h4672c.2.1
                                    have p4672_2 := h4672c.2.2.1
                                    have p4672_3 := h4672c.2.2.2
                                    linarith only [h4346, hlam, p4672_1]
                                  · have p4672_0 := h4672c.1
                                    have p4672_1 := h4672c.2.1
                                    have p4672_2 := h4672c.2.2.1
                                    have p4672_3 := h4672c.2.2.2
                                    linarith only [h4456, hlam, p4672_1]
                                  · have p4672_0 := h4672c.1
                                    have p4672_1 := h4672c.2.1
                                    have p4672_2 := h4672c.2.2.1
                                    have p4672_3 := h4672c.2.2.2
                                    linarith only [h4336, hlam, p4672_0]
                                  · have p4672_0 := h4672c.1
                                    have p4672_1 := h4672c.2.1
                                    have p4672_2 := h4672c.2.2.1
                                    have p4672_3 := h4672c.2.2.2
                                    linarith only [h4341, hlam, p4672_0]
                                  · have p4672_0 := h4672c.1
                                    have p4672_1 := h4672c.2.1
                                    have p4672_2 := h4672c.2.2.1
                                    have p4672_3 := h4672c.2.2.2
                                    linarith only [h4044, h4339, h4340, h4343, h4346, h4619, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4672_1]
                                  · have p4672_0 := h4672c.1
                                    have p4672_1 := h4672c.2.1
                                    have p4672_2 := h4672c.2.2.1
                                    have p4672_3 := h4672c.2.2.2
                                    linarith only [hlam, p4672_0]
                                  · have p4672_0 := h4672c.1
                                    have p4672_1 := h4672c.2.1
                                    have p4672_2 := h4672c.2.2.1
                                    have p4672_3 := h4672c.2.2.2
                                    linarith only [h4458, hlam, p4672_0]
                                  · have p4672_0 := h4672c.1
                                    have p4672_1 := h4672c.2.1
                                    have p4672_2 := h4672c.2.2.1
                                    have p4672_3 := h4672c.2.2.2
                                    linarith only [h4337, hlam, p4672_0]
                                  · have p4672_0 := h4672c.1
                                    have p4672_1 := h4672c.2.1
                                    have p4672_2 := h4672c.2.2.1
                                    have p4672_3 := h4672c.2.2.2
                                    linarith only [h4342, hlam, p4672_0]
                                  · have p4672_0 := h4672c.1
                                    have p4672_1 := h4672c.2.1
                                    have p4672_2 := h4672c.2.2.1
                                    have p4672_3 := h4672c.2.2.2
                                    rcases p4672_3 (m.d 0 2) (by simp) with h4766 | h4766
                                    · rcases p4672_3 (m.d 1 2) (by simp) with h4767 | h4767
                                      · rcases p4672_3 (m.d 2 3) (by simp) with h4768 | h4768
                                        · linarith only [h4456, h4768, hlam]
                                        · rcases p4672_3 (m.d 2 4) (by simp) with h4770 | h4770
                                          · linarith only [h4458, h4770, hlam]
                                          · linarith only [h4346, h4770, hlam]
                                      · linarith only [h4340, h4767, hlam]
                                    · linarith only [h4335, h4766, hlam]
                                  · have p4672_0 := h4672c.1
                                    have p4672_1 := h4672c.2.1
                                    have p4672_2 := h4672c.2.2.1
                                    have p4672_3 := h4672c.2.2.2
                                    linarith only [h4337, hc02, hlam, hphi, ht0b, ht45, ht5b, p4672_1, u4ehi2]
                                  · have p4672_0 := h4672c.1
                                    have p4672_1 := h4672c.2.1
                                    have p4672_2 := h4672c.2.2.1
                                    have p4672_3 := h4672c.2.2.2
                                    linarith only [hlam, p4672_0]
                                · linarith only [h4671, hlam, p4621_0]
                              · linarith only [h4044, h4670, hlam]
                            · linarith only [h3473, h4669, hlam]
                          · linarith only [h0, h4668, hlam]
                      · have p4621_0 := h4621c.1
                        have p4621_1 := h4621c.2.1
                        have p4621_2 := h4621c.2.2.1
                        have p4621_3 := h4621c.2.2.2
                        linarith only [h4342, hlam, p4621_0]
                      · have p4621_0 := h4621c.1
                        have p4621_1 := h4621c.2.1
                        have p4621_2 := h4621c.2.2.1
                        have p4621_3 := h4621c.2.2.2
                        linarith only [h4344, hlam, p4621_0]
                      · have p4621_0 := h4621c.1
                        have p4621_1 := h4621c.2.1
                        have p4621_2 := h4621c.2.2.1
                        have p4621_3 := h4621c.2.2.2
                        linarith only [h4345, hlam, p4621_0]
                      · have p4621_0 := h4621c.1
                        have p4621_1 := h4621c.2.1
                        have p4621_2 := h4621c.2.2.1
                        have p4621_3 := h4621c.2.2.2
                        linarith only [hlam, p4621_0]
            · linarith only [h4044, h4339, h4345, hlam]
          · linarith only [h3473, h4338, h4344, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4787 | h4787
          · rcases m.htr 1 4 5 (by decide) (by decide) with h4788 | h4788
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4789 | h4789
              · linarith only [h3473, h4338, h4343, h4789, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4791 | h4791
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4792 | h4792
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4793 | h4793
                    · rcases h1bigk with h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c | h4794c
                      · have p4794_0 := h4794c.1
                        have p4794_1 := h4794c.2.1
                        have p4794_2 := h4794c.2.2.1
                        have p4794_3 := h4794c.2.2.2
                        linarith only [hlam, p4794_0]
                      · have p4794_0 := h4794c.1
                        have p4794_1 := h4794c.2.1
                        have p4794_2 := h4794c.2.2.1
                        have p4794_3 := h4794c.2.2.2
                        linarith only [h0, hlam, p4794_0]
                      · have p4794_0 := h4794c.1
                        have p4794_1 := h4794c.2.1
                        have p4794_2 := h4794c.2.2.1
                        have p4794_3 := h4794c.2.2.2
                        linarith only [h3473, hlam, p4794_0]
                      · have p4794_0 := h4794c.1
                        have p4794_1 := h4794c.2.1
                        have p4794_2 := h4794c.2.2.1
                        have p4794_3 := h4794c.2.2.2
                        linarith only [h4044, hlam, p4794_0]
                      · have p4794_0 := h4794c.1
                        have p4794_1 := h4794c.2.1
                        have p4794_2 := h4794c.2.2.1
                        have p4794_3 := h4794c.2.2.2
                        linarith only [h4238, hlam, p4794_0]
                      · have p4794_0 := h4794c.1
                        have p4794_1 := h4794c.2.1
                        have p4794_2 := h4794c.2.2.1
                        have p4794_3 := h4794c.2.2.2
                        rcases p4794_3 (m.d 0 1) (by simp) with h4800 | h4800
                        · linarith only [h4800, hlam, p4794_0]
                        · rcases p4794_3 (m.d 1 2) (by simp) with h4802 | h4802
                          · rcases p4794_3 (m.d 1 3) (by simp) with h4803 | h4803
                            · linarith only [h4340, h4803, hlam]
                            · linarith only [h3473, h4803, hlam]
                          · linarith only [h4802, hlam, p4794_0]
                      · have p4794_0 := h4794c.1
                        have p4794_1 := h4794c.2.1
                        have p4794_2 := h4794c.2.2.1
                        have p4794_3 := h4794c.2.2.2
                        linarith only [hlam, p4794_0]
                      · have p4794_0 := h4794c.1
                        have p4794_1 := h4794c.2.1
                        have p4794_2 := h4794c.2.2.1
                        have p4794_3 := h4794c.2.2.2
                        linarith only [h3473, h4335, h4791, h4793, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4794_1, u4ehi4]
                      · have p4794_0 := h4794c.1
                        have p4794_1 := h4794c.2.1
                        have p4794_2 := h4794c.2.2.1
                        have p4794_3 := h4794c.2.2.2
                        linarith only [h3473, h4335, h4343, h4791, h4793, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4794_1, u4ehi4]
                      · have p4794_0 := h4794c.1
                        have p4794_1 := h4794c.2.1
                        have p4794_2 := h4794c.2.2.1
                        have p4794_3 := h4794c.2.2.2
                        linarith only [h4238, hc01, hc12, hlam, hphi, p4794_1]
                      · have p4794_0 := h4794c.1
                        have p4794_1 := h4794c.2.1
                        have p4794_2 := h4794c.2.2.1
                        have p4794_3 := h4794c.2.2.2
                        linarith only [h4343, hc01, hc34, hlam, hphi, ht12, ht23, p4794_1]
                      · have p4794_0 := h4794c.1
                        have p4794_1 := h4794c.2.1
                        have p4794_2 := h4794c.2.2.1
                        have p4794_3 := h4794c.2.2.2
                        linarith only [h4340, hlam, p4794_0]
                      · have p4794_0 := h4794c.1
                        have p4794_1 := h4794c.2.1
                        have p4794_2 := h4794c.2.2.1
                        have p4794_3 := h4794c.2.2.2
                        linarith only [hlam, p4794_0]
                      · have p4794_0 := h4794c.1
                        have p4794_1 := h4794c.2.1
                        have p4794_2 := h4794c.2.2.1
                        have p4794_3 := h4794c.2.2.2
                        linarith only [h4343, hlam, p4794_0]
                      · have p4794_0 := h4794c.1
                        have p4794_1 := h4794c.2.1
                        have p4794_2 := h4794c.2.2.1
                        have p4794_3 := h4794c.2.2.2
                        linarith only [h4238, h4343, hc01, hc34, hlam, hphi, ht12, ht23, p4794_1]
                      · have p4794_0 := h4794c.1
                        have p4794_1 := h4794c.2.1
                        have p4794_2 := h4794c.2.2.1
                        have p4794_3 := h4794c.2.2.2
                        rcases p4794_3 (m.d 0 1) (by simp) with h4816 | h4816
                        · linarith only [h4816, hlam, p4794_0]
                        · rcases p4794_3 (m.d 1 2) (by simp) with h4818 | h4818
                          · rcases p4794_3 (m.d 1 3) (by simp) with h4819 | h4819
                            · linarith only [h4343, h4819, hlam]
                            · linarith only [h3473, h4819, hlam]
                          · linarith only [h0, h4818, hlam]
                      · have p4794_0 := h4794c.1
                        have p4794_1 := h4794c.2.1
                        have p4794_2 := h4794c.2.2.1
                        have p4794_3 := h4794c.2.2.2
                        linarith only [h4341, hlam, p4794_0]
                      · have p4794_0 := h4794c.1
                        have p4794_1 := h4794c.2.1
                        have p4794_2 := h4794c.2.2.1
                        have p4794_3 := h4794c.2.2.2
                        linarith only [h3473, hc01, hc14, hlam, hphi, p4794_1]
                      · have p4794_0 := h4794c.1
                        have p4794_1 := h4794c.2.1
                        have p4794_2 := h4794c.2.2.1
                        have p4794_3 := h4794c.2.2.2
                        linarith only [hlam, p4794_0]
                      · have p4794_0 := h4794c.1
                        have p4794_1 := h4794c.2.1
                        have p4794_2 := h4794c.2.2.1
                        have p4794_3 := h4794c.2.2.2
                        linarith only [h4238, h4343, hc01, hc34, hlam, hphi, ht12, ht23, p4794_1]
                      · have p4794_0 := h4794c.1
                        have p4794_1 := h4794c.2.1
                        have p4794_2 := h4794c.2.2.1
                        have p4794_3 := h4794c.2.2.2
                        linarith only [h4343, h4787, hc01, hc34, hlam, hphi, ht12, ht23, p4794_1]
                      · have p4794_0 := h4794c.1
                        have p4794_1 := h4794c.2.1
                        have p4794_2 := h4794c.2.2.1
                        have p4794_3 := h4794c.2.2.2
                        linarith only [h4342, hlam, p4794_0]
                      · have p4794_0 := h4794c.1
                        have p4794_1 := h4794c.2.1
                        have p4794_2 := h4794c.2.2.1
                        have p4794_3 := h4794c.2.2.2
                        linarith only [h4787, hlam, p4794_0]
                      · have p4794_0 := h4794c.1
                        have p4794_1 := h4794c.2.1
                        have p4794_2 := h4794c.2.2.1
                        have p4794_3 := h4794c.2.2.2
                        linarith only [h4788, hlam, p4794_0]
                      · have p4794_0 := h4794c.1
                        have p4794_1 := h4794c.2.1
                        have p4794_2 := h4794c.2.2.1
                        have p4794_3 := h4794c.2.2.2
                        linarith only [hlam, p4794_0]
                    · linarith only [h3473, h4343, h4793, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h4044, h4339, h4343, h4789, h4791, h4792, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · linarith only [h3473, h4338, h4343, h4791, hc23, hc34, hlam, hphi]
            · linarith only [h4044, h4339, h4788, hlam]
          · linarith only [h3473, h4338, h4787, hlam]
      · linarith only [h0, h4337, h4342, hlam]
    · linarith only [h0, h4336, h4341, hlam]
  · linarith only [h0, h4335, h4340, hlam]

end R2N4
