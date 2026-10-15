import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5172000 in
set_option maxHeartbeats 5172000 in
theorem r1l7_12_24_L_I_M_IR_s3_x1_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3260 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4130 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h4359 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2bigk := hb2.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h3260 := hg3260
  rcases m.htr 0 2 3 (by decide) (by decide) with h4360 | h4360
  · rcases m.htr 0 2 4 (by decide) (by decide) with h4361 | h4361
    · rcases m.htr 0 2 5 (by decide) (by decide) with h4362 | h4362
      · rcases m.htr 0 3 4 (by decide) (by decide) with h4363 | h4363
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4364 | h4364
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4365 | h4365
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4366 | h4366
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4367 | h4367
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4368 | h4368
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4369 | h4369
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4370 | h4370
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4371 | h4371
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4372 | h4372
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4373 | h4373
                            · linarith only [h4360, h4370, h4373, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h4130, h4359, h4367, h4368, h4372, h4373, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                          · linarith only [h4130, h4359, h4365, h4368, h4369, h4372, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                        · linarith only [h4130, h4359, h4365, h4367, h4368, h4370, h4371, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4378 | h4378
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4379 | h4379
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4380 | h4380
                            · linarith only [h3260, h4363, h4365, h4370, h4378, h4380, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h4370, h4378, h4379, h4380, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · linarith only [h4130, h4359, h4365, h4368, h4369, h4379, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4384 | h4384
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4385 | h4385
                            · rcases h2bigk with h4386c | h4386c | h4386c | h4386c | h4386c | h4386c | h4386c | h4386c | h4386c | h4386c | h4386c | h4386c | h4386c | h4386c | h4386c | h4386c | h4386c | h4386c | h4386c | h4386c | h4386c | h4386c | h4386c | h4386c | h4386c
                              · have p4386_0 := h4386c.1
                                have p4386_1 := h4386c.2.1
                                have p4386_2 := h4386c.2.2.1
                                have p4386_3 := h4386c.2.2.2
                                linarith only [hlam, p4386_0]
                              · have p4386_0 := h4386c.1
                                have p4386_1 := h4386c.2.1
                                have p4386_2 := h4386c.2.2.1
                                have p4386_3 := h4386c.2.2.2
                                linarith only [h0, hlam, p4386_0]
                              · have p4386_0 := h4386c.1
                                have p4386_1 := h4386c.2.1
                                have p4386_2 := h4386c.2.2.1
                                have p4386_3 := h4386c.2.2.2
                                rcases p4386_3 (m.d 0 2) (by simp) with h4389 | h4389
                                · rcases p4386_3 (m.d 1 2) (by simp) with h4390 | h4390
                                  · rcases p4386_3 (m.d 2 3) (by simp) with h4391 | h4391
                                    · linarith only [h4391, hlam, p4386_0]
                                    · rcases p4386_3 (m.d 2 4) (by simp) with h4393 | h4393
                                      · linarith only [h4361, h4393, hlam]
                                      · linarith only [h4370, h4393, hlam]
                                  · linarith only [h4365, h4390, hlam]
                                · linarith only [h4389, hlam, p4386_0]
                              · have p4386_0 := h4386c.1
                                have p4386_1 := h4386c.2.1
                                have p4386_2 := h4386c.2.2.1
                                have p4386_3 := h4386c.2.2.2
                                linarith only [h0, h4384, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4386_1, u4ehi4]
                              · have p4386_0 := h4386c.1
                                have p4386_1 := h4386c.2.1
                                have p4386_2 := h4386c.2.2.1
                                have p4386_3 := h4386c.2.2.2
                                rcases p4386_3 (m.d 0 2) (by simp) with h4399 | h4399
                                · rcases p4386_3 (m.d 1 2) (by simp) with h4400 | h4400
                                  · rcases p4386_3 (m.d 2 3) (by simp) with h4401 | h4401
                                    · linarith only [h4360, h4401, hlam]
                                    · rcases p4386_3 (m.d 2 4) (by simp) with h4403 | h4403
                                      · linarith only [h4361, h4403, hlam]
                                      · linarith only [h4384, h4403, hlam]
                                  · linarith only [h4367, h4400, hlam]
                                · linarith only [h4399, hlam, p4386_0]
                              · have p4386_0 := h4386c.1
                                have p4386_1 := h4386c.2.1
                                have p4386_2 := h4386c.2.2.1
                                have p4386_3 := h4386c.2.2.2
                                linarith only [h4360, h4363, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4386_1, u4ehi3]
                              · have p4386_0 := h4386c.1
                                have p4386_1 := h4386c.2.1
                                have p4386_2 := h4386c.2.2.1
                                have p4386_3 := h4386c.2.2.2
                                linarith only [hlam, p4386_0]
                              · have p4386_0 := h4386c.1
                                have p4386_1 := h4386c.2.1
                                have p4386_2 := h4386c.2.2.1
                                have p4386_3 := h4386c.2.2.2
                                rcases p4386_3 (m.d 0 2) (by simp) with h4410 | h4410
                                · linarith only [h0, h4410, hlam]
                                · linarith only [h4360, h4410, hlam]
                              · have p4386_0 := h4386c.1
                                have p4386_1 := h4386c.2.1
                                have p4386_2 := h4386c.2.2.1
                                have p4386_3 := h4386c.2.2.2
                                linarith only [h4384, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4386_1, u4ehi4]
                              · have p4386_0 := h4386c.1
                                have p4386_1 := h4386c.2.1
                                have p4386_2 := h4386c.2.2.1
                                have p4386_3 := h4386c.2.2.2
                                rcases p4386_3 (m.d 0 2) (by simp) with h4414 | h4414
                                · linarith only [h0, h4414, hlam]
                                · linarith only [h4362, h4414, hlam]
                              · have p4386_0 := h4386c.1
                                have p4386_1 := h4386c.2.1
                                have p4386_2 := h4386c.2.2.1
                                have p4386_3 := h4386c.2.2.2
                                linarith only [h4360, hlam, p4386_0]
                              · have p4386_0 := h4386c.1
                                have p4386_1 := h4386c.2.1
                                have p4386_2 := h4386c.2.2.1
                                have p4386_3 := h4386c.2.2.2
                                linarith only [h4365, hlam, p4386_0]
                              · have p4386_0 := h4386c.1
                                have p4386_1 := h4386c.2.1
                                have p4386_2 := h4386c.2.2.1
                                have p4386_3 := h4386c.2.2.2
                                linarith only [hlam, p4386_0]
                              · have p4386_0 := h4386c.1
                                have p4386_1 := h4386c.2.1
                                have p4386_2 := h4386c.2.2.1
                                have p4386_3 := h4386c.2.2.2
                                linarith only [h4370, hlam, p4386_1]
                              · have p4386_0 := h4386c.1
                                have p4386_1 := h4386c.2.1
                                have p4386_2 := h4386c.2.2.1
                                have p4386_3 := h4386c.2.2.2
                                linarith only [h4378, hlam, p4386_1]
                              · have p4386_0 := h4386c.1
                                have p4386_1 := h4386c.2.1
                                have p4386_2 := h4386c.2.2.1
                                have p4386_3 := h4386c.2.2.2
                                linarith only [h4361, hlam, p4386_0]
                              · have p4386_0 := h4386c.1
                                have p4386_1 := h4386c.2.1
                                have p4386_2 := h4386c.2.2.1
                                have p4386_3 := h4386c.2.2.2
                                linarith only [h4366, hlam, p4386_0]
                              · have p4386_0 := h4386c.1
                                have p4386_1 := h4386c.2.1
                                have p4386_2 := h4386c.2.2.1
                                have p4386_3 := h4386c.2.2.2
                                rcases p4386_3 (m.d 0 2) (by simp) with h4424 | h4424
                                · rcases p4386_3 (m.d 1 2) (by simp) with h4425 | h4425
                                  · rcases p4386_3 (m.d 2 3) (by simp) with h4426 | h4426
                                    · linarith only [h4370, h4426, hlam]
                                    · rcases p4386_3 (m.d 2 4) (by simp) with h4428 | h4428
                                      · rcases p4386_3 (m.d 2 5) (by simp) with h4429 | h4429
                                        · linarith only [h4384, h4429, hlam]
                                        · linarith only [h4378, h4429, hlam]
                                      · linarith only [h4370, h4428, hlam]
                                  · linarith only [h4365, h4425, hlam]
                                · linarith only [h4360, h4424, hlam]
                              · have p4386_0 := h4386c.1
                                have p4386_1 := h4386c.2.1
                                have p4386_2 := h4386c.2.2.1
                                have p4386_3 := h4386c.2.2.2
                                linarith only [hlam, p4386_0]
                              · have p4386_0 := h4386c.1
                                have p4386_1 := h4386c.2.1
                                have p4386_2 := h4386c.2.2.1
                                have p4386_3 := h4386c.2.2.2
                                linarith only [h3260, h4363, h4365, h4370, h4384, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4386_1, u4ehi4]
                              · have p4386_0 := h4386c.1
                                have p4386_1 := h4386c.2.1
                                have p4386_2 := h4386c.2.2.1
                                have p4386_3 := h4386c.2.2.2
                                linarith only [h4362, hlam, p4386_0]
                              · have p4386_0 := h4386c.1
                                have p4386_1 := h4386c.2.1
                                have p4386_2 := h4386c.2.2.1
                                have p4386_3 := h4386c.2.2.2
                                linarith only [h4367, hlam, p4386_0]
                              · have p4386_0 := h4386c.1
                                have p4386_1 := h4386c.2.1
                                have p4386_2 := h4386c.2.2.1
                                have p4386_3 := h4386c.2.2.2
                                linarith only [h0, h4359, h4367, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4386_1]
                              · have p4386_0 := h4386c.1
                                have p4386_1 := h4386c.2.1
                                have p4386_2 := h4386c.2.2.1
                                have p4386_3 := h4386c.2.2.2
                                linarith only [h4384, hlam, p4386_1]
                              · have p4386_0 := h4386c.1
                                have p4386_1 := h4386c.2.1
                                have p4386_2 := h4386c.2.2.1
                                have p4386_3 := h4386c.2.2.2
                                linarith only [hlam, p4386_0]
                            · linarith only [h4130, h4359, h4365, h4368, h4369, h4370, h4385, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                          · linarith only [h4130, h4359, h4365, h4368, h4369, h4384, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                    · linarith only [h4130, h4364, h4369, hlam]
                  · linarith only [h0, h3260, h4360, h4363, h4368, hc01, hc12, hlam, hphi]
                · linarith only [h0, h4362, h4367, hlam]
              · linarith only [h0, h4361, h4366, hlam]
            · linarith only [h0, h4360, h4365, hlam]
          · linarith only [h4130, h4359, h4364, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4450 | h4450
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4451 | h4451
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4452 | h4452
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4453 | h4453
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4454 | h4454
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4455 | h4455
                    · linarith only [h3260, h4359, h4363, h4451, h4454, h4455, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h3260, h4359, h4361, h4363, h4450, h4454, h4455, hc02, hc15, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4458 | h4458
                    · linarith only [h3260, h4359, h4454, h4458, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                    · linarith only [h4130, h4450, h4458, hlam]
                · linarith only [h0, h4359, h4362, h4453, hc02, hc15, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h4361, h4452, hlam]
            · linarith only [h0, h4360, h4451, hlam]
          · linarith only [h3260, h4359, h4363, h4450, hlam]
      · linarith only [h0, h4359, h4362, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h4466 | h4466
      · rcases m.htr 0 3 4 (by decide) (by decide) with h4467 | h4467
        · linarith only [h4360, h4361, h4467, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4469 | h4469
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4470 | h4470
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4471 | h4471
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4472 | h4472
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4473 | h4473
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4474 | h4474
                    · linarith only [h3260, h4359, h4360, h4361, h4471, h4474, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h4130, h4359, h4469, h4474, hc04, hc15, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4477 | h4477
                    · linarith only [h3260, h4359, h4360, h4361, h4471, h4477, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h4130, h4469, h4477, hlam]
                · linarith only [h4361, h4466, h4472, hc12, hc24, hlam, hphi]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4481 | h4481
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4482 | h4482
                  · linarith only [h3260, h4359, h4467, h4469, h4470, h4471, h4482, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4484 | h4484
                    · linarith only [h0, h4359, h4471, h4484, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · linarith only [h4130, h4359, h4469, h4484, hc04, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h4466, h4481, hlam]
            · linarith only [h0, h4360, h4470, hlam]
          · linarith only [h0, h4359, h4361, h4469, hlam]
      · linarith only [h3260, h4359, h4360, h4466, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h4491 | h4491
    · rcases m.htr 0 2 5 (by decide) (by decide) with h4492 | h4492
      · rcases m.htr 0 3 4 (by decide) (by decide) with h4493 | h4493
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4494 | h4494
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4495 | h4495
            · linarith only [h4360, h4491, h4494, h4495, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4497 | h4497
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4498 | h4498
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4499 | h4499
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4500 | h4500
                    · linarith only [h4130, h4359, h4495, h4497, h4500, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · linarith only [h4130, h4359, h4491, h4494, h4500, hc02, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h3260, h4130, h4359, h4493, h4494, h4495, h4497, h4499, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · linarith only [h0, h4359, h4360, h4492, h4494, h4498, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
              · linarith only [h0, h4491, h4497, hlam]
          · linarith only [h4130, h4359, h4494, hlam]
        · linarith only [h4360, h4491, h4493, hlam]
      · linarith only [h0, h4359, h4492, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h4509 | h4509
      · rcases m.htr 0 3 4 (by decide) (by decide) with h4510 | h4510
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4511 | h4511
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4512 | h4512
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4513 | h4513
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4514 | h4514
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4515 | h4515
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4516 | h4516
                    · linarith only [h0, h4359, h4360, h4512, h4516, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h0, h4359, h4491, h4510, h4511, h4513, h4516, hc03, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h3260, h4510, h4515, hlam]
                · linarith only [h0, h4359, h4509, h4511, h4514, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
              · linarith only [h4360, h4512, h4513, hc02, hc24, hlam, hphi]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4522 | h4522
              · linarith only [h0, h4359, h4491, h4511, h4512, h4522, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4524 | h4524
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4525 | h4525
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4526 | h4526
                    · linarith only [h0, h4359, h4512, h4526, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · linarith only [h0, h4359, h4510, h4511, h4522, h4526, hc03, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h3260, h4510, h4525, hlam]
                · linarith only [h0, h4359, h4509, h4511, h4524, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
          · linarith only [h0, h4359, h4491, h4511, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4532 | h4532
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4533 | h4533
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4534 | h4534
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4535 | h4535
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4536 | h4536
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4537 | h4537
                    · linarith only [h0, h4359, h4360, h4510, h4533, h4536, h4537, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h0, h4359, h4360, h4510, h4532, h4536, h4537, hc04, hc15, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4540 | h4540
                    · linarith only [h0, h4359, h4491, h4534, h4540, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h4130, h4359, h4532, h4540, hlam]
                · linarith only [h0, h4359, h4491, h4532, h4534, h4535, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · linarith only [h0, h4359, h4360, h4532, h4533, h4534, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4545 | h4545
              · linarith only [h0, h4359, h4491, h4532, h4533, h4545, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4547 | h4547
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4548 | h4548
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4549 | h4549
                    · linarith only [h0, h4359, h4360, h4510, h4548, h4549, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h0, h4359, h4532, h4545, h4547, h4549, hc04, hc25, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4552 | h4552
                    · linarith only [h0, h4359, h4533, h4552, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · linarith only [h4130, h4532, h4552, hlam]
                · linarith only [h0, h4359, h4509, h4532, h4547, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
          · linarith only [h0, h4359, h4360, h4510, h4532, hlam]
      · linarith only [h0, h4359, h4509, hlam]

set_option maxHeartbeats 5172000 in
set_option maxHeartbeats 5172000 in
theorem r1l7_12_24_L_I_M_IR_s3_x1_x1_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3260 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4130 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h4359 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4558 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4559 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4560 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4561 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2bigk := hb2.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h3260 := hg3260
  rcases m.htr 0 4 5 (by decide) (by decide) with h4562 | h4562
  · rcases m.htr 1 2 3 (by decide) (by decide) with h4563 | h4563
    · rcases m.htr 1 2 4 (by decide) (by decide) with h4564 | h4564
      · rcases m.htr 1 2 5 (by decide) (by decide) with h4565 | h4565
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4566 | h4566
          · rcases m.htr 1 4 5 (by decide) (by decide) with h4567 | h4567
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4568 | h4568
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4569 | h4569
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4570 | h4570
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4571 | h4571
                    · linarith only [h4558, h4568, h4571, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h0, h4559, h4570, h4571, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4574 | h4574
                    · linarith only [h4568, h4570, h4574, hlam]
                    · rcases h2bigk with h4576c | h4576c | h4576c | h4576c | h4576c | h4576c | h4576c | h4576c | h4576c | h4576c | h4576c | h4576c | h4576c | h4576c | h4576c | h4576c | h4576c | h4576c | h4576c | h4576c | h4576c | h4576c | h4576c | h4576c | h4576c
                      · have p4576_0 := h4576c.1
                        have p4576_1 := h4576c.2.1
                        have p4576_2 := h4576c.2.2.1
                        have p4576_3 := h4576c.2.2.2
                        linarith only [hlam, p4576_0]
                      · have p4576_0 := h4576c.1
                        have p4576_1 := h4576c.2.1
                        have p4576_2 := h4576c.2.2.1
                        have p4576_3 := h4576c.2.2.2
                        linarith only [h0, hlam, p4576_0]
                      · have p4576_0 := h4576c.1
                        have p4576_1 := h4576c.2.1
                        have p4576_2 := h4576c.2.2.1
                        have p4576_3 := h4576c.2.2.2
                        linarith only [h0, h4568, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4576_1, u4ehi3]
                      · have p4576_0 := h4576c.1
                        have p4576_1 := h4576c.2.1
                        have p4576_2 := h4576c.2.2.1
                        have p4576_3 := h4576c.2.2.2
                        rcases p4576_3 (m.d 0 2) (by simp) with h4580 | h4580
                        · rcases p4576_3 (m.d 1 2) (by simp) with h4581 | h4581
                          · rcases p4576_3 (m.d 2 3) (by simp) with h4582 | h4582
                            · linarith only [h4558, h4582, hlam]
                            · linarith only [h4568, h4582, hlam]
                          · linarith only [h4564, h4581, hlam]
                        · linarith only [h4580, hlam, p4576_0]
                      · have p4576_0 := h4576c.1
                        have p4576_1 := h4576c.2.1
                        have p4576_2 := h4576c.2.2.1
                        have p4576_3 := h4576c.2.2.2
                        rcases p4576_3 (m.d 0 2) (by simp) with h4587 | h4587
                        · rcases p4576_3 (m.d 1 2) (by simp) with h4588 | h4588
                          · rcases p4576_3 (m.d 2 3) (by simp) with h4589 | h4589
                            · linarith only [h4558, h4589, hlam]
                            · linarith only [h4569, h4589, hlam]
                          · linarith only [h4565, h4588, hlam]
                        · linarith only [h4587, hlam, p4576_0]
                      · have p4576_0 := h4576c.1
                        have p4576_1 := h4576c.2.1
                        have p4576_2 := h4576c.2.2.1
                        have p4576_3 := h4576c.2.2.2
                        linarith only [h4558, h4561, h4562, h4570, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4576_1, u4ehi2]
                      · have p4576_0 := h4576c.1
                        have p4576_1 := h4576c.2.1
                        have p4576_2 := h4576c.2.2.1
                        have p4576_3 := h4576c.2.2.2
                        linarith only [hlam, p4576_0]
                      · have p4576_0 := h4576c.1
                        have p4576_1 := h4576c.2.1
                        have p4576_2 := h4576c.2.2.1
                        have p4576_3 := h4576c.2.2.2
                        linarith only [h4569, h4574, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4576_1, u4ehi3]
                      · have p4576_0 := h4576c.1
                        have p4576_1 := h4576c.2.1
                        have p4576_2 := h4576c.2.2.1
                        have p4576_3 := h4576c.2.2.2
                        rcases p4576_3 (m.d 0 2) (by simp) with h4597 | h4597
                        · linarith only [h0, h4597, hlam]
                        · linarith only [h4559, h4597, hlam]
                      · have p4576_0 := h4576c.1
                        have p4576_1 := h4576c.2.1
                        have p4576_2 := h4576c.2.2.1
                        have p4576_3 := h4576c.2.2.2
                        rcases p4576_3 (m.d 0 2) (by simp) with h4600 | h4600
                        · linarith only [h0, h4600, hlam]
                        · linarith only [h4560, h4600, hlam]
                      · have p4576_0 := h4576c.1
                        have p4576_1 := h4576c.2.1
                        have p4576_2 := h4576c.2.2.1
                        have p4576_3 := h4576c.2.2.2
                        linarith only [h4558, hlam, p4576_0]
                      · have p4576_0 := h4576c.1
                        have p4576_1 := h4576c.2.1
                        have p4576_2 := h4576c.2.2.1
                        have p4576_3 := h4576c.2.2.2
                        linarith only [h4563, hlam, p4576_0]
                      · have p4576_0 := h4576c.1
                        have p4576_1 := h4576c.2.1
                        have p4576_2 := h4576c.2.2.1
                        have p4576_3 := h4576c.2.2.2
                        linarith only [hlam, p4576_0]
                      · have p4576_0 := h4576c.1
                        have p4576_1 := h4576c.2.1
                        have p4576_2 := h4576c.2.2.1
                        have p4576_3 := h4576c.2.2.2
                        linarith only [h4558, h4568, hc02, hlam, hphi, ht0b, ht45, ht5b, p4576_1, u4ehi3]
                      · have p4576_0 := h4576c.1
                        have p4576_1 := h4576c.2.1
                        have p4576_2 := h4576c.2.2.1
                        have p4576_3 := h4576c.2.2.2
                        linarith only [h0, h4558, h4569, h4574, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4576_1, u4ehi3]
                      · have p4576_0 := h4576c.1
                        have p4576_1 := h4576c.2.1
                        have p4576_2 := h4576c.2.2.1
                        have p4576_3 := h4576c.2.2.2
                        linarith only [h4559, hlam, p4576_0]
                      · have p4576_0 := h4576c.1
                        have p4576_1 := h4576c.2.1
                        have p4576_2 := h4576c.2.2.1
                        have p4576_3 := h4576c.2.2.2
                        linarith only [h4564, hlam, p4576_0]
                      · have p4576_0 := h4576c.1
                        have p4576_1 := h4576c.2.1
                        have p4576_2 := h4576c.2.2.1
                        have p4576_3 := h4576c.2.2.2
                        linarith only [h4568, hlam, p4576_0]
                      · have p4576_0 := h4576c.1
                        have p4576_1 := h4576c.2.1
                        have p4576_2 := h4576c.2.2.1
                        have p4576_3 := h4576c.2.2.2
                        linarith only [hlam, p4576_0]
                      · have p4576_0 := h4576c.1
                        have p4576_1 := h4576c.2.1
                        have p4576_2 := h4576c.2.2.1
                        have p4576_3 := h4576c.2.2.2
                        linarith only [h4570, hlam, p4576_0]
                      · have p4576_0 := h4576c.1
                        have p4576_1 := h4576c.2.1
                        have p4576_2 := h4576c.2.2.1
                        have p4576_3 := h4576c.2.2.2
                        linarith only [h4560, hlam, p4576_0]
                      · have p4576_0 := h4576c.1
                        have p4576_1 := h4576c.2.1
                        have p4576_2 := h4576c.2.2.1
                        have p4576_3 := h4576c.2.2.2
                        linarith only [h4565, hlam, p4576_0]
                      · have p4576_0 := h4576c.1
                        have p4576_1 := h4576c.2.1
                        have p4576_2 := h4576c.2.2.1
                        have p4576_3 := h4576c.2.2.2
                        linarith only [h4569, hlam, p4576_0]
                      · have p4576_0 := h4576c.1
                        have p4576_1 := h4576c.2.1
                        have p4576_2 := h4576c.2.2.1
                        have p4576_3 := h4576c.2.2.2
                        linarith only [h0, h4560, h4568, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4576_1, u4ehi3]
                      · have p4576_0 := h4576c.1
                        have p4576_1 := h4576c.2.1
                        have p4576_2 := h4576c.2.2.1
                        have p4576_3 := h4576c.2.2.2
                        linarith only [hlam, p4576_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4618 | h4618
                  · linarith only [h4568, h4569, h4618, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4620 | h4620
                    · linarith only [h4568, h4569, h4618, h4620, hlam]
                    · linarith only [h4561, h4562, h4568, h4569, h4620, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4623 | h4623
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4624 | h4624
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4625 | h4625
                    · linarith only [h3260, h4561, h4563, h4568, h4623, h4625, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h4568, h4623, h4624, h4625, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h4568, h4623, h4624, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4629 | h4629
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4630 | h4630
                    · rcases h2bigk with h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c
                      · have p4631_0 := h4631c.1
                        have p4631_1 := h4631c.2.1
                        have p4631_2 := h4631c.2.2.1
                        have p4631_3 := h4631c.2.2.2
                        linarith only [hlam, p4631_0]
                      · have p4631_0 := h4631c.1
                        have p4631_1 := h4631c.2.1
                        have p4631_2 := h4631c.2.2.1
                        have p4631_3 := h4631c.2.2.2
                        linarith only [h0, hlam, p4631_0]
                      · have p4631_0 := h4631c.1
                        have p4631_1 := h4631c.2.1
                        have p4631_2 := h4631c.2.2.1
                        have p4631_3 := h4631c.2.2.2
                        rcases p4631_3 (m.d 0 2) (by simp) with h4634 | h4634
                        · rcases p4631_3 (m.d 1 2) (by simp) with h4635 | h4635
                          · rcases p4631_3 (m.d 2 3) (by simp) with h4636 | h4636
                            · linarith only [h4636, hlam, p4631_0]
                            · rcases p4631_3 (m.d 2 4) (by simp) with h4638 | h4638
                              · linarith only [h4559, h4638, hlam]
                              · linarith only [h4568, h4638, hlam]
                          · linarith only [h4563, h4635, hlam]
                        · linarith only [h4634, hlam, p4631_0]
                      · have p4631_0 := h4631c.1
                        have p4631_1 := h4631c.2.1
                        have p4631_2 := h4631c.2.2.1
                        have p4631_3 := h4631c.2.2.2
                        linarith only [h0, h4629, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4631_1, u4ehi4]
                      · have p4631_0 := h4631c.1
                        have p4631_1 := h4631c.2.1
                        have p4631_2 := h4631c.2.2.1
                        have p4631_3 := h4631c.2.2.2
                        rcases p4631_3 (m.d 0 2) (by simp) with h4644 | h4644
                        · rcases p4631_3 (m.d 1 2) (by simp) with h4645 | h4645
                          · rcases p4631_3 (m.d 2 3) (by simp) with h4646 | h4646
                            · linarith only [h4558, h4646, hlam]
                            · rcases p4631_3 (m.d 2 4) (by simp) with h4648 | h4648
                              · linarith only [h4559, h4648, hlam]
                              · linarith only [h4629, h4648, hlam]
                          · linarith only [h4565, h4645, hlam]
                        · linarith only [h4644, hlam, p4631_0]
                      · have p4631_0 := h4631c.1
                        have p4631_1 := h4631c.2.1
                        have p4631_2 := h4631c.2.2.1
                        have p4631_3 := h4631c.2.2.2
                        linarith only [h4558, h4561, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4631_1, u4ehi3]
                      · have p4631_0 := h4631c.1
                        have p4631_1 := h4631c.2.1
                        have p4631_2 := h4631c.2.2.1
                        have p4631_3 := h4631c.2.2.2
                        linarith only [hlam, p4631_0]
                      · have p4631_0 := h4631c.1
                        have p4631_1 := h4631c.2.1
                        have p4631_2 := h4631c.2.2.1
                        have p4631_3 := h4631c.2.2.2
                        rcases p4631_3 (m.d 0 2) (by simp) with h4655 | h4655
                        · linarith only [h0, h4655, hlam]
                        · linarith only [h4558, h4655, hlam]
                      · have p4631_0 := h4631c.1
                        have p4631_1 := h4631c.2.1
                        have p4631_2 := h4631c.2.2.1
                        have p4631_3 := h4631c.2.2.2
                        linarith only [h4629, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4631_1, u4ehi4]
                      · have p4631_0 := h4631c.1
                        have p4631_1 := h4631c.2.1
                        have p4631_2 := h4631c.2.2.1
                        have p4631_3 := h4631c.2.2.2
                        rcases p4631_3 (m.d 0 2) (by simp) with h4659 | h4659
                        · linarith only [h0, h4659, hlam]
                        · linarith only [h4560, h4659, hlam]
                      · have p4631_0 := h4631c.1
                        have p4631_1 := h4631c.2.1
                        have p4631_2 := h4631c.2.2.1
                        have p4631_3 := h4631c.2.2.2
                        linarith only [h4558, hlam, p4631_0]
                      · have p4631_0 := h4631c.1
                        have p4631_1 := h4631c.2.1
                        have p4631_2 := h4631c.2.2.1
                        have p4631_3 := h4631c.2.2.2
                        linarith only [h4563, hlam, p4631_0]
                      · have p4631_0 := h4631c.1
                        have p4631_1 := h4631c.2.1
                        have p4631_2 := h4631c.2.2.1
                        have p4631_3 := h4631c.2.2.2
                        linarith only [hlam, p4631_0]
                      · have p4631_0 := h4631c.1
                        have p4631_1 := h4631c.2.1
                        have p4631_2 := h4631c.2.2.1
                        have p4631_3 := h4631c.2.2.2
                        linarith only [h4568, hlam, p4631_1]
                      · have p4631_0 := h4631c.1
                        have p4631_1 := h4631c.2.1
                        have p4631_2 := h4631c.2.2.1
                        have p4631_3 := h4631c.2.2.2
                        linarith only [h4623, hlam, p4631_1]
                      · have p4631_0 := h4631c.1
                        have p4631_1 := h4631c.2.1
                        have p4631_2 := h4631c.2.2.1
                        have p4631_3 := h4631c.2.2.2
                        linarith only [h4559, hlam, p4631_0]
                      · have p4631_0 := h4631c.1
                        have p4631_1 := h4631c.2.1
                        have p4631_2 := h4631c.2.2.1
                        have p4631_3 := h4631c.2.2.2
                        linarith only [h4564, hlam, p4631_0]
                      · have p4631_0 := h4631c.1
                        have p4631_1 := h4631c.2.1
                        have p4631_2 := h4631c.2.2.1
                        have p4631_3 := h4631c.2.2.2
                        rcases p4631_3 (m.d 0 2) (by simp) with h4669 | h4669
                        · rcases p4631_3 (m.d 1 2) (by simp) with h4670 | h4670
                          · rcases p4631_3 (m.d 2 3) (by simp) with h4671 | h4671
                            · linarith only [h4568, h4671, hlam]
                            · rcases p4631_3 (m.d 2 4) (by simp) with h4673 | h4673
                              · rcases p4631_3 (m.d 2 5) (by simp) with h4674 | h4674
                                · linarith only [h4629, h4674, hlam]
                                · linarith only [h4623, h4674, hlam]
                              · linarith only [h4568, h4673, hlam]
                          · linarith only [h4563, h4670, hlam]
                        · linarith only [h4558, h4669, hlam]
                      · have p4631_0 := h4631c.1
                        have p4631_1 := h4631c.2.1
                        have p4631_2 := h4631c.2.2.1
                        have p4631_3 := h4631c.2.2.2
                        linarith only [hlam, p4631_0]
                      · have p4631_0 := h4631c.1
                        have p4631_1 := h4631c.2.1
                        have p4631_2 := h4631c.2.2.1
                        have p4631_3 := h4631c.2.2.2
                        linarith only [h4558, h4561, h4568, h4629, hc02, hlam, hphi, ht0b, ht45, ht5b, p4631_1, u4ehi4]
                      · have p4631_0 := h4631c.1
                        have p4631_1 := h4631c.2.1
                        have p4631_2 := h4631c.2.2.1
                        have p4631_3 := h4631c.2.2.2
                        linarith only [h4560, hlam, p4631_0]
                      · have p4631_0 := h4631c.1
                        have p4631_1 := h4631c.2.1
                        have p4631_2 := h4631c.2.2.1
                        have p4631_3 := h4631c.2.2.2
                        linarith only [h4565, hlam, p4631_0]
                      · have p4631_0 := h4631c.1
                        have p4631_1 := h4631c.2.1
                        have p4631_2 := h4631c.2.2.1
                        have p4631_3 := h4631c.2.2.2
                        rcases p4631_3 (m.d 0 2) (by simp) with h4684 | h4684
                        · rcases p4631_3 (m.d 1 2) (by simp) with h4685 | h4685
                          · rcases p4631_3 (m.d 2 3) (by simp) with h4686 | h4686
                            · linarith only [h4623, h4686, hlam]
                            · rcases p4631_3 (m.d 2 4) (by simp) with h4688 | h4688
                              · rcases p4631_3 (m.d 2 5) (by simp) with h4689 | h4689
                                · rcases h4bigk with h4690c | h4690c | h4690c | h4690c | h4690c | h4690c | h4690c | h4690c | h4690c | h4690c | h4690c | h4690c | h4690c | h4690c | h4690c | h4690c | h4690c | h4690c | h4690c | h4690c | h4690c | h4690c | h4690c | h4690c | h4690c
                                  · have p4690_0 := h4690c.1
                                    have p4690_1 := h4690c.2.1
                                    have p4690_2 := h4690c.2.2.1
                                    have p4690_3 := h4690c.2.2.2
                                    linarith only [hlam, p4690_0]
                                  · have p4690_0 := h4690c.1
                                    have p4690_1 := h4690c.2.1
                                    have p4690_2 := h4690c.2.2.1
                                    have p4690_3 := h4690c.2.2.2
                                    linarith only [h4130, hlam, p4690_1]
                                  · have p4690_0 := h4690c.1
                                    have p4690_1 := h4690c.2.1
                                    have p4690_2 := h4690c.2.2.1
                                    have p4690_3 := h4690c.2.2.2
                                    linarith only [h4629, hc04, hlam, hphi, ht0b, ht45, ht5b, p4690_1, u4ehi4]
                                  · have p4690_0 := h4690c.1
                                    have p4690_1 := h4690c.2.1
                                    have p4690_2 := h4690c.2.2.1
                                    have p4690_3 := h4690c.2.2.2
                                    linarith only [h4130, h4563, h4566, h4568, h4629, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4690_1, u4ehi4]
                                  · have p4690_0 := h4690c.1
                                    have p4690_1 := h4690c.2.1
                                    have p4690_2 := h4690c.2.2.1
                                    have p4690_3 := h4690c.2.2.2
                                    rcases p4690_3 (m.d 0 4) (by simp) with h4695 | h4695
                                    · rcases p4690_3 (m.d 1 4) (by simp) with h4696 | h4696
                                      · rcases p4690_3 (m.d 2 4) (by simp) with h4697 | h4697
                                        · linarith only [h4559, h4697, hlam]
                                        · linarith only [h4629, h4697, hlam]
                                      · linarith only [h4567, h4696, hlam]
                                    · linarith only [h4695, hlam, p4690_0]
                                  · have p4690_0 := h4690c.1
                                    have p4690_1 := h4690c.2.1
                                    have p4690_2 := h4690c.2.2.1
                                    have p4690_3 := h4690c.2.2.2
                                    linarith only [h4559, h4563, h4566, h4629, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4631_1, p4690_1]
                                  · have p4690_0 := h4690c.1
                                    have p4690_1 := h4690c.2.1
                                    have p4690_2 := h4690c.2.2.1
                                    have p4690_3 := h4690c.2.2.2
                                    linarith only [hlam, p4690_0]
                                  · have p4690_0 := h4690c.1
                                    have p4690_1 := h4690c.2.1
                                    have p4690_2 := h4690c.2.2.1
                                    have p4690_3 := h4690c.2.2.2
                                    linarith only [h4563, h4566, h4629, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4631_1, p4690_1]
                                  · have p4690_0 := h4690c.1
                                    have p4690_1 := h4690c.2.1
                                    have p4690_2 := h4690c.2.2.1
                                    have p4690_3 := h4690c.2.2.2
                                    linarith only [h4563, h4566, h4623, h4630, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4631_1, p4690_1]
                                  · have p4690_0 := h4690c.1
                                    have p4690_1 := h4690c.2.1
                                    have p4690_2 := h4690c.2.2.1
                                    have p4690_3 := h4690c.2.2.2
                                    rcases p4690_3 (m.d 0 4) (by simp) with h4706 | h4706
                                    · linarith only [h4130, h4706, hlam]
                                    · linarith only [h4562, h4706, hlam]
                                  · have p4690_0 := h4690c.1
                                    have p4690_1 := h4690c.2.1
                                    have p4690_2 := h4690c.2.2.1
                                    have p4690_3 := h4690c.2.2.2
                                    linarith only [h4559, hlam, p4690_0]
                                  · have p4690_0 := h4690c.1
                                    have p4690_1 := h4690c.2.1
                                    have p4690_2 := h4690c.2.2.1
                                    have p4690_3 := h4690c.2.2.2
                                    linarith only [h4564, hlam, p4690_0]
                                  · have p4690_0 := h4690c.1
                                    have p4690_1 := h4690c.2.1
                                    have p4690_2 := h4690c.2.2.1
                                    have p4690_3 := h4690c.2.2.2
                                    linarith only [hlam, p4690_0]
                                  · have p4690_0 := h4690c.1
                                    have p4690_1 := h4690c.2.1
                                    have p4690_2 := h4690c.2.2.1
                                    have p4690_3 := h4690c.2.2.2
                                    linarith only [h4568, hlam, p4690_1]
                                  · have p4690_0 := h4690c.1
                                    have p4690_1 := h4690c.2.1
                                    have p4690_2 := h4690c.2.2.1
                                    have p4690_3 := h4690c.2.2.2
                                    linarith only [h0, h4559, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4690_1, u4ehi4]
                                  · have p4690_0 := h4690c.1
                                    have p4690_1 := h4690c.2.1
                                    have p4690_2 := h4690c.2.2.1
                                    have p4690_3 := h4690c.2.2.2
                                    linarith only [h4561, hlam, p4690_0]
                                  · have p4690_0 := h4690c.1
                                    have p4690_1 := h4690c.2.1
                                    have p4690_2 := h4690c.2.2.1
                                    have p4690_3 := h4690c.2.2.2
                                    linarith only [h4566, hlam, p4690_0]
                                  · have p4690_0 := h4690c.1
                                    have p4690_1 := h4690c.2.1
                                    have p4690_2 := h4690c.2.2.1
                                    have p4690_3 := h4690c.2.2.2
                                    linarith only [h0, h4558, h4561, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4690_1, u4ehi2]
                                  · have p4690_0 := h4690c.1
                                    have p4690_1 := h4690c.2.1
                                    have p4690_2 := h4690c.2.2.1
                                    have p4690_3 := h4690c.2.2.2
                                    linarith only [hlam, p4690_0]
                                  · have p4690_0 := h4690c.1
                                    have p4690_1 := h4690c.2.1
                                    have p4690_2 := h4690c.2.2.1
                                    have p4690_3 := h4690c.2.2.2
                                    linarith only [h0, h4558, h4561, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4690_1, u4ehi4]
                                  · have p4690_0 := h4690c.1
                                    have p4690_1 := h4690c.2.1
                                    have p4690_2 := h4690c.2.2.1
                                    have p4690_3 := h4690c.2.2.2
                                    linarith only [h4562, hlam, p4690_0]
                                  · have p4690_0 := h4690c.1
                                    have p4690_1 := h4690c.2.1
                                    have p4690_2 := h4690c.2.2.1
                                    have p4690_3 := h4690c.2.2.2
                                    linarith only [h4567, hlam, p4690_0]
                                  · have p4690_0 := h4690c.1
                                    have p4690_1 := h4690c.2.1
                                    have p4690_2 := h4690c.2.2.1
                                    have p4690_3 := h4690c.2.2.2
                                    linarith only [h4629, hlam, p4690_0]
                                  · have p4690_0 := h4690c.1
                                    have p4690_1 := h4690c.2.1
                                    have p4690_2 := h4690c.2.2.1
                                    have p4690_3 := h4690c.2.2.2
                                    linarith only [h4630, hlam, p4690_0]
                                  · have p4690_0 := h4690c.1
                                    have p4690_1 := h4690c.2.1
                                    have p4690_2 := h4690c.2.2.1
                                    have p4690_3 := h4690c.2.2.2
                                    linarith only [hlam, p4690_0]
                                · linarith only [h4623, h4689, hlam]
                              · linarith only [h4568, h4688, hlam]
                          · linarith only [h4563, h4685, hlam]
                        · linarith only [h4558, h4684, hlam]
                      · have p4631_0 := h4631c.1
                        have p4631_1 := h4631c.2.1
                        have p4631_2 := h4631c.2.2.1
                        have p4631_3 := h4631c.2.2.2
                        linarith only [h4629, hlam, p4631_1]
                      · have p4631_0 := h4631c.1
                        have p4631_1 := h4631c.2.1
                        have p4631_2 := h4631c.2.2.1
                        have p4631_3 := h4631c.2.2.2
                        linarith only [hlam, p4631_0]
                    · linarith only [h4568, h4629, h4630, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4731 | h4731
                    · linarith only [h0, h4558, h4561, h4629, h4731, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                    · rcases h2bigk with h4733c | h4733c | h4733c | h4733c | h4733c | h4733c | h4733c | h4733c | h4733c | h4733c | h4733c | h4733c | h4733c | h4733c | h4733c | h4733c | h4733c | h4733c | h4733c | h4733c | h4733c | h4733c | h4733c | h4733c | h4733c
                      · have p4733_0 := h4733c.1
                        have p4733_1 := h4733c.2.1
                        have p4733_2 := h4733c.2.2.1
                        have p4733_3 := h4733c.2.2.2
                        linarith only [hlam, p4733_0]
                      · have p4733_0 := h4733c.1
                        have p4733_1 := h4733c.2.1
                        have p4733_2 := h4733c.2.2.1
                        have p4733_3 := h4733c.2.2.2
                        linarith only [h0, hlam, p4733_0]
                      · have p4733_0 := h4733c.1
                        have p4733_1 := h4733c.2.1
                        have p4733_2 := h4733c.2.2.1
                        have p4733_3 := h4733c.2.2.2
                        linarith only [h4558, h4561, h4562, h4568, h4731, hlam, p4733_2]
                      · have p4733_0 := h4733c.1
                        have p4733_1 := h4733c.2.1
                        have p4733_2 := h4733c.2.2.1
                        have p4733_3 := h4733c.2.2.2
                        rcases p4733_3 (m.d 0 2) (by simp) with h4737 | h4737
                        · rcases p4733_3 (m.d 1 2) (by simp) with h4738 | h4738
                          · rcases p4733_3 (m.d 2 3) (by simp) with h4739 | h4739
                            · linarith only [h4558, h4739, hlam]
                            · rcases p4733_3 (m.d 2 4) (by simp) with h4741 | h4741
                              · linarith only [h4741, hlam, p4733_0]
                              · rcases p4733_3 (m.d 2 5) (by simp) with h4743 | h4743
                                · linarith only [h4560, h4743, hlam]
                                · linarith only [h4629, h4743, hlam]
                          · linarith only [h4564, h4738, hlam]
                        · linarith only [h4737, hlam, p4733_0]
                      · have p4733_0 := h4733c.1
                        have p4733_1 := h4733c.2.1
                        have p4733_2 := h4733c.2.2.1
                        have p4733_3 := h4733c.2.2.2
                        rcases p4733_3 (m.d 0 2) (by simp) with h4748 | h4748
                        · rcases p4733_3 (m.d 1 2) (by simp) with h4749 | h4749
                          · rcases p4733_3 (m.d 2 3) (by simp) with h4750 | h4750
                            · linarith only [h4558, h4750, hlam]
                            · rcases p4733_3 (m.d 2 4) (by simp) with h4752 | h4752
                              · linarith only [h4559, h4752, hlam]
                              · rcases p4733_3 (m.d 2 5) (by simp) with h4754 | h4754
                                · linarith only [h4754, hlam, p4733_0]
                                · rcases h4bigk with h4756c | h4756c | h4756c | h4756c | h4756c | h4756c | h4756c | h4756c | h4756c | h4756c | h4756c | h4756c | h4756c | h4756c | h4756c | h4756c | h4756c | h4756c | h4756c | h4756c | h4756c | h4756c | h4756c | h4756c | h4756c
                                  · have p4756_0 := h4756c.1
                                    have p4756_1 := h4756c.2.1
                                    have p4756_2 := h4756c.2.2.1
                                    have p4756_3 := h4756c.2.2.2
                                    linarith only [hlam, p4756_0]
                                  · have p4756_0 := h4756c.1
                                    have p4756_1 := h4756c.2.1
                                    have p4756_2 := h4756c.2.2.1
                                    have p4756_3 := h4756c.2.2.2
                                    linarith only [h4130, hlam, p4756_1]
                                  · have p4756_0 := h4756c.1
                                    have p4756_1 := h4756c.2.1
                                    have p4756_2 := h4756c.2.2.1
                                    have p4756_3 := h4756c.2.2.2
                                    rcases p4756_3 (m.d 0 4) (by simp) with h4759 | h4759
                                    · rcases p4756_3 (m.d 1 4) (by simp) with h4760 | h4760
                                      · rcases p4756_3 (m.d 2 4) (by simp) with h4761 | h4761
                                        · linarith only [h4559, h4761, hlam]
                                        · rcases p4756_3 (m.d 3 4) (by simp) with h4763 | h4763
                                          · linarith only [h4561, h4763, hlam]
                                          · linarith only [h4568, h4763, hlam]
                                      · linarith only [h4564, h4760, hlam]
                                    · linarith only [h4559, h4759, hlam]
                                  · have p4756_0 := h4756c.1
                                    have p4756_1 := h4756c.2.1
                                    have p4756_2 := h4756c.2.2.1
                                    have p4756_3 := h4756c.2.2.2
                                    rcases p4756_3 (m.d 0 4) (by simp) with h4768 | h4768
                                    · rcases p4756_3 (m.d 1 4) (by simp) with h4769 | h4769
                                      · rcases p4756_3 (m.d 2 4) (by simp) with h4770 | h4770
                                        · linarith only [h4559, h4770, hlam]
                                        · rcases p4756_3 (m.d 3 4) (by simp) with h4772 | h4772
                                          · linarith only [h4561, h4772, hlam]
                                          · rcases p4756_3 (m.d 4 5) (by simp) with h4774 | h4774
                                            · linarith only [h4562, h4774, hlam]
                                            · linarith only [h4731, h4774, hlam]
                                      · linarith only [h4566, h4769, hlam]
                                    · linarith only [h4561, h4768, hlam]
                                  · have p4756_0 := h4756c.1
                                    have p4756_1 := h4756c.2.1
                                    have p4756_2 := h4756c.2.2.1
                                    have p4756_3 := h4756c.2.2.2
                                    linarith only [h4558, h4561, h4568, h4731, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4756_1]
                                  · have p4756_0 := h4756c.1
                                    have p4756_1 := h4756c.2.1
                                    have p4756_2 := h4756c.2.2.1
                                    have p4756_3 := h4756c.2.2.2
                                    linarith only [h4562, h4563, h4566, h4568, h4731, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4756_1]
                                  · have p4756_0 := h4756c.1
                                    have p4756_1 := h4756c.2.1
                                    have p4756_2 := h4756c.2.2.1
                                    have p4756_3 := h4756c.2.2.2
                                    linarith only [hlam, p4756_0]
                                  · have p4756_0 := h4756c.1
                                    have p4756_1 := h4756c.2.1
                                    have p4756_2 := h4756c.2.2.1
                                    have p4756_3 := h4756c.2.2.2
                                    rcases p4756_3 (m.d 0 4) (by simp) with h4782 | h4782
                                    · linarith only [h4130, h4782, hlam]
                                    · linarith only [h4559, h4782, hlam]
                                  · have p4756_0 := h4756c.1
                                    have p4756_1 := h4756c.2.1
                                    have p4756_2 := h4756c.2.2.1
                                    have p4756_3 := h4756c.2.2.2
                                    rcases p4756_3 (m.d 0 4) (by simp) with h4785 | h4785
                                    · linarith only [h4130, h4785, hlam]
                                    · linarith only [h4561, h4785, hlam]
                                  · have p4756_0 := h4756c.1
                                    have p4756_1 := h4756c.2.1
                                    have p4756_2 := h4756c.2.2.1
                                    have p4756_3 := h4756c.2.2.2
                                    linarith only [h4563, h4566, h4568, h4731, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4756_1]
                                  · have p4756_0 := h4756c.1
                                    have p4756_1 := h4756c.2.1
                                    have p4756_2 := h4756c.2.2.1
                                    have p4756_3 := h4756c.2.2.2
                                    linarith only [h4559, hlam, p4756_0]
                                  · have p4756_0 := h4756c.1
                                    have p4756_1 := h4756c.2.1
                                    have p4756_2 := h4756c.2.2.1
                                    have p4756_3 := h4756c.2.2.2
                                    linarith only [h4564, hlam, p4756_0]
                                  · have p4756_0 := h4756c.1
                                    have p4756_1 := h4756c.2.1
                                    have p4756_2 := h4756c.2.2.1
                                    have p4756_3 := h4756c.2.2.2
                                    linarith only [hlam, p4756_0]
                                  · have p4756_0 := h4756c.1
                                    have p4756_1 := h4756c.2.1
                                    have p4756_2 := h4756c.2.2.1
                                    have p4756_3 := h4756c.2.2.2
                                    linarith only [h4568, hlam, p4756_1]
                                  · have p4756_0 := h4756c.1
                                    have p4756_1 := h4756c.2.1
                                    have p4756_2 := h4756c.2.2.1
                                    have p4756_3 := h4756c.2.2.2
                                    linarith only [h4629, hlam, p4756_0]
                                  · have p4756_0 := h4756c.1
                                    have p4756_1 := h4756c.2.1
                                    have p4756_2 := h4756c.2.2.1
                                    have p4756_3 := h4756c.2.2.2
                                    linarith only [h4561, hlam, p4756_0]
                                  · have p4756_0 := h4756c.1
                                    have p4756_1 := h4756c.2.1
                                    have p4756_2 := h4756c.2.2.1
                                    have p4756_3 := h4756c.2.2.2
                                    linarith only [h4566, hlam, p4756_0]
                                  · have p4756_0 := h4756c.1
                                    have p4756_1 := h4756c.2.1
                                    have p4756_2 := h4756c.2.2.1
                                    have p4756_3 := h4756c.2.2.2
                                    linarith only [h4562, h4731, hc04, hlam, hphi, ht0b, ht45, ht5b, p4756_1, u4ehi2]
                                  · have p4756_0 := h4756c.1
                                    have p4756_1 := h4756c.2.1
                                    have p4756_2 := h4756c.2.2.1
                                    have p4756_3 := h4756c.2.2.2
                                    linarith only [hlam, p4756_0]
                                  · have p4756_0 := h4756c.1
                                    have p4756_1 := h4756c.2.1
                                    have p4756_2 := h4756c.2.2.1
                                    have p4756_3 := h4756c.2.2.2
                                    linarith only [h4731, hlam, p4756_0]
                                  · have p4756_0 := h4756c.1
                                    have p4756_1 := h4756c.2.1
                                    have p4756_2 := h4756c.2.2.1
                                    have p4756_3 := h4756c.2.2.2
                                    linarith only [h4562, hlam, p4756_0]
                                  · have p4756_0 := h4756c.1
                                    have p4756_1 := h4756c.2.1
                                    have p4756_2 := h4756c.2.2.1
                                    have p4756_3 := h4756c.2.2.2
                                    linarith only [h4567, hlam, p4756_0]
                                  · have p4756_0 := h4756c.1
                                    have p4756_1 := h4756c.2.1
                                    have p4756_2 := h4756c.2.2.1
                                    have p4756_3 := h4756c.2.2.2
                                    linarith only [h4130, h4562, h4563, h4566, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4756_1, u4ehi2]
                                  · have p4756_0 := h4756c.1
                                    have p4756_1 := h4756c.2.1
                                    have p4756_2 := h4756c.2.2.1
                                    have p4756_3 := h4756c.2.2.2
                                    linarith only [h4130, h4562, h4563, h4566, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4756_1, u4ehi3]
                                  · have p4756_0 := h4756c.1
                                    have p4756_1 := h4756c.2.1
                                    have p4756_2 := h4756c.2.2.1
                                    have p4756_3 := h4756c.2.2.2
                                    linarith only [hlam, p4756_0]
                          · linarith only [h4565, h4749, hlam]
                        · linarith only [h4748, hlam, p4733_0]
                      · have p4733_0 := h4733c.1
                        have p4733_1 := h4733c.2.1
                        have p4733_2 := h4733c.2.2.1
                        have p4733_3 := h4733c.2.2.2
                        linarith only [h4559, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4733_1, u4ehi2]
                      · have p4733_0 := h4733c.1
                        have p4733_1 := h4733c.2.1
                        have p4733_2 := h4733c.2.2.1
                        have p4733_3 := h4733c.2.2.2
                        linarith only [hlam, p4733_0]
                      · have p4733_0 := h4733c.1
                        have p4733_1 := h4733c.2.1
                        have p4733_2 := h4733c.2.2.1
                        have p4733_3 := h4733c.2.2.2
                        linarith only [h4130, h4562, h4563, h4566, h4568, h4731, hlam, p4733_2]
                      · have p4733_0 := h4733c.1
                        have p4733_1 := h4733c.2.1
                        have p4733_2 := h4733c.2.2.1
                        have p4733_3 := h4733c.2.2.2
                        rcases p4733_3 (m.d 0 2) (by simp) with h4809 | h4809
                        · linarith only [h0, h4809, hlam]
                        · linarith only [h4559, h4809, hlam]
                      · have p4733_0 := h4733c.1
                        have p4733_1 := h4733c.2.1
                        have p4733_2 := h4733c.2.2.1
                        have p4733_3 := h4733c.2.2.2
                        rcases p4733_3 (m.d 0 2) (by simp) with h4812 | h4812
                        · linarith only [h0, h4812, hlam]
                        · linarith only [h4560, h4812, hlam]
                      · have p4733_0 := h4733c.1
                        have p4733_1 := h4733c.2.1
                        have p4733_2 := h4733c.2.2.1
                        have p4733_3 := h4733c.2.2.2
                        linarith only [h4558, hlam, p4733_0]
                      · have p4733_0 := h4733c.1
                        have p4733_1 := h4733c.2.1
                        have p4733_2 := h4733c.2.2.1
                        have p4733_3 := h4733c.2.2.2
                        linarith only [h4563, hlam, p4733_0]
                      · have p4733_0 := h4733c.1
                        have p4733_1 := h4733c.2.1
                        have p4733_2 := h4733c.2.2.1
                        have p4733_3 := h4733c.2.2.2
                        linarith only [hlam, p4733_0]
                      · have p4733_0 := h4733c.1
                        have p4733_1 := h4733c.2.1
                        have p4733_2 := h4733c.2.2.1
                        have p4733_3 := h4733c.2.2.2
                        linarith only [h4568, hlam, p4733_1]
                      · have p4733_0 := h4733c.1
                        have p4733_1 := h4733c.2.1
                        have p4733_2 := h4733c.2.2.1
                        have p4733_3 := h4733c.2.2.2
                        linarith only [h4623, hlam, p4733_1]
                      · have p4733_0 := h4733c.1
                        have p4733_1 := h4733c.2.1
                        have p4733_2 := h4733c.2.2.1
                        have p4733_3 := h4733c.2.2.2
                        linarith only [h4559, hlam, p4733_0]
                      · have p4733_0 := h4733c.1
                        have p4733_1 := h4733c.2.1
                        have p4733_2 := h4733c.2.2.1
                        have p4733_3 := h4733c.2.2.2
                        linarith only [h4564, hlam, p4733_0]
                      · have p4733_0 := h4733c.1
                        have p4733_1 := h4733c.2.1
                        have p4733_2 := h4733c.2.2.1
                        have p4733_3 := h4733c.2.2.2
                        linarith only [h4130, h4562, h4563, h4566, h4568, h4731, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4733_1]
                      · have p4733_0 := h4733c.1
                        have p4733_1 := h4733c.2.1
                        have p4733_2 := h4733c.2.2.1
                        have p4733_3 := h4733c.2.2.2
                        linarith only [hlam, p4733_0]
                      · have p4733_0 := h4733c.1
                        have p4733_1 := h4733c.2.1
                        have p4733_2 := h4733c.2.2.1
                        have p4733_3 := h4733c.2.2.2
                        linarith only [h4629, hlam, p4733_0]
                      · have p4733_0 := h4733c.1
                        have p4733_1 := h4733c.2.1
                        have p4733_2 := h4733c.2.2.1
                        have p4733_3 := h4733c.2.2.2
                        linarith only [h4560, hlam, p4733_0]
                      · have p4733_0 := h4733c.1
                        have p4733_1 := h4733c.2.1
                        have p4733_2 := h4733c.2.2.1
                        have p4733_3 := h4733c.2.2.2
                        linarith only [h4565, hlam, p4733_0]
                      · have p4733_0 := h4733c.1
                        have p4733_1 := h4733c.2.1
                        have p4733_2 := h4733c.2.2.1
                        have p4733_3 := h4733c.2.2.2
                        rcases p4733_3 (m.d 0 2) (by simp) with h4827 | h4827
                        · rcases p4733_3 (m.d 1 2) (by simp) with h4828 | h4828
                          · rcases p4733_3 (m.d 2 3) (by simp) with h4829 | h4829
                            · linarith only [h4623, h4829, hlam]
                            · rcases p4733_3 (m.d 2 4) (by simp) with h4831 | h4831
                              · linarith only [h4629, h4831, hlam]
                              · linarith only [h4568, h4831, hlam]
                          · linarith only [h4563, h4828, hlam]
                        · linarith only [h4558, h4827, hlam]
                      · have p4733_0 := h4733c.1
                        have p4733_1 := h4733c.2.1
                        have p4733_2 := h4733c.2.2.1
                        have p4733_3 := h4733c.2.2.2
                        linarith only [h4560, hc02, hlam, hphi, ht0b, ht45, ht5b, p4733_1, u4ehi2]
                      · have p4733_0 := h4733c.1
                        have p4733_1 := h4733c.2.1
                        have p4733_2 := h4733c.2.2.1
                        have p4733_3 := h4733c.2.2.2
                        linarith only [hlam, p4733_0]
            · linarith only [h4130, h4562, h4567, hlam]
          · linarith only [h3260, h4561, h4566, hlam]
        · linarith only [h0, h4558, h4560, h4561, h4562, h4565, hlam]
      · linarith only [h0, h4559, h4564, hlam]
    · linarith only [h0, h4558, h4563, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h4843 | h4843
    · rcases m.htr 1 2 4 (by decide) (by decide) with h4844 | h4844
      · rcases m.htr 1 2 5 (by decide) (by decide) with h4845 | h4845
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4846 | h4846
          · rcases m.htr 1 4 5 (by decide) (by decide) with h4847 | h4847
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4848 | h4848
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4849 | h4849
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4850 | h4850
                  · linarith only [h4559, h4562, h4850, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4852 | h4852
                    · linarith only [h4558, h4562, h4848, h4852, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                    · rcases h2bigk with h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c | h4854c
                      · have p4854_0 := h4854c.1
                        have p4854_1 := h4854c.2.1
                        have p4854_2 := h4854c.2.2.1
                        have p4854_3 := h4854c.2.2.2
                        linarith only [hlam, p4854_0]
                      · have p4854_0 := h4854c.1
                        have p4854_1 := h4854c.2.1
                        have p4854_2 := h4854c.2.2.1
                        have p4854_3 := h4854c.2.2.2
                        linarith only [h0, hlam, p4854_0]
                      · have p4854_0 := h4854c.1
                        have p4854_1 := h4854c.2.1
                        have p4854_2 := h4854c.2.2.1
                        have p4854_3 := h4854c.2.2.2
                        linarith only [h0, h4848, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4854_1, u4ehi3]
                      · have p4854_0 := h4854c.1
                        have p4854_1 := h4854c.2.1
                        have p4854_2 := h4854c.2.2.1
                        have p4854_3 := h4854c.2.2.2
                        rcases p4854_3 (m.d 0 2) (by simp) with h4858 | h4858
                        · rcases p4854_3 (m.d 1 2) (by simp) with h4859 | h4859
                          · rcases p4854_3 (m.d 2 3) (by simp) with h4860 | h4860
                            · linarith only [h4558, h4860, hlam]
                            · linarith only [h4848, h4860, hlam]
                          · linarith only [h4844, h4859, hlam]
                        · linarith only [h4858, hlam, p4854_0]
                      · have p4854_0 := h4854c.1
                        have p4854_1 := h4854c.2.1
                        have p4854_2 := h4854c.2.2.1
                        have p4854_3 := h4854c.2.2.2
                        rcases p4854_3 (m.d 0 2) (by simp) with h4865 | h4865
                        · rcases p4854_3 (m.d 1 2) (by simp) with h4866 | h4866
                          · rcases p4854_3 (m.d 2 3) (by simp) with h4867 | h4867
                            · linarith only [h4558, h4867, hlam]
                            · linarith only [h4849, h4867, hlam]
                          · linarith only [h4845, h4866, hlam]
                        · linarith only [h4865, hlam, p4854_0]
                      · have p4854_0 := h4854c.1
                        have p4854_1 := h4854c.2.1
                        have p4854_2 := h4854c.2.2.1
                        have p4854_3 := h4854c.2.2.2
                        linarith only [h4558, h4849, h4852, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4854_1, u4ehi3]
                      · have p4854_0 := h4854c.1
                        have p4854_1 := h4854c.2.1
                        have p4854_2 := h4854c.2.2.1
                        have p4854_3 := h4854c.2.2.2
                        linarith only [hlam, p4854_0]
                      · have p4854_0 := h4854c.1
                        have p4854_1 := h4854c.2.1
                        have p4854_2 := h4854c.2.2.1
                        have p4854_3 := h4854c.2.2.2
                        linarith only [h4849, h4852, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4854_1, u4ehi3]
                      · have p4854_0 := h4854c.1
                        have p4854_1 := h4854c.2.1
                        have p4854_2 := h4854c.2.2.1
                        have p4854_3 := h4854c.2.2.2
                        rcases p4854_3 (m.d 0 2) (by simp) with h4875 | h4875
                        · linarith only [h0, h4875, hlam]
                        · linarith only [h4559, h4875, hlam]
                      · have p4854_0 := h4854c.1
                        have p4854_1 := h4854c.2.1
                        have p4854_2 := h4854c.2.2.1
                        have p4854_3 := h4854c.2.2.2
                        rcases p4854_3 (m.d 0 2) (by simp) with h4878 | h4878
                        · linarith only [h0, h4878, hlam]
                        · linarith only [h4560, h4878, hlam]
                      · have p4854_0 := h4854c.1
                        have p4854_1 := h4854c.2.1
                        have p4854_2 := h4854c.2.2.1
                        have p4854_3 := h4854c.2.2.2
                        linarith only [h4558, hlam, p4854_0]
                      · have p4854_0 := h4854c.1
                        have p4854_1 := h4854c.2.1
                        have p4854_2 := h4854c.2.2.1
                        have p4854_3 := h4854c.2.2.2
                        linarith only [h4843, hlam, p4854_0]
                      · have p4854_0 := h4854c.1
                        have p4854_1 := h4854c.2.1
                        have p4854_2 := h4854c.2.2.1
                        have p4854_3 := h4854c.2.2.2
                        linarith only [hlam, p4854_0]
                      · have p4854_0 := h4854c.1
                        have p4854_1 := h4854c.2.1
                        have p4854_2 := h4854c.2.2.1
                        have p4854_3 := h4854c.2.2.2
                        linarith only [h4558, h4848, hc02, hlam, hphi, ht0b, ht45, ht5b, p4854_1, u4ehi3]
                      · have p4854_0 := h4854c.1
                        have p4854_1 := h4854c.2.1
                        have p4854_2 := h4854c.2.2.1
                        have p4854_3 := h4854c.2.2.2
                        linarith only [h0, h4558, h4849, h4852, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4854_1, u4ehi3]
                      · have p4854_0 := h4854c.1
                        have p4854_1 := h4854c.2.1
                        have p4854_2 := h4854c.2.2.1
                        have p4854_3 := h4854c.2.2.2
                        linarith only [h4559, hlam, p4854_0]
                      · have p4854_0 := h4854c.1
                        have p4854_1 := h4854c.2.1
                        have p4854_2 := h4854c.2.2.1
                        have p4854_3 := h4854c.2.2.2
                        linarith only [h4844, hlam, p4854_0]
                      · have p4854_0 := h4854c.1
                        have p4854_1 := h4854c.2.1
                        have p4854_2 := h4854c.2.2.1
                        have p4854_3 := h4854c.2.2.2
                        linarith only [h4848, hlam, p4854_0]
                      · have p4854_0 := h4854c.1
                        have p4854_1 := h4854c.2.1
                        have p4854_2 := h4854c.2.2.1
                        have p4854_3 := h4854c.2.2.2
                        linarith only [hlam, p4854_0]
                      · have p4854_0 := h4854c.1
                        have p4854_1 := h4854c.2.1
                        have p4854_2 := h4854c.2.2.1
                        have p4854_3 := h4854c.2.2.2
                        linarith only [h4850, hlam, p4854_0]
                      · have p4854_0 := h4854c.1
                        have p4854_1 := h4854c.2.1
                        have p4854_2 := h4854c.2.2.1
                        have p4854_3 := h4854c.2.2.2
                        linarith only [h4560, hlam, p4854_0]
                      · have p4854_0 := h4854c.1
                        have p4854_1 := h4854c.2.1
                        have p4854_2 := h4854c.2.2.1
                        have p4854_3 := h4854c.2.2.2
                        linarith only [h4845, hlam, p4854_0]
                      · have p4854_0 := h4854c.1
                        have p4854_1 := h4854c.2.1
                        have p4854_2 := h4854c.2.2.1
                        have p4854_3 := h4854c.2.2.2
                        linarith only [h4849, hlam, p4854_0]
                      · have p4854_0 := h4854c.1
                        have p4854_1 := h4854c.2.1
                        have p4854_2 := h4854c.2.2.1
                        have p4854_3 := h4854c.2.2.2
                        linarith only [h0, h4560, h4848, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4854_1, u4ehi3]
                      · have p4854_0 := h4854c.1
                        have p4854_1 := h4854c.2.1
                        have p4854_2 := h4854c.2.2.1
                        have p4854_3 := h4854c.2.2.2
                        linarith only [hlam, p4854_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4896 | h4896
                  · linarith only [h0, h4559, h4562, h4896, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4898 | h4898
                    · linarith only [h4560, h4562, h4848, h4849, h4898, hlam]
                    · linarith only [h4848, h4849, h4898, hc45, hlam, hphi, u4ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4901 | h4901
                · linarith only [h4561, h4562, h4843, h4846, h4847, h4848, h4901, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4903 | h4903
                  · linarith only [h4561, h4562, h4848, h4903, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4905 | h4905
                    · linarith only [h4561, h4562, h4905, hlam]
                    · rcases h2bigk with h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c
                      · have p4907_0 := h4907c.1
                        have p4907_1 := h4907c.2.1
                        have p4907_2 := h4907c.2.2.1
                        have p4907_3 := h4907c.2.2.2
                        linarith only [hlam, p4907_0]
                      · have p4907_0 := h4907c.1
                        have p4907_1 := h4907c.2.1
                        have p4907_2 := h4907c.2.2.1
                        have p4907_3 := h4907c.2.2.2
                        linarith only [h0, hlam, p4907_0]
                      · have p4907_0 := h4907c.1
                        have p4907_1 := h4907c.2.1
                        have p4907_2 := h4907c.2.2.1
                        have p4907_3 := h4907c.2.2.2
                        rcases p4907_3 (m.d 0 2) (by simp) with h4910 | h4910
                        · rcases p4907_3 (m.d 1 2) (by simp) with h4911 | h4911
                          · rcases p4907_3 (m.d 2 3) (by simp) with h4912 | h4912
                            · linarith only [h4912, hlam, p4907_0]
                            · rcases p4907_3 (m.d 2 4) (by simp) with h4914 | h4914
                              · linarith only [h4559, h4914, hlam]
                              · linarith only [h4848, h4914, hlam]
                          · linarith only [h4843, h4911, hlam]
                        · linarith only [h4910, hlam, p4907_0]
                      · have p4907_0 := h4907c.1
                        have p4907_1 := h4907c.2.1
                        have p4907_2 := h4907c.2.2.1
                        have p4907_3 := h4907c.2.2.2
                        rcases p4907_3 (m.d 0 2) (by simp) with h4919 | h4919
                        · rcases p4907_3 (m.d 1 2) (by simp) with h4920 | h4920
                          · rcases p4907_3 (m.d 2 3) (by simp) with h4921 | h4921
                            · linarith only [h4558, h4921, hlam]
                            · rcases p4907_3 (m.d 2 4) (by simp) with h4923 | h4923
                              · linarith only [h4923, hlam, p4907_0]
                              · rcases p4907_3 (m.d 2 5) (by simp) with h4925 | h4925
                                · linarith only [h4560, h4925, hlam]
                                · linarith only [h4903, h4925, hlam]
                          · linarith only [h4844, h4920, hlam]
                        · linarith only [h4919, hlam, p4907_0]
                      · have p4907_0 := h4907c.1
                        have p4907_1 := h4907c.2.1
                        have p4907_2 := h4907c.2.2.1
                        have p4907_3 := h4907c.2.2.2
                        rcases p4907_3 (m.d 0 2) (by simp) with h4930 | h4930
                        · rcases p4907_3 (m.d 1 2) (by simp) with h4931 | h4931
                          · rcases p4907_3 (m.d 2 3) (by simp) with h4932 | h4932
                            · linarith only [h4558, h4932, hlam]
                            · rcases p4907_3 (m.d 2 4) (by simp) with h4934 | h4934
                              · linarith only [h4559, h4934, hlam]
                              · rcases p4907_3 (m.d 2 5) (by simp) with h4936 | h4936
                                · linarith only [h4936, hlam, p4907_0]
                                · rcases h4bigk with h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c | h4938c
                                  · have p4938_0 := h4938c.1
                                    have p4938_1 := h4938c.2.1
                                    have p4938_2 := h4938c.2.2.1
                                    have p4938_3 := h4938c.2.2.2
                                    linarith only [hlam, p4938_0]
                                  · have p4938_0 := h4938c.1
                                    have p4938_1 := h4938c.2.1
                                    have p4938_2 := h4938c.2.2.1
                                    have p4938_3 := h4938c.2.2.2
                                    linarith only [h4130, hlam, p4938_1]
                                  · have p4938_0 := h4938c.1
                                    have p4938_1 := h4938c.2.1
                                    have p4938_2 := h4938c.2.2.1
                                    have p4938_3 := h4938c.2.2.2
                                    linarith only [h4562, h4843, h4846, h4847, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4938_1, u4ehi2]
                                  · have p4938_0 := h4938c.1
                                    have p4938_1 := h4938c.2.1
                                    have p4938_2 := h4938c.2.2.1
                                    have p4938_3 := h4938c.2.2.2
                                    linarith only [h4562, h4843, h4846, h4847, h4848, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4938_1]
                                  · have p4938_0 := h4938c.1
                                    have p4938_1 := h4938c.2.1
                                    have p4938_2 := h4938c.2.2.1
                                    have p4938_3 := h4938c.2.2.2
                                    linarith only [h4562, hlam, p4938_0]
                                  · have p4938_0 := h4938c.1
                                    have p4938_1 := h4938c.2.1
                                    have p4938_2 := h4938c.2.2.1
                                    have p4938_3 := h4938c.2.2.2
                                    rcases p4938_3 (m.d 0 4) (by simp) with h4944 | h4944
                                    · linarith only [h4130, h4944, hlam]
                                    · rcases p4938_3 (m.d 1 4) (by simp) with h4946 | h4946
                                      · rcases p4938_3 (m.d 2 4) (by simp) with h4947 | h4947
                                        · linarith only [h4844, h4947, hlam]
                                        · rcases p4938_3 (m.d 3 4) (by simp) with h4949 | h4949
                                          · linarith only [h4846, h4949, hlam]
                                          · rcases p4938_3 (m.d 4 5) (by simp) with h4951 | h4951
                                            · linarith only [h4847, h4951, hlam]
                                            · linarith only [h4562, h4951, hlam]
                                      · linarith only [h4130, h4946, hlam]
                                  · have p4938_0 := h4938c.1
                                    have p4938_1 := h4938c.2.1
                                    have p4938_2 := h4938c.2.2.1
                                    have p4938_3 := h4938c.2.2.2
                                    linarith only [hlam, p4938_0]
                                  · have p4938_0 := h4938c.1
                                    have p4938_1 := h4938c.2.1
                                    have p4938_2 := h4938c.2.2.1
                                    have p4938_3 := h4938c.2.2.2
                                    rcases p4938_3 (m.d 0 4) (by simp) with h4956 | h4956
                                    · linarith only [h4130, h4956, hlam]
                                    · linarith only [h4559, h4956, hlam]
                                  · have p4938_0 := h4938c.1
                                    have p4938_1 := h4938c.2.1
                                    have p4938_2 := h4938c.2.2.1
                                    have p4938_3 := h4938c.2.2.2
                                    rcases p4938_3 (m.d 0 4) (by simp) with h4959 | h4959
                                    · linarith only [h4130, h4959, hlam]
                                    · linarith only [h4561, h4959, hlam]
                                  · have p4938_0 := h4938c.1
                                    have p4938_1 := h4938c.2.1
                                    have p4938_2 := h4938c.2.2.1
                                    have p4938_3 := h4938c.2.2.2
                                    linarith only [h4562, h4843, h4846, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4938_1, u4ehi0]
                                  · have p4938_0 := h4938c.1
                                    have p4938_1 := h4938c.2.1
                                    have p4938_2 := h4938c.2.2.1
                                    have p4938_3 := h4938c.2.2.2
                                    linarith only [h4559, hlam, p4938_0]
                                  · have p4938_0 := h4938c.1
                                    have p4938_1 := h4938c.2.1
                                    have p4938_2 := h4938c.2.2.1
                                    have p4938_3 := h4938c.2.2.2
                                    linarith only [h4844, hlam, p4938_0]
                                  · have p4938_0 := h4938c.1
                                    have p4938_1 := h4938c.2.1
                                    have p4938_2 := h4938c.2.2.1
                                    have p4938_3 := h4938c.2.2.2
                                    linarith only [hlam, p4938_0]
                                  · have p4938_0 := h4938c.1
                                    have p4938_1 := h4938c.2.1
                                    have p4938_2 := h4938c.2.2.1
                                    have p4938_3 := h4938c.2.2.2
                                    linarith only [h4848, hlam, p4938_1]
                                  · have p4938_0 := h4938c.1
                                    have p4938_1 := h4938c.2.1
                                    have p4938_2 := h4938c.2.2.1
                                    have p4938_3 := h4938c.2.2.2
                                    linarith only [h4903, hlam, p4938_0]
                                  · have p4938_0 := h4938c.1
                                    have p4938_1 := h4938c.2.1
                                    have p4938_2 := h4938c.2.2.1
                                    have p4938_3 := h4938c.2.2.2
                                    linarith only [h4561, hlam, p4938_0]
                                  · have p4938_0 := h4938c.1
                                    have p4938_1 := h4938c.2.1
                                    have p4938_2 := h4938c.2.2.1
                                    have p4938_3 := h4938c.2.2.2
                                    linarith only [h4846, hlam, p4938_0]
                                  · have p4938_0 := h4938c.1
                                    have p4938_1 := h4938c.2.1
                                    have p4938_2 := h4938c.2.2.1
                                    have p4938_3 := h4938c.2.2.2
                                    linarith only [h4561, hc03, hlam, hphi, ht0b, ht45, ht5b, p4938_1, u4ehi2]
                                  · have p4938_0 := h4938c.1
                                    have p4938_1 := h4938c.2.1
                                    have p4938_2 := h4938c.2.2.1
                                    have p4938_3 := h4938c.2.2.2
                                    linarith only [hlam, p4938_0]
                                  · have p4938_0 := h4938c.1
                                    have p4938_1 := h4938c.2.1
                                    have p4938_2 := h4938c.2.2.1
                                    have p4938_3 := h4938c.2.2.2
                                    linarith only [h4905, hlam, p4938_0]
                                  · have p4938_0 := h4938c.1
                                    have p4938_1 := h4938c.2.1
                                    have p4938_2 := h4938c.2.2.1
                                    have p4938_3 := h4938c.2.2.2
                                    linarith only [hc45, hlam, hphi, p4938_1, u4ehi0]
                                  · have p4938_0 := h4938c.1
                                    have p4938_1 := h4938c.2.1
                                    have p4938_2 := h4938c.2.2.1
                                    have p4938_3 := h4938c.2.2.2
                                    linarith only [h4847, hlam, p4938_0]
                                  · have p4938_0 := h4938c.1
                                    have p4938_1 := h4938c.2.1
                                    have p4938_2 := h4938c.2.2.1
                                    have p4938_3 := h4938c.2.2.2
                                    linarith only [h4843, h4846, h4847, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4938_1, u4ehi2]
                                  · have p4938_0 := h4938c.1
                                    have p4938_1 := h4938c.2.1
                                    have p4938_2 := h4938c.2.2.1
                                    have p4938_3 := h4938c.2.2.2
                                    linarith only [h4843, h4846, h4847, h4848, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4938_1]
                                  · have p4938_0 := h4938c.1
                                    have p4938_1 := h4938c.2.1
                                    have p4938_2 := h4938c.2.2.1
                                    have p4938_3 := h4938c.2.2.2
                                    linarith only [hlam, p4938_0]
                          · linarith only [h4845, h4931, hlam]
                        · linarith only [h4930, hlam, p4907_0]
                      · have p4907_0 := h4907c.1
                        have p4907_1 := h4907c.2.1
                        have p4907_2 := h4907c.2.2.1
                        have p4907_3 := h4907c.2.2.2
                        linarith only [h4559, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4907_1, u4ehi2]
                      · have p4907_0 := h4907c.1
                        have p4907_1 := h4907c.2.1
                        have p4907_2 := h4907c.2.2.1
                        have p4907_3 := h4907c.2.2.2
                        linarith only [hlam, p4907_0]
                      · have p4907_0 := h4907c.1
                        have p4907_1 := h4907c.2.1
                        have p4907_2 := h4907c.2.2.1
                        have p4907_3 := h4907c.2.2.2
                        linarith only [h4561, h4562, h4843, h4846, h4847, h4848, hlam, p4907_2]
                      · have p4907_0 := h4907c.1
                        have p4907_1 := h4907c.2.1
                        have p4907_2 := h4907c.2.2.1
                        have p4907_3 := h4907c.2.2.2
                        rcases p4907_3 (m.d 0 2) (by simp) with h4983 | h4983
                        · linarith only [h0, h4983, hlam]
                        · linarith only [h4559, h4983, hlam]
                      · have p4907_0 := h4907c.1
                        have p4907_1 := h4907c.2.1
                        have p4907_2 := h4907c.2.2.1
                        have p4907_3 := h4907c.2.2.2
                        rcases p4907_3 (m.d 0 2) (by simp) with h4986 | h4986
                        · linarith only [h0, h4986, hlam]
                        · linarith only [h4560, h4986, hlam]
                      · have p4907_0 := h4907c.1
                        have p4907_1 := h4907c.2.1
                        have p4907_2 := h4907c.2.2.1
                        have p4907_3 := h4907c.2.2.2
                        linarith only [h4558, hlam, p4907_0]
                      · have p4907_0 := h4907c.1
                        have p4907_1 := h4907c.2.1
                        have p4907_2 := h4907c.2.2.1
                        have p4907_3 := h4907c.2.2.2
                        linarith only [h4843, hlam, p4907_0]
                      · have p4907_0 := h4907c.1
                        have p4907_1 := h4907c.2.1
                        have p4907_2 := h4907c.2.2.1
                        have p4907_3 := h4907c.2.2.2
                        linarith only [hlam, p4907_0]
                      · have p4907_0 := h4907c.1
                        have p4907_1 := h4907c.2.1
                        have p4907_2 := h4907c.2.2.1
                        have p4907_3 := h4907c.2.2.2
                        linarith only [h4848, hlam, p4907_1]
                      · have p4907_0 := h4907c.1
                        have p4907_1 := h4907c.2.1
                        have p4907_2 := h4907c.2.2.1
                        have p4907_3 := h4907c.2.2.2
                        linarith only [h4901, hlam, p4907_1]
                      · have p4907_0 := h4907c.1
                        have p4907_1 := h4907c.2.1
                        have p4907_2 := h4907c.2.2.1
                        have p4907_3 := h4907c.2.2.2
                        linarith only [h4559, hlam, p4907_0]
                      · have p4907_0 := h4907c.1
                        have p4907_1 := h4907c.2.1
                        have p4907_2 := h4907c.2.2.1
                        have p4907_3 := h4907c.2.2.2
                        linarith only [h4844, hlam, p4907_0]
                      · have p4907_0 := h4907c.1
                        have p4907_1 := h4907c.2.1
                        have p4907_2 := h4907c.2.2.1
                        have p4907_3 := h4907c.2.2.2
                        linarith only [h4559, h4562, h4843, h4846, h4847, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4907_1]
                      · have p4907_0 := h4907c.1
                        have p4907_1 := h4907c.2.1
                        have p4907_2 := h4907c.2.2.1
                        have p4907_3 := h4907c.2.2.2
                        linarith only [hlam, p4907_0]
                      · have p4907_0 := h4907c.1
                        have p4907_1 := h4907c.2.1
                        have p4907_2 := h4907c.2.2.1
                        have p4907_3 := h4907c.2.2.2
                        linarith only [h4903, hlam, p4907_0]
                      · have p4907_0 := h4907c.1
                        have p4907_1 := h4907c.2.1
                        have p4907_2 := h4907c.2.2.1
                        have p4907_3 := h4907c.2.2.2
                        linarith only [h4560, hlam, p4907_0]
                      · have p4907_0 := h4907c.1
                        have p4907_1 := h4907c.2.1
                        have p4907_2 := h4907c.2.2.1
                        have p4907_3 := h4907c.2.2.2
                        linarith only [h4845, hlam, p4907_0]
                      · have p4907_0 := h4907c.1
                        have p4907_1 := h4907c.2.1
                        have p4907_2 := h4907c.2.2.1
                        have p4907_3 := h4907c.2.2.2
                        rcases p4907_3 (m.d 0 2) (by simp) with h5001 | h5001
                        · rcases p4907_3 (m.d 1 2) (by simp) with h5002 | h5002
                          · rcases p4907_3 (m.d 2 3) (by simp) with h5003 | h5003
                            · linarith only [h4901, h5003, hlam]
                            · rcases p4907_3 (m.d 2 4) (by simp) with h5005 | h5005
                              · linarith only [h4903, h5005, hlam]
                              · linarith only [h4848, h5005, hlam]
                          · linarith only [h4843, h5002, hlam]
                        · linarith only [h4558, h5001, hlam]
                      · have p4907_0 := h4907c.1
                        have p4907_1 := h4907c.2.1
                        have p4907_2 := h4907c.2.2.1
                        have p4907_3 := h4907c.2.2.2
                        linarith only [h4560, hc02, hlam, hphi, ht0b, ht45, ht5b, p4907_1, u4ehi2]
                      · have p4907_0 := h4907c.1
                        have p4907_1 := h4907c.2.1
                        have p4907_2 := h4907c.2.2.1
                        have p4907_3 := h4907c.2.2.2
                        linarith only [hlam, p4907_0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5012 | h5012
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5013 | h5013
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5014 | h5014
                  · linarith only [h4130, h4847, h5014, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5016 | h5016
                    · linarith only [h4130, h4558, h4847, h5012, h5016, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                    · rcases h2bigk with h5018c | h5018c | h5018c | h5018c | h5018c | h5018c | h5018c | h5018c | h5018c | h5018c | h5018c | h5018c | h5018c | h5018c | h5018c | h5018c | h5018c | h5018c | h5018c | h5018c | h5018c | h5018c | h5018c | h5018c | h5018c
                      · have p5018_0 := h5018c.1
                        have p5018_1 := h5018c.2.1
                        have p5018_2 := h5018c.2.2.1
                        have p5018_3 := h5018c.2.2.2
                        linarith only [hlam, p5018_0]
                      · have p5018_0 := h5018c.1
                        have p5018_1 := h5018c.2.1
                        have p5018_2 := h5018c.2.2.1
                        have p5018_3 := h5018c.2.2.2
                        linarith only [h0, hlam, p5018_0]
                      · have p5018_0 := h5018c.1
                        have p5018_1 := h5018c.2.1
                        have p5018_2 := h5018c.2.2.1
                        have p5018_3 := h5018c.2.2.2
                        linarith only [h0, h5012, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5018_1, u4ehi3]
                      · have p5018_0 := h5018c.1
                        have p5018_1 := h5018c.2.1
                        have p5018_2 := h5018c.2.2.1
                        have p5018_3 := h5018c.2.2.2
                        rcases p5018_3 (m.d 0 2) (by simp) with h5022 | h5022
                        · rcases p5018_3 (m.d 1 2) (by simp) with h5023 | h5023
                          · rcases p5018_3 (m.d 2 3) (by simp) with h5024 | h5024
                            · linarith only [h4558, h5024, hlam]
                            · linarith only [h5012, h5024, hlam]
                          · linarith only [h4844, h5023, hlam]
                        · linarith only [h5022, hlam, p5018_0]
                      · have p5018_0 := h5018c.1
                        have p5018_1 := h5018c.2.1
                        have p5018_2 := h5018c.2.2.1
                        have p5018_3 := h5018c.2.2.2
                        rcases p5018_3 (m.d 0 2) (by simp) with h5029 | h5029
                        · rcases p5018_3 (m.d 1 2) (by simp) with h5030 | h5030
                          · rcases p5018_3 (m.d 2 3) (by simp) with h5031 | h5031
                            · linarith only [h4558, h5031, hlam]
                            · linarith only [h5013, h5031, hlam]
                          · linarith only [h4845, h5030, hlam]
                        · linarith only [h5029, hlam, p5018_0]
                      · have p5018_0 := h5018c.1
                        have p5018_1 := h5018c.2.1
                        have p5018_2 := h5018c.2.2.1
                        have p5018_3 := h5018c.2.2.2
                        linarith only [h4558, h5013, h5016, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5018_1, u4ehi3]
                      · have p5018_0 := h5018c.1
                        have p5018_1 := h5018c.2.1
                        have p5018_2 := h5018c.2.2.1
                        have p5018_3 := h5018c.2.2.2
                        linarith only [hlam, p5018_0]
                      · have p5018_0 := h5018c.1
                        have p5018_1 := h5018c.2.1
                        have p5018_2 := h5018c.2.2.1
                        have p5018_3 := h5018c.2.2.2
                        linarith only [h5013, h5016, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5018_1, u4ehi3]
                      · have p5018_0 := h5018c.1
                        have p5018_1 := h5018c.2.1
                        have p5018_2 := h5018c.2.2.1
                        have p5018_3 := h5018c.2.2.2
                        rcases p5018_3 (m.d 0 2) (by simp) with h5039 | h5039
                        · linarith only [h0, h5039, hlam]
                        · linarith only [h4559, h5039, hlam]
                      · have p5018_0 := h5018c.1
                        have p5018_1 := h5018c.2.1
                        have p5018_2 := h5018c.2.2.1
                        have p5018_3 := h5018c.2.2.2
                        rcases p5018_3 (m.d 0 2) (by simp) with h5042 | h5042
                        · linarith only [h0, h5042, hlam]
                        · linarith only [h4560, h5042, hlam]
                      · have p5018_0 := h5018c.1
                        have p5018_1 := h5018c.2.1
                        have p5018_2 := h5018c.2.2.1
                        have p5018_3 := h5018c.2.2.2
                        linarith only [h4558, hlam, p5018_0]
                      · have p5018_0 := h5018c.1
                        have p5018_1 := h5018c.2.1
                        have p5018_2 := h5018c.2.2.1
                        have p5018_3 := h5018c.2.2.2
                        linarith only [h4843, hlam, p5018_0]
                      · have p5018_0 := h5018c.1
                        have p5018_1 := h5018c.2.1
                        have p5018_2 := h5018c.2.2.1
                        have p5018_3 := h5018c.2.2.2
                        linarith only [hlam, p5018_0]
                      · have p5018_0 := h5018c.1
                        have p5018_1 := h5018c.2.1
                        have p5018_2 := h5018c.2.2.1
                        have p5018_3 := h5018c.2.2.2
                        linarith only [h4558, h5012, hc02, hlam, hphi, ht0b, ht45, ht5b, p5018_1, u4ehi3]
                      · have p5018_0 := h5018c.1
                        have p5018_1 := h5018c.2.1
                        have p5018_2 := h5018c.2.2.1
                        have p5018_3 := h5018c.2.2.2
                        linarith only [h0, h4558, h5012, h5014, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5018_1, u4ehi3]
                      · have p5018_0 := h5018c.1
                        have p5018_1 := h5018c.2.1
                        have p5018_2 := h5018c.2.2.1
                        have p5018_3 := h5018c.2.2.2
                        linarith only [h4559, hlam, p5018_0]
                      · have p5018_0 := h5018c.1
                        have p5018_1 := h5018c.2.1
                        have p5018_2 := h5018c.2.2.1
                        have p5018_3 := h5018c.2.2.2
                        linarith only [h4844, hlam, p5018_0]
                      · have p5018_0 := h5018c.1
                        have p5018_1 := h5018c.2.1
                        have p5018_2 := h5018c.2.2.1
                        have p5018_3 := h5018c.2.2.2
                        linarith only [h5012, hlam, p5018_0]
                      · have p5018_0 := h5018c.1
                        have p5018_1 := h5018c.2.1
                        have p5018_2 := h5018c.2.2.1
                        have p5018_3 := h5018c.2.2.2
                        linarith only [hlam, p5018_0]
                      · have p5018_0 := h5018c.1
                        have p5018_1 := h5018c.2.1
                        have p5018_2 := h5018c.2.2.1
                        have p5018_3 := h5018c.2.2.2
                        linarith only [h5014, hlam, p5018_0]
                      · have p5018_0 := h5018c.1
                        have p5018_1 := h5018c.2.1
                        have p5018_2 := h5018c.2.2.1
                        have p5018_3 := h5018c.2.2.2
                        linarith only [h4560, hlam, p5018_0]
                      · have p5018_0 := h5018c.1
                        have p5018_1 := h5018c.2.1
                        have p5018_2 := h5018c.2.2.1
                        have p5018_3 := h5018c.2.2.2
                        linarith only [h4845, hlam, p5018_0]
                      · have p5018_0 := h5018c.1
                        have p5018_1 := h5018c.2.1
                        have p5018_2 := h5018c.2.2.1
                        have p5018_3 := h5018c.2.2.2
                        linarith only [h5013, hlam, p5018_0]
                      · have p5018_0 := h5018c.1
                        have p5018_1 := h5018c.2.1
                        have p5018_2 := h5018c.2.2.1
                        have p5018_3 := h5018c.2.2.2
                        linarith only [h0, h4560, h5012, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5018_1, u4ehi3]
                      · have p5018_0 := h5018c.1
                        have p5018_1 := h5018c.2.1
                        have p5018_2 := h5018c.2.2.1
                        have p5018_3 := h5018c.2.2.2
                        linarith only [hlam, p5018_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5060 | h5060
                  · linarith only [h4130, h4847, h5060, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5062 | h5062
                    · linarith only [h4130, h4847, h5062, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h5012, h5013, h5062, hc45, hlam, hphi, u4ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5065 | h5065
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5066 | h5066
                  · linarith only [h0, h4359, h4559, h4847, h5066, hc01, hc12, hlam, hphi]
                  · linarith only [h4130, h4561, h4847, h5012, h5065, h5066, hc45, hlam, hphi, u4ehi2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5069 | h5069
                  · linarith only [h4130, h4847, h5069, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5071 | h5071
                    · linarith only [h4130, h4561, h4847, h5071, hlam]
                    · rcases h2bigk with h5073c | h5073c | h5073c | h5073c | h5073c | h5073c | h5073c | h5073c | h5073c | h5073c | h5073c | h5073c | h5073c | h5073c | h5073c | h5073c | h5073c | h5073c | h5073c | h5073c | h5073c | h5073c | h5073c | h5073c | h5073c
                      · have p5073_0 := h5073c.1
                        have p5073_1 := h5073c.2.1
                        have p5073_2 := h5073c.2.2.1
                        have p5073_3 := h5073c.2.2.2
                        linarith only [hlam, p5073_0]
                      · have p5073_0 := h5073c.1
                        have p5073_1 := h5073c.2.1
                        have p5073_2 := h5073c.2.2.1
                        have p5073_3 := h5073c.2.2.2
                        linarith only [h0, hlam, p5073_0]
                      · have p5073_0 := h5073c.1
                        have p5073_1 := h5073c.2.1
                        have p5073_2 := h5073c.2.2.1
                        have p5073_3 := h5073c.2.2.2
                        rcases p5073_3 (m.d 0 2) (by simp) with h5076 | h5076
                        · rcases p5073_3 (m.d 1 2) (by simp) with h5077 | h5077
                          · rcases p5073_3 (m.d 2 3) (by simp) with h5078 | h5078
                            · linarith only [h5078, hlam, p5073_0]
                            · rcases p5073_3 (m.d 2 4) (by simp) with h5080 | h5080
                              · linarith only [h4559, h5080, hlam]
                              · linarith only [h5012, h5080, hlam]
                          · linarith only [h4843, h5077, hlam]
                        · linarith only [h5076, hlam, p5073_0]
                      · have p5073_0 := h5073c.1
                        have p5073_1 := h5073c.2.1
                        have p5073_2 := h5073c.2.2.1
                        have p5073_3 := h5073c.2.2.2
                        rcases p5073_3 (m.d 0 2) (by simp) with h5085 | h5085
                        · rcases p5073_3 (m.d 1 2) (by simp) with h5086 | h5086
                          · rcases p5073_3 (m.d 2 3) (by simp) with h5087 | h5087
                            · linarith only [h4558, h5087, hlam]
                            · rcases p5073_3 (m.d 2 4) (by simp) with h5089 | h5089
                              · linarith only [h5089, hlam, p5073_0]
                              · rcases p5073_3 (m.d 2 5) (by simp) with h5091 | h5091
                                · linarith only [h4560, h5091, hlam]
                                · linarith only [h5069, h5091, hlam]
                          · linarith only [h4844, h5086, hlam]
                        · linarith only [h5085, hlam, p5073_0]
                      · have p5073_0 := h5073c.1
                        have p5073_1 := h5073c.2.1
                        have p5073_2 := h5073c.2.2.1
                        have p5073_3 := h5073c.2.2.2
                        rcases p5073_3 (m.d 0 2) (by simp) with h5096 | h5096
                        · rcases p5073_3 (m.d 1 2) (by simp) with h5097 | h5097
                          · rcases p5073_3 (m.d 2 3) (by simp) with h5098 | h5098
                            · linarith only [h4558, h5098, hlam]
                            · rcases p5073_3 (m.d 2 4) (by simp) with h5100 | h5100
                              · linarith only [h4559, h5100, hlam]
                              · rcases p5073_3 (m.d 2 5) (by simp) with h5102 | h5102
                                · linarith only [h5102, hlam, p5073_0]
                                · rcases h4bigk with h5104c | h5104c | h5104c | h5104c | h5104c | h5104c | h5104c | h5104c | h5104c | h5104c | h5104c | h5104c | h5104c | h5104c | h5104c | h5104c | h5104c | h5104c | h5104c | h5104c | h5104c | h5104c | h5104c | h5104c | h5104c
                                  · have p5104_0 := h5104c.1
                                    have p5104_1 := h5104c.2.1
                                    have p5104_2 := h5104c.2.2.1
                                    have p5104_3 := h5104c.2.2.2
                                    linarith only [hlam, p5104_0]
                                  · have p5104_0 := h5104c.1
                                    have p5104_1 := h5104c.2.1
                                    have p5104_2 := h5104c.2.2.1
                                    have p5104_3 := h5104c.2.2.2
                                    linarith only [h4130, hlam, p5104_1]
                                  · have p5104_0 := h5104c.1
                                    have p5104_1 := h5104c.2.1
                                    have p5104_2 := h5104c.2.2.1
                                    have p5104_3 := h5104c.2.2.2
                                    linarith only [h4130, h4847, hc45, hlam, hphi, p5104_1, u4ehi2]
                                  · have p5104_0 := h5104c.1
                                    have p5104_1 := h5104c.2.1
                                    have p5104_2 := h5104c.2.2.1
                                    have p5104_3 := h5104c.2.2.2
                                    linarith only [h4130, h4847, h5012, hc23, hc45, hlam, hphi, ht34, p5104_1]
                                  · have p5104_0 := h5104c.1
                                    have p5104_1 := h5104c.2.1
                                    have p5104_2 := h5104c.2.2.1
                                    have p5104_3 := h5104c.2.2.2
                                    linarith only [h4562, hlam, p5104_0]
                                  · have p5104_0 := h5104c.1
                                    have p5104_1 := h5104c.2.1
                                    have p5104_2 := h5104c.2.2.1
                                    have p5104_3 := h5104c.2.2.2
                                    linarith only [h4847, hc45, hlam, hphi, p5104_1, u4ehi0]
                                  · have p5104_0 := h5104c.1
                                    have p5104_1 := h5104c.2.1
                                    have p5104_2 := h5104c.2.2.1
                                    have p5104_3 := h5104c.2.2.2
                                    linarith only [hlam, p5104_0]
                                  · have p5104_0 := h5104c.1
                                    have p5104_1 := h5104c.2.1
                                    have p5104_2 := h5104c.2.2.1
                                    have p5104_3 := h5104c.2.2.2
                                    linarith only [h4847, hc45, hlam, hphi, p5104_1, u4ehi2]
                                  · have p5104_0 := h5104c.1
                                    have p5104_1 := h5104c.2.1
                                    have p5104_2 := h5104c.2.2.1
                                    have p5104_3 := h5104c.2.2.2
                                    linarith only [h4847, h5012, hc23, hc45, hlam, hphi, ht34, p5104_1]
                                  · have p5104_0 := h5104c.1
                                    have p5104_1 := h5104c.2.1
                                    have p5104_2 := h5104c.2.2.1
                                    have p5104_3 := h5104c.2.2.2
                                    linarith only [h4847, hlam, p5104_0]
                                  · have p5104_0 := h5104c.1
                                    have p5104_1 := h5104c.2.1
                                    have p5104_2 := h5104c.2.2.1
                                    have p5104_3 := h5104c.2.2.2
                                    linarith only [h4559, hlam, p5104_0]
                                  · have p5104_0 := h5104c.1
                                    have p5104_1 := h5104c.2.1
                                    have p5104_2 := h5104c.2.2.1
                                    have p5104_3 := h5104c.2.2.2
                                    linarith only [h4844, hlam, p5104_0]
                                  · have p5104_0 := h5104c.1
                                    have p5104_1 := h5104c.2.1
                                    have p5104_2 := h5104c.2.2.1
                                    have p5104_3 := h5104c.2.2.2
                                    linarith only [hlam, p5104_0]
                                  · have p5104_0 := h5104c.1
                                    have p5104_1 := h5104c.2.1
                                    have p5104_2 := h5104c.2.2.1
                                    have p5104_3 := h5104c.2.2.2
                                    linarith only [h5012, hlam, p5104_1]
                                  · have p5104_0 := h5104c.1
                                    have p5104_1 := h5104c.2.1
                                    have p5104_2 := h5104c.2.2.1
                                    have p5104_3 := h5104c.2.2.2
                                    linarith only [h5069, hlam, p5104_0]
                                  · have p5104_0 := h5104c.1
                                    have p5104_1 := h5104c.2.1
                                    have p5104_2 := h5104c.2.2.1
                                    have p5104_3 := h5104c.2.2.2
                                    linarith only [h4561, hlam, p5104_0]
                                  · have p5104_0 := h5104c.1
                                    have p5104_1 := h5104c.2.1
                                    have p5104_2 := h5104c.2.2.1
                                    have p5104_3 := h5104c.2.2.2
                                    linarith only [h4846, hlam, p5104_0]
                                  · have p5104_0 := h5104c.1
                                    have p5104_1 := h5104c.2.1
                                    have p5104_2 := h5104c.2.2.1
                                    have p5104_3 := h5104c.2.2.2
                                    linarith only [h4130, h4561, h4847, hc45, hlam, hphi, p5104_1, u4ehi2]
                                  · have p5104_0 := h5104c.1
                                    have p5104_1 := h5104c.2.1
                                    have p5104_2 := h5104c.2.2.1
                                    have p5104_3 := h5104c.2.2.2
                                    linarith only [hlam, p5104_0]
                                  · have p5104_0 := h5104c.1
                                    have p5104_1 := h5104c.2.1
                                    have p5104_2 := h5104c.2.2.1
                                    have p5104_3 := h5104c.2.2.2
                                    linarith only [h5071, hlam, p5104_0]
                                  · have p5104_0 := h5104c.1
                                    have p5104_1 := h5104c.2.1
                                    have p5104_2 := h5104c.2.2.1
                                    have p5104_3 := h5104c.2.2.2
                                    linarith only [hc45, hlam, hphi, p5104_1, u4ehi0]
                                  · have p5104_0 := h5104c.1
                                    have p5104_1 := h5104c.2.1
                                    have p5104_2 := h5104c.2.2.1
                                    have p5104_3 := h5104c.2.2.2
                                    linarith only [h4130, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5104_1]
                                  · have p5104_0 := h5104c.1
                                    have p5104_1 := h5104c.2.1
                                    have p5104_2 := h5104c.2.2.1
                                    have p5104_3 := h5104c.2.2.2
                                    linarith only [hc45, hlam, hphi, p5104_1, u4ehi2]
                                  · have p5104_0 := h5104c.1
                                    have p5104_1 := h5104c.2.1
                                    have p5104_2 := h5104c.2.2.1
                                    have p5104_3 := h5104c.2.2.2
                                    linarith only [h5012, hc23, hc45, hlam, hphi, ht34, p5104_1]
                                  · have p5104_0 := h5104c.1
                                    have p5104_1 := h5104c.2.1
                                    have p5104_2 := h5104c.2.2.1
                                    have p5104_3 := h5104c.2.2.2
                                    linarith only [hlam, p5104_0]
                          · linarith only [h4845, h5097, hlam]
                        · linarith only [h5096, hlam, p5073_0]
                      · have p5073_0 := h5073c.1
                        have p5073_1 := h5073c.2.1
                        have p5073_2 := h5073c.2.2.1
                        have p5073_3 := h5073c.2.2.2
                        linarith only [h4559, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5073_1, u4ehi2]
                      · have p5073_0 := h5073c.1
                        have p5073_1 := h5073c.2.1
                        have p5073_2 := h5073c.2.2.1
                        have p5073_3 := h5073c.2.2.2
                        linarith only [hlam, p5073_0]
                      · have p5073_0 := h5073c.1
                        have p5073_1 := h5073c.2.1
                        have p5073_2 := h5073c.2.2.1
                        have p5073_3 := h5073c.2.2.2
                        rcases p5073_3 (m.d 0 2) (by simp) with h5134 | h5134
                        · linarith only [h0, h5134, hlam]
                        · linarith only [h4558, h5134, hlam]
                      · have p5073_0 := h5073c.1
                        have p5073_1 := h5073c.2.1
                        have p5073_2 := h5073c.2.2.1
                        have p5073_3 := h5073c.2.2.2
                        rcases p5073_3 (m.d 0 2) (by simp) with h5137 | h5137
                        · linarith only [h0, h5137, hlam]
                        · linarith only [h4559, h5137, hlam]
                      · have p5073_0 := h5073c.1
                        have p5073_1 := h5073c.2.1
                        have p5073_2 := h5073c.2.2.1
                        have p5073_3 := h5073c.2.2.2
                        rcases p5073_3 (m.d 0 2) (by simp) with h5140 | h5140
                        · linarith only [h0, h5140, hlam]
                        · linarith only [h4560, h5140, hlam]
                      · have p5073_0 := h5073c.1
                        have p5073_1 := h5073c.2.1
                        have p5073_2 := h5073c.2.2.1
                        have p5073_3 := h5073c.2.2.2
                        linarith only [h4558, hlam, p5073_0]
                      · have p5073_0 := h5073c.1
                        have p5073_1 := h5073c.2.1
                        have p5073_2 := h5073c.2.2.1
                        have p5073_3 := h5073c.2.2.2
                        linarith only [h4843, hlam, p5073_0]
                      · have p5073_0 := h5073c.1
                        have p5073_1 := h5073c.2.1
                        have p5073_2 := h5073c.2.2.1
                        have p5073_3 := h5073c.2.2.2
                        linarith only [hlam, p5073_0]
                      · have p5073_0 := h5073c.1
                        have p5073_1 := h5073c.2.1
                        have p5073_2 := h5073c.2.2.1
                        have p5073_3 := h5073c.2.2.2
                        linarith only [h5012, hlam, p5073_1]
                      · have p5073_0 := h5073c.1
                        have p5073_1 := h5073c.2.1
                        have p5073_2 := h5073c.2.2.1
                        have p5073_3 := h5073c.2.2.2
                        linarith only [h5065, hlam, p5073_1]
                      · have p5073_0 := h5073c.1
                        have p5073_1 := h5073c.2.1
                        have p5073_2 := h5073c.2.2.1
                        have p5073_3 := h5073c.2.2.2
                        linarith only [h4559, hlam, p5073_0]
                      · have p5073_0 := h5073c.1
                        have p5073_1 := h5073c.2.1
                        have p5073_2 := h5073c.2.2.1
                        have p5073_3 := h5073c.2.2.2
                        linarith only [h4844, hlam, p5073_0]
                      · have p5073_0 := h5073c.1
                        have p5073_1 := h5073c.2.1
                        have p5073_2 := h5073c.2.2.1
                        have p5073_3 := h5073c.2.2.2
                        linarith only [h4559, h4562, hc23, hc45, hlam, hphi, ht34, p5073_1]
                      · have p5073_0 := h5073c.1
                        have p5073_1 := h5073c.2.1
                        have p5073_2 := h5073c.2.2.1
                        have p5073_3 := h5073c.2.2.2
                        linarith only [hlam, p5073_0]
                      · have p5073_0 := h5073c.1
                        have p5073_1 := h5073c.2.1
                        have p5073_2 := h5073c.2.2.1
                        have p5073_3 := h5073c.2.2.2
                        linarith only [h5069, hlam, p5073_0]
                      · have p5073_0 := h5073c.1
                        have p5073_1 := h5073c.2.1
                        have p5073_2 := h5073c.2.2.1
                        have p5073_3 := h5073c.2.2.2
                        linarith only [h4560, hlam, p5073_0]
                      · have p5073_0 := h5073c.1
                        have p5073_1 := h5073c.2.1
                        have p5073_2 := h5073c.2.2.1
                        have p5073_3 := h5073c.2.2.2
                        linarith only [h4845, hlam, p5073_0]
                      · have p5073_0 := h5073c.1
                        have p5073_1 := h5073c.2.1
                        have p5073_2 := h5073c.2.2.1
                        have p5073_3 := h5073c.2.2.2
                        rcases p5073_3 (m.d 0 2) (by simp) with h5155 | h5155
                        · rcases p5073_3 (m.d 1 2) (by simp) with h5156 | h5156
                          · rcases p5073_3 (m.d 2 3) (by simp) with h5157 | h5157
                            · linarith only [h5065, h5157, hlam]
                            · rcases p5073_3 (m.d 2 4) (by simp) with h5159 | h5159
                              · linarith only [h5069, h5159, hlam]
                              · linarith only [h5012, h5159, hlam]
                          · linarith only [h4843, h5156, hlam]
                        · linarith only [h4558, h5155, hlam]
                      · have p5073_0 := h5073c.1
                        have p5073_1 := h5073c.2.1
                        have p5073_2 := h5073c.2.2.1
                        have p5073_3 := h5073c.2.2.2
                        linarith only [h4560, hc02, hlam, hphi, ht0b, ht45, ht5b, p5073_1, u4ehi2]
                      · have p5073_0 := h5073c.1
                        have p5073_1 := h5073c.2.1
                        have p5073_2 := h5073c.2.2.1
                        have p5073_3 := h5073c.2.2.2
                        linarith only [hlam, p5073_0]
          · linarith only [h3260, h4561, h4846, hlam]
        · linarith only [h0, h4560, h4845, hlam]
      · linarith only [h0, h4559, h4844, hlam]
    · linarith only [h0, h4558, h4843, hlam]

end R2N4
