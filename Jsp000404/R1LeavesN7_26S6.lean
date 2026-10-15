import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_26S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5262000 in
set_option maxHeartbeats 5262000 in
theorem r1l7_10_12_23_L_I_L_I_M_IR_s3_x1_x1_x1_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3129 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3354 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3617 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3773 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3774 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3775 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h3776 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 5 (by decide) (by decide) with h4421 | h4421
  · linarith only [h3776, h4421, hc34, hlam, hphi, u3ehi4]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4423 | h4423
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4424 | h4424
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4425 | h4425
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4426 | h4426
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4427 | h4427
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4428 | h4428
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4429 | h4429
                · linarith only [h3773, h3776, h4429, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4431 | h4431
                  · linarith only [h3773, h4421, h4431, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4433 | h4433
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4434 | h4434
                      · rcases h0bigk with h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c | h4435c
                        · have p4435_0 := h4435c.1
                          have p4435_1 := h4435c.2.1
                          have p4435_2 := h4435c.2.2.1
                          have p4435_3 := h4435c.2.2.2
                          linarith only [hlam, p4435_0]
                        · have p4435_0 := h4435c.1
                          have p4435_1 := h4435c.2.1
                          have p4435_2 := h4435c.2.2.1
                          have p4435_3 := h4435c.2.2.2
                          linarith only [h0, hlam, p4435_1]
                        · have p4435_0 := h4435c.1
                          have p4435_1 := h4435c.2.1
                          have p4435_2 := h4435c.2.2.1
                          have p4435_3 := h4435c.2.2.2
                          linarith only [h3129, hlam, p4435_0]
                        · have p4435_0 := h4435c.1
                          have p4435_1 := h4435c.2.1
                          have p4435_2 := h4435c.2.2.1
                          have p4435_3 := h4435c.2.2.2
                          linarith only [h3354, hlam, p4435_1]
                        · have p4435_0 := h4435c.1
                          have p4435_1 := h4435c.2.1
                          have p4435_2 := h4435c.2.2.1
                          have p4435_3 := h4435c.2.2.2
                          linarith only [h3617, hlam, p4435_1]
                        · have p4435_0 := h4435c.1
                          have p4435_1 := h4435c.2.1
                          have p4435_2 := h4435c.2.2.1
                          have p4435_3 := h4435c.2.2.2
                          rcases p4435_3 (m.d 0 1) (by simp) with h4441 | h4441
                          · linarith only [h0, h4441, hlam]
                          · rcases p4435_3 (m.d 0 2) (by simp) with h4443 | h4443
                            · rcases p4435_3 (m.d 0 3) (by simp) with h4444 | h4444
                              · linarith only [h3773, h4444, hlam]
                              · linarith only [h3129, h4444, hlam]
                            · linarith only [h0, h4443, hlam]
                        · have p4435_0 := h4435c.1
                          have p4435_1 := h4435c.2.1
                          have p4435_2 := h4435c.2.2.1
                          have p4435_3 := h4435c.2.2.2
                          linarith only [hlam, p4435_0]
                        · have p4435_0 := h4435c.1
                          have p4435_1 := h4435c.2.1
                          have p4435_2 := h4435c.2.2.1
                          have p4435_3 := h4435c.2.2.2
                          rcases p4435_3 (m.d 0 1) (by simp) with h4449 | h4449
                          · linarith only [h0, h4449, hlam]
                          · rcases p4435_3 (m.d 0 2) (by simp) with h4451 | h4451
                            · rcases p4435_3 (m.d 0 3) (by simp) with h4452 | h4452
                              · linarith only [h3773, h4452, hlam]
                              · rcases p4435_3 (m.d 0 4) (by simp) with h4454 | h4454
                                · linarith only [h3774, h4454, hlam]
                                · linarith only [h3776, h4454, hlam]
                            · linarith only [h3773, h4451, hlam]
                        · have p4435_0 := h4435c.1
                          have p4435_1 := h4435c.2.1
                          have p4435_2 := h4435c.2.2.1
                          have p4435_3 := h4435c.2.2.2
                          rcases p4435_3 (m.d 0 1) (by simp) with h4458 | h4458
                          · linarith only [h0, h4458, hlam]
                          · rcases p4435_3 (m.d 0 2) (by simp) with h4460 | h4460
                            · rcases p4435_3 (m.d 0 3) (by simp) with h4461 | h4461
                              · linarith only [h3773, h4461, hlam]
                              · rcases p4435_3 (m.d 0 4) (by simp) with h4463 | h4463
                                · linarith only [h3774, h4463, hlam]
                                · rcases p4435_3 (m.d 0 5) (by simp) with h4465 | h4465
                                  · linarith only [h3775, h4465, hlam]
                                  · rcases h2bigk with h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c
                                    · have p4467_0 := h4467c.1
                                      have p4467_1 := h4467c.2.1
                                      have p4467_2 := h4467c.2.2.1
                                      have p4467_3 := h4467c.2.2.2
                                      linarith only [hlam, p4467_0]
                                    · have p4467_0 := h4467c.1
                                      have p4467_1 := h4467c.2.1
                                      have p4467_2 := h4467c.2.2.1
                                      have p4467_3 := h4467c.2.2.2
                                      linarith only [h0, hlam, p4467_1]
                                    · have p4467_0 := h4467c.1
                                      have p4467_1 := h4467c.2.1
                                      have p4467_2 := h4467c.2.2.1
                                      have p4467_3 := h4467c.2.2.2
                                      rcases p4467_3 (m.d 0 2) (by simp) with h4470 | h4470
                                      · rcases p4467_3 (m.d 1 2) (by simp) with h4471 | h4471
                                        · rcases p4467_3 (m.d 2 3) (by simp) with h4472 | h4472
                                          · linarith only [h4472, hlam, p4467_0]
                                          · rcases p4467_3 (m.d 2 4) (by simp) with h4474 | h4474
                                            · linarith only [h3774, h4474, hlam]
                                            · linarith only [h4429, h4474, hlam]
                                        · linarith only [h4424, h4471, hlam]
                                      · linarith only [h4470, hlam, p4467_0]
                                    · have p4467_0 := h4467c.1
                                      have p4467_1 := h4467c.2.1
                                      have p4467_2 := h4467c.2.2.1
                                      have p4467_3 := h4467c.2.2.2
                                      rcases p4467_3 (m.d 0 2) (by simp) with h4479 | h4479
                                      · rcases p4467_3 (m.d 1 2) (by simp) with h4480 | h4480
                                        · rcases p4467_3 (m.d 2 3) (by simp) with h4481 | h4481
                                          · linarith only [h3773, h4481, hlam]
                                          · rcases p4467_3 (m.d 2 4) (by simp) with h4483 | h4483
                                            · linarith only [h4483, hlam, p4467_0]
                                            · rcases p4467_3 (m.d 2 5) (by simp) with h4485 | h4485
                                              · linarith only [h3775, h4485, hlam]
                                              · rcases h3bigk with h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [hlam, p4487_0]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [h3129, hlam, p4487_1]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [h0, h4421, h4423, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4435_1, p4487_1, u3ehi2]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [h3776, hlam, p4487_0]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [h4421, hlam, p4487_0]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  rcases p4487_3 (m.d 0 3) (by simp) with h4493 | h4493
                                                  · linarith only [h3129, h4493, hlam]
                                                  · rcases p4487_3 (m.d 1 3) (by simp) with h4495 | h4495
                                                    · rcases p4487_3 (m.d 2 3) (by simp) with h4496 | h4496
                                                      · linarith only [h4424, h4496, hlam]
                                                      · rcases p4487_3 (m.d 3 4) (by simp) with h4498 | h4498
                                                        · linarith only [h4427, h4498, hlam]
                                                        · linarith only [h3776, h4498, hlam]
                                                    · linarith only [h3129, h4495, hlam]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [hlam, p4487_0]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  rcases p4487_3 (m.d 0 3) (by simp) with h4503 | h4503
                                                  · linarith only [h3129, h4503, hlam]
                                                  · linarith only [h3773, h4503, hlam]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [h3776, h4424, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4487_1, u3ehi0]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [h3773, h4421, h4424, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4487_1, u3ehi2]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [h3773, hlam, p4487_0]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [h4424, hlam, p4487_0]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [hlam, p4487_0]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [h4429, hlam, p4487_0]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [h4431, hlam, p4487_0]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [h3773, hc34, hlam, hphi, p4487_1, u3ehi2]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [h4427, hlam, p4487_0]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [h4424, h4427, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4487_1, u3ehi2]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [hlam, p4487_0]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [h3773, h4421, h4424, h4427, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4487_1, u3ehi2]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [h3773, hc35, hlam, hphi, p4487_1, u3ehi2]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [h4428, hlam, p4487_0]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [h4424, h4428, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4487_1, u3ehi2]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [h4434, hlam, p4487_0]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [hlam, p4487_0]
                                        · linarith only [h4425, h4480, hlam]
                                      · linarith only [h4479, hlam, p4467_0]
                                    · have p4467_0 := h4467c.1
                                      have p4467_1 := h4467c.2.1
                                      have p4467_2 := h4467c.2.2.1
                                      have p4467_3 := h4467c.2.2.2
                                      rcases p4467_3 (m.d 0 2) (by simp) with h4525 | h4525
                                      · rcases p4467_3 (m.d 1 2) (by simp) with h4526 | h4526
                                        · rcases p4467_3 (m.d 2 3) (by simp) with h4527 | h4527
                                          · linarith only [h3773, h4527, hlam]
                                          · rcases p4467_3 (m.d 2 4) (by simp) with h4529 | h4529
                                            · linarith only [h3774, h4529, hlam]
                                            · linarith only [h4433, h4529, hlam]
                                        · linarith only [h4426, h4526, hlam]
                                      · linarith only [h4525, hlam, p4467_0]
                                    · have p4467_0 := h4467c.1
                                      have p4467_1 := h4467c.2.1
                                      have p4467_2 := h4467c.2.2.1
                                      have p4467_3 := h4467c.2.2.2
                                      linarith only [hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4435_1, p4467_1]
                                    · have p4467_0 := h4467c.1
                                      have p4467_1 := h4467c.2.1
                                      have p4467_2 := h4467c.2.2.1
                                      have p4467_3 := h4467c.2.2.2
                                      linarith only [hlam, p4467_0]
                                    · have p4467_0 := h4467c.1
                                      have p4467_1 := h4467c.2.1
                                      have p4467_2 := h4467c.2.2.1
                                      have p4467_3 := h4467c.2.2.2
                                      rcases p4467_3 (m.d 0 2) (by simp) with h4536 | h4536
                                      · linarith only [h0, h4536, hlam]
                                      · linarith only [h3773, h4536, hlam]
                                    · have p4467_0 := h4467c.1
                                      have p4467_1 := h4467c.2.1
                                      have p4467_2 := h4467c.2.2.1
                                      have p4467_3 := h4467c.2.2.2
                                      rcases p4467_3 (m.d 0 2) (by simp) with h4539 | h4539
                                      · linarith only [h0, h4539, hlam]
                                      · linarith only [h3774, h4539, hlam]
                                    · have p4467_0 := h4467c.1
                                      have p4467_1 := h4467c.2.1
                                      have p4467_2 := h4467c.2.2.1
                                      have p4467_3 := h4467c.2.2.2
                                      rcases p4467_3 (m.d 0 2) (by simp) with h4542 | h4542
                                      · linarith only [h0, h4542, hlam]
                                      · linarith only [h3775, h4542, hlam]
                                    · have p4467_0 := h4467c.1
                                      have p4467_1 := h4467c.2.1
                                      have p4467_2 := h4467c.2.2.1
                                      have p4467_3 := h4467c.2.2.2
                                      linarith only [h3773, hlam, p4467_0]
                                    · have p4467_0 := h4467c.1
                                      have p4467_1 := h4467c.2.1
                                      have p4467_2 := h4467c.2.2.1
                                      have p4467_3 := h4467c.2.2.2
                                      linarith only [h4424, hlam, p4467_0]
                                    · have p4467_0 := h4467c.1
                                      have p4467_1 := h4467c.2.1
                                      have p4467_2 := h4467c.2.2.1
                                      have p4467_3 := h4467c.2.2.2
                                      linarith only [hlam, p4467_0]
                                    · have p4467_0 := h4467c.1
                                      have p4467_1 := h4467c.2.1
                                      have p4467_2 := h4467c.2.2.1
                                      have p4467_3 := h4467c.2.2.2
                                      linarith only [h4429, hlam, p4467_0]
                                    · have p4467_0 := h4467c.1
                                      have p4467_1 := h4467c.2.1
                                      have p4467_2 := h4467c.2.2.1
                                      have p4467_3 := h4467c.2.2.2
                                      linarith only [h4431, hlam, p4467_0]
                                    · have p4467_0 := h4467c.1
                                      have p4467_1 := h4467c.2.1
                                      have p4467_2 := h4467c.2.2.1
                                      have p4467_3 := h4467c.2.2.2
                                      linarith only [h3774, hlam, p4467_0]
                                    · have p4467_0 := h4467c.1
                                      have p4467_1 := h4467c.2.1
                                      have p4467_2 := h4467c.2.2.1
                                      have p4467_3 := h4467c.2.2.2
                                      linarith only [h4425, hlam, p4467_0]
                                    · have p4467_0 := h4467c.1
                                      have p4467_1 := h4467c.2.1
                                      have p4467_2 := h4467c.2.2.1
                                      have p4467_3 := h4467c.2.2.2
                                      linarith only [h3774, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p4467_1, u3ehi2]
                                    · have p4467_0 := h4467c.1
                                      have p4467_1 := h4467c.2.1
                                      have p4467_2 := h4467c.2.2.1
                                      have p4467_3 := h4467c.2.2.2
                                      linarith only [hlam, p4467_0]
                                    · have p4467_0 := h4467c.1
                                      have p4467_1 := h4467c.2.1
                                      have p4467_2 := h4467c.2.2.1
                                      have p4467_3 := h4467c.2.2.2
                                      linarith only [h0, h3774, h4431, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4435_1, p4467_1, u3ehi2]
                                    · have p4467_0 := h4467c.1
                                      have p4467_1 := h4467c.2.1
                                      have p4467_2 := h4467c.2.2.1
                                      have p4467_3 := h4467c.2.2.2
                                      linarith only [h3775, hlam, p4467_0]
                                    · have p4467_0 := h4467c.1
                                      have p4467_1 := h4467c.2.1
                                      have p4467_2 := h4467c.2.2.1
                                      have p4467_3 := h4467c.2.2.2
                                      linarith only [h4426, hlam, p4467_0]
                                    · have p4467_0 := h4467c.1
                                      have p4467_1 := h4467c.2.1
                                      have p4467_2 := h4467c.2.2.1
                                      have p4467_3 := h4467c.2.2.2
                                      linarith only [h0, h3775, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4467_1, u3ehi2]
                                    · have p4467_0 := h4467c.1
                                      have p4467_1 := h4467c.2.1
                                      have p4467_2 := h4467c.2.2.1
                                      have p4467_3 := h4467c.2.2.2
                                      linarith only [h4433, hlam, p4467_0]
                                    · have p4467_0 := h4467c.1
                                      have p4467_1 := h4467c.2.1
                                      have p4467_2 := h4467c.2.2.1
                                      have p4467_3 := h4467c.2.2.2
                                      linarith only [hlam, p4467_0]
                            · linarith only [h3774, h4460, hlam]
                        · have p4435_0 := h4435c.1
                          have p4435_1 := h4435c.2.1
                          have p4435_2 := h4435c.2.2.1
                          have p4435_3 := h4435c.2.2.2
                          rcases p4435_3 (m.d 0 1) (by simp) with h4561 | h4561
                          · linarith only [h0, h4561, hlam]
                          · rcases p4435_3 (m.d 0 2) (by simp) with h4563 | h4563
                            · rcases p4435_3 (m.d 0 3) (by simp) with h4564 | h4564
                              · linarith only [h3773, h4564, hlam]
                              · rcases p4435_3 (m.d 0 4) (by simp) with h4566 | h4566
                                · linarith only [h3774, h4566, hlam]
                                · linarith only [h4423, h4566, hlam]
                            · linarith only [h3775, h4563, hlam]
                        · have p4435_0 := h4435c.1
                          have p4435_1 := h4435c.2.1
                          have p4435_2 := h4435c.2.2.1
                          have p4435_3 := h4435c.2.2.2
                          linarith only [h3776, h4424, h4427, hc01, hc12, hlam, hphi, p4435_1]
                        · have p4435_0 := h4435c.1
                          have p4435_1 := h4435c.2.1
                          have p4435_2 := h4435c.2.2.1
                          have p4435_3 := h4435c.2.2.2
                          linarith only [h3773, hlam, p4435_1]
                        · have p4435_0 := h4435c.1
                          have p4435_1 := h4435c.2.1
                          have p4435_2 := h4435c.2.2.1
                          have p4435_3 := h4435c.2.2.2
                          linarith only [hlam, p4435_0]
                        · have p4435_0 := h4435c.1
                          have p4435_1 := h4435c.2.1
                          have p4435_2 := h4435c.2.2.1
                          have p4435_3 := h4435c.2.2.2
                          linarith only [h3776, hlam, p4435_1]
                        · have p4435_0 := h4435c.1
                          have p4435_1 := h4435c.2.1
                          have p4435_2 := h4435c.2.2.1
                          have p4435_3 := h4435c.2.2.2
                          linarith only [h4421, hlam, p4435_1]
                        · have p4435_0 := h4435c.1
                          have p4435_1 := h4435c.2.1
                          have p4435_2 := h4435c.2.2.1
                          have p4435_3 := h4435c.2.2.2
                          linarith only [h3776, h4424, h4427, hc01, hc12, hlam, hphi, p4435_1]
                        · have p4435_0 := h4435c.1
                          have p4435_1 := h4435c.2.1
                          have p4435_2 := h4435c.2.2.1
                          have p4435_3 := h4435c.2.2.2
                          linarith only [h3774, hlam, p4435_0]
                        · have p4435_0 := h4435c.1
                          have p4435_1 := h4435c.2.1
                          have p4435_2 := h4435c.2.2.1
                          have p4435_3 := h4435c.2.2.2
                          linarith only [h3776, h4424, h4427, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4435_1, u3ehi0]
                        · have p4435_0 := h4435c.1
                          have p4435_1 := h4435c.2.1
                          have p4435_2 := h4435c.2.2.1
                          have p4435_3 := h4435c.2.2.2
                          linarith only [hlam, p4435_0]
                        · have p4435_0 := h4435c.1
                          have p4435_1 := h4435c.2.1
                          have p4435_2 := h4435c.2.2.1
                          have p4435_3 := h4435c.2.2.2
                          linarith only [h3773, h3776, h4421, h4424, h4427, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4435_1, u3ehi2]
                        · have p4435_0 := h4435c.1
                          have p4435_1 := h4435c.2.1
                          have p4435_2 := h4435c.2.2.1
                          have p4435_3 := h4435c.2.2.2
                          linarith only [h4421, h4424, h4427, h4434, hc01, hc12, hlam, hphi, p4435_1]
                        · have p4435_0 := h4435c.1
                          have p4435_1 := h4435c.2.1
                          have p4435_2 := h4435c.2.2.1
                          have p4435_3 := h4435c.2.2.2
                          linarith only [h3775, hlam, p4435_1]
                        · have p4435_0 := h4435c.1
                          have p4435_1 := h4435c.2.1
                          have p4435_2 := h4435c.2.2.1
                          have p4435_3 := h4435c.2.2.2
                          linarith only [h3773, h4421, h4424, h4427, h4434, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4435_1, u3ehi2]
                        · have p4435_0 := h4435c.1
                          have p4435_1 := h4435c.2.1
                          have p4435_2 := h4435c.2.2.1
                          have p4435_3 := h4435c.2.2.2
                          linarith only [h4423, hlam, p4435_1]
                        · have p4435_0 := h4435c.1
                          have p4435_1 := h4435c.2.1
                          have p4435_2 := h4435c.2.2.1
                          have p4435_3 := h4435c.2.2.2
                          linarith only [hlam, p4435_0]
                      · linarith only [h3773, h3776, h4434, hc45, hlam, hphi, ht34, u3ehi2]
                    · linarith only [h3776, h4423, h4424, h4427, h4429, h4433, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h3776, h4427, h4428, hc35, hlam, hphi, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4588 | h4588
              · linarith only [h4427, h4588, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4590 | h4590
                · linarith only [h3129, h4427, h4590, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4592 | h4592
                  · linarith only [h0, h3617, h3773, h4588, h4592, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4594 | h4594
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4595 | h4595
                      · rcases h0bigk with h4596c | h4596c | h4596c | h4596c | h4596c | h4596c | h4596c | h4596c | h4596c | h4596c | h4596c | h4596c | h4596c | h4596c | h4596c | h4596c | h4596c | h4596c | h4596c | h4596c | h4596c | h4596c | h4596c | h4596c | h4596c
                        · have p4596_0 := h4596c.1
                          have p4596_1 := h4596c.2.1
                          have p4596_2 := h4596c.2.2.1
                          have p4596_3 := h4596c.2.2.2
                          linarith only [hlam, p4596_0]
                        · have p4596_0 := h4596c.1
                          have p4596_1 := h4596c.2.1
                          have p4596_2 := h4596c.2.2.1
                          have p4596_3 := h4596c.2.2.2
                          linarith only [h0, hlam, p4596_1]
                        · have p4596_0 := h4596c.1
                          have p4596_1 := h4596c.2.1
                          have p4596_2 := h4596c.2.2.1
                          have p4596_3 := h4596c.2.2.2
                          linarith only [h3129, hlam, p4596_0]
                        · have p4596_0 := h4596c.1
                          have p4596_1 := h4596c.2.1
                          have p4596_2 := h4596c.2.2.1
                          have p4596_3 := h4596c.2.2.2
                          linarith only [h3354, hlam, p4596_1]
                        · have p4596_0 := h4596c.1
                          have p4596_1 := h4596c.2.1
                          have p4596_2 := h4596c.2.2.1
                          have p4596_3 := h4596c.2.2.2
                          linarith only [h3617, hlam, p4596_1]
                        · have p4596_0 := h4596c.1
                          have p4596_1 := h4596c.2.1
                          have p4596_2 := h4596c.2.2.1
                          have p4596_3 := h4596c.2.2.2
                          rcases p4596_3 (m.d 0 1) (by simp) with h4602 | h4602
                          · linarith only [h0, h4602, hlam]
                          · rcases p4596_3 (m.d 0 2) (by simp) with h4604 | h4604
                            · rcases p4596_3 (m.d 0 3) (by simp) with h4605 | h4605
                              · linarith only [h3773, h4605, hlam]
                              · linarith only [h3129, h4605, hlam]
                            · linarith only [h0, h4604, hlam]
                        · have p4596_0 := h4596c.1
                          have p4596_1 := h4596c.2.1
                          have p4596_2 := h4596c.2.2.1
                          have p4596_3 := h4596c.2.2.2
                          linarith only [hlam, p4596_0]
                        · have p4596_0 := h4596c.1
                          have p4596_1 := h4596c.2.1
                          have p4596_2 := h4596c.2.2.1
                          have p4596_3 := h4596c.2.2.2
                          rcases p4596_3 (m.d 0 1) (by simp) with h4610 | h4610
                          · linarith only [h0, h4610, hlam]
                          · rcases p4596_3 (m.d 0 2) (by simp) with h4612 | h4612
                            · rcases p4596_3 (m.d 0 3) (by simp) with h4613 | h4613
                              · linarith only [h3773, h4613, hlam]
                              · rcases p4596_3 (m.d 0 4) (by simp) with h4615 | h4615
                                · linarith only [h3774, h4615, hlam]
                                · linarith only [h3776, h4615, hlam]
                            · linarith only [h3773, h4612, hlam]
                        · have p4596_0 := h4596c.1
                          have p4596_1 := h4596c.2.1
                          have p4596_2 := h4596c.2.2.1
                          have p4596_3 := h4596c.2.2.2
                          rcases p4596_3 (m.d 0 1) (by simp) with h4619 | h4619
                          · linarith only [h0, h4619, hlam]
                          · rcases p4596_3 (m.d 0 2) (by simp) with h4621 | h4621
                            · rcases p4596_3 (m.d 0 3) (by simp) with h4622 | h4622
                              · linarith only [h3773, h4622, hlam]
                              · rcases p4596_3 (m.d 0 4) (by simp) with h4624 | h4624
                                · linarith only [h3774, h4624, hlam]
                                · rcases p4596_3 (m.d 0 5) (by simp) with h4626 | h4626
                                  · linarith only [h3775, h4626, hlam]
                                  · rcases h2bigk with h4628c | h4628c | h4628c | h4628c | h4628c | h4628c | h4628c | h4628c | h4628c | h4628c | h4628c | h4628c | h4628c | h4628c | h4628c | h4628c | h4628c | h4628c | h4628c | h4628c | h4628c | h4628c | h4628c | h4628c | h4628c
                                    · have p4628_0 := h4628c.1
                                      have p4628_1 := h4628c.2.1
                                      have p4628_2 := h4628c.2.2.1
                                      have p4628_3 := h4628c.2.2.2
                                      linarith only [hlam, p4628_0]
                                    · have p4628_0 := h4628c.1
                                      have p4628_1 := h4628c.2.1
                                      have p4628_2 := h4628c.2.2.1
                                      have p4628_3 := h4628c.2.2.2
                                      linarith only [h0, hlam, p4628_1]
                                    · have p4628_0 := h4628c.1
                                      have p4628_1 := h4628c.2.1
                                      have p4628_2 := h4628c.2.2.1
                                      have p4628_3 := h4628c.2.2.2
                                      rcases p4628_3 (m.d 0 2) (by simp) with h4631 | h4631
                                      · rcases p4628_3 (m.d 1 2) (by simp) with h4632 | h4632
                                        · rcases p4628_3 (m.d 2 3) (by simp) with h4633 | h4633
                                          · linarith only [h4633, hlam, p4628_0]
                                          · rcases p4628_3 (m.d 2 4) (by simp) with h4635 | h4635
                                            · linarith only [h3774, h4635, hlam]
                                            · linarith only [h4590, h4635, hlam]
                                        · linarith only [h4424, h4632, hlam]
                                      · linarith only [h4631, hlam, p4628_0]
                                    · have p4628_0 := h4628c.1
                                      have p4628_1 := h4628c.2.1
                                      have p4628_2 := h4628c.2.2.1
                                      have p4628_3 := h4628c.2.2.2
                                      rcases p4628_3 (m.d 0 2) (by simp) with h4640 | h4640
                                      · rcases p4628_3 (m.d 1 2) (by simp) with h4641 | h4641
                                        · rcases p4628_3 (m.d 2 3) (by simp) with h4642 | h4642
                                          · linarith only [h3773, h4642, hlam]
                                          · rcases p4628_3 (m.d 2 4) (by simp) with h4644 | h4644
                                            · linarith only [h4644, hlam, p4628_0]
                                            · rcases p4628_3 (m.d 2 5) (by simp) with h4646 | h4646
                                              · linarith only [h3775, h4646, hlam]
                                              · rcases h3bigk with h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c
                                                · have p4648_0 := h4648c.1
                                                  have p4648_1 := h4648c.2.1
                                                  have p4648_2 := h4648c.2.2.1
                                                  have p4648_3 := h4648c.2.2.2
                                                  linarith only [hlam, p4648_0]
                                                · have p4648_0 := h4648c.1
                                                  have p4648_1 := h4648c.2.1
                                                  have p4648_2 := h4648c.2.2.1
                                                  have p4648_3 := h4648c.2.2.2
                                                  linarith only [h3129, hlam, p4648_1]
                                                · have p4648_0 := h4648c.1
                                                  have p4648_1 := h4648c.2.1
                                                  have p4648_2 := h4648c.2.2.1
                                                  have p4648_3 := h4648c.2.2.2
                                                  linarith only [h0, h4421, h4423, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4596_1, p4648_1, u3ehi2]
                                                · have p4648_0 := h4648c.1
                                                  have p4648_1 := h4648c.2.1
                                                  have p4648_2 := h4648c.2.2.1
                                                  have p4648_3 := h4648c.2.2.2
                                                  linarith only [h3776, hlam, p4648_0]
                                                · have p4648_0 := h4648c.1
                                                  have p4648_1 := h4648c.2.1
                                                  have p4648_2 := h4648c.2.2.1
                                                  have p4648_3 := h4648c.2.2.2
                                                  linarith only [h4421, hlam, p4648_0]
                                                · have p4648_0 := h4648c.1
                                                  have p4648_1 := h4648c.2.1
                                                  have p4648_2 := h4648c.2.2.1
                                                  have p4648_3 := h4648c.2.2.2
                                                  linarith only [h4588, h4595, hc34, hlam, hphi, p4648_1, u3ehi0]
                                                · have p4648_0 := h4648c.1
                                                  have p4648_1 := h4648c.2.1
                                                  have p4648_2 := h4648c.2.2.1
                                                  have p4648_3 := h4648c.2.2.2
                                                  linarith only [hlam, p4648_0]
                                                · have p4648_0 := h4648c.1
                                                  have p4648_1 := h4648c.2.1
                                                  have p4648_2 := h4648c.2.2.1
                                                  have p4648_3 := h4648c.2.2.2
                                                  linarith only [h4588, h4595, hc34, hlam, hphi, p4648_1, u3ehi2]
                                                · have p4648_0 := h4648c.1
                                                  have p4648_1 := h4648c.2.1
                                                  have p4648_2 := h4648c.2.2.1
                                                  have p4648_3 := h4648c.2.2.2
                                                  linarith only [h4427, hlam, p4648_0]
                                                · have p4648_0 := h4648c.1
                                                  have p4648_1 := h4648c.2.1
                                                  have p4648_2 := h4648c.2.2.1
                                                  have p4648_3 := h4648c.2.2.2
                                                  linarith only [h4588, hlam, p4648_0]
                                                · have p4648_0 := h4648c.1
                                                  have p4648_1 := h4648c.2.1
                                                  have p4648_2 := h4648c.2.2.1
                                                  have p4648_3 := h4648c.2.2.2
                                                  linarith only [h3773, hlam, p4648_0]
                                                · have p4648_0 := h4648c.1
                                                  have p4648_1 := h4648c.2.1
                                                  have p4648_2 := h4648c.2.2.1
                                                  have p4648_3 := h4648c.2.2.2
                                                  linarith only [h4424, hlam, p4648_0]
                                                · have p4648_0 := h4648c.1
                                                  have p4648_1 := h4648c.2.1
                                                  have p4648_2 := h4648c.2.2.1
                                                  have p4648_3 := h4648c.2.2.2
                                                  linarith only [hlam, p4648_0]
                                                · have p4648_0 := h4648c.1
                                                  have p4648_1 := h4648c.2.1
                                                  have p4648_2 := h4648c.2.2.1
                                                  have p4648_3 := h4648c.2.2.2
                                                  linarith only [h4590, hlam, p4648_0]
                                                · have p4648_0 := h4648c.1
                                                  have p4648_1 := h4648c.2.1
                                                  have p4648_2 := h4648c.2.2.1
                                                  have p4648_3 := h4648c.2.2.2
                                                  linarith only [h4592, hlam, p4648_0]
                                                · have p4648_0 := h4648c.1
                                                  have p4648_1 := h4648c.2.1
                                                  have p4648_2 := h4648c.2.2.1
                                                  have p4648_3 := h4648c.2.2.2
                                                  linarith only [h3773, hc34, hlam, hphi, p4648_1, u3ehi2]
                                                · have p4648_0 := h4648c.1
                                                  have p4648_1 := h4648c.2.1
                                                  have p4648_2 := h4648c.2.2.1
                                                  have p4648_3 := h4648c.2.2.2
                                                  linarith only [hc34, hlam, hphi, p4648_1, u3ehi1]
                                                · have p4648_0 := h4648c.1
                                                  have p4648_1 := h4648c.2.1
                                                  have p4648_2 := h4648c.2.2.1
                                                  have p4648_3 := h4648c.2.2.2
                                                  linarith only [hc34, hlam, hphi, p4648_1, u3ehi2]
                                                · have p4648_0 := h4648c.1
                                                  have p4648_1 := h4648c.2.1
                                                  have p4648_2 := h4648c.2.2.1
                                                  have p4648_3 := h4648c.2.2.2
                                                  linarith only [hlam, p4648_0]
                                                · have p4648_0 := h4648c.1
                                                  have p4648_1 := h4648c.2.1
                                                  have p4648_2 := h4648c.2.2.1
                                                  have p4648_3 := h4648c.2.2.2
                                                  linarith only [hc34, hlam, hphi, p4648_1, u3ehi4]
                                                · have p4648_0 := h4648c.1
                                                  have p4648_1 := h4648c.2.1
                                                  have p4648_2 := h4648c.2.2.1
                                                  have p4648_3 := h4648c.2.2.2
                                                  linarith only [h3773, hc35, hlam, hphi, p4648_1, u3ehi2]
                                                · have p4648_0 := h4648c.1
                                                  have p4648_1 := h4648c.2.1
                                                  have p4648_2 := h4648c.2.2.1
                                                  have p4648_3 := h4648c.2.2.2
                                                  linarith only [h3129, hc01, hc35, hlam, hphi, ht12, ht23, p4648_1]
                                                · have p4648_0 := h4648c.1
                                                  have p4648_1 := h4648c.2.1
                                                  have p4648_2 := h4648c.2.2.1
                                                  have p4648_3 := h4648c.2.2.2
                                                  linarith only [hc35, hlam, hphi, p4648_1, u3ehi2]
                                                · have p4648_0 := h4648c.1
                                                  have p4648_1 := h4648c.2.1
                                                  have p4648_2 := h4648c.2.2.1
                                                  have p4648_3 := h4648c.2.2.2
                                                  linarith only [h4595, hlam, p4648_0]
                                                · have p4648_0 := h4648c.1
                                                  have p4648_1 := h4648c.2.1
                                                  have p4648_2 := h4648c.2.2.1
                                                  have p4648_3 := h4648c.2.2.2
                                                  linarith only [hlam, p4648_0]
                                        · linarith only [h4425, h4641, hlam]
                                      · linarith only [h4640, hlam, p4628_0]
                                    · have p4628_0 := h4628c.1
                                      have p4628_1 := h4628c.2.1
                                      have p4628_2 := h4628c.2.2.1
                                      have p4628_3 := h4628c.2.2.2
                                      rcases p4628_3 (m.d 0 2) (by simp) with h4676 | h4676
                                      · rcases p4628_3 (m.d 1 2) (by simp) with h4677 | h4677
                                        · rcases p4628_3 (m.d 2 3) (by simp) with h4678 | h4678
                                          · linarith only [h3773, h4678, hlam]
                                          · rcases p4628_3 (m.d 2 4) (by simp) with h4680 | h4680
                                            · linarith only [h3774, h4680, hlam]
                                            · linarith only [h4594, h4680, hlam]
                                        · linarith only [h4426, h4677, hlam]
                                      · linarith only [h4676, hlam, p4628_0]
                                    · have p4628_0 := h4628c.1
                                      have p4628_1 := h4628c.2.1
                                      have p4628_2 := h4628c.2.2.1
                                      have p4628_3 := h4628c.2.2.2
                                      linarith only [h3773, h4421, h4423, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4596_1, p4628_1, u3ehi2]
                                    · have p4628_0 := h4628c.1
                                      have p4628_1 := h4628c.2.1
                                      have p4628_2 := h4628c.2.2.1
                                      have p4628_3 := h4628c.2.2.2
                                      linarith only [hlam, p4628_0]
                                    · have p4628_0 := h4628c.1
                                      have p4628_1 := h4628c.2.1
                                      have p4628_2 := h4628c.2.2.1
                                      have p4628_3 := h4628c.2.2.2
                                      rcases p4628_3 (m.d 0 2) (by simp) with h4687 | h4687
                                      · linarith only [h0, h4687, hlam]
                                      · linarith only [h3773, h4687, hlam]
                                    · have p4628_0 := h4628c.1
                                      have p4628_1 := h4628c.2.1
                                      have p4628_2 := h4628c.2.2.1
                                      have p4628_3 := h4628c.2.2.2
                                      rcases p4628_3 (m.d 0 2) (by simp) with h4690 | h4690
                                      · linarith only [h0, h4690, hlam]
                                      · linarith only [h3774, h4690, hlam]
                                    · have p4628_0 := h4628c.1
                                      have p4628_1 := h4628c.2.1
                                      have p4628_2 := h4628c.2.2.1
                                      have p4628_3 := h4628c.2.2.2
                                      rcases p4628_3 (m.d 0 2) (by simp) with h4693 | h4693
                                      · linarith only [h0, h4693, hlam]
                                      · linarith only [h3775, h4693, hlam]
                                    · have p4628_0 := h4628c.1
                                      have p4628_1 := h4628c.2.1
                                      have p4628_2 := h4628c.2.2.1
                                      have p4628_3 := h4628c.2.2.2
                                      linarith only [h3773, hlam, p4628_0]
                                    · have p4628_0 := h4628c.1
                                      have p4628_1 := h4628c.2.1
                                      have p4628_2 := h4628c.2.2.1
                                      have p4628_3 := h4628c.2.2.2
                                      linarith only [h4424, hlam, p4628_0]
                                    · have p4628_0 := h4628c.1
                                      have p4628_1 := h4628c.2.1
                                      have p4628_2 := h4628c.2.2.1
                                      have p4628_3 := h4628c.2.2.2
                                      linarith only [hlam, p4628_0]
                                    · have p4628_0 := h4628c.1
                                      have p4628_1 := h4628c.2.1
                                      have p4628_2 := h4628c.2.2.1
                                      have p4628_3 := h4628c.2.2.2
                                      linarith only [h4590, hlam, p4628_0]
                                    · have p4628_0 := h4628c.1
                                      have p4628_1 := h4628c.2.1
                                      have p4628_2 := h4628c.2.2.1
                                      have p4628_3 := h4628c.2.2.2
                                      linarith only [h4592, hlam, p4628_0]
                                    · have p4628_0 := h4628c.1
                                      have p4628_1 := h4628c.2.1
                                      have p4628_2 := h4628c.2.2.1
                                      have p4628_3 := h4628c.2.2.2
                                      linarith only [h3774, hlam, p4628_0]
                                    · have p4628_0 := h4628c.1
                                      have p4628_1 := h4628c.2.1
                                      have p4628_2 := h4628c.2.2.1
                                      have p4628_3 := h4628c.2.2.2
                                      linarith only [h4425, hlam, p4628_0]
                                    · have p4628_0 := h4628c.1
                                      have p4628_1 := h4628c.2.1
                                      have p4628_2 := h4628c.2.2.1
                                      have p4628_3 := h4628c.2.2.2
                                      linarith only [h3774, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p4596_1, p4628_1, u3ehi2]
                                    · have p4628_0 := h4628c.1
                                      have p4628_1 := h4628c.2.1
                                      have p4628_2 := h4628c.2.2.1
                                      have p4628_3 := h4628c.2.2.2
                                      linarith only [hlam, p4628_0]
                                    · have p4628_0 := h4628c.1
                                      have p4628_1 := h4628c.2.1
                                      have p4628_2 := h4628c.2.2.1
                                      have p4628_3 := h4628c.2.2.2
                                      linarith only [h3774, hc02, hc25, hlam, hphi, ht0b, ht5b, p4596_1, p4628_1]
                                    · have p4628_0 := h4628c.1
                                      have p4628_1 := h4628c.2.1
                                      have p4628_2 := h4628c.2.2.1
                                      have p4628_3 := h4628c.2.2.2
                                      linarith only [h3775, hlam, p4628_0]
                                    · have p4628_0 := h4628c.1
                                      have p4628_1 := h4628c.2.1
                                      have p4628_2 := h4628c.2.2.1
                                      have p4628_3 := h4628c.2.2.2
                                      linarith only [h4426, hlam, p4628_0]
                                    · have p4628_0 := h4628c.1
                                      have p4628_1 := h4628c.2.1
                                      have p4628_2 := h4628c.2.2.1
                                      have p4628_3 := h4628c.2.2.2
                                      linarith only [h0, h3775, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4628_1, u3ehi2]
                                    · have p4628_0 := h4628c.1
                                      have p4628_1 := h4628c.2.1
                                      have p4628_2 := h4628c.2.2.1
                                      have p4628_3 := h4628c.2.2.2
                                      linarith only [h4594, hlam, p4628_0]
                                    · have p4628_0 := h4628c.1
                                      have p4628_1 := h4628c.2.1
                                      have p4628_2 := h4628c.2.2.1
                                      have p4628_3 := h4628c.2.2.2
                                      linarith only [hlam, p4628_0]
                            · linarith only [h3774, h4621, hlam]
                        · have p4596_0 := h4596c.1
                          have p4596_1 := h4596c.2.1
                          have p4596_2 := h4596c.2.2.1
                          have p4596_3 := h4596c.2.2.2
                          rcases p4596_3 (m.d 0 1) (by simp) with h4712 | h4712
                          · linarith only [h0, h4712, hlam]
                          · rcases p4596_3 (m.d 0 2) (by simp) with h4714 | h4714
                            · rcases p4596_3 (m.d 0 3) (by simp) with h4715 | h4715
                              · linarith only [h3773, h4715, hlam]
                              · rcases p4596_3 (m.d 0 4) (by simp) with h4717 | h4717
                                · linarith only [h3774, h4717, hlam]
                                · linarith only [h4423, h4717, hlam]
                            · linarith only [h3775, h4714, hlam]
                        · have p4596_0 := h4596c.1
                          have p4596_1 := h4596c.2.1
                          have p4596_2 := h4596c.2.2.1
                          have p4596_3 := h4596c.2.2.2
                          linarith only [h3776, hc01, hc34, hlam, hphi, ht12, ht23, p4596_1]
                        · have p4596_0 := h4596c.1
                          have p4596_1 := h4596c.2.1
                          have p4596_2 := h4596c.2.2.1
                          have p4596_3 := h4596c.2.2.2
                          linarith only [h3773, hlam, p4596_1]
                        · have p4596_0 := h4596c.1
                          have p4596_1 := h4596c.2.1
                          have p4596_2 := h4596c.2.2.1
                          have p4596_3 := h4596c.2.2.2
                          linarith only [hlam, p4596_0]
                        · have p4596_0 := h4596c.1
                          have p4596_1 := h4596c.2.1
                          have p4596_2 := h4596c.2.2.1
                          have p4596_3 := h4596c.2.2.2
                          linarith only [h3776, hlam, p4596_1]
                        · have p4596_0 := h4596c.1
                          have p4596_1 := h4596c.2.1
                          have p4596_2 := h4596c.2.2.1
                          have p4596_3 := h4596c.2.2.2
                          linarith only [h4421, hlam, p4596_1]
                        · have p4596_0 := h4596c.1
                          have p4596_1 := h4596c.2.1
                          have p4596_2 := h4596c.2.2.1
                          have p4596_3 := h4596c.2.2.2
                          rcases p4596_3 (m.d 0 1) (by simp) with h4726 | h4726
                          · linarith only [h3354, h4726, hlam]
                          · rcases p4596_3 (m.d 0 2) (by simp) with h4728 | h4728
                            · rcases p4596_3 (m.d 0 3) (by simp) with h4729 | h4729
                              · linarith only [h3776, h4729, hlam]
                              · linarith only [h3129, h4729, hlam]
                            · linarith only [h0, h4728, hlam]
                        · have p4596_0 := h4596c.1
                          have p4596_1 := h4596c.2.1
                          have p4596_2 := h4596c.2.2.1
                          have p4596_3 := h4596c.2.2.2
                          linarith only [h3774, hlam, p4596_0]
                        · have p4596_0 := h4596c.1
                          have p4596_1 := h4596c.2.1
                          have p4596_2 := h4596c.2.2.1
                          have p4596_3 := h4596c.2.2.2
                          linarith only [h3354, h4427, hc34, hlam, hphi, p4596_1, u3ehi0]
                        · have p4596_0 := h4596c.1
                          have p4596_1 := h4596c.2.1
                          have p4596_2 := h4596c.2.2.1
                          have p4596_3 := h4596c.2.2.2
                          linarith only [hlam, p4596_0]
                        · have p4596_0 := h4596c.1
                          have p4596_1 := h4596c.2.1
                          have p4596_2 := h4596c.2.2.1
                          have p4596_3 := h4596c.2.2.2
                          linarith only [h3354, h3773, h4421, h4427, hc34, hlam, hphi, p4596_1, u3ehi2]
                        · have p4596_0 := h4596c.1
                          have p4596_1 := h4596c.2.1
                          have p4596_2 := h4596c.2.2.1
                          have p4596_3 := h4596c.2.2.2
                          rcases p4596_3 (m.d 0 1) (by simp) with h4737 | h4737
                          · linarith only [h3617, h4737, hlam]
                          · rcases p4596_3 (m.d 0 2) (by simp) with h4739 | h4739
                            · rcases p4596_3 (m.d 0 3) (by simp) with h4740 | h4740
                              · linarith only [h4421, h4740, hlam]
                              · linarith only [h3129, h4740, hlam]
                            · linarith only [h0, h4739, hlam]
                        · have p4596_0 := h4596c.1
                          have p4596_1 := h4596c.2.1
                          have p4596_2 := h4596c.2.2.1
                          have p4596_3 := h4596c.2.2.2
                          linarith only [h3775, hlam, p4596_1]
                        · have p4596_0 := h4596c.1
                          have p4596_1 := h4596c.2.1
                          have p4596_2 := h4596c.2.2.1
                          have p4596_3 := h4596c.2.2.2
                          linarith only [h3773, h4421, h4595, hc34, hlam, hphi, p4596_1, u3ehi2]
                        · have p4596_0 := h4596c.1
                          have p4596_1 := h4596c.2.1
                          have p4596_2 := h4596c.2.2.1
                          have p4596_3 := h4596c.2.2.2
                          linarith only [h4423, hlam, p4596_1]
                        · have p4596_0 := h4596c.1
                          have p4596_1 := h4596c.2.1
                          have p4596_2 := h4596c.2.2.1
                          have p4596_3 := h4596c.2.2.2
                          linarith only [hlam, p4596_0]
                      · linarith only [h0, h3774, h4594, h4595, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h3776, h4423, h4590, h4594, hc34, hlam, hphi, u3ehi2]
          · linarith only [h0, h3775, h4426, hlam]
        · linarith only [h0, h3774, h4425, hlam]
      · linarith only [h0, h3773, h4424, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4753 | h4753
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4754 | h4754
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4755 | h4755
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4756 | h4756
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4757 | h4757
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4758 | h4758
                · linarith only [h3773, h3776, h4758, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4760 | h4760
                  · linarith only [h3773, h4421, h4760, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4762 | h4762
                    · linarith only [h0, h3354, h3774, h4423, h4762, hc01, hc12, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4764 | h4764
                      · linarith only [h3773, h3776, h4423, h4753, h4756, h4764, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h3773, h3776, h4764, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h3773, h3776, h4756, h4757, hc35, hlam, hphi, u3ehi2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4768 | h4768
              · linarith only [h4756, h4768, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4770 | h4770
                · linarith only [h3129, h4756, h4770, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4772 | h4772
                  · linarith only [h3129, h3773, h4768, h4772, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4774 | h4774
                    · linarith only [h3774, h4423, h4774, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4776 | h4776
                      · linarith only [h3776, h4423, h4776, hc34, hlam, hphi, u3ehi0]
                      · linarith only [h3773, h3776, h4776, hc45, hlam, hphi, ht34, u3ehi2]
          · linarith only [h0, h3775, h4755, hlam]
        · linarith only [h0, h3774, h4423, h4754, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
      · linarith only [h0, h3773, h4753, hlam]

set_option maxHeartbeats 5262000 in
set_option maxHeartbeats 5262000 in
theorem r1l7_10_12_23_L_I_L_I_M_IR_s3_x1_x1_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3129 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3354 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3617 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3773 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3774 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3775 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 4 (by decide) (by decide) with h3776 | h3776
  · exact r1l7_10_12_23_L_I_L_I_M_IR_s3_x1_x1_x1_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 h3129 h3354 h3617 h3773 h3774 h3775 h3776
  · exact r1l7_10_12_23_L_I_L_I_M_IR_s3_x1_x1_x1_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 h3129 h3354 h3617 h3773 h3774 h3775 h3776

set_option maxHeartbeats 5262000 in
set_option maxHeartbeats 5262000 in
theorem r1l7_10_12_23_L_I_L_I_M_IR_s3_x1_x1_x1_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3129 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3354 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3617 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3773 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3774 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3775 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 4 (by decide) (by decide) with h4782 | h4782
  · rcases m.htr 0 3 5 (by decide) (by decide) with h4783 | h4783
    · linarith only [h3773, h3775, h4783, hlam]
    · linarith only [h4782, h4783, hc35, hlam, hphi, u3ehi3]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h4786 | h4786
    · linarith only [h4782, h4786, hc34, hlam, hphi, u3ehi4]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h4788 | h4788
      · linarith only [h3774, h3775, h4788, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4790 | h4790
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4791 | h4791
          · rcases m.htr 1 2 5 (by decide) (by decide) with h4792 | h4792
            · linarith only [h3773, h3775, h4792, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h4794 | h4794
              · linarith only [h4782, h4790, h4792, h4794, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h4796 | h4796
                · linarith only [h3773, h3775, h4786, h4790, h4792, h4796, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4798 | h4798
                  · linarith only [h3773, h4794, h4798, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4800 | h4800
                    · linarith only [h0, h3774, h4792, h4798, h4800, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                    · linarith only [h0, h3774, h4792, h4798, h4800, hc35, hlam, hphi, u3ehi2]
          · linarith only [h0, h3774, h4791, hlam]
        · linarith only [h0, h3773, h4790, hlam]

set_option maxHeartbeats 5262000 in
set_option maxHeartbeats 5262000 in
theorem r1l7_10_12_23_L_I_L_I_M_IR_s3_x1_x1_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3129 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3354 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3617 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3773 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3774 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 5 (by decide) (by decide) with h3775 | h3775
  · exact r1l7_10_12_23_L_I_L_I_M_IR_s3_x1_x1_x1_x0_x0_x0 m hb0 hb2 hb3 hg0 h3129 h3354 h3617 h3773 h3774 h3775
  · exact r1l7_10_12_23_L_I_L_I_M_IR_s3_x1_x1_x1_x0_x0_x1 m hb0 hb2 hb3 hg0 h3129 h3354 h3617 h3773 h3774 h3775

set_option maxHeartbeats 5262000 in
set_option maxHeartbeats 5262000 in
theorem r1l7_10_12_23_L_I_L_I_M_IR_s3_x1_x1_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3129 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3354 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3617 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3773 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3774 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 5 (by decide) (by decide) with h4805 | h4805
  · rcases m.htr 0 3 4 (by decide) (by decide) with h4806 | h4806
    · linarith only [h3773, h3774, h4806, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4808 | h4808
      · linarith only [h4806, h4808, hc34, hlam, hphi, u3ehi4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4810 | h4810
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4811 | h4811
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4812 | h4812
            · linarith only [h3773, h3774, h4812, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4814 | h4814
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4815 | h4815
                · linarith only [h4806, h4811, h4812, h4815, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4817 | h4817
                  · linarith only [h3773, h4808, h4815, h4817, hc34, hlam, hphi, u3ehi2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4819 | h4819
                    · linarith only [h3773, h4815, h4819, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h0, h3773, h4812, h4819, hc34, hlam, hphi, u3ehi2]
              · linarith only [h0, h4805, h4814, hlam]
          · linarith only [h0, h3773, h4811, hlam]
        · linarith only [h3773, h3774, h4810, hc45, hlam, hphi, ht34, u3ehi2]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h4825 | h4825
    · linarith only [h3773, h3774, h4825, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4827 | h4827
      · linarith only [h4825, h4827, hc34, hlam, hphi, u3ehi4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4829 | h4829
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4830 | h4830
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4831 | h4831
            · linarith only [h3773, h3774, h4831, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4833 | h4833
              · linarith only [h3773, h4805, h4831, h4833, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4835 | h4835
                · linarith only [h4825, h4830, h4831, h4835, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4837 | h4837
                  · linarith only [h3773, h4805, h4827, h4835, h4837, hc34, hlam, hphi, u3ehi2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4839 | h4839
                    · linarith only [h3773, h4835, h4839, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h0, h3773, h4831, h4839, hc34, hlam, hphi, u3ehi2]
          · linarith only [h0, h3773, h4830, hlam]
        · linarith only [h3773, h3774, h4829, hc45, hlam, hphi, ht34, u3ehi2]

set_option maxHeartbeats 5262000 in
set_option maxHeartbeats 5262000 in
theorem r1l7_10_12_23_L_I_L_I_M_IR_s3_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3129 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3354 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3617 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3773 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 4 (by decide) (by decide) with h3774 | h3774
  · exact r1l7_10_12_23_L_I_L_I_M_IR_s3_x1_x1_x1_x0_x0 m hb0 hb2 hb3 hg0 h3129 h3354 h3617 h3773 h3774
  · exact r1l7_10_12_23_L_I_L_I_M_IR_s3_x1_x1_x1_x0_x1 m hb0 hb2 hb3 hg0 h3129 h3354 h3617 h3773 h3774

set_option maxHeartbeats 5262000 in
set_option maxHeartbeats 5262000 in
theorem r1l7_10_12_23_L_I_L_I_M_IR_s3_x1_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3129 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3354 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3617 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3773 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h4844 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 5 (by decide) (by decide) with h4845 | h4845
  · rcases m.htr 0 3 4 (by decide) (by decide) with h4846 | h4846
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4847 | h4847
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4848 | h4848
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4849 | h4849
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4850 | h4850
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4851 | h4851
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4852 | h4852
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4853 | h4853
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4854 | h4854
                    · linarith only [h3773, h4844, h4849, h4854, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h3773, h4844, h4846, h4854, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h3773, h4844, h4847, h4848, h4849, h4853, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h3773, h4844, h4846, h4849, h4852, hlam]
              · linarith only [h3773, h4845, h4849, h4851, hlam]
            · linarith only [h3773, h4844, h4849, h4850, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4861 | h4861
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4862 | h4862
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4863 | h4863
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4864 | h4864
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4865 | h4865
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h4866 | h4866
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4867 | h4867
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4868 | h4868
                          · rcases h0bigk with h4869c | h4869c | h4869c | h4869c | h4869c | h4869c | h4869c | h4869c | h4869c | h4869c | h4869c | h4869c | h4869c | h4869c | h4869c | h4869c | h4869c | h4869c | h4869c | h4869c | h4869c | h4869c | h4869c | h4869c | h4869c
                            · have p4869_0 := h4869c.1
                              have p4869_1 := h4869c.2.1
                              have p4869_2 := h4869c.2.2.1
                              have p4869_3 := h4869c.2.2.2
                              linarith only [hlam, p4869_0]
                            · have p4869_0 := h4869c.1
                              have p4869_1 := h4869c.2.1
                              have p4869_2 := h4869c.2.2.1
                              have p4869_3 := h4869c.2.2.2
                              linarith only [h0, hlam, p4869_1]
                            · have p4869_0 := h4869c.1
                              have p4869_1 := h4869c.2.1
                              have p4869_2 := h4869c.2.2.1
                              have p4869_3 := h4869c.2.2.2
                              linarith only [h3129, hlam, p4869_0]
                            · have p4869_0 := h4869c.1
                              have p4869_1 := h4869c.2.1
                              have p4869_2 := h4869c.2.2.1
                              have p4869_3 := h4869c.2.2.2
                              linarith only [h3354, hlam, p4869_1]
                            · have p4869_0 := h4869c.1
                              have p4869_1 := h4869c.2.1
                              have p4869_2 := h4869c.2.2.1
                              have p4869_3 := h4869c.2.2.2
                              linarith only [h3617, hlam, p4869_1]
                            · have p4869_0 := h4869c.1
                              have p4869_1 := h4869c.2.1
                              have p4869_2 := h4869c.2.2.1
                              have p4869_3 := h4869c.2.2.2
                              linarith only [h0, h4849, hc01, hc23, hlam, hphi, ht12, p4869_1]
                            · have p4869_0 := h4869c.1
                              have p4869_1 := h4869c.2.1
                              have p4869_2 := h4869c.2.2.1
                              have p4869_3 := h4869c.2.2.2
                              linarith only [hlam, p4869_0]
                            · have p4869_0 := h4869c.1
                              have p4869_1 := h4869c.2.1
                              have p4869_2 := h4869c.2.2.1
                              have p4869_3 := h4869c.2.2.2
                              linarith only [h3773, hlam, p4869_0]
                            · have p4869_0 := h4869c.1
                              have p4869_1 := h4869c.2.1
                              have p4869_2 := h4869c.2.2.1
                              have p4869_3 := h4869c.2.2.2
                              linarith only [h0, h4845, h4848, h4849, h4866, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4869_1, u3ehi4]
                            · have p4869_0 := h4869c.1
                              have p4869_1 := h4869c.2.1
                              have p4869_2 := h4869c.2.2.1
                              have p4869_3 := h4869c.2.2.2
                              linarith only [h0, h4845, h4849, h4866, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4869_1, u3ehi4]
                            · have p4869_0 := h4869c.1
                              have p4869_1 := h4869c.2.1
                              have p4869_2 := h4869c.2.2.1
                              have p4869_3 := h4869c.2.2.2
                              rcases p4869_3 (m.d 0 1) (by simp) with h4880 | h4880
                              · linarith only [h3129, h4880, hlam]
                              · rcases p4869_3 (m.d 0 2) (by simp) with h4882 | h4882
                                · linarith only [h3773, h4882, hlam]
                                · linarith only [h0, h4882, hlam]
                            · have p4869_0 := h4869c.1
                              have p4869_1 := h4869c.2.1
                              have p4869_2 := h4869c.2.2.1
                              have p4869_3 := h4869c.2.2.2
                              linarith only [h3129, h4844, h4849, h4866, h4867, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4869_1, u3ehi4]
                            · have p4869_0 := h4869c.1
                              have p4869_1 := h4869c.2.1
                              have p4869_2 := h4869c.2.2.1
                              have p4869_3 := h4869c.2.2.2
                              linarith only [hlam, p4869_0]
                            · have p4869_0 := h4869c.1
                              have p4869_1 := h4869c.2.1
                              have p4869_2 := h4869c.2.2.1
                              have p4869_3 := h4869c.2.2.2
                              rcases p4869_3 (m.d 0 1) (by simp) with h4887 | h4887
                              · linarith only [h3129, h4887, hlam]
                              · rcases p4869_3 (m.d 0 2) (by simp) with h4889 | h4889
                                · linarith only [h3773, h4889, hlam]
                                · linarith only [h4844, h4889, hlam]
                            · have p4869_0 := h4869c.1
                              have p4869_1 := h4869c.2.1
                              have p4869_2 := h4869c.2.2.1
                              have p4869_3 := h4869c.2.2.2
                              rcases p4869_3 (m.d 0 1) (by simp) with h4892 | h4892
                              · linarith only [h3129, h4892, hlam]
                              · rcases p4869_3 (m.d 0 2) (by simp) with h4894 | h4894
                                · linarith only [h3773, h4894, hlam]
                                · linarith only [h4845, h4894, hlam]
                            · have p4869_0 := h4869c.1
                              have p4869_1 := h4869c.2.1
                              have p4869_2 := h4869c.2.2.1
                              have p4869_3 := h4869c.2.2.2
                              linarith only [h0, h4844, h4849, hc01, hc23, hlam, hphi, ht12, p4869_1]
                            · have p4869_0 := h4869c.1
                              have p4869_1 := h4869c.2.1
                              have p4869_2 := h4869c.2.2.1
                              have p4869_3 := h4869c.2.2.2
                              linarith only [h4844, hlam, p4869_0]
                            · have p4869_0 := h4869c.1
                              have p4869_1 := h4869c.2.1
                              have p4869_2 := h4869c.2.2.1
                              have p4869_3 := h4869c.2.2.2
                              linarith only [h4846, hlam, p4869_0]
                            · have p4869_0 := h4869c.1
                              have p4869_1 := h4869c.2.1
                              have p4869_2 := h4869c.2.2.1
                              have p4869_3 := h4869c.2.2.2
                              linarith only [hlam, p4869_0]
                            · have p4869_0 := h4869c.1
                              have p4869_1 := h4869c.2.1
                              have p4869_2 := h4869c.2.2.1
                              have p4869_3 := h4869c.2.2.2
                              linarith only [h0, h4844, h4845, h4849, h4866, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4869_1, u3ehi4]
                            · have p4869_0 := h4869c.1
                              have p4869_1 := h4869c.2.1
                              have p4869_2 := h4869c.2.2.1
                              have p4869_3 := h4869c.2.2.2
                              linarith only [h0, h4845, h4849, hc01, hc23, hlam, hphi, ht12, p4869_1]
                            · have p4869_0 := h4869c.1
                              have p4869_1 := h4869c.2.1
                              have p4869_2 := h4869c.2.2.1
                              have p4869_3 := h4869c.2.2.2
                              linarith only [h4845, hlam, p4869_1]
                            · have p4869_0 := h4869c.1
                              have p4869_1 := h4869c.2.1
                              have p4869_2 := h4869c.2.2.1
                              have p4869_3 := h4869c.2.2.2
                              linarith only [h4847, hlam, p4869_0]
                            · have p4869_0 := h4869c.1
                              have p4869_1 := h4869c.2.1
                              have p4869_2 := h4869c.2.2.1
                              have p4869_3 := h4869c.2.2.2
                              linarith only [h4848, hlam, p4869_1]
                            · have p4869_0 := h4869c.1
                              have p4869_1 := h4869c.2.1
                              have p4869_2 := h4869c.2.2.1
                              have p4869_3 := h4869c.2.2.2
                              linarith only [hlam, p4869_0]
                          · linarith only [h0, h4844, h4848, h4849, h4868, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h4844, h4848, h4849, h4865, h4867, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h0, h4849, h4866, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h4844, h4846, h4849, h4865, hlam]
                  · linarith only [h0, h3129, h4844, h4847, h4848, h4849, h4864, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h3129, h4846, h4863, hlam]
              · linarith only [h0, h4845, h4862, hlam]
            · linarith only [h0, h4844, h4861, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4915 | h4915
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4916 | h4916
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4917 | h4917
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4918 | h4918
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4919 | h4919
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4920 | h4920
                    · linarith only [h3773, h4844, h4915, h4920, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h3773, h4844, h4846, h4920, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h3773, h4845, h4847, h4915, h4919, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h3773, h4845, h4846, h4848, h4915, h4918, hlam]
              · linarith only [h3773, h4845, h4915, h4917, hlam]
            · linarith only [h3773, h4915, h4916, hc02, hc24, hlam, hphi]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4927 | h4927
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4928 | h4928
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4929 | h4929
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4930 | h4930
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4931 | h4931
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h4932 | h4932
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4933 | h4933
                        · linarith only [h4844, h4848, h4933, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4935 | h4935
                          · linarith only [h4844, h4848, h4931, h4935, hlam]
                          · rcases h0bigk with h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c | h4937c
                            · have p4937_0 := h4937c.1
                              have p4937_1 := h4937c.2.1
                              have p4937_2 := h4937c.2.2.1
                              have p4937_3 := h4937c.2.2.2
                              linarith only [hlam, p4937_0]
                            · have p4937_0 := h4937c.1
                              have p4937_1 := h4937c.2.1
                              have p4937_2 := h4937c.2.2.1
                              have p4937_3 := h4937c.2.2.2
                              linarith only [h0, hlam, p4937_1]
                            · have p4937_0 := h4937c.1
                              have p4937_1 := h4937c.2.1
                              have p4937_2 := h4937c.2.2.1
                              have p4937_3 := h4937c.2.2.2
                              linarith only [h3129, hlam, p4937_0]
                            · have p4937_0 := h4937c.1
                              have p4937_1 := h4937c.2.1
                              have p4937_2 := h4937c.2.2.1
                              have p4937_3 := h4937c.2.2.2
                              linarith only [h3354, hlam, p4937_1]
                            · have p4937_0 := h4937c.1
                              have p4937_1 := h4937c.2.1
                              have p4937_2 := h4937c.2.2.1
                              have p4937_3 := h4937c.2.2.2
                              linarith only [h3617, hlam, p4937_1]
                            · have p4937_0 := h4937c.1
                              have p4937_1 := h4937c.2.1
                              have p4937_2 := h4937c.2.2.1
                              have p4937_3 := h4937c.2.2.2
                              linarith only [h0, h4915, hc01, hc23, hlam, hphi, ht12, p4937_1]
                            · have p4937_0 := h4937c.1
                              have p4937_1 := h4937c.2.1
                              have p4937_2 := h4937c.2.2.1
                              have p4937_3 := h4937c.2.2.2
                              linarith only [hlam, p4937_0]
                            · have p4937_0 := h4937c.1
                              have p4937_1 := h4937c.2.1
                              have p4937_2 := h4937c.2.2.1
                              have p4937_3 := h4937c.2.2.2
                              linarith only [h3773, hlam, p4937_0]
                            · have p4937_0 := h4937c.1
                              have p4937_1 := h4937c.2.1
                              have p4937_2 := h4937c.2.2.1
                              have p4937_3 := h4937c.2.2.2
                              linarith only [h0, h4844, h4915, h4931, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4937_1, u3ehi3]
                            · have p4937_0 := h4937c.1
                              have p4937_1 := h4937c.2.1
                              have p4937_2 := h4937c.2.2.1
                              have p4937_3 := h4937c.2.2.2
                              linarith only [h0, h4844, h4848, h4915, h4931, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4937_1, u3ehi3]
                            · have p4937_0 := h4937c.1
                              have p4937_1 := h4937c.2.1
                              have p4937_2 := h4937c.2.2.1
                              have p4937_3 := h4937c.2.2.2
                              rcases p4937_3 (m.d 0 1) (by simp) with h4948 | h4948
                              · linarith only [h3129, h4948, hlam]
                              · rcases p4937_3 (m.d 0 2) (by simp) with h4950 | h4950
                                · linarith only [h3773, h4950, hlam]
                                · linarith only [h0, h4950, hlam]
                            · have p4937_0 := h4937c.1
                              have p4937_1 := h4937c.2.1
                              have p4937_2 := h4937c.2.2.1
                              have p4937_3 := h4937c.2.2.2
                              linarith only [h3129, h4844, h4915, h4931, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4937_1, u3ehi3]
                            · have p4937_0 := h4937c.1
                              have p4937_1 := h4937c.2.1
                              have p4937_2 := h4937c.2.2.1
                              have p4937_3 := h4937c.2.2.2
                              linarith only [hlam, p4937_0]
                            · have p4937_0 := h4937c.1
                              have p4937_1 := h4937c.2.1
                              have p4937_2 := h4937c.2.2.1
                              have p4937_3 := h4937c.2.2.2
                              rcases p4937_3 (m.d 0 1) (by simp) with h4955 | h4955
                              · linarith only [h3129, h4955, hlam]
                              · rcases p4937_3 (m.d 0 2) (by simp) with h4957 | h4957
                                · linarith only [h3773, h4957, hlam]
                                · linarith only [h4844, h4957, hlam]
                            · have p4937_0 := h4937c.1
                              have p4937_1 := h4937c.2.1
                              have p4937_2 := h4937c.2.2.1
                              have p4937_3 := h4937c.2.2.2
                              rcases p4937_3 (m.d 0 1) (by simp) with h4960 | h4960
                              · linarith only [h3129, h4960, hlam]
                              · rcases p4937_3 (m.d 0 2) (by simp) with h4962 | h4962
                                · linarith only [h3773, h4962, hlam]
                                · linarith only [h4845, h4962, hlam]
                            · have p4937_0 := h4937c.1
                              have p4937_1 := h4937c.2.1
                              have p4937_2 := h4937c.2.2.1
                              have p4937_3 := h4937c.2.2.2
                              linarith only [h4848, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4937_1]
                            · have p4937_0 := h4937c.1
                              have p4937_1 := h4937c.2.1
                              have p4937_2 := h4937c.2.2.1
                              have p4937_3 := h4937c.2.2.2
                              linarith only [h4844, hlam, p4937_0]
                            · have p4937_0 := h4937c.1
                              have p4937_1 := h4937c.2.1
                              have p4937_2 := h4937c.2.2.1
                              have p4937_3 := h4937c.2.2.2
                              linarith only [h4846, hlam, p4937_0]
                            · have p4937_0 := h4937c.1
                              have p4937_1 := h4937c.2.1
                              have p4937_2 := h4937c.2.2.1
                              have p4937_3 := h4937c.2.2.2
                              linarith only [hlam, p4937_0]
                            · have p4937_0 := h4937c.1
                              have p4937_1 := h4937c.2.1
                              have p4937_2 := h4937c.2.2.1
                              have p4937_3 := h4937c.2.2.2
                              linarith only [h4848, hlam, p4937_0]
                            · have p4937_0 := h4937c.1
                              have p4937_1 := h4937c.2.1
                              have p4937_2 := h4937c.2.2.1
                              have p4937_3 := h4937c.2.2.2
                              linarith only [h0, h4845, h4915, hc01, hc23, hlam, hphi, ht12, p4937_1]
                            · have p4937_0 := h4937c.1
                              have p4937_1 := h4937c.2.1
                              have p4937_2 := h4937c.2.2.1
                              have p4937_3 := h4937c.2.2.2
                              linarith only [h4845, hlam, p4937_1]
                            · have p4937_0 := h4937c.1
                              have p4937_1 := h4937c.2.1
                              have p4937_2 := h4937c.2.2.1
                              have p4937_3 := h4937c.2.2.2
                              linarith only [h4847, hlam, p4937_0]
                            · have p4937_0 := h4937c.1
                              have p4937_1 := h4937c.2.1
                              have p4937_2 := h4937c.2.2.1
                              have p4937_3 := h4937c.2.2.2
                              linarith only [h0, h3354, h4845, h4915, hc01, hc23, hlam, hphi, ht12, p4937_1]
                            · have p4937_0 := h4937c.1
                              have p4937_1 := h4937c.2.1
                              have p4937_2 := h4937c.2.2.1
                              have p4937_3 := h4937c.2.2.2
                              linarith only [hlam, p4937_0]
                      · linarith only [h0, h4915, h4932, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h4845, h4847, h4915, h4931, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h0, h3129, h4845, h4847, h4915, h4930, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h3129, h4847, h4929, hc34, hlam, hphi, u3ehi4]
              · linarith only [h0, h4845, h4928, hlam]
            · linarith only [h0, h4844, h4927, hlam]
      · linarith only [h4846, h4847, hc35, hlam, hphi, u3ehi3]
    · linarith only [h3773, h4844, h4846, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h4983 | h4983
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4984 | h4984
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4985 | h4985
        · linarith only [h4844, h4845, h4985, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4987 | h4987
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4988 | h4988
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4989 | h4989
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4990 | h4990
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4991 | h4991
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4992 | h4992
                    · linarith only [h3773, h4844, h4987, h4992, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h3773, h4844, h4983, h4992, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h3129, h4983, h4991, hc35, hlam, hphi, u3ehi3]
                · linarith only [h4983, h4985, h4990, hc45, hlam, hphi, ht34, u3ehi1]
              · linarith only [h3773, h4987, h4989, hc02, hc25, hlam, hphi]
            · linarith only [h3773, h4844, h4983, h4987, h4988, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4999 | h4999
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5000 | h5000
              · linarith only [h4844, h4845, h4983, h4987, h5000, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5002 | h5002
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5003 | h5003
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5004 | h5004
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5005 | h5005
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5006 | h5006
                        · linarith only [h4844, h4985, h5006, hlam]
                        · linarith only [h0, h4844, h5000, h5004, h5006, hc45, hlam, hphi, ht34, u3ehi3]
                      · linarith only [h3773, h4844, h5004, h5005, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h3129, h4984, h4987, h5004, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h3129, h4983, h5003, hc35, hlam, hphi, u3ehi3]
                · linarith only [h3129, h4983, h5002, hlam]
            · linarith only [h0, h4844, h4999, hlam]
      · linarith only [h4983, h4984, hc35, hlam, hphi, u3ehi3]
    · linarith only [h3773, h4844, h4983, hlam]

end R2N4
