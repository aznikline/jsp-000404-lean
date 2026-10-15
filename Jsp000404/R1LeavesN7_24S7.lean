import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5514000 in
set_option maxHeartbeats 5514000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s5_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3363 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4426 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h4427 | h4427
  · rcases m.htr 0 2 3 (by decide) (by decide) with h4428 | h4428
    · rcases m.htr 0 2 4 (by decide) (by decide) with h4429 | h4429
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4430 | h4430
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4431 | h4431
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4432 | h4432
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4433 | h4433
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4434 | h4434
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4435 | h4435
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4436 | h4436
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4437 | h4437
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4438 | h4438
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4439 | h4439
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4440 | h4440
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h4441 | h4441
                              · linarith only [h3363, h4426, h4435, h4441, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                              · linarith only [h3363, h4426, h4433, h4439, h4441, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · linarith only [h4432, h4439, h4440, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                          · linarith only [h3363, h4431, h4439, hc23, hlam, hphi, u3elo1]
                        · linarith only [h3363, h4438, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h3363, h4437, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h0, h4426, h4430, h4435, h4436, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h4429, h4435, hlam]
                · linarith only [h0, h4434, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4451 | h4451
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4452 | h4452
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4453 | h4453
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4454 | h4454
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4455 | h4455
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4456 | h4456
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4457 | h4457
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h4458 | h4458
                              · linarith only [h3363, h4426, h4433, h4451, h4452, h4458, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h4460 | h4460
                                · linarith only [h3363, h4427, h4433, h4453, h4456, h4458, h4460, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                · rcases h0bigk with h4462c | h4462c | h4462c | h4462c | h4462c | h4462c | h4462c | h4462c | h4462c | h4462c | h4462c | h4462c | h4462c | h4462c | h4462c | h4462c | h4462c | h4462c | h4462c | h4462c | h4462c | h4462c | h4462c | h4462c | h4462c
                                  · have p4462_0 := h4462c.1
                                    have p4462_1 := h4462c.2.1
                                    have p4462_2 := h4462c.2.2.1
                                    have p4462_3 := h4462c.2.2.2
                                    linarith only [hlam, p4462_0]
                                  · have p4462_0 := h4462c.1
                                    have p4462_1 := h4462c.2.1
                                    have p4462_2 := h4462c.2.2.1
                                    have p4462_3 := h4462c.2.2.2
                                    linarith only [h0, hlam, p4462_1]
                                  · have p4462_0 := h4462c.1
                                    have p4462_1 := h4462c.2.1
                                    have p4462_2 := h4462c.2.2.1
                                    have p4462_3 := h4462c.2.2.2
                                    linarith only [h3363, hlam, p4462_0]
                                  · have p4462_0 := h4462c.1
                                    have p4462_1 := h4462c.2.1
                                    have p4462_2 := h4462c.2.2.1
                                    have p4462_3 := h4462c.2.2.2
                                    linarith only [h3363, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4462_1, u3elo1]
                                  · have p4462_0 := h4462c.1
                                    have p4462_1 := h4462c.2.1
                                    have p4462_2 := h4462c.2.2.1
                                    have p4462_3 := h4462c.2.2.2
                                    linarith only [h3363, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4462_1, u3elo1]
                                  · have p4462_0 := h4462c.1
                                    have p4462_1 := h4462c.2.1
                                    have p4462_2 := h4462c.2.2.1
                                    have p4462_3 := h4462c.2.2.2
                                    rcases p4462_3 (m.d 0 1) (by simp) with h4468 | h4468
                                    · linarith only [h0, h4468, hlam]
                                    · rcases p4462_3 (m.d 0 2) (by simp) with h4470 | h4470
                                      · rcases p4462_3 (m.d 0 3) (by simp) with h4471 | h4471
                                        · linarith only [h4428, h4471, hlam]
                                        · linarith only [h3363, h4471, hlam]
                                      · linarith only [h0, h4470, hlam]
                                  · have p4462_0 := h4462c.1
                                    have p4462_1 := h4462c.2.1
                                    have p4462_2 := h4462c.2.2.1
                                    have p4462_3 := h4462c.2.2.2
                                    linarith only [hlam, p4462_0]
                                  · have p4462_0 := h4462c.1
                                    have p4462_1 := h4462c.2.1
                                    have p4462_2 := h4462c.2.2.1
                                    have p4462_3 := h4462c.2.2.2
                                    rcases p4462_3 (m.d 0 1) (by simp) with h4476 | h4476
                                    · linarith only [h0, h4476, hlam]
                                    · rcases p4462_3 (m.d 0 2) (by simp) with h4478 | h4478
                                      · rcases p4462_3 (m.d 0 3) (by simp) with h4479 | h4479
                                        · linarith only [h4428, h4479, hlam]
                                        · rcases p4462_3 (m.d 0 4) (by simp) with h4481 | h4481
                                          · linarith only [h4429, h4481, hlam]
                                          · rcases p4462_3 (m.d 0 5) (by simp) with h4483 | h4483
                                            · linarith only [h4430, h4483, hlam]
                                            · rcases h0emin with h4485 | h4485 | h4485 | h4485 | h4485
                                              · linarith only [h3363, h4485, hlam, ht01, ht12, ht23, u3elo1]
                                              · rcases h2bigk with h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [hlam, p4487_0]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [h0, hlam, p4487_1]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  rcases p4487_3 (m.d 0 2) (by simp) with h4490 | h4490
                                                  · rcases p4487_3 (m.d 1 2) (by simp) with h4491 | h4491
                                                    · rcases p4487_3 (m.d 2 3) (by simp) with h4492 | h4492
                                                      · linarith only [h4492, hlam, p4487_0]
                                                      · rcases p4487_3 (m.d 2 4) (by simp) with h4494 | h4494
                                                        · linarith only [h4429, h4494, hlam]
                                                        · rcases p4487_3 (m.d 2 5) (by simp) with h4496 | h4496
                                                          · linarith only [h4430, h4496, hlam]
                                                          · rcases h2emin with h4498 | h4498 | h4498 | h4498 | h4498
                                                            · rcases h3bigk with h4499c | h4499c | h4499c | h4499c | h4499c | h4499c | h4499c | h4499c | h4499c | h4499c | h4499c | h4499c | h4499c | h4499c | h4499c | h4499c | h4499c | h4499c | h4499c | h4499c | h4499c | h4499c | h4499c | h4499c | h4499c
                                                              · have p4499_0 := h4499c.1
                                                                have p4499_1 := h4499c.2.1
                                                                have p4499_2 := h4499c.2.2.1
                                                                have p4499_3 := h4499c.2.2.2
                                                                linarith only [hlam, p4499_0]
                                                              · have p4499_0 := h4499c.1
                                                                have p4499_1 := h4499c.2.1
                                                                have p4499_2 := h4499c.2.2.1
                                                                have p4499_3 := h4499c.2.2.2
                                                                linarith only [h3363, hlam, p4499_1]
                                                              · have p4499_0 := h4499c.1
                                                                have p4499_1 := h4499c.2.1
                                                                have p4499_2 := h4499c.2.2.1
                                                                have p4499_3 := h4499c.2.2.2
                                                                linarith only [h0, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4462_1, p4499_1]
                                                              · have p4499_0 := h4499c.1
                                                                have p4499_1 := h4499c.2.1
                                                                have p4499_2 := h4499c.2.2.1
                                                                have p4499_3 := h4499c.2.2.2
                                                                linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4462_1, p4499_1]
                                                              · have p4499_0 := h4499c.1
                                                                have p4499_1 := h4499c.2.1
                                                                have p4499_2 := h4499c.2.2.1
                                                                have p4499_3 := h4499c.2.2.2
                                                                linarith only [h0, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p4462_1, p4499_1]
                                                              · have p4499_0 := h4499c.1
                                                                have p4499_1 := h4499c.2.1
                                                                have p4499_2 := h4499c.2.2.1
                                                                have p4499_3 := h4499c.2.2.2
                                                                linarith only [hc03, hlam, hphi, p4499_1, u3elo1]
                                                              · have p4499_0 := h4499c.1
                                                                have p4499_1 := h4499c.2.1
                                                                have p4499_2 := h4499c.2.2.1
                                                                have p4499_3 := h4499c.2.2.2
                                                                linarith only [hlam, p4499_0]
                                                              · have p4499_0 := h4499c.1
                                                                have p4499_1 := h4499c.2.1
                                                                have p4499_2 := h4499c.2.2.1
                                                                have p4499_3 := h4499c.2.2.2
                                                                linarith only [hc23, hlam, hphi, p4499_1, u3elo1]
                                                              · have p4499_0 := h4499c.1
                                                                have p4499_1 := h4499c.2.1
                                                                have p4499_2 := h4499c.2.2.1
                                                                have p4499_3 := h4499c.2.2.2
                                                                rcases p4499_3 (m.d 0 3) (by simp) with h4508 | h4508
                                                                · linarith only [h3363, h4508, hlam]
                                                                · linarith only [h4431, h4508, hlam]
                                                              · have p4499_0 := h4499c.1
                                                                have p4499_1 := h4499c.2.1
                                                                have p4499_2 := h4499c.2.2.1
                                                                have p4499_3 := h4499c.2.2.2
                                                                rcases p4499_3 (m.d 0 3) (by simp) with h4511 | h4511
                                                                · linarith only [h3363, h4511, hlam]
                                                                · linarith only [h4432, h4511, hlam]
                                                              · have p4499_0 := h4499c.1
                                                                have p4499_1 := h4499c.2.1
                                                                have p4499_2 := h4499c.2.2.1
                                                                have p4499_3 := h4499c.2.2.2
                                                                linarith only [h4428, hlam, p4499_0]
                                                              · have p4499_0 := h4499c.1
                                                                have p4499_1 := h4499c.2.1
                                                                have p4499_2 := h4499c.2.2.1
                                                                have p4499_3 := h4499c.2.2.2
                                                                linarith only [h4451, hlam, p4499_0]
                                                              · have p4499_0 := h4499c.1
                                                                have p4499_1 := h4499c.2.1
                                                                have p4499_2 := h4499c.2.2.1
                                                                have p4499_3 := h4499c.2.2.2
                                                                linarith only [hlam, p4499_0]
                                                              · have p4499_0 := h4499c.1
                                                                have p4499_1 := h4499c.2.1
                                                                have p4499_2 := h4499c.2.2.1
                                                                have p4499_3 := h4499c.2.2.2
                                                                linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4487_1, p4499_1]
                                                              · have p4499_0 := h4499c.1
                                                                have p4499_1 := h4499c.2.1
                                                                have p4499_2 := h4499c.2.2.1
                                                                have p4499_3 := h4499c.2.2.2
                                                                linarith only [h0, h4460, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4487_1, p4499_1]
                                                              · have p4499_0 := h4499c.1
                                                                have p4499_1 := h4499c.2.1
                                                                have p4499_2 := h4499c.2.2.1
                                                                have p4499_3 := h4499c.2.2.2
                                                                linarith only [h4431, hlam, p4499_0]
                                                              · have p4499_0 := h4499c.1
                                                                have p4499_1 := h4499c.2.1
                                                                have p4499_2 := h4499c.2.2.1
                                                                have p4499_3 := h4499c.2.2.2
                                                                linarith only [h4454, hlam, p4499_0]
                                                              · have p4499_0 := h4499c.1
                                                                have p4499_1 := h4499c.2.1
                                                                have p4499_2 := h4499c.2.2.1
                                                                have p4499_3 := h4499c.2.2.2
                                                                linarith only [h4456, hlam, p4499_0]
                                                              · have p4499_0 := h4499c.1
                                                                have p4499_1 := h4499c.2.1
                                                                have p4499_2 := h4499c.2.2.1
                                                                have p4499_3 := h4499c.2.2.2
                                                                linarith only [hlam, p4499_0]
                                                              · have p4499_0 := h4499c.1
                                                                have p4499_1 := h4499c.2.1
                                                                have p4499_2 := h4499c.2.2.1
                                                                have p4499_3 := h4499c.2.2.2
                                                                linarith only [h4460, hlam, p4499_1]
                                                              · have p4499_0 := h4499c.1
                                                                have p4499_1 := h4499c.2.1
                                                                have p4499_2 := h4499c.2.2.1
                                                                have p4499_3 := h4499c.2.2.2
                                                                linarith only [h4432, hlam, p4499_0]
                                                              · have p4499_0 := h4499c.1
                                                                have p4499_1 := h4499c.2.1
                                                                have p4499_2 := h4499c.2.2.1
                                                                have p4499_3 := h4499c.2.2.2
                                                                linarith only [h4455, hlam, p4499_0]
                                                              · have p4499_0 := h4499c.1
                                                                have p4499_1 := h4499c.2.1
                                                                have p4499_2 := h4499c.2.2.1
                                                                have p4499_3 := h4499c.2.2.2
                                                                linarith only [h4457, hlam, p4499_0]
                                                              · have p4499_0 := h4499c.1
                                                                have p4499_1 := h4499c.2.1
                                                                have p4499_2 := h4499c.2.2.1
                                                                have p4499_3 := h4499c.2.2.2
                                                                linarith only [h0, h4432, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4462_1, p4499_1]
                                                              · have p4499_0 := h4499c.1
                                                                have p4499_1 := h4499c.2.1
                                                                have p4499_2 := h4499c.2.2.1
                                                                have p4499_3 := h4499c.2.2.2
                                                                linarith only [hlam, p4499_0]
                                                            · rcases h3bigk with h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c
                                                              · have p4529_0 := h4529c.1
                                                                have p4529_1 := h4529c.2.1
                                                                have p4529_2 := h4529c.2.2.1
                                                                have p4529_3 := h4529c.2.2.2
                                                                linarith only [hlam, p4529_0]
                                                              · have p4529_0 := h4529c.1
                                                                have p4529_1 := h4529c.2.1
                                                                have p4529_2 := h4529c.2.2.1
                                                                have p4529_3 := h4529c.2.2.2
                                                                linarith only [h3363, hlam, p4529_1]
                                                              · have p4529_0 := h4529c.1
                                                                have p4529_1 := h4529c.2.1
                                                                have p4529_2 := h4529c.2.2.1
                                                                have p4529_3 := h4529c.2.2.2
                                                                linarith only [h0, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4462_1, p4529_1]
                                                              · have p4529_0 := h4529c.1
                                                                have p4529_1 := h4529c.2.1
                                                                have p4529_2 := h4529c.2.2.1
                                                                have p4529_3 := h4529c.2.2.2
                                                                linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4462_1, p4529_1]
                                                              · have p4529_0 := h4529c.1
                                                                have p4529_1 := h4529c.2.1
                                                                have p4529_2 := h4529c.2.2.1
                                                                have p4529_3 := h4529c.2.2.2
                                                                linarith only [h0, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p4462_1, p4529_1]
                                                              · have p4529_0 := h4529c.1
                                                                have p4529_1 := h4529c.2.1
                                                                have p4529_2 := h4529c.2.2.1
                                                                have p4529_3 := h4529c.2.2.2
                                                                linarith only [hc03, hlam, hphi, p4529_1, u3elo1]
                                                              · have p4529_0 := h4529c.1
                                                                have p4529_1 := h4529c.2.1
                                                                have p4529_2 := h4529c.2.2.1
                                                                have p4529_3 := h4529c.2.2.2
                                                                linarith only [hlam, p4529_0]
                                                              · have p4529_0 := h4529c.1
                                                                have p4529_1 := h4529c.2.1
                                                                have p4529_2 := h4529c.2.2.1
                                                                have p4529_3 := h4529c.2.2.2
                                                                linarith only [hc23, hlam, hphi, p4529_1, u3elo1]
                                                              · have p4529_0 := h4529c.1
                                                                have p4529_1 := h4529c.2.1
                                                                have p4529_2 := h4529c.2.2.1
                                                                have p4529_3 := h4529c.2.2.2
                                                                rcases p4529_3 (m.d 0 3) (by simp) with h4538 | h4538
                                                                · linarith only [h3363, h4538, hlam]
                                                                · linarith only [h4431, h4538, hlam]
                                                              · have p4529_0 := h4529c.1
                                                                have p4529_1 := h4529c.2.1
                                                                have p4529_2 := h4529c.2.2.1
                                                                have p4529_3 := h4529c.2.2.2
                                                                rcases p4529_3 (m.d 0 3) (by simp) with h4541 | h4541
                                                                · linarith only [h3363, h4541, hlam]
                                                                · linarith only [h4432, h4541, hlam]
                                                              · have p4529_0 := h4529c.1
                                                                have p4529_1 := h4529c.2.1
                                                                have p4529_2 := h4529c.2.2.1
                                                                have p4529_3 := h4529c.2.2.2
                                                                linarith only [h4428, hlam, p4529_0]
                                                              · have p4529_0 := h4529c.1
                                                                have p4529_1 := h4529c.2.1
                                                                have p4529_2 := h4529c.2.2.1
                                                                have p4529_3 := h4529c.2.2.2
                                                                linarith only [h4451, hlam, p4529_0]
                                                              · have p4529_0 := h4529c.1
                                                                have p4529_1 := h4529c.2.1
                                                                have p4529_2 := h4529c.2.2.1
                                                                have p4529_3 := h4529c.2.2.2
                                                                linarith only [hlam, p4529_0]
                                                              · have p4529_0 := h4529c.1
                                                                have p4529_1 := h4529c.2.1
                                                                have p4529_2 := h4529c.2.2.1
                                                                have p4529_3 := h4529c.2.2.2
                                                                linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4487_1, p4529_1]
                                                              · have p4529_0 := h4529c.1
                                                                have p4529_1 := h4529c.2.1
                                                                have p4529_2 := h4529c.2.2.1
                                                                have p4529_3 := h4529c.2.2.2
                                                                linarith only [h0, h4460, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4487_1, p4529_1]
                                                              · have p4529_0 := h4529c.1
                                                                have p4529_1 := h4529c.2.1
                                                                have p4529_2 := h4529c.2.2.1
                                                                have p4529_3 := h4529c.2.2.2
                                                                linarith only [h4431, hlam, p4529_0]
                                                              · have p4529_0 := h4529c.1
                                                                have p4529_1 := h4529c.2.1
                                                                have p4529_2 := h4529c.2.2.1
                                                                have p4529_3 := h4529c.2.2.2
                                                                linarith only [h4454, hlam, p4529_0]
                                                              · have p4529_0 := h4529c.1
                                                                have p4529_1 := h4529c.2.1
                                                                have p4529_2 := h4529c.2.2.1
                                                                have p4529_3 := h4529c.2.2.2
                                                                linarith only [h4456, hlam, p4529_0]
                                                              · have p4529_0 := h4529c.1
                                                                have p4529_1 := h4529c.2.1
                                                                have p4529_2 := h4529c.2.2.1
                                                                have p4529_3 := h4529c.2.2.2
                                                                linarith only [hlam, p4529_0]
                                                              · have p4529_0 := h4529c.1
                                                                have p4529_1 := h4529c.2.1
                                                                have p4529_2 := h4529c.2.2.1
                                                                have p4529_3 := h4529c.2.2.2
                                                                linarith only [h4460, hlam, p4529_1]
                                                              · have p4529_0 := h4529c.1
                                                                have p4529_1 := h4529c.2.1
                                                                have p4529_2 := h4529c.2.2.1
                                                                have p4529_3 := h4529c.2.2.2
                                                                linarith only [h4432, hlam, p4529_0]
                                                              · have p4529_0 := h4529c.1
                                                                have p4529_1 := h4529c.2.1
                                                                have p4529_2 := h4529c.2.2.1
                                                                have p4529_3 := h4529c.2.2.2
                                                                linarith only [h4455, hlam, p4529_0]
                                                              · have p4529_0 := h4529c.1
                                                                have p4529_1 := h4529c.2.1
                                                                have p4529_2 := h4529c.2.2.1
                                                                have p4529_3 := h4529c.2.2.2
                                                                linarith only [h4457, hlam, p4529_0]
                                                              · have p4529_0 := h4529c.1
                                                                have p4529_1 := h4529c.2.1
                                                                have p4529_2 := h4529c.2.2.1
                                                                have p4529_3 := h4529c.2.2.2
                                                                linarith only [h0, h4432, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4462_1, p4529_1]
                                                              · have p4529_0 := h4529c.1
                                                                have p4529_1 := h4529c.2.1
                                                                have p4529_2 := h4529c.2.2.1
                                                                have p4529_3 := h4529c.2.2.2
                                                                linarith only [hlam, p4529_0]
                                                            · linarith only [h0, h4428, h4498, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4462_1]
                                                            · linarith only [h4426, h4433, h4452, h4498, hc45, hlam, ht23, ht34]
                                                            · linarith only [h0, h4427, h4453, h4498, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                                                    · linarith only [h4451, h4491, hlam]
                                                  · linarith only [h4490, hlam, p4487_0]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [h3363, h4426, h4452, hlam, p4462_1, p4487_2]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [h3363, h4427, h4453, hlam, p4462_1, p4487_2]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [h3363, h4426, h4452, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p4462_1, p4487_1]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [hlam, p4487_0]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  rcases p4487_3 (m.d 0 2) (by simp) with h4568 | h4568
                                                  · linarith only [h0, h4568, hlam]
                                                  · linarith only [h4428, h4568, hlam]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [h0, h3363, h4427, h4453, h4458, hlam, p4462_1, p4487_2]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [h0, h3363, h4427, h4453, hlam, p4462_1, p4487_2]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [h4428, hlam, p4487_0]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [h4451, hlam, p4487_0]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [hlam, p4487_0]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [h4428, h4456, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p4462_1, p4487_1]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [h0, h4428, h4456, h4458, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4462_1, p4487_1]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [h4429, hlam, p4487_0]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [h4452, hlam, p4487_0]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [h4456, hlam, p4487_1]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [hlam, p4487_0]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [h4458, hlam, p4487_1]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [h4430, hlam, p4487_0]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [h4453, hlam, p4487_0]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [h4457, hlam, p4487_1]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [h0, h4427, h4453, h4456, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4487_1]
                                                · have p4487_0 := h4487c.1
                                                  have p4487_1 := h4487c.2.1
                                                  have p4487_2 := h4487c.2.2.1
                                                  have p4487_3 := h4487c.2.2.2
                                                  linarith only [hlam, p4487_0]
                                              · linarith only [h0, h4485, hc12, hlam, ht01, p4462_1]
                                              · linarith only [h0, h4427, h4433, h4485, hc12, hlam, ht01]
                                              · linarith only [h0, h4427, h4485, hc12, hlam, ht01]
                                      · linarith only [h4428, h4478, hlam]
                                  · have p4462_0 := h4462c.1
                                    have p4462_1 := h4462c.2.1
                                    have p4462_2 := h4462c.2.2.1
                                    have p4462_3 := h4462c.2.2.2
                                    rcases p4462_3 (m.d 0 1) (by simp) with h4592 | h4592
                                    · linarith only [h0, h4592, hlam]
                                    · linarith only [h4426, h4592, hlam]
                                  · have p4462_0 := h4462c.1
                                    have p4462_1 := h4462c.2.1
                                    have p4462_2 := h4462c.2.2.1
                                    have p4462_3 := h4462c.2.2.2
                                    rcases p4462_3 (m.d 0 1) (by simp) with h4595 | h4595
                                    · linarith only [h0, h4595, hlam]
                                    · linarith only [h4427, h4595, hlam]
                                  · have p4462_0 := h4462c.1
                                    have p4462_1 := h4462c.2.1
                                    have p4462_2 := h4462c.2.2.1
                                    have p4462_3 := h4462c.2.2.2
                                    linarith only [hc01, hlam, hphi, ht12, ht23, p4462_1, u3elo0]
                                  · have p4462_0 := h4462c.1
                                    have p4462_1 := h4462c.2.1
                                    have p4462_2 := h4462c.2.2.1
                                    have p4462_3 := h4462c.2.2.2
                                    linarith only [h4428, hlam, p4462_1]
                                  · have p4462_0 := h4462c.1
                                    have p4462_1 := h4462c.2.1
                                    have p4462_2 := h4462c.2.2.1
                                    have p4462_3 := h4462c.2.2.2
                                    linarith only [hlam, p4462_0]
                                  · have p4462_0 := h4462c.1
                                    have p4462_1 := h4462c.2.1
                                    have p4462_2 := h4462c.2.2.1
                                    have p4462_3 := h4462c.2.2.2
                                    rcases p4462_3 (m.d 0 1) (by simp) with h4601 | h4601
                                    · linarith only [h3363, h4601, hlam]
                                    · linarith only [h4426, h4601, hlam]
                                  · have p4462_0 := h4462c.1
                                    have p4462_1 := h4462c.2.1
                                    have p4462_2 := h4462c.2.2.1
                                    have p4462_3 := h4462c.2.2.2
                                    rcases p4462_3 (m.d 0 1) (by simp) with h4604 | h4604
                                    · linarith only [h3363, h4604, hlam]
                                    · linarith only [h4427, h4604, hlam]
                                  · have p4462_0 := h4462c.1
                                    have p4462_1 := h4462c.2.1
                                    have p4462_2 := h4462c.2.2.1
                                    have p4462_3 := h4462c.2.2.2
                                    linarith only [h4426, hlam, p4462_0]
                                  · have p4462_0 := h4462c.1
                                    have p4462_1 := h4462c.2.1
                                    have p4462_2 := h4462c.2.2.1
                                    have p4462_3 := h4462c.2.2.2
                                    linarith only [h4429, hlam, p4462_0]
                                  · have p4462_0 := h4462c.1
                                    have p4462_1 := h4462c.2.1
                                    have p4462_2 := h4462c.2.2.1
                                    have p4462_3 := h4462c.2.2.2
                                    linarith only [h4431, hlam, p4462_0]
                                  · have p4462_0 := h4462c.1
                                    have p4462_1 := h4462c.2.1
                                    have p4462_2 := h4462c.2.2.1
                                    have p4462_3 := h4462c.2.2.2
                                    linarith only [hlam, p4462_0]
                                  · have p4462_0 := h4462c.1
                                    have p4462_1 := h4462c.2.1
                                    have p4462_2 := h4462c.2.2.1
                                    have p4462_3 := h4462c.2.2.2
                                    linarith only [h4433, hlam, p4462_0]
                                  · have p4462_0 := h4462c.1
                                    have p4462_1 := h4462c.2.1
                                    have p4462_2 := h4462c.2.2.1
                                    have p4462_3 := h4462c.2.2.2
                                    linarith only [h4427, hlam, p4462_0]
                                  · have p4462_0 := h4462c.1
                                    have p4462_1 := h4462c.2.1
                                    have p4462_2 := h4462c.2.2.1
                                    have p4462_3 := h4462c.2.2.2
                                    linarith only [h4430, hlam, p4462_1]
                                  · have p4462_0 := h4462c.1
                                    have p4462_1 := h4462c.2.1
                                    have p4462_2 := h4462c.2.2.1
                                    have p4462_3 := h4462c.2.2.2
                                    linarith only [h4432, hlam, p4462_0]
                                  · have p4462_0 := h4462c.1
                                    have p4462_1 := h4462c.2.1
                                    have p4462_2 := h4462c.2.2.1
                                    have p4462_3 := h4462c.2.2.2
                                    linarith only [h3363, h4426, h4427, h4452, h4456, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4462_1, u3elo1]
                                  · have p4462_0 := h4462c.1
                                    have p4462_1 := h4462c.2.1
                                    have p4462_2 := h4462c.2.2.1
                                    have p4462_3 := h4462c.2.2.2
                                    linarith only [hlam, p4462_0]
                            · linarith only [h3363, h4427, h4455, h4457, hc23, hlam, hphi, u3elo1]
                          · linarith only [h3363, h4431, h4456, hc23, hlam, hphi, u3elo1]
                        · linarith only [h3363, h4426, h4452, h4455, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · linarith only [h3363, h4426, h4452, h4454, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h0, h4430, h4453, hlam]
                  · linarith only [h0, h4429, h4452, hlam]
                · linarith only [h0, h4451, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h3363, h4427, h4432, hlam]
          · linarith only [h3363, h4426, h4431, hlam]
        · linarith only [h0, h4427, h4430, hlam]
      · linarith only [h3363, h4426, h4428, h4429, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h4628 | h4628
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4629 | h4629
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4630 | h4630
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4631 | h4631
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4632 | h4632
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4633 | h4633
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4634 | h4634
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4635 | h4635
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4636 | h4636
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4637 | h4637
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4638 | h4638
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4639 | h4639
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h4640 | h4640
                              · linarith only [h0, h4426, h4428, h4633, h4634, h4640, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h0, h4426, h4428, h4632, h4633, h4638, h4640, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · linarith only [h0, h4428, h4639, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h0, h4428, h4638, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h4426, h4428, h4633, h4634, h4637, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · linarith only [h0, h4426, h4428, h4633, h4634, h4636, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h0, h4426, h4428, h4633, h4634, h4635, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h4426, h4428, h4633, h4634, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h4426, h4633, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4650 | h4650
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4651 | h4651
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4652 | h4652
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4653 | h4653
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4654 | h4654
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4655 | h4655
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4656 | h4656
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h4657 | h4657
                              · linarith only [h0, h4426, h4428, h4632, h4651, h4657, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h4659 | h4659
                                · linarith only [h4428, h4630, h4632, h4650, h4659, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                · rcases h0bigk with h4661c | h4661c | h4661c | h4661c | h4661c | h4661c | h4661c | h4661c | h4661c | h4661c | h4661c | h4661c | h4661c | h4661c | h4661c | h4661c | h4661c | h4661c | h4661c | h4661c | h4661c | h4661c | h4661c | h4661c | h4661c
                                  · have p4661_0 := h4661c.1
                                    have p4661_1 := h4661c.2.1
                                    have p4661_2 := h4661c.2.2.1
                                    have p4661_3 := h4661c.2.2.2
                                    linarith only [hlam, p4661_0]
                                  · have p4661_0 := h4661c.1
                                    have p4661_1 := h4661c.2.1
                                    have p4661_2 := h4661c.2.2.1
                                    have p4661_3 := h4661c.2.2.2
                                    linarith only [h0, hlam, p4661_1]
                                  · have p4661_0 := h4661c.1
                                    have p4661_1 := h4661c.2.1
                                    have p4661_2 := h4661c.2.2.1
                                    have p4661_3 := h4661c.2.2.2
                                    linarith only [h3363, hlam, p4661_0]
                                  · have p4661_0 := h4661c.1
                                    have p4661_1 := h4661c.2.1
                                    have p4661_2 := h4661c.2.2.1
                                    have p4661_3 := h4661c.2.2.2
                                    linarith only [h0, h4426, h4428, h4650, h4651, h4655, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4661_1, u3elo1]
                                  · have p4661_0 := h4661c.1
                                    have p4661_1 := h4661c.2.1
                                    have p4661_2 := h4661c.2.2.1
                                    have p4661_3 := h4661c.2.2.2
                                    linarith only [h0, h4428, h4650, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4661_1, u3elo1]
                                  · have p4661_0 := h4661c.1
                                    have p4661_1 := h4661c.2.1
                                    have p4661_2 := h4661c.2.2.1
                                    have p4661_3 := h4661c.2.2.2
                                    linarith only [h4428, h4650, hc01, hlam, hphi, ht12, ht23, p4661_1, u3elo1]
                                  · have p4661_0 := h4661c.1
                                    have p4661_1 := h4661c.2.1
                                    have p4661_2 := h4661c.2.2.1
                                    have p4661_3 := h4661c.2.2.2
                                    linarith only [hlam, p4661_0]
                                  · have p4661_0 := h4661c.1
                                    have p4661_1 := h4661c.2.1
                                    have p4661_2 := h4661c.2.2.1
                                    have p4661_3 := h4661c.2.2.2
                                    linarith only [h4428, hlam, p4661_0]
                                  · have p4661_0 := h4661c.1
                                    have p4661_1 := h4661c.2.1
                                    have p4661_2 := h4661c.2.2.1
                                    have p4661_3 := h4661c.2.2.2
                                    linarith only [h4426, h4428, h4650, h4651, h4655, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4661_1, u3elo1]
                                  · have p4661_0 := h4661c.1
                                    have p4661_1 := h4661c.2.1
                                    have p4661_2 := h4661c.2.2.1
                                    have p4661_3 := h4661c.2.2.2
                                    linarith only [h4427, h4428, h4650, h4652, h4656, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4661_1, u3elo1]
                                  · have p4661_0 := h4661c.1
                                    have p4661_1 := h4661c.2.1
                                    have p4661_2 := h4661c.2.2.1
                                    have p4661_3 := h4661c.2.2.2
                                    linarith only [h4426, h4428, h4650, h4651, h4655, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4661_1, u3elo1]
                                  · have p4661_0 := h4661c.1
                                    have p4661_1 := h4661c.2.1
                                    have p4661_2 := h4661c.2.2.1
                                    have p4661_3 := h4661c.2.2.2
                                    linarith only [h4428, h4650, hc02, hlam, hphi, ht23, p4661_1, u3elo1]
                                  · have p4661_0 := h4661c.1
                                    have p4661_1 := h4661c.2.1
                                    have p4661_2 := h4661c.2.2.1
                                    have p4661_3 := h4661c.2.2.2
                                    linarith only [hlam, p4661_0]
                                  · have p4661_0 := h4661c.1
                                    have p4661_1 := h4661c.2.1
                                    have p4661_2 := h4661c.2.2.1
                                    have p4661_3 := h4661c.2.2.2
                                    rcases p4661_3 (m.d 0 1) (by simp) with h4675 | h4675
                                    · linarith only [h3363, h4675, hlam]
                                    · linarith only [h4426, h4675, hlam]
                                  · have p4661_0 := h4661c.1
                                    have p4661_1 := h4661c.2.1
                                    have p4661_2 := h4661c.2.2.1
                                    have p4661_3 := h4661c.2.2.2
                                    rcases p4661_3 (m.d 0 1) (by simp) with h4678 | h4678
                                    · linarith only [h3363, h4678, hlam]
                                    · linarith only [h4427, h4678, hlam]
                                  · have p4661_0 := h4661c.1
                                    have p4661_1 := h4661c.2.1
                                    have p4661_2 := h4661c.2.2.1
                                    have p4661_3 := h4661c.2.2.2
                                    linarith only [h4426, hlam, p4661_0]
                                  · have p4661_0 := h4661c.1
                                    have p4661_1 := h4661c.2.1
                                    have p4661_2 := h4661c.2.2.1
                                    have p4661_3 := h4661c.2.2.2
                                    linarith only [h4628, hlam, p4661_0]
                                  · have p4661_0 := h4661c.1
                                    have p4661_1 := h4661c.2.1
                                    have p4661_2 := h4661c.2.2.1
                                    have p4661_3 := h4661c.2.2.2
                                    linarith only [h4630, hlam, p4661_0]
                                  · have p4661_0 := h4661c.1
                                    have p4661_1 := h4661c.2.1
                                    have p4661_2 := h4661c.2.2.1
                                    have p4661_3 := h4661c.2.2.2
                                    linarith only [hlam, p4661_0]
                                  · have p4661_0 := h4661c.1
                                    have p4661_1 := h4661c.2.1
                                    have p4661_2 := h4661c.2.2.1
                                    have p4661_3 := h4661c.2.2.2
                                    linarith only [h4632, hlam, p4661_0]
                                  · have p4661_0 := h4661c.1
                                    have p4661_1 := h4661c.2.1
                                    have p4661_2 := h4661c.2.2.1
                                    have p4661_3 := h4661c.2.2.2
                                    linarith only [h4427, hlam, p4661_0]
                                  · have p4661_0 := h4661c.1
                                    have p4661_1 := h4661c.2.1
                                    have p4661_2 := h4661c.2.2.1
                                    have p4661_3 := h4661c.2.2.2
                                    linarith only [h4629, hlam, p4661_1]
                                  · have p4661_0 := h4661c.1
                                    have p4661_1 := h4661c.2.1
                                    have p4661_2 := h4661c.2.2.1
                                    have p4661_3 := h4661c.2.2.2
                                    linarith only [h4631, hlam, p4661_0]
                                  · have p4661_0 := h4661c.1
                                    have p4661_1 := h4661c.2.1
                                    have p4661_2 := h4661c.2.2.1
                                    have p4661_3 := h4661c.2.2.2
                                    linarith only [h3363, h4426, h4427, h4651, h4655, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4661_1, u3elo1]
                                  · have p4661_0 := h4661c.1
                                    have p4661_1 := h4661c.2.1
                                    have p4661_2 := h4661c.2.2.1
                                    have p4661_3 := h4661c.2.2.2
                                    linarith only [hlam, p4661_0]
                            · linarith only [h0, h4428, h4656, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h0, h4426, h4428, h4651, h4655, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h0, h4426, h4428, h4650, h4651, h4654, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · linarith only [h0, h4426, h4428, h4650, h4651, h4653, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h0, h4426, h4428, h4650, h4651, h4652, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h4426, h4428, h4650, h4651, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h4426, h4650, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
            · linarith only [h3363, h4427, h4631, hlam]
          · linarith only [h0, h4426, h4428, h4630, hlam]
        · linarith only [h0, h4427, h4629, hlam]
      · linarith only [h0, h4426, h4628, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h4702 | h4702
    · rcases m.htr 0 2 4 (by decide) (by decide) with h4703 | h4703
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4704 | h4704
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4705 | h4705
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4706 | h4706
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4707 | h4707
              · linarith only [h4426, h4427, h4707, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4709 | h4709
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4710 | h4710
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4711 | h4711
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4712 | h4712
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4713 | h4713
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4714 | h4714
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4715 | h4715
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h4716 | h4716
                              · linarith only [h4426, h4427, h4707, h4710, h4716, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h4718 | h4718
                                · linarith only [h4426, h4427, h4707, h4710, h4714, h4718, hlam]
                                · rcases h0bigk with h4720c | h4720c | h4720c | h4720c | h4720c | h4720c | h4720c | h4720c | h4720c | h4720c | h4720c | h4720c | h4720c | h4720c | h4720c | h4720c | h4720c | h4720c | h4720c | h4720c | h4720c | h4720c | h4720c | h4720c | h4720c
                                  · have p4720_0 := h4720c.1
                                    have p4720_1 := h4720c.2.1
                                    have p4720_2 := h4720c.2.2.1
                                    have p4720_3 := h4720c.2.2.2
                                    linarith only [hlam, p4720_0]
                                  · have p4720_0 := h4720c.1
                                    have p4720_1 := h4720c.2.1
                                    have p4720_2 := h4720c.2.2.1
                                    have p4720_3 := h4720c.2.2.2
                                    linarith only [h0, hlam, p4720_1]
                                  · have p4720_0 := h4720c.1
                                    have p4720_1 := h4720c.2.1
                                    have p4720_2 := h4720c.2.2.1
                                    have p4720_3 := h4720c.2.2.2
                                    linarith only [h3363, hlam, p4720_0]
                                  · have p4720_0 := h4720c.1
                                    have p4720_1 := h4720c.2.1
                                    have p4720_2 := h4720c.2.2.1
                                    have p4720_3 := h4720c.2.2.2
                                    linarith only [h4427, h4713, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4720_1, u3elo1]
                                  · have p4720_0 := h4720c.1
                                    have p4720_1 := h4720c.2.1
                                    have p4720_2 := h4720c.2.2.1
                                    have p4720_3 := h4720c.2.2.2
                                    linarith only [h4427, hlam, p4720_1]
                                  · have p4720_0 := h4720c.1
                                    have p4720_1 := h4720c.2.1
                                    have p4720_2 := h4720c.2.2.1
                                    have p4720_3 := h4720c.2.2.2
                                    rcases p4720_3 (m.d 0 1) (by simp) with h4726 | h4726
                                    · linarith only [h0, h4726, hlam]
                                    · rcases p4720_3 (m.d 0 2) (by simp) with h4728 | h4728
                                      · rcases p4720_3 (m.d 0 3) (by simp) with h4729 | h4729
                                        · linarith only [h4702, h4729, hlam]
                                        · linarith only [h3363, h4729, hlam]
                                      · linarith only [h0, h4728, hlam]
                                  · have p4720_0 := h4720c.1
                                    have p4720_1 := h4720c.2.1
                                    have p4720_2 := h4720c.2.2.1
                                    have p4720_3 := h4720c.2.2.2
                                    linarith only [hlam, p4720_0]
                                  · have p4720_0 := h4720c.1
                                    have p4720_1 := h4720c.2.1
                                    have p4720_2 := h4720c.2.2.1
                                    have p4720_3 := h4720c.2.2.2
                                    rcases p4720_3 (m.d 0 1) (by simp) with h4734 | h4734
                                    · linarith only [h0, h4734, hlam]
                                    · rcases p4720_3 (m.d 0 2) (by simp) with h4736 | h4736
                                      · rcases p4720_3 (m.d 0 3) (by simp) with h4737 | h4737
                                        · linarith only [h4702, h4737, hlam]
                                        · rcases p4720_3 (m.d 0 4) (by simp) with h4739 | h4739
                                          · linarith only [h4703, h4739, hlam]
                                          · rcases p4720_3 (m.d 0 5) (by simp) with h4741 | h4741
                                            · linarith only [h4704, h4741, hlam]
                                            · rcases h0emin with h4743 | h4743 | h4743 | h4743 | h4743
                                              · linarith only [h4427, h4713, h4743, hlam, ht01, ht12, ht23, u3elo1]
                                              · rcases h2bigk with h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c | h4745c
                                                · have p4745_0 := h4745c.1
                                                  have p4745_1 := h4745c.2.1
                                                  have p4745_2 := h4745c.2.2.1
                                                  have p4745_3 := h4745c.2.2.2
                                                  linarith only [hlam, p4745_0]
                                                · have p4745_0 := h4745c.1
                                                  have p4745_1 := h4745c.2.1
                                                  have p4745_2 := h4745c.2.2.1
                                                  have p4745_3 := h4745c.2.2.2
                                                  linarith only [h0, hlam, p4745_1]
                                                · have p4745_0 := h4745c.1
                                                  have p4745_1 := h4745c.2.1
                                                  have p4745_2 := h4745c.2.2.1
                                                  have p4745_3 := h4745c.2.2.2
                                                  rcases p4745_3 (m.d 0 2) (by simp) with h4748 | h4748
                                                  · rcases p4745_3 (m.d 1 2) (by simp) with h4749 | h4749
                                                    · rcases p4745_3 (m.d 2 3) (by simp) with h4750 | h4750
                                                      · linarith only [h4750, hlam, p4745_0]
                                                      · rcases p4745_3 (m.d 2 4) (by simp) with h4752 | h4752
                                                        · linarith only [h4703, h4752, hlam]
                                                        · rcases p4745_3 (m.d 2 5) (by simp) with h4754 | h4754
                                                          · linarith only [h4704, h4754, hlam]
                                                          · rcases h2emin with h4756 | h4756 | h4756 | h4756 | h4756
                                                            · rcases h3bigk with h4757c | h4757c | h4757c | h4757c | h4757c | h4757c | h4757c | h4757c | h4757c | h4757c | h4757c | h4757c | h4757c | h4757c | h4757c | h4757c | h4757c | h4757c | h4757c | h4757c | h4757c | h4757c | h4757c | h4757c | h4757c
                                                              · have p4757_0 := h4757c.1
                                                                have p4757_1 := h4757c.2.1
                                                                have p4757_2 := h4757c.2.2.1
                                                                have p4757_3 := h4757c.2.2.2
                                                                linarith only [hlam, p4757_0]
                                                              · have p4757_0 := h4757c.1
                                                                have p4757_1 := h4757c.2.1
                                                                have p4757_2 := h4757c.2.2.1
                                                                have p4757_3 := h4757c.2.2.2
                                                                linarith only [h3363, hlam, p4757_1]
                                                              · have p4757_0 := h4757c.1
                                                                have p4757_1 := h4757c.2.1
                                                                have p4757_2 := h4757c.2.2.1
                                                                have p4757_3 := h4757c.2.2.2
                                                                linarith only [h0, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4720_1, p4757_1]
                                                              · have p4757_0 := h4757c.1
                                                                have p4757_1 := h4757c.2.1
                                                                have p4757_2 := h4757c.2.2.1
                                                                have p4757_3 := h4757c.2.2.2
                                                                linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4720_1, p4757_1]
                                                              · have p4757_0 := h4757c.1
                                                                have p4757_1 := h4757c.2.1
                                                                have p4757_2 := h4757c.2.2.1
                                                                have p4757_3 := h4757c.2.2.2
                                                                linarith only [h0, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p4720_1, p4757_1]
                                                              · have p4757_0 := h4757c.1
                                                                have p4757_1 := h4757c.2.1
                                                                have p4757_2 := h4757c.2.2.1
                                                                have p4757_3 := h4757c.2.2.2
                                                                linarith only [hc03, hlam, hphi, p4757_1, u3elo1]
                                                              · have p4757_0 := h4757c.1
                                                                have p4757_1 := h4757c.2.1
                                                                have p4757_2 := h4757c.2.2.1
                                                                have p4757_3 := h4757c.2.2.2
                                                                linarith only [hlam, p4757_0]
                                                              · have p4757_0 := h4757c.1
                                                                have p4757_1 := h4757c.2.1
                                                                have p4757_2 := h4757c.2.2.1
                                                                have p4757_3 := h4757c.2.2.2
                                                                linarith only [h4715, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4757_1, u3elo1]
                                                              · have p4757_0 := h4757c.1
                                                                have p4757_1 := h4757c.2.1
                                                                have p4757_2 := h4757c.2.2.1
                                                                have p4757_3 := h4757c.2.2.2
                                                                rcases p4757_3 (m.d 0 3) (by simp) with h4766 | h4766
                                                                · linarith only [h3363, h4766, hlam]
                                                                · linarith only [h4705, h4766, hlam]
                                                              · have p4757_0 := h4757c.1
                                                                have p4757_1 := h4757c.2.1
                                                                have p4757_2 := h4757c.2.2.1
                                                                have p4757_3 := h4757c.2.2.2
                                                                rcases p4757_3 (m.d 0 3) (by simp) with h4769 | h4769
                                                                · linarith only [h3363, h4769, hlam]
                                                                · linarith only [h4706, h4769, hlam]
                                                              · have p4757_0 := h4757c.1
                                                                have p4757_1 := h4757c.2.1
                                                                have p4757_2 := h4757c.2.2.1
                                                                have p4757_3 := h4757c.2.2.2
                                                                linarith only [h4702, hlam, p4757_0]
                                                              · have p4757_0 := h4757c.1
                                                                have p4757_1 := h4757c.2.1
                                                                have p4757_2 := h4757c.2.2.1
                                                                have p4757_3 := h4757c.2.2.2
                                                                linarith only [h4709, hlam, p4757_0]
                                                              · have p4757_0 := h4757c.1
                                                                have p4757_1 := h4757c.2.1
                                                                have p4757_2 := h4757c.2.2.1
                                                                have p4757_3 := h4757c.2.2.2
                                                                linarith only [hlam, p4757_0]
                                                              · have p4757_0 := h4757c.1
                                                                have p4757_1 := h4757c.2.1
                                                                have p4757_2 := h4757c.2.2.1
                                                                have p4757_3 := h4757c.2.2.2
                                                                linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4745_1, p4757_1]
                                                              · have p4757_0 := h4757c.1
                                                                have p4757_1 := h4757c.2.1
                                                                have p4757_2 := h4757c.2.2.1
                                                                have p4757_3 := h4757c.2.2.2
                                                                linarith only [h0, h4702, h4718, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4720_1, p4757_1]
                                                              · have p4757_0 := h4757c.1
                                                                have p4757_1 := h4757c.2.1
                                                                have p4757_2 := h4757c.2.2.1
                                                                have p4757_3 := h4757c.2.2.2
                                                                linarith only [h4705, hlam, p4757_0]
                                                              · have p4757_0 := h4757c.1
                                                                have p4757_1 := h4757c.2.1
                                                                have p4757_2 := h4757c.2.2.1
                                                                have p4757_3 := h4757c.2.2.2
                                                                linarith only [h4712, hlam, p4757_0]
                                                              · have p4757_0 := h4757c.1
                                                                have p4757_1 := h4757c.2.1
                                                                have p4757_2 := h4757c.2.2.1
                                                                have p4757_3 := h4757c.2.2.2
                                                                linarith only [h4714, hlam, p4757_0]
                                                              · have p4757_0 := h4757c.1
                                                                have p4757_1 := h4757c.2.1
                                                                have p4757_2 := h4757c.2.2.1
                                                                have p4757_3 := h4757c.2.2.2
                                                                linarith only [hlam, p4757_0]
                                                              · have p4757_0 := h4757c.1
                                                                have p4757_1 := h4757c.2.1
                                                                have p4757_2 := h4757c.2.2.1
                                                                have p4757_3 := h4757c.2.2.2
                                                                linarith only [h4718, hlam, p4757_1]
                                                              · have p4757_0 := h4757c.1
                                                                have p4757_1 := h4757c.2.1
                                                                have p4757_2 := h4757c.2.2.1
                                                                have p4757_3 := h4757c.2.2.2
                                                                linarith only [h4706, hlam, p4757_0]
                                                              · have p4757_0 := h4757c.1
                                                                have p4757_1 := h4757c.2.1
                                                                have p4757_2 := h4757c.2.2.1
                                                                have p4757_3 := h4757c.2.2.2
                                                                linarith only [h4713, hlam, p4757_0]
                                                              · have p4757_0 := h4757c.1
                                                                have p4757_1 := h4757c.2.1
                                                                have p4757_2 := h4757c.2.2.1
                                                                have p4757_3 := h4757c.2.2.2
                                                                linarith only [h4715, hlam, p4757_0]
                                                              · have p4757_0 := h4757c.1
                                                                have p4757_1 := h4757c.2.1
                                                                have p4757_2 := h4757c.2.2.1
                                                                have p4757_3 := h4757c.2.2.2
                                                                linarith only [h0, h4706, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4720_1, p4757_1]
                                                              · have p4757_0 := h4757c.1
                                                                have p4757_1 := h4757c.2.1
                                                                have p4757_2 := h4757c.2.2.1
                                                                have p4757_3 := h4757c.2.2.2
                                                                linarith only [hlam, p4757_0]
                                                            · rcases h3bigk with h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c | h4787c
                                                              · have p4787_0 := h4787c.1
                                                                have p4787_1 := h4787c.2.1
                                                                have p4787_2 := h4787c.2.2.1
                                                                have p4787_3 := h4787c.2.2.2
                                                                linarith only [hlam, p4787_0]
                                                              · have p4787_0 := h4787c.1
                                                                have p4787_1 := h4787c.2.1
                                                                have p4787_2 := h4787c.2.2.1
                                                                have p4787_3 := h4787c.2.2.2
                                                                linarith only [h3363, hlam, p4787_1]
                                                              · have p4787_0 := h4787c.1
                                                                have p4787_1 := h4787c.2.1
                                                                have p4787_2 := h4787c.2.2.1
                                                                have p4787_3 := h4787c.2.2.2
                                                                linarith only [h0, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4720_1, p4787_1]
                                                              · have p4787_0 := h4787c.1
                                                                have p4787_1 := h4787c.2.1
                                                                have p4787_2 := h4787c.2.2.1
                                                                have p4787_3 := h4787c.2.2.2
                                                                linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4720_1, p4787_1]
                                                              · have p4787_0 := h4787c.1
                                                                have p4787_1 := h4787c.2.1
                                                                have p4787_2 := h4787c.2.2.1
                                                                have p4787_3 := h4787c.2.2.2
                                                                linarith only [h0, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p4720_1, p4787_1]
                                                              · have p4787_0 := h4787c.1
                                                                have p4787_1 := h4787c.2.1
                                                                have p4787_2 := h4787c.2.2.1
                                                                have p4787_3 := h4787c.2.2.2
                                                                linarith only [hc03, hlam, hphi, p4787_1, u3elo1]
                                                              · have p4787_0 := h4787c.1
                                                                have p4787_1 := h4787c.2.1
                                                                have p4787_2 := h4787c.2.2.1
                                                                have p4787_3 := h4787c.2.2.2
                                                                linarith only [hlam, p4787_0]
                                                              · have p4787_0 := h4787c.1
                                                                have p4787_1 := h4787c.2.1
                                                                have p4787_2 := h4787c.2.2.1
                                                                have p4787_3 := h4787c.2.2.2
                                                                linarith only [h4715, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4787_1, u3elo1]
                                                              · have p4787_0 := h4787c.1
                                                                have p4787_1 := h4787c.2.1
                                                                have p4787_2 := h4787c.2.2.1
                                                                have p4787_3 := h4787c.2.2.2
                                                                rcases p4787_3 (m.d 0 3) (by simp) with h4796 | h4796
                                                                · linarith only [h3363, h4796, hlam]
                                                                · linarith only [h4705, h4796, hlam]
                                                              · have p4787_0 := h4787c.1
                                                                have p4787_1 := h4787c.2.1
                                                                have p4787_2 := h4787c.2.2.1
                                                                have p4787_3 := h4787c.2.2.2
                                                                rcases p4787_3 (m.d 0 3) (by simp) with h4799 | h4799
                                                                · linarith only [h3363, h4799, hlam]
                                                                · linarith only [h4706, h4799, hlam]
                                                              · have p4787_0 := h4787c.1
                                                                have p4787_1 := h4787c.2.1
                                                                have p4787_2 := h4787c.2.2.1
                                                                have p4787_3 := h4787c.2.2.2
                                                                linarith only [h4702, hlam, p4787_0]
                                                              · have p4787_0 := h4787c.1
                                                                have p4787_1 := h4787c.2.1
                                                                have p4787_2 := h4787c.2.2.1
                                                                have p4787_3 := h4787c.2.2.2
                                                                linarith only [h4709, hlam, p4787_0]
                                                              · have p4787_0 := h4787c.1
                                                                have p4787_1 := h4787c.2.1
                                                                have p4787_2 := h4787c.2.2.1
                                                                have p4787_3 := h4787c.2.2.2
                                                                linarith only [hlam, p4787_0]
                                                              · have p4787_0 := h4787c.1
                                                                have p4787_1 := h4787c.2.1
                                                                have p4787_2 := h4787c.2.2.1
                                                                have p4787_3 := h4787c.2.2.2
                                                                linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4745_1, p4787_1]
                                                              · have p4787_0 := h4787c.1
                                                                have p4787_1 := h4787c.2.1
                                                                have p4787_2 := h4787c.2.2.1
                                                                have p4787_3 := h4787c.2.2.2
                                                                linarith only [h0, h4702, h4718, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4720_1, p4787_1]
                                                              · have p4787_0 := h4787c.1
                                                                have p4787_1 := h4787c.2.1
                                                                have p4787_2 := h4787c.2.2.1
                                                                have p4787_3 := h4787c.2.2.2
                                                                linarith only [h4705, hlam, p4787_0]
                                                              · have p4787_0 := h4787c.1
                                                                have p4787_1 := h4787c.2.1
                                                                have p4787_2 := h4787c.2.2.1
                                                                have p4787_3 := h4787c.2.2.2
                                                                linarith only [h4712, hlam, p4787_0]
                                                              · have p4787_0 := h4787c.1
                                                                have p4787_1 := h4787c.2.1
                                                                have p4787_2 := h4787c.2.2.1
                                                                have p4787_3 := h4787c.2.2.2
                                                                linarith only [h4714, hlam, p4787_0]
                                                              · have p4787_0 := h4787c.1
                                                                have p4787_1 := h4787c.2.1
                                                                have p4787_2 := h4787c.2.2.1
                                                                have p4787_3 := h4787c.2.2.2
                                                                linarith only [hlam, p4787_0]
                                                              · have p4787_0 := h4787c.1
                                                                have p4787_1 := h4787c.2.1
                                                                have p4787_2 := h4787c.2.2.1
                                                                have p4787_3 := h4787c.2.2.2
                                                                linarith only [h4718, hlam, p4787_1]
                                                              · have p4787_0 := h4787c.1
                                                                have p4787_1 := h4787c.2.1
                                                                have p4787_2 := h4787c.2.2.1
                                                                have p4787_3 := h4787c.2.2.2
                                                                linarith only [h4706, hlam, p4787_0]
                                                              · have p4787_0 := h4787c.1
                                                                have p4787_1 := h4787c.2.1
                                                                have p4787_2 := h4787c.2.2.1
                                                                have p4787_3 := h4787c.2.2.2
                                                                linarith only [h4713, hlam, p4787_0]
                                                              · have p4787_0 := h4787c.1
                                                                have p4787_1 := h4787c.2.1
                                                                have p4787_2 := h4787c.2.2.1
                                                                have p4787_3 := h4787c.2.2.2
                                                                linarith only [h4715, hlam, p4787_0]
                                                              · have p4787_0 := h4787c.1
                                                                have p4787_1 := h4787c.2.1
                                                                have p4787_2 := h4787c.2.2.1
                                                                have p4787_3 := h4787c.2.2.2
                                                                linarith only [h0, h4706, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4720_1, p4787_1]
                                                              · have p4787_0 := h4787c.1
                                                                have p4787_1 := h4787c.2.1
                                                                have p4787_2 := h4787c.2.2.1
                                                                have p4787_3 := h4787c.2.2.2
                                                                linarith only [hlam, p4787_0]
                                                            · linarith only [h0, h4702, h4756, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4720_1]
                                                            · linarith only [h4426, h4427, h4710, h4756, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                                                            · linarith only [h0, h4704, h4706, h4756, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4720_1]
                                                    · linarith only [h4709, h4749, hlam]
                                                  · linarith only [h4748, hlam, p4745_0]
                                                · have p4745_0 := h4745c.1
                                                  have p4745_1 := h4745c.2.1
                                                  have p4745_2 := h4745c.2.2.1
                                                  have p4745_3 := h4745c.2.2.2
                                                  linarith only [h3363, h4426, h4710, hlam, p4720_1, p4745_2]
                                                · have p4745_0 := h4745c.1
                                                  have p4745_1 := h4745c.2.1
                                                  have p4745_2 := h4745c.2.2.1
                                                  have p4745_3 := h4745c.2.2.2
                                                  rcases p4745_3 (m.d 0 2) (by simp) with h4823 | h4823
                                                  · rcases p4745_3 (m.d 1 2) (by simp) with h4824 | h4824
                                                    · rcases p4745_3 (m.d 2 3) (by simp) with h4825 | h4825
                                                      · linarith only [h4702, h4825, hlam]
                                                      · linarith only [h4715, h4825, hlam]
                                                    · linarith only [h4711, h4824, hlam]
                                                  · linarith only [h4823, hlam, p4745_0]
                                                · have p4745_0 := h4745c.1
                                                  have p4745_1 := h4745c.2.1
                                                  have p4745_2 := h4745c.2.2.1
                                                  have p4745_3 := h4745c.2.2.2
                                                  linarith only [h4426, h4427, h4706, h4710, h4714, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4720_1, p4745_1]
                                                · have p4745_0 := h4745c.1
                                                  have p4745_1 := h4745c.2.1
                                                  have p4745_2 := h4745c.2.2.1
                                                  have p4745_3 := h4745c.2.2.2
                                                  linarith only [hlam, p4745_0]
                                                · have p4745_0 := h4745c.1
                                                  have p4745_1 := h4745c.2.1
                                                  have p4745_2 := h4745c.2.2.1
                                                  have p4745_3 := h4745c.2.2.2
                                                  rcases p4745_3 (m.d 0 2) (by simp) with h4832 | h4832
                                                  · linarith only [h0, h4832, hlam]
                                                  · linarith only [h4702, h4832, hlam]
                                                · have p4745_0 := h4745c.1
                                                  have p4745_1 := h4745c.2.1
                                                  have p4745_2 := h4745c.2.2.1
                                                  have p4745_3 := h4745c.2.2.2
                                                  linarith only [h0, h4426, h4427, h4706, h4710, hlam, p4720_1, p4745_2]
                                                · have p4745_0 := h4745c.1
                                                  have p4745_1 := h4745c.2.1
                                                  have p4745_2 := h4745c.2.2.1
                                                  have p4745_3 := h4745c.2.2.2
                                                  rcases p4745_3 (m.d 0 2) (by simp) with h4836 | h4836
                                                  · linarith only [h0, h4836, hlam]
                                                  · linarith only [h4704, h4836, hlam]
                                                · have p4745_0 := h4745c.1
                                                  have p4745_1 := h4745c.2.1
                                                  have p4745_2 := h4745c.2.2.1
                                                  have p4745_3 := h4745c.2.2.2
                                                  linarith only [h4702, hlam, p4745_0]
                                                · have p4745_0 := h4745c.1
                                                  have p4745_1 := h4745c.2.1
                                                  have p4745_2 := h4745c.2.2.1
                                                  have p4745_3 := h4745c.2.2.2
                                                  linarith only [h4709, hlam, p4745_0]
                                                · have p4745_0 := h4745c.1
                                                  have p4745_1 := h4745c.2.1
                                                  have p4745_2 := h4745c.2.2.1
                                                  have p4745_3 := h4745c.2.2.2
                                                  linarith only [hlam, p4745_0]
                                                · have p4745_0 := h4745c.1
                                                  have p4745_1 := h4745c.2.1
                                                  have p4745_2 := h4745c.2.2.1
                                                  have p4745_3 := h4745c.2.2.2
                                                  linarith only [h4702, h4714, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p4720_1, p4745_1]
                                                · have p4745_0 := h4745c.1
                                                  have p4745_1 := h4745c.2.1
                                                  have p4745_2 := h4745c.2.2.1
                                                  have p4745_3 := h4745c.2.2.2
                                                  linarith only [h0, h4702, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p4720_1, p4745_1]
                                                · have p4745_0 := h4745c.1
                                                  have p4745_1 := h4745c.2.1
                                                  have p4745_2 := h4745c.2.2.1
                                                  have p4745_3 := h4745c.2.2.2
                                                  linarith only [h4703, hlam, p4745_0]
                                                · have p4745_0 := h4745c.1
                                                  have p4745_1 := h4745c.2.1
                                                  have p4745_2 := h4745c.2.2.1
                                                  have p4745_3 := h4745c.2.2.2
                                                  linarith only [h4710, hlam, p4745_0]
                                                · have p4745_0 := h4745c.1
                                                  have p4745_1 := h4745c.2.1
                                                  have p4745_2 := h4745c.2.2.1
                                                  have p4745_3 := h4745c.2.2.2
                                                  linarith only [h4714, hlam, p4745_1]
                                                · have p4745_0 := h4745c.1
                                                  have p4745_1 := h4745c.2.1
                                                  have p4745_2 := h4745c.2.2.1
                                                  have p4745_3 := h4745c.2.2.2
                                                  linarith only [hlam, p4745_0]
                                                · have p4745_0 := h4745c.1
                                                  have p4745_1 := h4745c.2.1
                                                  have p4745_2 := h4745c.2.2.1
                                                  have p4745_3 := h4745c.2.2.2
                                                  linarith only [h4716, hlam, p4745_1]
                                                · have p4745_0 := h4745c.1
                                                  have p4745_1 := h4745c.2.1
                                                  have p4745_2 := h4745c.2.2.1
                                                  have p4745_3 := h4745c.2.2.2
                                                  linarith only [h4704, hlam, p4745_0]
                                                · have p4745_0 := h4745c.1
                                                  have p4745_1 := h4745c.2.1
                                                  have p4745_2 := h4745c.2.2.1
                                                  have p4745_3 := h4745c.2.2.2
                                                  linarith only [h4711, hlam, p4745_0]
                                                · have p4745_0 := h4745c.1
                                                  have p4745_1 := h4745c.2.1
                                                  have p4745_2 := h4745c.2.2.1
                                                  have p4745_3 := h4745c.2.2.2
                                                  linarith only [h4715, hlam, p4745_1]
                                                · have p4745_0 := h4745c.1
                                                  have p4745_1 := h4745c.2.1
                                                  have p4745_2 := h4745c.2.2.1
                                                  have p4745_3 := h4745c.2.2.2
                                                  linarith only [h0, h4704, h4706, h4714, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4720_1, p4745_1]
                                                · have p4745_0 := h4745c.1
                                                  have p4745_1 := h4745c.2.1
                                                  have p4745_2 := h4745c.2.2.1
                                                  have p4745_3 := h4745c.2.2.2
                                                  linarith only [hlam, p4745_0]
                                              · linarith only [h0, h4743, hc12, hlam, ht01, p4720_1]
                                              · linarith only [h4426, h4427, h4713, h4743, hlam, ht01, ht12, ht23, u3elo1]
                                              · linarith only [h0, h4706, h4743, hc12, hlam, ht01, p4720_1]
                                      · linarith only [h4702, h4736, hlam]
                                  · have p4720_0 := h4720c.1
                                    have p4720_1 := h4720c.2.1
                                    have p4720_2 := h4720c.2.2.1
                                    have p4720_3 := h4720c.2.2.2
                                    rcases p4720_3 (m.d 0 1) (by simp) with h4858 | h4858
                                    · linarith only [h0, h4858, hlam]
                                    · linarith only [h4426, h4858, hlam]
                                  · have p4720_0 := h4720c.1
                                    have p4720_1 := h4720c.2.1
                                    have p4720_2 := h4720c.2.2.1
                                    have p4720_3 := h4720c.2.2.2
                                    rcases p4720_3 (m.d 0 1) (by simp) with h4861 | h4861
                                    · linarith only [h0, h4861, hlam]
                                    · rcases p4720_3 (m.d 0 2) (by simp) with h4863 | h4863
                                      · rcases p4720_3 (m.d 0 3) (by simp) with h4864 | h4864
                                        · linarith only [h4702, h4864, hlam]
                                        · linarith only [h4706, h4864, hlam]
                                      · linarith only [h4704, h4863, hlam]
                                  · have p4720_0 := h4720c.1
                                    have p4720_1 := h4720c.2.1
                                    have p4720_2 := h4720c.2.2.1
                                    have p4720_3 := h4720c.2.2.2
                                    linarith only [hc01, hlam, hphi, ht12, ht23, p4720_1, u3elo0]
                                  · have p4720_0 := h4720c.1
                                    have p4720_1 := h4720c.2.1
                                    have p4720_2 := h4720c.2.2.1
                                    have p4720_3 := h4720c.2.2.2
                                    linarith only [h4702, hlam, p4720_1]
                                  · have p4720_0 := h4720c.1
                                    have p4720_1 := h4720c.2.1
                                    have p4720_2 := h4720c.2.2.1
                                    have p4720_3 := h4720c.2.2.2
                                    linarith only [hlam, p4720_0]
                                  · have p4720_0 := h4720c.1
                                    have p4720_1 := h4720c.2.1
                                    have p4720_2 := h4720c.2.2.1
                                    have p4720_3 := h4720c.2.2.2
                                    rcases p4720_3 (m.d 0 1) (by simp) with h4871 | h4871
                                    · linarith only [h3363, h4871, hlam]
                                    · linarith only [h4426, h4871, hlam]
                                  · have p4720_0 := h4720c.1
                                    have p4720_1 := h4720c.2.1
                                    have p4720_2 := h4720c.2.2.1
                                    have p4720_3 := h4720c.2.2.2
                                    linarith only [h3363, h4426, h4427, h4710, h4714, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4720_1, u3elo1]
                                  · have p4720_0 := h4720c.1
                                    have p4720_1 := h4720c.2.1
                                    have p4720_2 := h4720c.2.2.1
                                    have p4720_3 := h4720c.2.2.2
                                    linarith only [h4426, hlam, p4720_0]
                                  · have p4720_0 := h4720c.1
                                    have p4720_1 := h4720c.2.1
                                    have p4720_2 := h4720c.2.2.1
                                    have p4720_3 := h4720c.2.2.2
                                    linarith only [h4703, hlam, p4720_0]
                                  · have p4720_0 := h4720c.1
                                    have p4720_1 := h4720c.2.1
                                    have p4720_2 := h4720c.2.2.1
                                    have p4720_3 := h4720c.2.2.2
                                    linarith only [h4705, hlam, p4720_0]
                                  · have p4720_0 := h4720c.1
                                    have p4720_1 := h4720c.2.1
                                    have p4720_2 := h4720c.2.2.1
                                    have p4720_3 := h4720c.2.2.2
                                    linarith only [hlam, p4720_0]
                                  · have p4720_0 := h4720c.1
                                    have p4720_1 := h4720c.2.1
                                    have p4720_2 := h4720c.2.2.1
                                    have p4720_3 := h4720c.2.2.2
                                    linarith only [h4707, hlam, p4720_0]
                                  · have p4720_0 := h4720c.1
                                    have p4720_1 := h4720c.2.1
                                    have p4720_2 := h4720c.2.2.1
                                    have p4720_3 := h4720c.2.2.2
                                    linarith only [h4426, h4707, h4710, h4714, hc34, hc45, hlam, hphi, p4720_1]
                                  · have p4720_0 := h4720c.1
                                    have p4720_1 := h4720c.2.1
                                    have p4720_2 := h4720c.2.2.1
                                    have p4720_3 := h4720c.2.2.2
                                    linarith only [h4704, hlam, p4720_1]
                                  · have p4720_0 := h4720c.1
                                    have p4720_1 := h4720c.2.1
                                    have p4720_2 := h4720c.2.2.1
                                    have p4720_3 := h4720c.2.2.2
                                    linarith only [h4706, hlam, p4720_0]
                                  · have p4720_0 := h4720c.1
                                    have p4720_1 := h4720c.2.1
                                    have p4720_2 := h4720c.2.2.1
                                    have p4720_3 := h4720c.2.2.2
                                    rcases p4720_3 (m.d 0 1) (by simp) with h4883 | h4883
                                    · linarith only [h4427, h4883, hlam]
                                    · linarith only [h4426, h4883, hlam]
                                  · have p4720_0 := h4720c.1
                                    have p4720_1 := h4720c.2.1
                                    have p4720_2 := h4720c.2.2.1
                                    have p4720_3 := h4720c.2.2.2
                                    linarith only [hlam, p4720_0]
                            · linarith only [h3363, h4706, h4715, hc23, hlam, hphi, u3elo1]
                          · linarith only [h3363, h4705, h4714, hc23, hlam, hphi, u3elo1]
                        · linarith only [h3363, h4706, h4713, hlam]
                      · linarith only [h3363, h4712, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h0, h4426, h4704, h4706, h4710, h4711, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                  · linarith only [h0, h4703, h4710, hlam]
                · linarith only [h0, h4709, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4894 | h4894
              · linarith only [h4426, h4427, h4894, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4896 | h4896
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4897 | h4897
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4898 | h4898
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4899 | h4899
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4900 | h4900
                        · linarith only [h4706, h4900, hc03, hlam, hphi, u3elo1]
                        · linarith only [h3363, h4426, h4897, h4900, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · linarith only [h3363, h4426, h4897, h4899, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h3363, h4426, h4704, h4896, h4897, h4898, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h4703, h4897, hlam]
                · linarith only [h0, h4896, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · linarith only [h3363, h4426, h4705, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4908 | h4908
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4909 | h4909
            · linarith only [h4702, h4704, h4909, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4911 | h4911
              · linarith only [h3363, h4426, h4702, h4704, h4911, hc23, hlam, hphi, u3elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4913 | h4913
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4914 | h4914
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4915 | h4915
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4916 | h4916
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4917 | h4917
                        · linarith only [h3363, h4426, h4909, h4914, h4917, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                        · linarith only [h3363, h4426, h4914, h4917, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · linarith only [h3363, h4426, h4914, h4916, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4921 | h4921
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4922 | h4922
                        · linarith only [h3363, h4426, h4909, h4914, h4922, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                        · linarith only [h3363, h4426, h4914, h4922, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · linarith only [h3363, h4426, h4914, h4921, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                  · linarith only [h0, h4426, h4703, h4704, h4914, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h4426, h4913, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
          · linarith only [h3363, h4426, h4908, hlam]
      · linarith only [h0, h4426, h4703, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h4930 | h4930
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4931 | h4931
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4932 | h4932
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4933 | h4933
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4934 | h4934
              · linarith only [h4426, h4427, h4934, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4936 | h4936
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4937 | h4937
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4938 | h4938
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4939 | h4939
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4940 | h4940
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4941 | h4941
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4942 | h4942
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h4943 | h4943
                              · linarith only [h4426, h4427, h4702, h4931, h4934, h4936, h4937, h4943, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h4945 | h4945
                                · linarith only [h4426, h4427, h4934, h4937, h4941, h4945, hlam]
                                · rcases h0bigk with h4947c | h4947c | h4947c | h4947c | h4947c | h4947c | h4947c | h4947c | h4947c | h4947c | h4947c | h4947c | h4947c | h4947c | h4947c | h4947c | h4947c | h4947c | h4947c | h4947c | h4947c | h4947c | h4947c | h4947c | h4947c
                                  · have p4947_0 := h4947c.1
                                    have p4947_1 := h4947c.2.1
                                    have p4947_2 := h4947c.2.2.1
                                    have p4947_3 := h4947c.2.2.2
                                    linarith only [hlam, p4947_0]
                                  · have p4947_0 := h4947c.1
                                    have p4947_1 := h4947c.2.1
                                    have p4947_2 := h4947c.2.2.1
                                    have p4947_3 := h4947c.2.2.2
                                    linarith only [h0, hlam, p4947_1]
                                  · have p4947_0 := h4947c.1
                                    have p4947_1 := h4947c.2.1
                                    have p4947_2 := h4947c.2.2.1
                                    have p4947_3 := h4947c.2.2.2
                                    linarith only [h3363, hlam, p4947_0]
                                  · have p4947_0 := h4947c.1
                                    have p4947_1 := h4947c.2.1
                                    have p4947_2 := h4947c.2.2.1
                                    have p4947_3 := h4947c.2.2.2
                                    linarith only [h4427, h4702, h4931, h4936, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4947_1, u3elo1]
                                  · have p4947_0 := h4947c.1
                                    have p4947_1 := h4947c.2.1
                                    have p4947_2 := h4947c.2.2.1
                                    have p4947_3 := h4947c.2.2.2
                                    linarith only [h4427, hlam, p4947_1]
                                  · have p4947_0 := h4947c.1
                                    have p4947_1 := h4947c.2.1
                                    have p4947_2 := h4947c.2.2.1
                                    have p4947_3 := h4947c.2.2.2
                                    linarith only [h4702, h4936, hc01, hlam, hphi, ht12, ht23, p4947_1, u3elo1]
                                  · have p4947_0 := h4947c.1
                                    have p4947_1 := h4947c.2.1
                                    have p4947_2 := h4947c.2.2.1
                                    have p4947_3 := h4947c.2.2.2
                                    linarith only [hlam, p4947_0]
                                  · have p4947_0 := h4947c.1
                                    have p4947_1 := h4947c.2.1
                                    have p4947_2 := h4947c.2.2.1
                                    have p4947_3 := h4947c.2.2.2
                                    linarith only [h4702, hlam, p4947_0]
                                  · have p4947_0 := h4947c.1
                                    have p4947_1 := h4947c.2.1
                                    have p4947_2 := h4947c.2.2.1
                                    have p4947_3 := h4947c.2.2.2
                                    linarith only [h4426, h4702, h4936, h4937, h4941, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4947_1, u3elo1]
                                  · have p4947_0 := h4947c.1
                                    have p4947_1 := h4947c.2.1
                                    have p4947_2 := h4947c.2.2.1
                                    have p4947_3 := h4947c.2.2.2
                                    linarith only [h4702, h4936, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4947_1, u3elo1]
                                  · have p4947_0 := h4947c.1
                                    have p4947_1 := h4947c.2.1
                                    have p4947_2 := h4947c.2.2.1
                                    have p4947_3 := h4947c.2.2.2
                                    linarith only [h4426, h4937, h4941, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4947_1, u3elo0]
                                  · have p4947_0 := h4947c.1
                                    have p4947_1 := h4947c.2.1
                                    have p4947_2 := h4947c.2.2.1
                                    have p4947_3 := h4947c.2.2.2
                                    linarith only [h4702, h4936, hc02, hlam, hphi, ht23, p4947_1, u3elo1]
                                  · have p4947_0 := h4947c.1
                                    have p4947_1 := h4947c.2.1
                                    have p4947_2 := h4947c.2.2.1
                                    have p4947_3 := h4947c.2.2.2
                                    linarith only [hlam, p4947_0]
                                  · have p4947_0 := h4947c.1
                                    have p4947_1 := h4947c.2.1
                                    have p4947_2 := h4947c.2.2.1
                                    have p4947_3 := h4947c.2.2.2
                                    rcases p4947_3 (m.d 0 1) (by simp) with h4961 | h4961
                                    · linarith only [h3363, h4961, hlam]
                                    · linarith only [h4426, h4961, hlam]
                                  · have p4947_0 := h4947c.1
                                    have p4947_1 := h4947c.2.1
                                    have p4947_2 := h4947c.2.2.1
                                    have p4947_3 := h4947c.2.2.2
                                    linarith only [h4426, h4427, h4702, h4936, h4937, h4941, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4947_1, u3elo1]
                                  · have p4947_0 := h4947c.1
                                    have p4947_1 := h4947c.2.1
                                    have p4947_2 := h4947c.2.2.1
                                    have p4947_3 := h4947c.2.2.2
                                    linarith only [h4426, hlam, p4947_0]
                                  · have p4947_0 := h4947c.1
                                    have p4947_1 := h4947c.2.1
                                    have p4947_2 := h4947c.2.2.1
                                    have p4947_3 := h4947c.2.2.2
                                    linarith only [h4930, hlam, p4947_0]
                                  · have p4947_0 := h4947c.1
                                    have p4947_1 := h4947c.2.1
                                    have p4947_2 := h4947c.2.2.1
                                    have p4947_3 := h4947c.2.2.2
                                    linarith only [h4932, hlam, p4947_0]
                                  · have p4947_0 := h4947c.1
                                    have p4947_1 := h4947c.2.1
                                    have p4947_2 := h4947c.2.2.1
                                    have p4947_3 := h4947c.2.2.2
                                    linarith only [hlam, p4947_0]
                                  · have p4947_0 := h4947c.1
                                    have p4947_1 := h4947c.2.1
                                    have p4947_2 := h4947c.2.2.1
                                    have p4947_3 := h4947c.2.2.2
                                    linarith only [h4934, hlam, p4947_0]
                                  · have p4947_0 := h4947c.1
                                    have p4947_1 := h4947c.2.1
                                    have p4947_2 := h4947c.2.2.1
                                    have p4947_3 := h4947c.2.2.2
                                    linarith only [h4426, h4934, h4937, h4941, hc34, hc45, hlam, hphi, p4947_1]
                                  · have p4947_0 := h4947c.1
                                    have p4947_1 := h4947c.2.1
                                    have p4947_2 := h4947c.2.2.1
                                    have p4947_3 := h4947c.2.2.2
                                    linarith only [h4931, hlam, p4947_1]
                                  · have p4947_0 := h4947c.1
                                    have p4947_1 := h4947c.2.1
                                    have p4947_2 := h4947c.2.2.1
                                    have p4947_3 := h4947c.2.2.2
                                    linarith only [h4933, hlam, p4947_0]
                                  · have p4947_0 := h4947c.1
                                    have p4947_1 := h4947c.2.1
                                    have p4947_2 := h4947c.2.2.1
                                    have p4947_3 := h4947c.2.2.2
                                    linarith only [h4426, h4702, h4931, h4936, h4937, h4941, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4947_1, u3elo1]
                                  · have p4947_0 := h4947c.1
                                    have p4947_1 := h4947c.2.1
                                    have p4947_2 := h4947c.2.2.1
                                    have p4947_3 := h4947c.2.2.2
                                    linarith only [hlam, p4947_0]
                            · linarith only [h4702, h4942, hc02, hlam, hphi, ht23, u3elo4]
                          · linarith only [h4426, h4427, h4702, h4931, h4937, h4941, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h4702, h4931, h4933, h4940, hc13, hlam, hphi, u3elo2]
                      · linarith only [h4426, h4427, h4702, h4931, h4936, h4937, h4939, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h4426, h4427, h4702, h4931, h4936, h4937, h4938, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h4426, h4427, h4702, h4931, h4936, h4937, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h4426, h4936, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
            · linarith only [h4702, h4931, h4933, hlam]
          · linarith only [h0, h4426, h4702, h4932, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4984 | h4984
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4985 | h4985
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4986 | h4986
              · linarith only [h0, h4426, h4931, h4986, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4988 | h4988
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4989 | h4989
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4990 | h4990
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4991 | h4991
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4992 | h4992
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4993 | h4993
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4994 | h4994
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h4995 | h4995
                              · linarith only [h0, h4426, h4931, h4986, h4989, h4995, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h4997 | h4997
                                · linarith only [h0, h4931, h4995, h4997, hc01, hlam, hphi, ht12, ht23, u3elo3]
                                · rcases h0bigk with h4999c | h4999c | h4999c | h4999c | h4999c | h4999c | h4999c | h4999c | h4999c | h4999c | h4999c | h4999c | h4999c | h4999c | h4999c | h4999c | h4999c | h4999c | h4999c | h4999c | h4999c | h4999c | h4999c | h4999c | h4999c
                                  · have p4999_0 := h4999c.1
                                    have p4999_1 := h4999c.2.1
                                    have p4999_2 := h4999c.2.2.1
                                    have p4999_3 := h4999c.2.2.2
                                    linarith only [hlam, p4999_0]
                                  · have p4999_0 := h4999c.1
                                    have p4999_1 := h4999c.2.1
                                    have p4999_2 := h4999c.2.2.1
                                    have p4999_3 := h4999c.2.2.2
                                    linarith only [h0, hlam, p4999_1]
                                  · have p4999_0 := h4999c.1
                                    have p4999_1 := h4999c.2.1
                                    have p4999_2 := h4999c.2.2.1
                                    have p4999_3 := h4999c.2.2.2
                                    linarith only [h3363, hlam, p4999_0]
                                  · have p4999_0 := h4999c.1
                                    have p4999_1 := h4999c.2.1
                                    have p4999_2 := h4999c.2.2.1
                                    have p4999_3 := h4999c.2.2.2
                                    linarith only [h0, h4931, h4995, hc04, hc45, hlam, hphi, p4999_1]
                                  · have p4999_0 := h4999c.1
                                    have p4999_1 := h4999c.2.1
                                    have p4999_2 := h4999c.2.2.1
                                    have p4999_3 := h4999c.2.2.2
                                    linarith only [h4427, hlam, p4999_1]
                                  · have p4999_0 := h4999c.1
                                    have p4999_1 := h4999c.2.1
                                    have p4999_2 := h4999c.2.2.1
                                    have p4999_3 := h4999c.2.2.2
                                    linarith only [h4931, h4990, h4992, hc01, hc13, hlam, hphi, p4999_1]
                                  · have p4999_0 := h4999c.1
                                    have p4999_1 := h4999c.2.1
                                    have p4999_2 := h4999c.2.2.1
                                    have p4999_3 := h4999c.2.2.2
                                    linarith only [hlam, p4999_0]
                                  · have p4999_0 := h4999c.1
                                    have p4999_1 := h4999c.2.1
                                    have p4999_2 := h4999c.2.2.1
                                    have p4999_3 := h4999c.2.2.2
                                    linarith only [h4702, hlam, p4999_0]
                                  · have p4999_0 := h4999c.1
                                    have p4999_1 := h4999c.2.1
                                    have p4999_2 := h4999c.2.2.1
                                    have p4999_3 := h4999c.2.2.2
                                    linarith only [h4426, h4702, h4988, h4989, h4993, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4999_1, u3elo1]
                                  · have p4999_0 := h4999c.1
                                    have p4999_1 := h4999c.2.1
                                    have p4999_2 := h4999c.2.2.1
                                    have p4999_3 := h4999c.2.2.2
                                    linarith only [h4931, hlam, p4999_0]
                                  · have p4999_0 := h4999c.1
                                    have p4999_1 := h4999c.2.1
                                    have p4999_2 := h4999c.2.2.1
                                    have p4999_3 := h4999c.2.2.2
                                    linarith only [h4426, h4702, h4988, h4989, h4993, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4999_1, u3elo1]
                                  · have p4999_0 := h4999c.1
                                    have p4999_1 := h4999c.2.1
                                    have p4999_2 := h4999c.2.2.1
                                    have p4999_3 := h4999c.2.2.2
                                    linarith only [h4702, h4988, hc02, hlam, hphi, ht23, p4999_1, u3elo1]
                                  · have p4999_0 := h4999c.1
                                    have p4999_1 := h4999c.2.1
                                    have p4999_2 := h4999c.2.2.1
                                    have p4999_3 := h4999c.2.2.2
                                    linarith only [hlam, p4999_0]
                                  · have p4999_0 := h4999c.1
                                    have p4999_1 := h4999c.2.1
                                    have p4999_2 := h4999c.2.2.1
                                    have p4999_3 := h4999c.2.2.2
                                    rcases p4999_3 (m.d 0 1) (by simp) with h5013 | h5013
                                    · linarith only [h3363, h5013, hlam]
                                    · linarith only [h4426, h5013, hlam]
                                  · have p4999_0 := h4999c.1
                                    have p4999_1 := h4999c.2.1
                                    have p4999_2 := h4999c.2.2.1
                                    have p4999_3 := h4999c.2.2.2
                                    linarith only [h4426, h4427, h4702, h4988, h4989, h4993, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4999_1, u3elo1]
                                  · have p4999_0 := h4999c.1
                                    have p4999_1 := h4999c.2.1
                                    have p4999_2 := h4999c.2.2.1
                                    have p4999_3 := h4999c.2.2.2
                                    linarith only [h4426, hlam, p4999_0]
                                  · have p4999_0 := h4999c.1
                                    have p4999_1 := h4999c.2.1
                                    have p4999_2 := h4999c.2.2.1
                                    have p4999_3 := h4999c.2.2.2
                                    linarith only [h4930, hlam, p4999_0]
                                  · have p4999_0 := h4999c.1
                                    have p4999_1 := h4999c.2.1
                                    have p4999_2 := h4999c.2.2.1
                                    have p4999_3 := h4999c.2.2.2
                                    linarith only [h4984, hlam, p4999_0]
                                  · have p4999_0 := h4999c.1
                                    have p4999_1 := h4999c.2.1
                                    have p4999_2 := h4999c.2.2.1
                                    have p4999_3 := h4999c.2.2.2
                                    linarith only [hlam, p4999_0]
                                  · have p4999_0 := h4999c.1
                                    have p4999_1 := h4999c.2.1
                                    have p4999_2 := h4999c.2.2.1
                                    have p4999_3 := h4999c.2.2.2
                                    linarith only [h4986, hlam, p4999_0]
                                  · have p4999_0 := h4999c.1
                                    have p4999_1 := h4999c.2.1
                                    have p4999_2 := h4999c.2.2.1
                                    have p4999_3 := h4999c.2.2.2
                                    linarith only [h4426, h4427, h4989, h4992, h4993, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4999_1, u3elo1]
                                  · have p4999_0 := h4999c.1
                                    have p4999_1 := h4999c.2.1
                                    have p4999_2 := h4999c.2.2.1
                                    have p4999_3 := h4999c.2.2.2
                                    linarith only [h0, h4426, h4931, h4989, h4990, h4992, h4993, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4999_1, u3elo1]
                                  · have p4999_0 := h4999c.1
                                    have p4999_1 := h4999c.2.1
                                    have p4999_2 := h4999c.2.2.1
                                    have p4999_3 := h4999c.2.2.2
                                    linarith only [h4985, hlam, p4999_0]
                                  · have p4999_0 := h4999c.1
                                    have p4999_1 := h4999c.2.1
                                    have p4999_2 := h4999c.2.2.1
                                    have p4999_3 := h4999c.2.2.2
                                    rcases p4999_3 (m.d 0 1) (by simp) with h5025 | h5025
                                    · linarith only [h4427, h5025, hlam]
                                    · linarith only [h4426, h5025, hlam]
                                  · have p4999_0 := h4999c.1
                                    have p4999_1 := h4999c.2.1
                                    have p4999_2 := h4999c.2.2.1
                                    have p4999_3 := h4999c.2.2.2
                                    linarith only [hlam, p4999_0]
                            · linarith only [h4702, h4985, h4994, hlam]
                          · linarith only [h0, h4426, h4702, h4989, h4993, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h3363, h4426, h4989, h4992, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · linarith only [h0, h4426, h4702, h4988, h4989, h4991, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h0, h4426, h4702, h4988, h4989, h4990, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h4702, h4988, h4989, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h4988, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h5036 | h5036
              · linarith only [h4426, h4427, h5036, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5038 | h5038
                · rcases m.htr 1 2 4 (by decide) (by decide) with h5039 | h5039
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h5040 | h5040
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h5041 | h5041
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h5042 | h5042
                        · linarith only [h4702, h4985, h5042, hc02, hlam, hphi, ht23, u3elo1]
                        · linarith only [h3363, h4426, h5039, h5042, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · linarith only [h0, h4426, h4702, h5038, h5039, h5041, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h0, h4426, h4702, h5038, h5039, h5040, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h4426, h4702, h5038, h5039, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h4426, h5038, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
          · linarith only [h0, h4426, h4702, h4984, hlam]
      · linarith only [h0, h4426, h4930, hlam]

set_option maxHeartbeats 5514000 in
set_option maxHeartbeats 5514000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s5_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3363 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4426 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h5051 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h5052 | h5052
  · rcases m.htr 0 2 4 (by decide) (by decide) with h5053 | h5053
    · rcases m.htr 0 2 5 (by decide) (by decide) with h5054 | h5054
      · rcases m.htr 0 3 4 (by decide) (by decide) with h5055 | h5055
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5056 | h5056
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5057 | h5057
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5058 | h5058
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5059 | h5059
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5060 | h5060
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5061 | h5061
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5062 | h5062
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h5063 | h5063
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h5064 | h5064
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h5065 | h5065
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h5066 | h5066
                              · rcases h0bigk with h5067c | h5067c | h5067c | h5067c | h5067c | h5067c | h5067c | h5067c | h5067c | h5067c | h5067c | h5067c | h5067c | h5067c | h5067c | h5067c | h5067c | h5067c | h5067c | h5067c | h5067c | h5067c | h5067c | h5067c | h5067c
                                · have p5067_0 := h5067c.1
                                  have p5067_1 := h5067c.2.1
                                  have p5067_2 := h5067c.2.2.1
                                  have p5067_3 := h5067c.2.2.2
                                  linarith only [hlam, p5067_0]
                                · have p5067_0 := h5067c.1
                                  have p5067_1 := h5067c.2.1
                                  have p5067_2 := h5067c.2.2.1
                                  have p5067_3 := h5067c.2.2.2
                                  linarith only [h0, hlam, p5067_1]
                                · have p5067_0 := h5067c.1
                                  have p5067_1 := h5067c.2.1
                                  have p5067_2 := h5067c.2.2.1
                                  have p5067_3 := h5067c.2.2.2
                                  linarith only [h3363, hlam, p5067_0]
                                · have p5067_0 := h5067c.1
                                  have p5067_1 := h5067c.2.1
                                  have p5067_2 := h5067c.2.2.1
                                  have p5067_3 := h5067c.2.2.2
                                  linarith only [h4426, hlam, p5067_1]
                                · have p5067_0 := h5067c.1
                                  have p5067_1 := h5067c.2.1
                                  have p5067_2 := h5067c.2.2.1
                                  have p5067_3 := h5067c.2.2.2
                                  linarith only [h4426, h5061, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5067_1, u3elo1]
                                · have p5067_0 := h5067c.1
                                  have p5067_1 := h5067c.2.1
                                  have p5067_2 := h5067c.2.2.1
                                  have p5067_3 := h5067c.2.2.2
                                  rcases p5067_3 (m.d 0 1) (by simp) with h5073 | h5073
                                  · linarith only [h0, h5073, hlam]
                                  · rcases p5067_3 (m.d 0 2) (by simp) with h5075 | h5075
                                    · rcases p5067_3 (m.d 0 3) (by simp) with h5076 | h5076
                                      · linarith only [h5052, h5076, hlam]
                                      · linarith only [h3363, h5076, hlam]
                                    · linarith only [h0, h5075, hlam]
                                · have p5067_0 := h5067c.1
                                  have p5067_1 := h5067c.2.1
                                  have p5067_2 := h5067c.2.2.1
                                  have p5067_3 := h5067c.2.2.2
                                  linarith only [hlam, p5067_0]
                                · have p5067_0 := h5067c.1
                                  have p5067_1 := h5067c.2.1
                                  have p5067_2 := h5067c.2.2.1
                                  have p5067_3 := h5067c.2.2.2
                                  linarith only [h5052, h5063, h5066, hc02, hc45, hlam, hphi, ht0b, ht5b, p5067_1]
                                · have p5067_0 := h5067c.1
                                  have p5067_1 := h5067c.2.1
                                  have p5067_2 := h5067c.2.2.1
                                  have p5067_3 := h5067c.2.2.2
                                  rcases p5067_3 (m.d 0 1) (by simp) with h5082 | h5082
                                  · linarith only [h0, h5082, hlam]
                                  · rcases p5067_3 (m.d 0 2) (by simp) with h5084 | h5084
                                    · rcases p5067_3 (m.d 0 3) (by simp) with h5085 | h5085
                                      · linarith only [h5052, h5085, hlam]
                                      · linarith only [h5055, h5085, hlam]
                                    · linarith only [h5053, h5084, hlam]
                                · have p5067_0 := h5067c.1
                                  have p5067_1 := h5067c.2.1
                                  have p5067_2 := h5067c.2.2.1
                                  have p5067_3 := h5067c.2.2.2
                                  rcases p5067_3 (m.d 0 1) (by simp) with h5089 | h5089
                                  · linarith only [h0, h5089, hlam]
                                  · linarith only [h5051, h5089, hlam]
                                · have p5067_0 := h5067c.1
                                  have p5067_1 := h5067c.2.1
                                  have p5067_2 := h5067c.2.2.1
                                  have p5067_3 := h5067c.2.2.2
                                  linarith only [h5051, h5060, h5064, h5066, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5067_1, u3elo0]
                                · have p5067_0 := h5067c.1
                                  have p5067_1 := h5067c.2.1
                                  have p5067_2 := h5067c.2.2.1
                                  have p5067_3 := h5067c.2.2.2
                                  linarith only [h5052, hlam, p5067_1]
                                · have p5067_0 := h5067c.1
                                  have p5067_1 := h5067c.2.1
                                  have p5067_2 := h5067c.2.2.1
                                  have p5067_3 := h5067c.2.2.2
                                  linarith only [hlam, p5067_0]
                                · have p5067_0 := h5067c.1
                                  have p5067_1 := h5067c.2.1
                                  have p5067_2 := h5067c.2.2.1
                                  have p5067_3 := h5067c.2.2.2
                                  linarith only [h3363, h4426, h5051, h5060, h5064, h5066, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5067_1, u3elo1]
                                · have p5067_0 := h5067c.1
                                  have p5067_1 := h5067c.2.1
                                  have p5067_2 := h5067c.2.2.1
                                  have p5067_3 := h5067c.2.2.2
                                  rcases p5067_3 (m.d 0 1) (by simp) with h5096 | h5096
                                  · linarith only [h3363, h5096, hlam]
                                  · linarith only [h5051, h5096, hlam]
                                · have p5067_0 := h5067c.1
                                  have p5067_1 := h5067c.2.1
                                  have p5067_2 := h5067c.2.2.1
                                  have p5067_3 := h5067c.2.2.2
                                  linarith only [h4426, h5051, h5060, h5061, h5064, h5066, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5067_1, u3elo1]
                                · have p5067_0 := h5067c.1
                                  have p5067_1 := h5067c.2.1
                                  have p5067_2 := h5067c.2.2.1
                                  have p5067_3 := h5067c.2.2.2
                                  linarith only [h5053, hlam, p5067_0]
                                · have p5067_0 := h5067c.1
                                  have p5067_1 := h5067c.2.1
                                  have p5067_2 := h5067c.2.2.1
                                  have p5067_3 := h5067c.2.2.2
                                  linarith only [h5055, hlam, p5067_0]
                                · have p5067_0 := h5067c.1
                                  have p5067_1 := h5067c.2.1
                                  have p5067_2 := h5067c.2.2.1
                                  have p5067_3 := h5067c.2.2.2
                                  linarith only [hlam, p5067_0]
                                · have p5067_0 := h5067c.1
                                  have p5067_1 := h5067c.2.1
                                  have p5067_2 := h5067c.2.2.1
                                  have p5067_3 := h5067c.2.2.2
                                  rcases p5067_3 (m.d 0 1) (by simp) with h5103 | h5103
                                  · linarith only [h4426, h5103, hlam]
                                  · linarith only [h5051, h5103, hlam]
                                · have p5067_0 := h5067c.1
                                  have p5067_1 := h5067c.2.1
                                  have p5067_2 := h5067c.2.2.1
                                  have p5067_3 := h5067c.2.2.2
                                  linarith only [h5051, hlam, p5067_0]
                                · have p5067_0 := h5067c.1
                                  have p5067_1 := h5067c.2.1
                                  have p5067_2 := h5067c.2.2.1
                                  have p5067_3 := h5067c.2.2.2
                                  linarith only [h5054, hlam, p5067_1]
                                · have p5067_0 := h5067c.1
                                  have p5067_1 := h5067c.2.1
                                  have p5067_2 := h5067c.2.2.1
                                  have p5067_3 := h5067c.2.2.2
                                  linarith only [h5056, hlam, p5067_0]
                                · have p5067_0 := h5067c.1
                                  have p5067_1 := h5067c.2.1
                                  have p5067_2 := h5067c.2.2.1
                                  have p5067_3 := h5067c.2.2.2
                                  linarith only [h5057, hlam, p5067_1]
                                · have p5067_0 := h5067c.1
                                  have p5067_1 := h5067c.2.1
                                  have p5067_2 := h5067c.2.2.1
                                  have p5067_3 := h5067c.2.2.2
                                  linarith only [hlam, p5067_0]
                              · linarith only [h3363, h5051, h5060, h5065, h5066, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h5112 | h5112
                              · linarith only [h5063, h5065, h5112, hlam]
                              · rcases h0bigk with h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c | h5114c
                                · have p5114_0 := h5114c.1
                                  have p5114_1 := h5114c.2.1
                                  have p5114_2 := h5114c.2.2.1
                                  have p5114_3 := h5114c.2.2.2
                                  linarith only [hlam, p5114_0]
                                · have p5114_0 := h5114c.1
                                  have p5114_1 := h5114c.2.1
                                  have p5114_2 := h5114c.2.2.1
                                  have p5114_3 := h5114c.2.2.2
                                  linarith only [h0, hlam, p5114_1]
                                · have p5114_0 := h5114c.1
                                  have p5114_1 := h5114c.2.1
                                  have p5114_2 := h5114c.2.2.1
                                  have p5114_3 := h5114c.2.2.2
                                  linarith only [h3363, hlam, p5114_0]
                                · have p5114_0 := h5114c.1
                                  have p5114_1 := h5114c.2.1
                                  have p5114_2 := h5114c.2.2.1
                                  have p5114_3 := h5114c.2.2.2
                                  linarith only [h4426, hlam, p5114_1]
                                · have p5114_0 := h5114c.1
                                  have p5114_1 := h5114c.2.1
                                  have p5114_2 := h5114c.2.2.1
                                  have p5114_3 := h5114c.2.2.2
                                  linarith only [h4426, h5057, h5061, h5063, h5065, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p5114_1, u3elo1]
                                · have p5114_0 := h5114c.1
                                  have p5114_1 := h5114c.2.1
                                  have p5114_2 := h5114c.2.2.1
                                  have p5114_3 := h5114c.2.2.2
                                  rcases p5114_3 (m.d 0 1) (by simp) with h5120 | h5120
                                  · linarith only [h0, h5120, hlam]
                                  · rcases p5114_3 (m.d 0 2) (by simp) with h5122 | h5122
                                    · rcases p5114_3 (m.d 0 3) (by simp) with h5123 | h5123
                                      · linarith only [h5052, h5123, hlam]
                                      · linarith only [h3363, h5123, hlam]
                                    · linarith only [h0, h5122, hlam]
                                · have p5114_0 := h5114c.1
                                  have p5114_1 := h5114c.2.1
                                  have p5114_2 := h5114c.2.2.1
                                  have p5114_3 := h5114c.2.2.2
                                  linarith only [hlam, p5114_0]
                                · have p5114_0 := h5114c.1
                                  have p5114_1 := h5114c.2.1
                                  have p5114_2 := h5114c.2.2.1
                                  have p5114_3 := h5114c.2.2.2
                                  linarith only [h0, h5055, h5057, h5063, h5065, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5114_1]
                                · have p5114_0 := h5114c.1
                                  have p5114_1 := h5114c.2.1
                                  have p5114_2 := h5114c.2.2.1
                                  have p5114_3 := h5114c.2.2.2
                                  linarith only [h0, h5057, h5063, h5065, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5114_1]
                                · have p5114_0 := h5114c.1
                                  have p5114_1 := h5114c.2.1
                                  have p5114_2 := h5114c.2.2.1
                                  have p5114_3 := h5114c.2.2.2
                                  rcases p5114_3 (m.d 0 1) (by simp) with h5130 | h5130
                                  · linarith only [h0, h5130, hlam]
                                  · linarith only [h5051, h5130, hlam]
                                · have p5114_0 := h5114c.1
                                  have p5114_1 := h5114c.2.1
                                  have p5114_2 := h5114c.2.2.1
                                  have p5114_3 := h5114c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, p5114_1, u3elo0]
                                · have p5114_0 := h5114c.1
                                  have p5114_1 := h5114c.2.1
                                  have p5114_2 := h5114c.2.2.1
                                  have p5114_3 := h5114c.2.2.2
                                  linarith only [h5052, hlam, p5114_1]
                                · have p5114_0 := h5114c.1
                                  have p5114_1 := h5114c.2.1
                                  have p5114_2 := h5114c.2.2.1
                                  have p5114_3 := h5114c.2.2.2
                                  linarith only [hlam, p5114_0]
                                · have p5114_0 := h5114c.1
                                  have p5114_1 := h5114c.2.1
                                  have p5114_2 := h5114c.2.2.1
                                  have p5114_3 := h5114c.2.2.2
                                  linarith only [h3363, h5057, h5063, h5065, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p5114_1, u3elo1]
                                · have p5114_0 := h5114c.1
                                  have p5114_1 := h5114c.2.1
                                  have p5114_2 := h5114c.2.2.1
                                  have p5114_3 := h5114c.2.2.2
                                  linarith only [h3363, h5057, h5063, h5065, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p5114_1, u3elo1]
                                · have p5114_0 := h5114c.1
                                  have p5114_1 := h5114c.2.1
                                  have p5114_2 := h5114c.2.2.1
                                  have p5114_3 := h5114c.2.2.2
                                  linarith only [h4426, h5051, h5057, h5061, h5063, h5065, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p5114_1, u3elo1]
                                · have p5114_0 := h5114c.1
                                  have p5114_1 := h5114c.2.1
                                  have p5114_2 := h5114c.2.2.1
                                  have p5114_3 := h5114c.2.2.2
                                  linarith only [h5053, hlam, p5114_0]
                                · have p5114_0 := h5114c.1
                                  have p5114_1 := h5114c.2.1
                                  have p5114_2 := h5114c.2.2.1
                                  have p5114_3 := h5114c.2.2.2
                                  linarith only [h5055, hlam, p5114_0]
                                · have p5114_0 := h5114c.1
                                  have p5114_1 := h5114c.2.1
                                  have p5114_2 := h5114c.2.2.1
                                  have p5114_3 := h5114c.2.2.2
                                  linarith only [hlam, p5114_0]
                                · have p5114_0 := h5114c.1
                                  have p5114_1 := h5114c.2.1
                                  have p5114_2 := h5114c.2.2.1
                                  have p5114_3 := h5114c.2.2.2
                                  linarith only [h4426, h5057, h5061, h5063, h5065, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p5114_1, u3elo1]
                                · have p5114_0 := h5114c.1
                                  have p5114_1 := h5114c.2.1
                                  have p5114_2 := h5114c.2.2.1
                                  have p5114_3 := h5114c.2.2.2
                                  linarith only [h5051, hlam, p5114_0]
                                · have p5114_0 := h5114c.1
                                  have p5114_1 := h5114c.2.1
                                  have p5114_2 := h5114c.2.2.1
                                  have p5114_3 := h5114c.2.2.2
                                  linarith only [h5054, hlam, p5114_1]
                                · have p5114_0 := h5114c.1
                                  have p5114_1 := h5114c.2.1
                                  have p5114_2 := h5114c.2.2.1
                                  have p5114_3 := h5114c.2.2.2
                                  linarith only [h5056, hlam, p5114_0]
                                · have p5114_0 := h5114c.1
                                  have p5114_1 := h5114c.2.1
                                  have p5114_2 := h5114c.2.2.1
                                  have p5114_3 := h5114c.2.2.2
                                  linarith only [h5057, hlam, p5114_1]
                                · have p5114_0 := h5114c.1
                                  have p5114_1 := h5114c.2.1
                                  have p5114_2 := h5114c.2.2.1
                                  have p5114_3 := h5114c.2.2.2
                                  linarith only [hlam, p5114_0]
                          · linarith only [h3363, h5051, h5062, h5064, hc23, hlam, hphi, u3elo1]
                        · linarith only [h3363, h5055, h5063, hc23, hlam, hphi, u3elo1]
                      · linarith only [h4426, h5061, h5062, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h3363, h5055, h5061, hlam]
                  · linarith only [h0, h5054, h5060, hlam]
                · linarith only [h0, h5053, h5059, hlam]
              · linarith only [h0, h5058, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h4426, h5051, h5057, hlam]
          · linarith only [h3363, h5051, h5056, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5157 | h5157
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5158 | h5158
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5159 | h5159
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5160 | h5160
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5161 | h5161
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5162 | h5162
                    · linarith only [h3363, h5055, h5162, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h3363, h5051, h5161, h5162, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                  · linarith only [h0, h5054, h5161, hlam]
                · linarith only [h0, h5053, h5160, hlam]
              · linarith only [h0, h5052, h5159, hlam]
            · linarith only [h3363, h5051, h5055, h5158, hlam]
          · linarith only [h3363, h5051, h5157, hlam]
      · linarith only [h3363, h5051, h5052, h5054, hc23, hlam, hphi, u3elo1]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h5171 | h5171
      · rcases m.htr 0 3 4 (by decide) (by decide) with h5172 | h5172
        · linarith only [h5052, h5053, h5172, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5174 | h5174
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5175 | h5175
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5176 | h5176
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5177 | h5177
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5178 | h5178
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5179 | h5179
                    · linarith only [h3363, h5051, h5172, h5178, h5179, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                    · linarith only [h3363, h5051, h5178, h5179, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                  · linarith only [h5052, h5053, h5177, h5178, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5183 | h5183
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5184 | h5184
                    · linarith only [h5172, h5184, hc03, hlam, hphi, u3elo1]
                    · linarith only [h3363, h5051, h5183, h5184, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                  · linarith only [h0, h5051, h5171, h5183, hc02, hc15, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h5051, h5176, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
            · linarith only [h0, h5051, h5053, h5175, hlam]
          · linarith only [h3363, h5051, h5174, hlam]
      · linarith only [h0, h5051, h5171, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h5192 | h5192
    · rcases m.htr 0 2 5 (by decide) (by decide) with h5193 | h5193
      · rcases m.htr 0 3 4 (by decide) (by decide) with h5194 | h5194
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5195 | h5195
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5196 | h5196
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5197 | h5197
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5198 | h5198
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5199 | h5199
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5200 | h5200
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5201 | h5201
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h5202 | h5202
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h5203 | h5203
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h5204 | h5204
                            · linarith only [h5052, h5192, h5197, h5204, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                            · linarith only [h5052, h5192, h5196, h5197, h5202, h5204, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                          · linarith only [h4426, h5052, h5192, h5203, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h4426, h5052, h5192, h5202, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h4426, h5051, h5052, h5192, h5197, h5199, h5201, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                    · linarith only [h4426, h5051, h5052, h5192, h5194, h5197, h5199, h5200, hc03, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h4426, h5052, h5192, h5197, h5199, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h5052, h5192, h5197, h5198, hlam]
              · linarith only [h0, h5051, h5197, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
            · linarith only [h4426, h5051, h5196, hlam]
          · linarith only [h3363, h5051, h5195, hlam]
        · linarith only [h5052, h5192, h5194, hlam]
      · linarith only [h4426, h5051, h5192, h5193, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h5218 | h5218
      · rcases m.htr 0 3 4 (by decide) (by decide) with h5219 | h5219
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5220 | h5220
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5221 | h5221
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5222 | h5222
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5223 | h5223
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5224 | h5224
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5225 | h5225
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5226 | h5226
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h5227 | h5227
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h5228 | h5228
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h5229 | h5229
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h5230 | h5230
                              · rcases h0bigk with h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c
                                · have p5231_0 := h5231c.1
                                  have p5231_1 := h5231c.2.1
                                  have p5231_2 := h5231c.2.2.1
                                  have p5231_3 := h5231c.2.2.2
                                  linarith only [hlam, p5231_0]
                                · have p5231_0 := h5231c.1
                                  have p5231_1 := h5231c.2.1
                                  have p5231_2 := h5231c.2.2.1
                                  have p5231_3 := h5231c.2.2.2
                                  linarith only [h0, hlam, p5231_1]
                                · have p5231_0 := h5231c.1
                                  have p5231_1 := h5231c.2.1
                                  have p5231_2 := h5231c.2.2.1
                                  have p5231_3 := h5231c.2.2.2
                                  linarith only [h3363, hlam, p5231_0]
                                · have p5231_0 := h5231c.1
                                  have p5231_1 := h5231c.2.1
                                  have p5231_2 := h5231c.2.2.1
                                  have p5231_3 := h5231c.2.2.2
                                  linarith only [h4426, hlam, p5231_1]
                                · have p5231_0 := h5231c.1
                                  have p5231_1 := h5231c.2.1
                                  have p5231_2 := h5231c.2.2.1
                                  have p5231_3 := h5231c.2.2.2
                                  linarith only [h3363, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5231_1, u3elo1]
                                · have p5231_0 := h5231c.1
                                  have p5231_1 := h5231c.2.1
                                  have p5231_2 := h5231c.2.2.1
                                  have p5231_3 := h5231c.2.2.2
                                  linarith only [h5192, h5223, hc01, hc14, hlam, hphi, p5231_1]
                                · have p5231_0 := h5231c.1
                                  have p5231_1 := h5231c.2.1
                                  have p5231_2 := h5231c.2.2.1
                                  have p5231_3 := h5231c.2.2.2
                                  linarith only [hlam, p5231_0]
                                · have p5231_0 := h5231c.1
                                  have p5231_1 := h5231c.2.1
                                  have p5231_2 := h5231c.2.2.1
                                  have p5231_3 := h5231c.2.2.2
                                  linarith only [h5052, hlam, p5231_0]
                                · have p5231_0 := h5231c.1
                                  have p5231_1 := h5231c.2.1
                                  have p5231_2 := h5231c.2.2.1
                                  have p5231_3 := h5231c.2.2.2
                                  linarith only [h5192, hlam, p5231_1]
                                · have p5231_0 := h5231c.1
                                  have p5231_1 := h5231c.2.1
                                  have p5231_2 := h5231c.2.2.1
                                  have p5231_3 := h5231c.2.2.2
                                  linarith only [h5051, h5052, h5222, h5224, h5228, h5230, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5231_1, u3elo1]
                                · have p5231_0 := h5231c.1
                                  have p5231_1 := h5231c.2.1
                                  have p5231_2 := h5231c.2.2.1
                                  have p5231_3 := h5231c.2.2.2
                                  linarith only [h5051, h5224, h5228, h5230, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5231_1, u3elo0]
                                · have p5231_0 := h5231c.1
                                  have p5231_1 := h5231c.2.1
                                  have p5231_2 := h5231c.2.2.1
                                  have p5231_3 := h5231c.2.2.2
                                  linarith only [h5052, h5222, hc02, hlam, hphi, ht23, p5231_1, u3elo1]
                                · have p5231_0 := h5231c.1
                                  have p5231_1 := h5231c.2.1
                                  have p5231_2 := h5231c.2.2.1
                                  have p5231_3 := h5231c.2.2.2
                                  linarith only [hlam, p5231_0]
                                · have p5231_0 := h5231c.1
                                  have p5231_1 := h5231c.2.1
                                  have p5231_2 := h5231c.2.2.1
                                  have p5231_3 := h5231c.2.2.2
                                  linarith only [h4426, h5051, h5052, h5222, h5224, h5228, h5230, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5231_1, u3elo1]
                                · have p5231_0 := h5231c.1
                                  have p5231_1 := h5231c.2.1
                                  have p5231_2 := h5231c.2.2.1
                                  have p5231_3 := h5231c.2.2.2
                                  rcases p5231_3 (m.d 0 1) (by simp) with h5246 | h5246
                                  · linarith only [h3363, h5246, hlam]
                                  · linarith only [h5051, h5246, hlam]
                                · have p5231_0 := h5231c.1
                                  have p5231_1 := h5231c.2.1
                                  have p5231_2 := h5231c.2.2.1
                                  have p5231_3 := h5231c.2.2.2
                                  linarith only [h4426, h5051, h5224, h5225, h5228, h5230, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5231_1, u3elo1]
                                · have p5231_0 := h5231c.1
                                  have p5231_1 := h5231c.2.1
                                  have p5231_2 := h5231c.2.2.1
                                  have p5231_3 := h5231c.2.2.2
                                  linarith only [h0, h5051, h5192, h5223, h5224, h5225, h5228, h5230, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5231_1, u3elo1]
                                · have p5231_0 := h5231c.1
                                  have p5231_1 := h5231c.2.1
                                  have p5231_2 := h5231c.2.2.1
                                  have p5231_3 := h5231c.2.2.2
                                  linarith only [h5219, hlam, p5231_0]
                                · have p5231_0 := h5231c.1
                                  have p5231_1 := h5231c.2.1
                                  have p5231_2 := h5231c.2.2.1
                                  have p5231_3 := h5231c.2.2.2
                                  linarith only [hlam, p5231_0]
                                · have p5231_0 := h5231c.1
                                  have p5231_1 := h5231c.2.1
                                  have p5231_2 := h5231c.2.2.1
                                  have p5231_3 := h5231c.2.2.2
                                  rcases p5231_3 (m.d 0 1) (by simp) with h5253 | h5253
                                  · linarith only [h4426, h5253, hlam]
                                  · linarith only [h5051, h5253, hlam]
                                · have p5231_0 := h5231c.1
                                  have p5231_1 := h5231c.2.1
                                  have p5231_2 := h5231c.2.2.1
                                  have p5231_3 := h5231c.2.2.2
                                  linarith only [h5051, hlam, p5231_0]
                                · have p5231_0 := h5231c.1
                                  have p5231_1 := h5231c.2.1
                                  have p5231_2 := h5231c.2.2.1
                                  have p5231_3 := h5231c.2.2.2
                                  linarith only [h5218, hlam, p5231_1]
                                · have p5231_0 := h5231c.1
                                  have p5231_1 := h5231c.2.1
                                  have p5231_2 := h5231c.2.2.1
                                  have p5231_3 := h5231c.2.2.2
                                  linarith only [h5220, hlam, p5231_0]
                                · have p5231_0 := h5231c.1
                                  have p5231_1 := h5231c.2.1
                                  have p5231_2 := h5231c.2.2.1
                                  have p5231_3 := h5231c.2.2.2
                                  linarith only [h5221, hlam, p5231_1]
                                · have p5231_0 := h5231c.1
                                  have p5231_1 := h5231c.2.1
                                  have p5231_2 := h5231c.2.2.1
                                  have p5231_3 := h5231c.2.2.2
                                  linarith only [hlam, p5231_0]
                              · linarith only [h0, h5051, h5192, h5223, h5224, h5225, h5229, h5230, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · linarith only [h5192, h5221, h5229, hlam]
                          · linarith only [h0, h5052, h5228, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h0, h5051, h5052, h5224, h5227, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                      · linarith only [h3363, h5051, h5224, h5226, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                    · linarith only [h5052, h5219, h5222, h5225, hlam]
                  · linarith only [h0, h5051, h5052, h5222, h5224, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · linarith only [h0, h5051, h5052, h5222, h5223, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · linarith only [h0, h5051, h5222, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
            · linarith only [h4426, h5051, h5221, hlam]
          · linarith only [h0, h5051, h5192, h5219, h5220, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5272 | h5272
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5273 | h5273
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5274 | h5274
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5275 | h5275
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5276 | h5276
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5277 | h5277
                    · linarith only [h5219, h5277, hc03, hlam, hphi, u3elo1]
                    · linarith only [h3363, h5051, h5276, h5277, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                  · linarith only [h0, h5051, h5052, h5274, h5276, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · linarith only [h0, h5051, h5052, h5274, h5275, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · linarith only [h0, h5051, h5274, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
            · linarith only [h0, h5051, h5052, h5219, h5273, hlam]
          · linarith only [h0, h5051, h5052, h5272, hlam]
      · linarith only [h0, h5051, h5218, hlam]

end R2N4
