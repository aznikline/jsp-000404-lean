import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6218000 in
set_option maxHeartbeats 6218000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s11_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg5543 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg6343 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h6418 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6419 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h6420 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5543 := hg5543
  have h6343 := hg6343
  rcases m.htr 1 2 3 (by decide) (by decide) with h6421 | h6421
  · linarith only [h0, h4, h6418, h6420, h6421, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h6423 | h6423
    · linarith only [h0, h5543, h6423, hlam]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h6425 | h6425
      · linarith only [h0, h6343, h6425, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h6427 | h6427
        · rcases m.htr 1 3 5 (by decide) (by decide) with h6428 | h6428
          · rcases m.htr 1 4 5 (by decide) (by decide) with h6429 | h6429
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6430 | h6430
              · rcases m.htr 2 3 5 (by decide) (by decide) with h6431 | h6431
                · rcases m.htr 2 4 5 (by decide) (by decide) with h6432 | h6432
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6433 | h6433
                    · linarith only [h1, h6427, h6433, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases h1bigk with h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c | h6435c
                      · have p6435_0 := h6435c.1
                        have p6435_1 := h6435c.2.1
                        have p6435_2 := h6435c.2.2.1
                        have p6435_3 := h6435c.2.2.2
                        linarith only [hlam, p6435_0]
                      · have p6435_0 := h6435c.1
                        have p6435_1 := h6435c.2.1
                        have p6435_2 := h6435c.2.2.1
                        have p6435_3 := h6435c.2.2.2
                        rcases p6435_3 (m.d 0 1) (by simp) with h6437 | h6437
                        · rcases p6435_3 (m.d 1 2) (by simp) with h6438 | h6438
                          · linarith only [h6438, hlam, p6435_0]
                          · rcases p6435_3 (m.d 1 3) (by simp) with h6440 | h6440
                            · linarith only [h1, h6440, hlam]
                            · linarith only [h6421, h6440, hlam]
                        · linarith only [h6437, hlam, p6435_0]
                      · have p6435_0 := h6435c.1
                        have p6435_1 := h6435c.2.1
                        have p6435_2 := h6435c.2.2.1
                        have p6435_3 := h6435c.2.2.2
                        linarith only [h6427, h6429, h6433, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6435_1]
                      · have p6435_0 := h6435c.1
                        have p6435_1 := h6435c.2.1
                        have p6435_2 := h6435c.2.2.1
                        have p6435_3 := h6435c.2.2.2
                        linarith only [h6429, h6433, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6435_1]
                      · have p6435_0 := h6435c.1
                        have p6435_1 := h6435c.2.1
                        have p6435_2 := h6435c.2.2.1
                        have p6435_3 := h6435c.2.2.2
                        rcases p6435_3 (m.d 0 1) (by simp) with h6446 | h6446
                        · rcases p6435_3 (m.d 1 2) (by simp) with h6447 | h6447
                          · linarith only [h0, h6447, hlam]
                          · rcases p6435_3 (m.d 1 3) (by simp) with h6449 | h6449
                            · linarith only [h1, h6449, hlam]
                            · linarith only [h6428, h6449, hlam]
                        · linarith only [h6446, hlam, p6435_0]
                      · have p6435_0 := h6435c.1
                        have p6435_1 := h6435c.2.1
                        have p6435_2 := h6435c.2.2.1
                        have p6435_3 := h6435c.2.2.2
                        linarith only [h0, hlam, p6435_0]
                      · have p6435_0 := h6435c.1
                        have p6435_1 := h6435c.2.1
                        have p6435_2 := h6435c.2.2.1
                        have p6435_3 := h6435c.2.2.2
                        linarith only [hlam, p6435_0]
                      · have p6435_0 := h6435c.1
                        have p6435_1 := h6435c.2.1
                        have p6435_2 := h6435c.2.2.1
                        have p6435_3 := h6435c.2.2.2
                        linarith only [h6421, hlam, p6435_0]
                      · have p6435_0 := h6435c.1
                        have p6435_1 := h6435c.2.1
                        have p6435_2 := h6435c.2.2.1
                        have p6435_3 := h6435c.2.2.2
                        linarith only [h6423, hlam, p6435_0]
                      · have p6435_0 := h6435c.1
                        have p6435_1 := h6435c.2.1
                        have p6435_2 := h6435c.2.2.1
                        have p6435_3 := h6435c.2.2.2
                        linarith only [h6425, hlam, p6435_0]
                      · have p6435_0 := h6435c.1
                        have p6435_1 := h6435c.2.1
                        have p6435_2 := h6435c.2.2.1
                        have p6435_3 := h6435c.2.2.2
                        linarith only [h1, hlam, p6435_0]
                      · have p6435_0 := h6435c.1
                        have p6435_1 := h6435c.2.1
                        have p6435_2 := h6435c.2.2.1
                        have p6435_3 := h6435c.2.2.2
                        rcases p6435_3 (m.d 0 1) (by simp) with h6459 | h6459
                        · rcases p6435_3 (m.d 1 2) (by simp) with h6460 | h6460
                          · linarith only [h6421, h6460, hlam]
                          · rcases p6435_3 (m.d 1 3) (by simp) with h6462 | h6462
                            · rcases p6435_3 (m.d 1 4) (by simp) with h6463 | h6463
                              · linarith only [h6427, h6463, hlam]
                              · linarith only [h6423, h6463, hlam]
                            · linarith only [h6421, h6462, hlam]
                        · linarith only [h0, h6459, hlam]
                      · have p6435_0 := h6435c.1
                        have p6435_1 := h6435c.2.1
                        have p6435_2 := h6435c.2.2.1
                        have p6435_3 := h6435c.2.2.2
                        linarith only [hlam, p6435_0]
                      · have p6435_0 := h6435c.1
                        have p6435_1 := h6435c.2.1
                        have p6435_2 := h6435c.2.2.1
                        have p6435_3 := h6435c.2.2.2
                        linarith only [h1, h6429, h6433, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p6435_1]
                      · have p6435_0 := h6435c.1
                        have p6435_1 := h6435c.2.1
                        have p6435_2 := h6435c.2.2.1
                        have p6435_3 := h6435c.2.2.2
                        linarith only [h1, h6429, h6433, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6435_1]
                      · have p6435_0 := h6435c.1
                        have p6435_1 := h6435c.2.1
                        have p6435_2 := h6435c.2.2.1
                        have p6435_3 := h6435c.2.2.2
                        linarith only [h2, hlam, p6435_0]
                      · have p6435_0 := h6435c.1
                        have p6435_1 := h6435c.2.1
                        have p6435_2 := h6435c.2.2.1
                        have p6435_3 := h6435c.2.2.2
                        rcases p6435_3 (m.d 0 1) (by simp) with h6472 | h6472
                        · rcases p6435_3 (m.d 1 2) (by simp) with h6473 | h6473
                          · linarith only [h6423, h6473, hlam]
                          · rcases p6435_3 (m.d 1 3) (by simp) with h6475 | h6475
                            · rcases p6435_3 (m.d 1 4) (by simp) with h6476 | h6476
                              · rcases p6435_3 (m.d 1 5) (by simp) with h6477 | h6477
                                · linarith only [h6429, h6477, hlam]
                                · linarith only [h6425, h6477, hlam]
                              · linarith only [h6423, h6476, hlam]
                            · linarith only [h6421, h6475, hlam]
                        · linarith only [h0, h6472, hlam]
                      · have p6435_0 := h6435c.1
                        have p6435_1 := h6435c.2.1
                        have p6435_2 := h6435c.2.2.1
                        have p6435_3 := h6435c.2.2.2
                        linarith only [h6427, hlam, p6435_0]
                      · have p6435_0 := h6435c.1
                        have p6435_1 := h6435c.2.1
                        have p6435_2 := h6435c.2.2.1
                        have p6435_3 := h6435c.2.2.2
                        linarith only [hlam, p6435_0]
                      · have p6435_0 := h6435c.1
                        have p6435_1 := h6435c.2.1
                        have p6435_2 := h6435c.2.2.1
                        have p6435_3 := h6435c.2.2.2
                        linarith only [h2, h6429, h6433, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6435_1]
                      · have p6435_0 := h6435c.1
                        have p6435_1 := h6435c.2.1
                        have p6435_2 := h6435c.2.2.1
                        have p6435_3 := h6435c.2.2.2
                        linarith only [h3, hlam, p6435_0]
                      · have p6435_0 := h6435c.1
                        have p6435_1 := h6435c.2.1
                        have p6435_2 := h6435c.2.2.1
                        have p6435_3 := h6435c.2.2.2
                        rcases p6435_3 (m.d 0 1) (by simp) with h6487 | h6487
                        · rcases p6435_3 (m.d 1 2) (by simp) with h6488 | h6488
                          · linarith only [h6425, h6488, hlam]
                          · rcases p6435_3 (m.d 1 3) (by simp) with h6490 | h6490
                            · rcases p6435_3 (m.d 1 4) (by simp) with h6491 | h6491
                              · rcases p6435_3 (m.d 1 5) (by simp) with h6492 | h6492
                                · rcases h1emax with h6493 | h6493 | h6493 | h6493 | h6493
                                  · linarith only [h1, h6427, h6429, h6493, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p6435_1]
                                  · rcases h3bigk with h6495c | h6495c | h6495c | h6495c | h6495c | h6495c | h6495c | h6495c | h6495c | h6495c | h6495c | h6495c | h6495c | h6495c | h6495c | h6495c | h6495c | h6495c | h6495c | h6495c | h6495c | h6495c | h6495c | h6495c | h6495c
                                    · have p6495_0 := h6495c.1
                                      have p6495_1 := h6495c.2.1
                                      have p6495_2 := h6495c.2.2.1
                                      have p6495_3 := h6495c.2.2.2
                                      linarith only [hlam, p6495_0]
                                    · have p6495_0 := h6495c.1
                                      have p6495_1 := h6495c.2.1
                                      have p6495_2 := h6495c.2.2.1
                                      have p6495_3 := h6495c.2.2.2
                                      linarith only [h4, h6427, h6429, hc12, hc23, hlam, hphi, p6435_1, p6495_1]
                                    · have p6495_0 := h6495c.1
                                      have p6495_1 := h6495c.2.1
                                      have p6495_2 := h6495c.2.2.1
                                      have p6495_3 := h6495c.2.2.2
                                      linarith only [h4, hlam, p6495_1]
                                    · have p6495_0 := h6495c.1
                                      have p6495_1 := h6495c.2.1
                                      have p6495_2 := h6495c.2.2.1
                                      have p6495_3 := h6495c.2.2.2
                                      rcases p6495_3 (m.d 0 3) (by simp) with h6499 | h6499
                                      · rcases p6495_3 (m.d 1 3) (by simp) with h6500 | h6500
                                        · linarith only [h1, h6500, hlam]
                                        · linarith only [h6427, h6500, hlam]
                                      · linarith only [h6499, hlam, p6495_0]
                                    · have p6495_0 := h6495c.1
                                      have p6495_1 := h6495c.2.1
                                      have p6495_2 := h6495c.2.2.1
                                      have p6495_3 := h6495c.2.2.2
                                      rcases p6495_3 (m.d 0 3) (by simp) with h6504 | h6504
                                      · rcases p6495_3 (m.d 1 3) (by simp) with h6505 | h6505
                                        · linarith only [h1, h6505, hlam]
                                        · linarith only [h6428, h6505, hlam]
                                      · linarith only [h6504, hlam, p6495_0]
                                    · have p6495_0 := h6495c.1
                                      have p6495_1 := h6495c.2.1
                                      have p6495_2 := h6495c.2.2.1
                                      have p6495_3 := h6495c.2.2.2
                                      linarith only [h1, hlam, p6495_0]
                                    · have p6495_0 := h6495c.1
                                      have p6495_1 := h6495c.2.1
                                      have p6495_2 := h6495c.2.2.1
                                      have p6495_3 := h6495c.2.2.2
                                      linarith only [hlam, p6495_0]
                                    · have p6495_0 := h6495c.1
                                      have p6495_1 := h6495c.2.1
                                      have p6495_2 := h6495c.2.2.1
                                      have p6495_3 := h6495c.2.2.2
                                      linarith only [h6421, hlam, p6495_1]
                                    · have p6495_0 := h6495c.1
                                      have p6495_1 := h6495c.2.1
                                      have p6495_2 := h6495c.2.2.1
                                      have p6495_3 := h6495c.2.2.2
                                      rcases p6495_3 (m.d 0 3) (by simp) with h6512 | h6512
                                      · rcases p6495_3 (m.d 1 3) (by simp) with h6513 | h6513
                                        · rcases p6495_3 (m.d 2 3) (by simp) with h6514 | h6514
                                          · rcases p6495_3 (m.d 3 4) (by simp) with h6515 | h6515
                                            · linarith only [h6515, hlam, p6495_0]
                                            · rcases p6495_3 (m.d 3 5) (by simp) with h6517 | h6517
                                              · linarith only [h6428, h6517, hlam]
                                              · linarith only [h6433, h6517, hlam]
                                          · linarith only [h6430, h6514, hlam]
                                        · linarith only [h6513, hlam, p6495_0]
                                      · linarith only [h6418, h6512, hlam]
                                    · have p6495_0 := h6495c.1
                                      have p6495_1 := h6495c.2.1
                                      have p6495_2 := h6495c.2.2.1
                                      have p6495_3 := h6495c.2.2.2
                                      linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p6495_1, u5ehi3]
                                    · have p6495_0 := h6495c.1
                                      have p6495_1 := h6495c.2.1
                                      have p6495_2 := h6495c.2.2.1
                                      have p6495_3 := h6495c.2.2.2
                                      linarith only [h3, h6418, h6420, hc12, hc23, hlam, hphi, p6435_1, p6495_1]
                                    · have p6495_0 := h6495c.1
                                      have p6495_1 := h6495c.2.1
                                      have p6495_2 := h6495c.2.2.1
                                      have p6495_3 := h6495c.2.2.2
                                      linarith only [h6427, h6429, hc12, hc23, hlam, hphi, p6435_1, p6495_1]
                                    · have p6495_0 := h6495c.1
                                      have p6495_1 := h6495c.2.1
                                      have p6495_2 := h6495c.2.2.1
                                      have p6495_3 := h6495c.2.2.2
                                      linarith only [hlam, p6495_0]
                                    · have p6495_0 := h6495c.1
                                      have p6495_1 := h6495c.2.1
                                      have p6495_2 := h6495c.2.2.1
                                      have p6495_3 := h6495c.2.2.2
                                      rcases p6495_3 (m.d 0 3) (by simp) with h6527 | h6527
                                      · linarith only [h4, h6527, hlam]
                                      · linarith only [h6418, h6527, hlam]
                                    · have p6495_0 := h6495c.1
                                      have p6495_1 := h6495c.2.1
                                      have p6495_2 := h6495c.2.2.1
                                      have p6495_3 := h6495c.2.2.2
                                      rcases p6495_3 (m.d 0 3) (by simp) with h6530 | h6530
                                      · linarith only [h4, h6530, hlam]
                                      · linarith only [h6419, h6530, hlam]
                                    · have p6495_0 := h6495c.1
                                      have p6495_1 := h6495c.2.1
                                      have p6495_2 := h6495c.2.2.1
                                      have p6495_3 := h6495c.2.2.2
                                      linarith only [h6418, hlam, p6495_0]
                                    · have p6495_0 := h6495c.1
                                      have p6495_1 := h6495c.2.1
                                      have p6495_2 := h6495c.2.2.1
                                      have p6495_3 := h6495c.2.2.2
                                      linarith only [h6427, hlam, p6495_0]
                                    · have p6495_0 := h6495c.1
                                      have p6495_1 := h6495c.2.1
                                      have p6495_2 := h6495c.2.2.1
                                      have p6495_3 := h6495c.2.2.2
                                      linarith only [h6430, hlam, p6495_0]
                                    · have p6495_0 := h6495c.1
                                      have p6495_1 := h6495c.2.1
                                      have p6495_2 := h6495c.2.2.1
                                      have p6495_3 := h6495c.2.2.2
                                      linarith only [hlam, p6495_0]
                                    · have p6495_0 := h6495c.1
                                      have p6495_1 := h6495c.2.1
                                      have p6495_2 := h6495c.2.2.1
                                      have p6495_3 := h6495c.2.2.2
                                      linarith only [h6433, hlam, p6495_1]
                                    · have p6495_0 := h6495c.1
                                      have p6495_1 := h6495c.2.1
                                      have p6495_2 := h6495c.2.2.1
                                      have p6495_3 := h6495c.2.2.2
                                      linarith only [h6419, hlam, p6495_0]
                                    · have p6495_0 := h6495c.1
                                      have p6495_1 := h6495c.2.1
                                      have p6495_2 := h6495c.2.2.1
                                      have p6495_3 := h6495c.2.2.2
                                      linarith only [h6428, hlam, p6495_0]
                                    · have p6495_0 := h6495c.1
                                      have p6495_1 := h6495c.2.1
                                      have p6495_2 := h6495c.2.2.1
                                      have p6495_3 := h6495c.2.2.2
                                      linarith only [h6431, hlam, p6495_0]
                                    · have p6495_0 := h6495c.1
                                      have p6495_1 := h6495c.2.1
                                      have p6495_2 := h6495c.2.2.1
                                      have p6495_3 := h6495c.2.2.2
                                      linarith only [h1, h6428, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6495_1]
                                    · have p6495_0 := h6495c.1
                                      have p6495_1 := h6495c.2.1
                                      have p6495_2 := h6495c.2.2.1
                                      have p6495_3 := h6495c.2.2.2
                                      linarith only [hlam, p6495_0]
                                  · linarith only [h6427, h6429, h6433, h6493, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                  · linarith only [h6429, h6493, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p6435_1]
                                  · linarith only [h6493, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p6435_1]
                                · linarith only [h6425, h6492, hlam]
                              · linarith only [h6423, h6491, hlam]
                            · linarith only [h6421, h6490, hlam]
                        · linarith only [h0, h6487, hlam]
                      · have p6435_0 := h6435c.1
                        have p6435_1 := h6435c.2.1
                        have p6435_2 := h6435c.2.2.1
                        have p6435_3 := h6435c.2.2.2
                        linarith only [h6428, hlam, p6435_0]
                      · have p6435_0 := h6435c.1
                        have p6435_1 := h6435c.2.1
                        have p6435_2 := h6435c.2.2.1
                        have p6435_3 := h6435c.2.2.2
                        linarith only [h6429, hlam, p6435_0]
                      · have p6435_0 := h6435c.1
                        have p6435_1 := h6435c.2.1
                        have p6435_2 := h6435c.2.2.1
                        have p6435_3 := h6435c.2.2.2
                        linarith only [hlam, p6435_0]
                  · linarith only [h5543, h6420, h6432, hlam]
                · linarith only [h4, h6419, h6431, hlam]
              · linarith only [h4, h6418, h6430, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6556 | h6556
              · rcases m.htr 2 3 5 (by decide) (by decide) with h6557 | h6557
                · rcases m.htr 2 4 5 (by decide) (by decide) with h6558 | h6558
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6559 | h6559
                    · linarith only [h1, h6427, h6429, h6559, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases h1bigk with h6561c | h6561c | h6561c | h6561c | h6561c | h6561c | h6561c | h6561c | h6561c | h6561c | h6561c | h6561c | h6561c | h6561c | h6561c | h6561c | h6561c | h6561c | h6561c | h6561c | h6561c | h6561c | h6561c | h6561c | h6561c
                      · have p6561_0 := h6561c.1
                        have p6561_1 := h6561c.2.1
                        have p6561_2 := h6561c.2.2.1
                        have p6561_3 := h6561c.2.2.2
                        linarith only [hlam, p6561_0]
                      · have p6561_0 := h6561c.1
                        have p6561_1 := h6561c.2.1
                        have p6561_2 := h6561c.2.2.1
                        have p6561_3 := h6561c.2.2.2
                        rcases p6561_3 (m.d 0 1) (by simp) with h6563 | h6563
                        · rcases p6561_3 (m.d 1 2) (by simp) with h6564 | h6564
                          · linarith only [h6564, hlam, p6561_0]
                          · rcases p6561_3 (m.d 1 3) (by simp) with h6566 | h6566
                            · linarith only [h1, h6566, hlam]
                            · linarith only [h6421, h6566, hlam]
                        · linarith only [h6563, hlam, p6561_0]
                      · have p6561_0 := h6561c.1
                        have p6561_1 := h6561c.2.1
                        have p6561_2 := h6561c.2.2.1
                        have p6561_3 := h6561c.2.2.2
                        linarith only [h6428, hc01, hlam, hphi, ht0b, ht5b, p6561_1, u5ehi3]
                      · have p6561_0 := h6561c.1
                        have p6561_1 := h6561c.2.1
                        have p6561_2 := h6561c.2.2.1
                        have p6561_3 := h6561c.2.2.2
                        rcases p6561_3 (m.d 0 1) (by simp) with h6571 | h6571
                        · rcases p6561_3 (m.d 1 2) (by simp) with h6572 | h6572
                          · linarith only [h0, h6572, hlam]
                          · rcases p6561_3 (m.d 1 3) (by simp) with h6574 | h6574
                            · linarith only [h1, h6574, hlam]
                            · linarith only [h6427, h6574, hlam]
                        · linarith only [h6571, hlam, p6561_0]
                      · have p6561_0 := h6561c.1
                        have p6561_1 := h6561c.2.1
                        have p6561_2 := h6561c.2.2.1
                        have p6561_3 := h6561c.2.2.2
                        rcases p6561_3 (m.d 0 1) (by simp) with h6578 | h6578
                        · rcases p6561_3 (m.d 1 2) (by simp) with h6579 | h6579
                          · linarith only [h0, h6579, hlam]
                          · rcases p6561_3 (m.d 1 3) (by simp) with h6581 | h6581
                            · linarith only [h1, h6581, hlam]
                            · linarith only [h6428, h6581, hlam]
                        · linarith only [h6578, hlam, p6561_0]
                      · have p6561_0 := h6561c.1
                        have p6561_1 := h6561c.2.1
                        have p6561_2 := h6561c.2.2.1
                        have p6561_3 := h6561c.2.2.2
                        linarith only [h0, hlam, p6561_0]
                      · have p6561_0 := h6561c.1
                        have p6561_1 := h6561c.2.1
                        have p6561_2 := h6561c.2.2.1
                        have p6561_3 := h6561c.2.2.2
                        linarith only [hlam, p6561_0]
                      · have p6561_0 := h6561c.1
                        have p6561_1 := h6561c.2.1
                        have p6561_2 := h6561c.2.2.1
                        have p6561_3 := h6561c.2.2.2
                        linarith only [h6421, hlam, p6561_0]
                      · have p6561_0 := h6561c.1
                        have p6561_1 := h6561c.2.1
                        have p6561_2 := h6561c.2.2.1
                        have p6561_3 := h6561c.2.2.2
                        linarith only [h6423, hlam, p6561_0]
                      · have p6561_0 := h6561c.1
                        have p6561_1 := h6561c.2.1
                        have p6561_2 := h6561c.2.2.1
                        have p6561_3 := h6561c.2.2.2
                        linarith only [h6425, hlam, p6561_0]
                      · have p6561_0 := h6561c.1
                        have p6561_1 := h6561c.2.1
                        have p6561_2 := h6561c.2.2.1
                        have p6561_3 := h6561c.2.2.2
                        linarith only [h1, hlam, p6561_0]
                      · have p6561_0 := h6561c.1
                        have p6561_1 := h6561c.2.1
                        have p6561_2 := h6561c.2.2.1
                        have p6561_3 := h6561c.2.2.2
                        rcases p6561_3 (m.d 0 1) (by simp) with h6591 | h6591
                        · rcases p6561_3 (m.d 1 2) (by simp) with h6592 | h6592
                          · linarith only [h6421, h6592, hlam]
                          · rcases p6561_3 (m.d 1 3) (by simp) with h6594 | h6594
                            · rcases p6561_3 (m.d 1 4) (by simp) with h6595 | h6595
                              · linarith only [h6427, h6595, hlam]
                              · linarith only [h6423, h6595, hlam]
                            · linarith only [h6421, h6594, hlam]
                        · linarith only [h0, h6591, hlam]
                      · have p6561_0 := h6561c.1
                        have p6561_1 := h6561c.2.1
                        have p6561_2 := h6561c.2.2.1
                        have p6561_3 := h6561c.2.2.2
                        linarith only [hlam, p6561_0]
                      · have p6561_0 := h6561c.1
                        have p6561_1 := h6561c.2.1
                        have p6561_2 := h6561c.2.2.1
                        have p6561_3 := h6561c.2.2.2
                        rcases p6561_3 (m.d 0 1) (by simp) with h6601 | h6601
                        · rcases p6561_3 (m.d 1 2) (by simp) with h6602 | h6602
                          · linarith only [h6421, h6602, hlam]
                          · rcases p6561_3 (m.d 1 3) (by simp) with h6604 | h6604
                            · rcases p6561_3 (m.d 1 4) (by simp) with h6605 | h6605
                              · linarith only [h6427, h6605, hlam]
                              · rcases p6561_3 (m.d 1 5) (by simp) with h6607 | h6607
                                · linarith only [h6428, h6607, hlam]
                                · linarith only [h6429, h6607, hlam]
                            · linarith only [h6427, h6604, hlam]
                        · linarith only [h2, h6601, hlam]
                      · have p6561_0 := h6561c.1
                        have p6561_1 := h6561c.2.1
                        have p6561_2 := h6561c.2.2.1
                        have p6561_3 := h6561c.2.2.2
                        linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p6561_1, u5ehi1]
                      · have p6561_0 := h6561c.1
                        have p6561_1 := h6561c.2.1
                        have p6561_2 := h6561c.2.2.1
                        have p6561_3 := h6561c.2.2.2
                        linarith only [h2, hlam, p6561_0]
                      · have p6561_0 := h6561c.1
                        have p6561_1 := h6561c.2.1
                        have p6561_2 := h6561c.2.2.1
                        have p6561_3 := h6561c.2.2.2
                        linarith only [h4, h6418, h6420, h6429, hc12, hc23, hlam, hphi, p6561_1]
                      · have p6561_0 := h6561c.1
                        have p6561_1 := h6561c.2.1
                        have p6561_2 := h6561c.2.2.1
                        have p6561_3 := h6561c.2.2.2
                        linarith only [h6427, hlam, p6561_0]
                      · have p6561_0 := h6561c.1
                        have p6561_1 := h6561c.2.1
                        have p6561_2 := h6561c.2.2.1
                        have p6561_3 := h6561c.2.2.2
                        linarith only [hlam, p6561_0]
                      · have p6561_0 := h6561c.1
                        have p6561_1 := h6561c.2.1
                        have p6561_2 := h6561c.2.2.1
                        have p6561_3 := h6561c.2.2.2
                        linarith only [h6429, hlam, p6561_1]
                      · have p6561_0 := h6561c.1
                        have p6561_1 := h6561c.2.1
                        have p6561_2 := h6561c.2.2.1
                        have p6561_3 := h6561c.2.2.2
                        linarith only [h3, hlam, p6561_0]
                      · have p6561_0 := h6561c.1
                        have p6561_1 := h6561c.2.1
                        have p6561_2 := h6561c.2.2.1
                        have p6561_3 := h6561c.2.2.2
                        linarith only [h4, h6418, h6420, h6429, hc12, hc23, hlam, hphi, p6561_1]
                      · have p6561_0 := h6561c.1
                        have p6561_1 := h6561c.2.1
                        have p6561_2 := h6561c.2.2.1
                        have p6561_3 := h6561c.2.2.2
                        linarith only [h6428, hlam, p6561_0]
                      · have p6561_0 := h6561c.1
                        have p6561_1 := h6561c.2.1
                        have p6561_2 := h6561c.2.2.1
                        have p6561_3 := h6561c.2.2.2
                        linarith only [h4, h6418, h6420, h6423, h6429, hc12, hc23, hlam, hphi, p6561_1]
                      · have p6561_0 := h6561c.1
                        have p6561_1 := h6561c.2.1
                        have p6561_2 := h6561c.2.2.1
                        have p6561_3 := h6561c.2.2.2
                        linarith only [hlam, p6561_0]
                  · linarith only [h5543, h6420, h6558, hlam]
                · linarith only [h4, h6419, h6557, hlam]
              · linarith only [h4, h6418, h6420, h6427, h6429, h6556, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h6626 | h6626
            · linarith only [h6419, h6427, h6428, h6626, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6628 | h6628
              · rcases m.htr 2 3 5 (by decide) (by decide) with h6629 | h6629
                · rcases m.htr 2 4 5 (by decide) (by decide) with h6630 | h6630
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6631 | h6631
                    · linarith only [h4, h6419, h6427, h6428, h6626, h6631, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · rcases h1bigk with h6633c | h6633c | h6633c | h6633c | h6633c | h6633c | h6633c | h6633c | h6633c | h6633c | h6633c | h6633c | h6633c | h6633c | h6633c | h6633c | h6633c | h6633c | h6633c | h6633c | h6633c | h6633c | h6633c | h6633c | h6633c
                      · have p6633_0 := h6633c.1
                        have p6633_1 := h6633c.2.1
                        have p6633_2 := h6633c.2.2.1
                        have p6633_3 := h6633c.2.2.2
                        linarith only [hlam, p6633_0]
                      · have p6633_0 := h6633c.1
                        have p6633_1 := h6633c.2.1
                        have p6633_2 := h6633c.2.2.1
                        have p6633_3 := h6633c.2.2.2
                        rcases p6633_3 (m.d 0 1) (by simp) with h6635 | h6635
                        · rcases p6633_3 (m.d 1 2) (by simp) with h6636 | h6636
                          · linarith only [h6636, hlam, p6633_0]
                          · rcases p6633_3 (m.d 1 3) (by simp) with h6638 | h6638
                            · linarith only [h1, h6638, hlam]
                            · linarith only [h6421, h6638, hlam]
                        · linarith only [h6635, hlam, p6633_0]
                      · have p6633_0 := h6633c.1
                        have p6633_1 := h6633c.2.1
                        have p6633_2 := h6633c.2.2.1
                        have p6633_3 := h6633c.2.2.2
                        rcases p6633_3 (m.d 0 1) (by simp) with h6642 | h6642
                        · rcases p6633_3 (m.d 1 2) (by simp) with h6643 | h6643
                          · linarith only [h0, h6643, hlam]
                          · rcases p6633_3 (m.d 1 3) (by simp) with h6645 | h6645
                            · linarith only [h6645, hlam, p6633_0]
                            · rcases p6633_3 (m.d 1 4) (by simp) with h6647 | h6647
                              · linarith only [h2, h6647, hlam]
                              · rcases p6633_3 (m.d 1 5) (by simp) with h6649 | h6649
                                · linarith only [h3, h6649, hlam]
                                · linarith only [h6428, h6649, hlam]
                        · linarith only [h6642, hlam, p6633_0]
                      · have p6633_0 := h6633c.1
                        have p6633_1 := h6633c.2.1
                        have p6633_2 := h6633c.2.2.1
                        have p6633_3 := h6633c.2.2.2
                        rcases p6633_3 (m.d 0 1) (by simp) with h6653 | h6653
                        · rcases p6633_3 (m.d 1 2) (by simp) with h6654 | h6654
                          · linarith only [h0, h6654, hlam]
                          · rcases p6633_3 (m.d 1 3) (by simp) with h6656 | h6656
                            · linarith only [h1, h6656, hlam]
                            · linarith only [h6427, h6656, hlam]
                        · linarith only [h6653, hlam, p6633_0]
                      · have p6633_0 := h6633c.1
                        have p6633_1 := h6633c.2.1
                        have p6633_2 := h6633c.2.2.1
                        have p6633_3 := h6633c.2.2.2
                        rcases p6633_3 (m.d 0 1) (by simp) with h6660 | h6660
                        · rcases p6633_3 (m.d 1 2) (by simp) with h6661 | h6661
                          · linarith only [h0, h6661, hlam]
                          · rcases p6633_3 (m.d 1 3) (by simp) with h6663 | h6663
                            · linarith only [h1, h6663, hlam]
                            · rcases p6633_3 (m.d 1 4) (by simp) with h6665 | h6665
                              · linarith only [h2, h6665, hlam]
                              · rcases p6633_3 (m.d 1 5) (by simp) with h6667 | h6667
                                · linarith only [h6667, hlam, p6633_0]
                                · rcases h1emax with h6669 | h6669 | h6669 | h6669 | h6669
                                  · linarith only [h1, h6427, h6669, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · rcases h3bigk with h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c
                                    · have p6671_0 := h6671c.1
                                      have p6671_1 := h6671c.2.1
                                      have p6671_2 := h6671c.2.2.1
                                      have p6671_3 := h6671c.2.2.2
                                      linarith only [hlam, p6671_0]
                                    · have p6671_0 := h6671c.1
                                      have p6671_1 := h6671c.2.1
                                      have p6671_2 := h6671c.2.2.1
                                      have p6671_3 := h6671c.2.2.2
                                      rcases p6671_3 (m.d 0 3) (by simp) with h6673 | h6673
                                      · rcases p6671_3 (m.d 1 3) (by simp) with h6674 | h6674
                                        · linarith only [h1, h6674, hlam]
                                        · rcases p6671_3 (m.d 2 3) (by simp) with h6676 | h6676
                                          · rcases p6671_3 (m.d 3 4) (by simp) with h6677 | h6677
                                            · linarith only [h6418, h6677, hlam]
                                            · rcases p6671_3 (m.d 3 5) (by simp) with h6679 | h6679
                                              · linarith only [h6419, h6679, hlam]
                                              · linarith only [h6428, h6679, hlam]
                                          · linarith only [h6421, h6676, hlam]
                                      · linarith only [h1, h6673, hlam]
                                    · have p6671_0 := h6671c.1
                                      have p6671_1 := h6671c.2.1
                                      have p6671_2 := h6671c.2.2.1
                                      have p6671_3 := h6671c.2.2.2
                                      linarith only [h4, hlam, p6671_1]
                                    · have p6671_0 := h6671c.1
                                      have p6671_1 := h6671c.2.1
                                      have p6671_2 := h6671c.2.2.1
                                      have p6671_3 := h6671c.2.2.2
                                      linarith only [h6419, h6427, h6428, hlam, p6671_2]
                                    · have p6671_0 := h6671c.1
                                      have p6671_1 := h6671c.2.1
                                      have p6671_2 := h6671c.2.2.1
                                      have p6671_3 := h6671c.2.2.2
                                      linarith only [h6427, h6428, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p6671_1]
                                    · have p6671_0 := h6671c.1
                                      have p6671_1 := h6671c.2.1
                                      have p6671_2 := h6671c.2.2.1
                                      have p6671_3 := h6671c.2.2.2
                                      linarith only [h1, hlam, p6671_0]
                                    · have p6671_0 := h6671c.1
                                      have p6671_1 := h6671c.2.1
                                      have p6671_2 := h6671c.2.2.1
                                      have p6671_3 := h6671c.2.2.2
                                      linarith only [hlam, p6671_0]
                                    · have p6671_0 := h6671c.1
                                      have p6671_1 := h6671c.2.1
                                      have p6671_2 := h6671c.2.2.1
                                      have p6671_3 := h6671c.2.2.2
                                      linarith only [h6421, hlam, p6671_1]
                                    · have p6671_0 := h6671c.1
                                      have p6671_1 := h6671c.2.1
                                      have p6671_2 := h6671c.2.2.1
                                      have p6671_3 := h6671c.2.2.2
                                      linarith only [h6428, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6633_1, p6671_1]
                                    · have p6671_0 := h6671c.1
                                      have p6671_1 := h6671c.2.1
                                      have p6671_2 := h6671c.2.2.1
                                      have p6671_3 := h6671c.2.2.2
                                      linarith only [h6428, hlam, p6671_0]
                                    · have p6671_0 := h6671c.1
                                      have p6671_1 := h6671c.2.1
                                      have p6671_2 := h6671c.2.2.1
                                      have p6671_3 := h6671c.2.2.2
                                      linarith only [h6419, h6428, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p6671_1]
                                    · have p6671_0 := h6671c.1
                                      have p6671_1 := h6671c.2.1
                                      have p6671_2 := h6671c.2.2.1
                                      have p6671_3 := h6671c.2.2.2
                                      rcases p6671_3 (m.d 0 3) (by simp) with h6693 | h6693
                                      · linarith only [h4, h6693, hlam]
                                      · linarith only [h1, h6693, hlam]
                                    · have p6671_0 := h6671c.1
                                      have p6671_1 := h6671c.2.1
                                      have p6671_2 := h6671c.2.2.1
                                      have p6671_3 := h6671c.2.2.2
                                      linarith only [hlam, p6671_0]
                                    · have p6671_0 := h6671c.1
                                      have p6671_1 := h6671c.2.1
                                      have p6671_2 := h6671c.2.2.1
                                      have p6671_3 := h6671c.2.2.2
                                      linarith only [h4, h6418, h6420, h6427, h6428, h6631, hlam, p6671_2]
                                    · have p6671_0 := h6671c.1
                                      have p6671_1 := h6671c.2.1
                                      have p6671_2 := h6671c.2.2.1
                                      have p6671_3 := h6671c.2.2.2
                                      linarith only [h6427, h6428, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6671_1]
                                    · have p6671_0 := h6671c.1
                                      have p6671_1 := h6671c.2.1
                                      have p6671_2 := h6671c.2.2.1
                                      have p6671_3 := h6671c.2.2.2
                                      linarith only [h6418, hlam, p6671_0]
                                    · have p6671_0 := h6671c.1
                                      have p6671_1 := h6671c.2.1
                                      have p6671_2 := h6671c.2.2.1
                                      have p6671_3 := h6671c.2.2.2
                                      linarith only [h6427, hlam, p6671_0]
                                    · have p6671_0 := h6671c.1
                                      have p6671_1 := h6671c.2.1
                                      have p6671_2 := h6671c.2.2.1
                                      have p6671_3 := h6671c.2.2.2
                                      linarith only [h6628, hlam, p6671_0]
                                    · have p6671_0 := h6671c.1
                                      have p6671_1 := h6671c.2.1
                                      have p6671_2 := h6671c.2.2.1
                                      have p6671_3 := h6671c.2.2.2
                                      linarith only [hlam, p6671_0]
                                    · have p6671_0 := h6671c.1
                                      have p6671_1 := h6671c.2.1
                                      have p6671_2 := h6671c.2.2.1
                                      have p6671_3 := h6671c.2.2.2
                                      linarith only [h6631, hlam, p6671_1]
                                    · have p6671_0 := h6671c.1
                                      have p6671_1 := h6671c.2.1
                                      have p6671_2 := h6671c.2.2.1
                                      have p6671_3 := h6671c.2.2.2
                                      linarith only [h6419, hlam, p6671_0]
                                    · have p6671_0 := h6671c.1
                                      have p6671_1 := h6671c.2.1
                                      have p6671_2 := h6671c.2.2.1
                                      have p6671_3 := h6671c.2.2.2
                                      linarith only [h6418, h6420, h6427, h6631, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p6671_1]
                                    · have p6671_0 := h6671c.1
                                      have p6671_1 := h6671c.2.1
                                      have p6671_2 := h6671c.2.2.1
                                      have p6671_3 := h6671c.2.2.2
                                      linarith only [h6629, hlam, p6671_0]
                                    · have p6671_0 := h6671c.1
                                      have p6671_1 := h6671c.2.1
                                      have p6671_2 := h6671c.2.2.1
                                      have p6671_3 := h6671c.2.2.2
                                      rcases p6671_3 (m.d 0 3) (by simp) with h6707 | h6707
                                      · rcases p6671_3 (m.d 1 3) (by simp) with h6708 | h6708
                                        · linarith only [h6428, h6708, hlam]
                                        · linarith only [h6427, h6708, hlam]
                                      · linarith only [h6418, h6707, hlam]
                                    · have p6671_0 := h6671c.1
                                      have p6671_1 := h6671c.2.1
                                      have p6671_2 := h6671c.2.2.1
                                      have p6671_3 := h6671c.2.2.2
                                      linarith only [hlam, p6671_0]
                                  · rcases h3bigk with h6713c | h6713c | h6713c | h6713c | h6713c | h6713c | h6713c | h6713c | h6713c | h6713c | h6713c | h6713c | h6713c | h6713c | h6713c | h6713c | h6713c | h6713c | h6713c | h6713c | h6713c | h6713c | h6713c | h6713c | h6713c
                                    · have p6713_0 := h6713c.1
                                      have p6713_1 := h6713c.2.1
                                      have p6713_2 := h6713c.2.2.1
                                      have p6713_3 := h6713c.2.2.2
                                      linarith only [hlam, p6713_0]
                                    · have p6713_0 := h6713c.1
                                      have p6713_1 := h6713c.2.1
                                      have p6713_2 := h6713c.2.2.1
                                      have p6713_3 := h6713c.2.2.2
                                      rcases p6713_3 (m.d 0 3) (by simp) with h6715 | h6715
                                      · rcases p6713_3 (m.d 1 3) (by simp) with h6716 | h6716
                                        · linarith only [h1, h6716, hlam]
                                        · rcases p6713_3 (m.d 2 3) (by simp) with h6718 | h6718
                                          · rcases p6713_3 (m.d 3 4) (by simp) with h6719 | h6719
                                            · linarith only [h6418, h6719, hlam]
                                            · rcases p6713_3 (m.d 3 5) (by simp) with h6721 | h6721
                                              · linarith only [h6419, h6721, hlam]
                                              · linarith only [h6428, h6721, hlam]
                                          · linarith only [h6421, h6718, hlam]
                                      · linarith only [h1, h6715, hlam]
                                    · have p6713_0 := h6713c.1
                                      have p6713_1 := h6713c.2.1
                                      have p6713_2 := h6713c.2.2.1
                                      have p6713_3 := h6713c.2.2.2
                                      linarith only [h4, hlam, p6713_1]
                                    · have p6713_0 := h6713c.1
                                      have p6713_1 := h6713c.2.1
                                      have p6713_2 := h6713c.2.2.1
                                      have p6713_3 := h6713c.2.2.2
                                      linarith only [h6418, h6420, h6427, h6428, h6631, hlam, p6713_2]
                                    · have p6713_0 := h6713c.1
                                      have p6713_1 := h6713c.2.1
                                      have p6713_2 := h6713c.2.2.1
                                      have p6713_3 := h6713c.2.2.2
                                      linarith only [h4, h6427, h6428, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6713_1]
                                    · have p6713_0 := h6713c.1
                                      have p6713_1 := h6713c.2.1
                                      have p6713_2 := h6713c.2.2.1
                                      have p6713_3 := h6713c.2.2.2
                                      linarith only [h1, hlam, p6713_0]
                                    · have p6713_0 := h6713c.1
                                      have p6713_1 := h6713c.2.1
                                      have p6713_2 := h6713c.2.2.1
                                      have p6713_3 := h6713c.2.2.2
                                      linarith only [hlam, p6713_0]
                                    · have p6713_0 := h6713c.1
                                      have p6713_1 := h6713c.2.1
                                      have p6713_2 := h6713c.2.2.1
                                      have p6713_3 := h6713c.2.2.2
                                      linarith only [h6421, hlam, p6713_1]
                                    · have p6713_0 := h6713c.1
                                      have p6713_1 := h6713c.2.1
                                      have p6713_2 := h6713c.2.2.1
                                      have p6713_3 := h6713c.2.2.2
                                      linarith only [h4, h6419, h6428, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6713_1]
                                    · have p6713_0 := h6713c.1
                                      have p6713_1 := h6713c.2.1
                                      have p6713_2 := h6713c.2.2.1
                                      have p6713_3 := h6713c.2.2.2
                                      linarith only [h6428, hlam, p6713_0]
                                    · have p6713_0 := h6713c.1
                                      have p6713_1 := h6713c.2.1
                                      have p6713_2 := h6713c.2.2.1
                                      have p6713_3 := h6713c.2.2.2
                                      linarith only [h6418, h6420, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p6713_1, u5ehi4]
                                    · have p6713_0 := h6713c.1
                                      have p6713_1 := h6713c.2.1
                                      have p6713_2 := h6713c.2.2.1
                                      have p6713_3 := h6713c.2.2.2
                                      rcases p6713_3 (m.d 0 3) (by simp) with h6735 | h6735
                                      · linarith only [h4, h6735, hlam]
                                      · linarith only [h1, h6735, hlam]
                                    · have p6713_0 := h6713c.1
                                      have p6713_1 := h6713c.2.1
                                      have p6713_2 := h6713c.2.2.1
                                      have p6713_3 := h6713c.2.2.2
                                      linarith only [hlam, p6713_0]
                                    · have p6713_0 := h6713c.1
                                      have p6713_1 := h6713c.2.1
                                      have p6713_2 := h6713c.2.2.1
                                      have p6713_3 := h6713c.2.2.2
                                      linarith only [h5543, h6420, h6427, h6428, h6628, h6631, hlam, p6713_2]
                                    · have p6713_0 := h6713c.1
                                      have p6713_1 := h6713c.2.1
                                      have p6713_2 := h6713c.2.2.1
                                      have p6713_3 := h6713c.2.2.2
                                      linarith only [h6427, h6428, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6713_1]
                                    · have p6713_0 := h6713c.1
                                      have p6713_1 := h6713c.2.1
                                      have p6713_2 := h6713c.2.2.1
                                      have p6713_3 := h6713c.2.2.2
                                      linarith only [h6418, hlam, p6713_0]
                                    · have p6713_0 := h6713c.1
                                      have p6713_1 := h6713c.2.1
                                      have p6713_2 := h6713c.2.2.1
                                      have p6713_3 := h6713c.2.2.2
                                      linarith only [h6427, hlam, p6713_0]
                                    · have p6713_0 := h6713c.1
                                      have p6713_1 := h6713c.2.1
                                      have p6713_2 := h6713c.2.2.1
                                      have p6713_3 := h6713c.2.2.2
                                      linarith only [h6628, hlam, p6713_0]
                                    · have p6713_0 := h6713c.1
                                      have p6713_1 := h6713c.2.1
                                      have p6713_2 := h6713c.2.2.1
                                      have p6713_3 := h6713c.2.2.2
                                      linarith only [hlam, p6713_0]
                                    · have p6713_0 := h6713c.1
                                      have p6713_1 := h6713c.2.1
                                      have p6713_2 := h6713c.2.2.1
                                      have p6713_3 := h6713c.2.2.2
                                      linarith only [h6631, hlam, p6713_1]
                                    · have p6713_0 := h6713c.1
                                      have p6713_1 := h6713c.2.1
                                      have p6713_2 := h6713c.2.2.1
                                      have p6713_3 := h6713c.2.2.2
                                      linarith only [h6419, hlam, p6713_0]
                                    · have p6713_0 := h6713c.1
                                      have p6713_1 := h6713c.2.1
                                      have p6713_2 := h6713c.2.2.1
                                      have p6713_3 := h6713c.2.2.2
                                      linarith only [h4, h6419, h6427, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6713_1]
                                    · have p6713_0 := h6713c.1
                                      have p6713_1 := h6713c.2.1
                                      have p6713_2 := h6713c.2.2.1
                                      have p6713_3 := h6713c.2.2.2
                                      linarith only [h6629, hlam, p6713_0]
                                    · have p6713_0 := h6713c.1
                                      have p6713_1 := h6713c.2.1
                                      have p6713_2 := h6713c.2.2.1
                                      have p6713_3 := h6713c.2.2.2
                                      rcases p6713_3 (m.d 0 3) (by simp) with h6749 | h6749
                                      · rcases p6713_3 (m.d 1 3) (by simp) with h6750 | h6750
                                        · linarith only [h6428, h6750, hlam]
                                        · linarith only [h6427, h6750, hlam]
                                      · linarith only [h6418, h6749, hlam]
                                    · have p6713_0 := h6713c.1
                                      have p6713_1 := h6713c.2.1
                                      have p6713_2 := h6713c.2.2.1
                                      have p6713_3 := h6713c.2.2.2
                                      linarith only [hlam, p6713_0]
                                  · rcases h3bigk with h6755c | h6755c | h6755c | h6755c | h6755c | h6755c | h6755c | h6755c | h6755c | h6755c | h6755c | h6755c | h6755c | h6755c | h6755c | h6755c | h6755c | h6755c | h6755c | h6755c | h6755c | h6755c | h6755c | h6755c | h6755c
                                    · have p6755_0 := h6755c.1
                                      have p6755_1 := h6755c.2.1
                                      have p6755_2 := h6755c.2.2.1
                                      have p6755_3 := h6755c.2.2.2
                                      linarith only [hlam, p6755_0]
                                    · have p6755_0 := h6755c.1
                                      have p6755_1 := h6755c.2.1
                                      have p6755_2 := h6755c.2.2.1
                                      have p6755_3 := h6755c.2.2.2
                                      rcases p6755_3 (m.d 0 3) (by simp) with h6757 | h6757
                                      · rcases p6755_3 (m.d 1 3) (by simp) with h6758 | h6758
                                        · linarith only [h1, h6758, hlam]
                                        · rcases p6755_3 (m.d 2 3) (by simp) with h6760 | h6760
                                          · rcases p6755_3 (m.d 3 4) (by simp) with h6761 | h6761
                                            · linarith only [h6418, h6761, hlam]
                                            · rcases p6755_3 (m.d 3 5) (by simp) with h6763 | h6763
                                              · linarith only [h6419, h6763, hlam]
                                              · linarith only [h6428, h6763, hlam]
                                          · linarith only [h6421, h6760, hlam]
                                      · linarith only [h1, h6757, hlam]
                                    · have p6755_0 := h6755c.1
                                      have p6755_1 := h6755c.2.1
                                      have p6755_2 := h6755c.2.2.1
                                      have p6755_3 := h6755c.2.2.2
                                      linarith only [h4, hlam, p6755_1]
                                    · have p6755_0 := h6755c.1
                                      have p6755_1 := h6755c.2.1
                                      have p6755_2 := h6755c.2.2.1
                                      have p6755_3 := h6755c.2.2.2
                                      linarith only [h6418, h6420, h6427, h6428, h6631, hlam, p6755_2]
                                    · have p6755_0 := h6755c.1
                                      have p6755_1 := h6755c.2.1
                                      have p6755_2 := h6755c.2.2.1
                                      have p6755_3 := h6755c.2.2.2
                                      linarith only [h6427, h6428, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p6755_1]
                                    · have p6755_0 := h6755c.1
                                      have p6755_1 := h6755c.2.1
                                      have p6755_2 := h6755c.2.2.1
                                      have p6755_3 := h6755c.2.2.2
                                      linarith only [h1, hlam, p6755_0]
                                    · have p6755_0 := h6755c.1
                                      have p6755_1 := h6755c.2.1
                                      have p6755_2 := h6755c.2.2.1
                                      have p6755_3 := h6755c.2.2.2
                                      linarith only [hlam, p6755_0]
                                    · have p6755_0 := h6755c.1
                                      have p6755_1 := h6755c.2.1
                                      have p6755_2 := h6755c.2.2.1
                                      have p6755_3 := h6755c.2.2.2
                                      linarith only [h6421, hlam, p6755_1]
                                    · have p6755_0 := h6755c.1
                                      have p6755_1 := h6755c.2.1
                                      have p6755_2 := h6755c.2.2.1
                                      have p6755_3 := h6755c.2.2.2
                                      linarith only [h4, h6419, h6428, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6755_1]
                                    · have p6755_0 := h6755c.1
                                      have p6755_1 := h6755c.2.1
                                      have p6755_2 := h6755c.2.2.1
                                      have p6755_3 := h6755c.2.2.2
                                      linarith only [h6428, hlam, p6755_0]
                                    · have p6755_0 := h6755c.1
                                      have p6755_1 := h6755c.2.1
                                      have p6755_2 := h6755c.2.2.1
                                      have p6755_3 := h6755c.2.2.2
                                      linarith only [h6418, h6420, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p6755_1, u5ehi4]
                                    · have p6755_0 := h6755c.1
                                      have p6755_1 := h6755c.2.1
                                      have p6755_2 := h6755c.2.2.1
                                      have p6755_3 := h6755c.2.2.2
                                      rcases p6755_3 (m.d 0 3) (by simp) with h6777 | h6777
                                      · linarith only [h4, h6777, hlam]
                                      · linarith only [h1, h6777, hlam]
                                    · have p6755_0 := h6755c.1
                                      have p6755_1 := h6755c.2.1
                                      have p6755_2 := h6755c.2.2.1
                                      have p6755_3 := h6755c.2.2.2
                                      linarith only [hlam, p6755_0]
                                    · have p6755_0 := h6755c.1
                                      have p6755_1 := h6755c.2.1
                                      have p6755_2 := h6755c.2.2.1
                                      have p6755_3 := h6755c.2.2.2
                                      linarith only [h5543, h6420, h6427, h6428, h6628, h6631, hlam, p6755_2]
                                    · have p6755_0 := h6755c.1
                                      have p6755_1 := h6755c.2.1
                                      have p6755_2 := h6755c.2.2.1
                                      have p6755_3 := h6755c.2.2.2
                                      linarith only [h6427, h6428, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6755_1]
                                    · have p6755_0 := h6755c.1
                                      have p6755_1 := h6755c.2.1
                                      have p6755_2 := h6755c.2.2.1
                                      have p6755_3 := h6755c.2.2.2
                                      linarith only [h6418, hlam, p6755_0]
                                    · have p6755_0 := h6755c.1
                                      have p6755_1 := h6755c.2.1
                                      have p6755_2 := h6755c.2.2.1
                                      have p6755_3 := h6755c.2.2.2
                                      linarith only [h6427, hlam, p6755_0]
                                    · have p6755_0 := h6755c.1
                                      have p6755_1 := h6755c.2.1
                                      have p6755_2 := h6755c.2.2.1
                                      have p6755_3 := h6755c.2.2.2
                                      linarith only [h6628, hlam, p6755_0]
                                    · have p6755_0 := h6755c.1
                                      have p6755_1 := h6755c.2.1
                                      have p6755_2 := h6755c.2.2.1
                                      have p6755_3 := h6755c.2.2.2
                                      linarith only [hlam, p6755_0]
                                    · have p6755_0 := h6755c.1
                                      have p6755_1 := h6755c.2.1
                                      have p6755_2 := h6755c.2.2.1
                                      have p6755_3 := h6755c.2.2.2
                                      linarith only [h6631, hlam, p6755_1]
                                    · have p6755_0 := h6755c.1
                                      have p6755_1 := h6755c.2.1
                                      have p6755_2 := h6755c.2.2.1
                                      have p6755_3 := h6755c.2.2.2
                                      linarith only [h6419, hlam, p6755_0]
                                    · have p6755_0 := h6755c.1
                                      have p6755_1 := h6755c.2.1
                                      have p6755_2 := h6755c.2.2.1
                                      have p6755_3 := h6755c.2.2.2
                                      linarith only [h6418, h6420, h6427, h6631, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p6755_1]
                                    · have p6755_0 := h6755c.1
                                      have p6755_1 := h6755c.2.1
                                      have p6755_2 := h6755c.2.2.1
                                      have p6755_3 := h6755c.2.2.2
                                      linarith only [h6629, hlam, p6755_0]
                                    · have p6755_0 := h6755c.1
                                      have p6755_1 := h6755c.2.1
                                      have p6755_2 := h6755c.2.2.1
                                      have p6755_3 := h6755c.2.2.2
                                      rcases p6755_3 (m.d 0 3) (by simp) with h6791 | h6791
                                      · rcases p6755_3 (m.d 1 3) (by simp) with h6792 | h6792
                                        · linarith only [h6428, h6792, hlam]
                                        · linarith only [h6427, h6792, hlam]
                                      · linarith only [h6418, h6791, hlam]
                                    · have p6755_0 := h6755c.1
                                      have p6755_1 := h6755c.2.1
                                      have p6755_2 := h6755c.2.2.1
                                      have p6755_3 := h6755c.2.2.2
                                      linarith only [hlam, p6755_0]
                                  · rcases h3bigk with h6797c | h6797c | h6797c | h6797c | h6797c | h6797c | h6797c | h6797c | h6797c | h6797c | h6797c | h6797c | h6797c | h6797c | h6797c | h6797c | h6797c | h6797c | h6797c | h6797c | h6797c | h6797c | h6797c | h6797c | h6797c
                                    · have p6797_0 := h6797c.1
                                      have p6797_1 := h6797c.2.1
                                      have p6797_2 := h6797c.2.2.1
                                      have p6797_3 := h6797c.2.2.2
                                      linarith only [hlam, p6797_0]
                                    · have p6797_0 := h6797c.1
                                      have p6797_1 := h6797c.2.1
                                      have p6797_2 := h6797c.2.2.1
                                      have p6797_3 := h6797c.2.2.2
                                      rcases p6797_3 (m.d 0 3) (by simp) with h6799 | h6799
                                      · rcases p6797_3 (m.d 1 3) (by simp) with h6800 | h6800
                                        · linarith only [h1, h6800, hlam]
                                        · rcases p6797_3 (m.d 2 3) (by simp) with h6802 | h6802
                                          · rcases p6797_3 (m.d 3 4) (by simp) with h6803 | h6803
                                            · linarith only [h6418, h6803, hlam]
                                            · rcases p6797_3 (m.d 3 5) (by simp) with h6805 | h6805
                                              · linarith only [h6419, h6805, hlam]
                                              · linarith only [h6428, h6805, hlam]
                                          · linarith only [h6421, h6802, hlam]
                                      · linarith only [h1, h6799, hlam]
                                    · have p6797_0 := h6797c.1
                                      have p6797_1 := h6797c.2.1
                                      have p6797_2 := h6797c.2.2.1
                                      have p6797_3 := h6797c.2.2.2
                                      linarith only [h4, hlam, p6797_1]
                                    · have p6797_0 := h6797c.1
                                      have p6797_1 := h6797c.2.1
                                      have p6797_2 := h6797c.2.2.1
                                      have p6797_3 := h6797c.2.2.2
                                      linarith only [h6418, h6420, h6427, h6428, h6631, hlam, p6797_2]
                                    · have p6797_0 := h6797c.1
                                      have p6797_1 := h6797c.2.1
                                      have p6797_2 := h6797c.2.2.1
                                      have p6797_3 := h6797c.2.2.2
                                      linarith only [h4, h6427, h6428, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6797_1]
                                    · have p6797_0 := h6797c.1
                                      have p6797_1 := h6797c.2.1
                                      have p6797_2 := h6797c.2.2.1
                                      have p6797_3 := h6797c.2.2.2
                                      linarith only [h1, hlam, p6797_0]
                                    · have p6797_0 := h6797c.1
                                      have p6797_1 := h6797c.2.1
                                      have p6797_2 := h6797c.2.2.1
                                      have p6797_3 := h6797c.2.2.2
                                      linarith only [hlam, p6797_0]
                                    · have p6797_0 := h6797c.1
                                      have p6797_1 := h6797c.2.1
                                      have p6797_2 := h6797c.2.2.1
                                      have p6797_3 := h6797c.2.2.2
                                      linarith only [h6421, hlam, p6797_1]
                                    · have p6797_0 := h6797c.1
                                      have p6797_1 := h6797c.2.1
                                      have p6797_2 := h6797c.2.2.1
                                      have p6797_3 := h6797c.2.2.2
                                      linarith only [h4, h6419, h6428, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6797_1]
                                    · have p6797_0 := h6797c.1
                                      have p6797_1 := h6797c.2.1
                                      have p6797_2 := h6797c.2.2.1
                                      have p6797_3 := h6797c.2.2.2
                                      linarith only [h6428, hlam, p6797_0]
                                    · have p6797_0 := h6797c.1
                                      have p6797_1 := h6797c.2.1
                                      have p6797_2 := h6797c.2.2.1
                                      have p6797_3 := h6797c.2.2.2
                                      linarith only [h6418, h6420, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p6797_1, u5ehi4]
                                    · have p6797_0 := h6797c.1
                                      have p6797_1 := h6797c.2.1
                                      have p6797_2 := h6797c.2.2.1
                                      have p6797_3 := h6797c.2.2.2
                                      rcases p6797_3 (m.d 0 3) (by simp) with h6819 | h6819
                                      · linarith only [h4, h6819, hlam]
                                      · linarith only [h1, h6819, hlam]
                                    · have p6797_0 := h6797c.1
                                      have p6797_1 := h6797c.2.1
                                      have p6797_2 := h6797c.2.2.1
                                      have p6797_3 := h6797c.2.2.2
                                      linarith only [hlam, p6797_0]
                                    · have p6797_0 := h6797c.1
                                      have p6797_1 := h6797c.2.1
                                      have p6797_2 := h6797c.2.2.1
                                      have p6797_3 := h6797c.2.2.2
                                      linarith only [h5543, h6420, h6427, h6428, h6628, h6631, hlam, p6797_2]
                                    · have p6797_0 := h6797c.1
                                      have p6797_1 := h6797c.2.1
                                      have p6797_2 := h6797c.2.2.1
                                      have p6797_3 := h6797c.2.2.2
                                      linarith only [h6427, h6428, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6797_1]
                                    · have p6797_0 := h6797c.1
                                      have p6797_1 := h6797c.2.1
                                      have p6797_2 := h6797c.2.2.1
                                      have p6797_3 := h6797c.2.2.2
                                      linarith only [h6418, hlam, p6797_0]
                                    · have p6797_0 := h6797c.1
                                      have p6797_1 := h6797c.2.1
                                      have p6797_2 := h6797c.2.2.1
                                      have p6797_3 := h6797c.2.2.2
                                      linarith only [h6427, hlam, p6797_0]
                                    · have p6797_0 := h6797c.1
                                      have p6797_1 := h6797c.2.1
                                      have p6797_2 := h6797c.2.2.1
                                      have p6797_3 := h6797c.2.2.2
                                      linarith only [h6628, hlam, p6797_0]
                                    · have p6797_0 := h6797c.1
                                      have p6797_1 := h6797c.2.1
                                      have p6797_2 := h6797c.2.2.1
                                      have p6797_3 := h6797c.2.2.2
                                      linarith only [hlam, p6797_0]
                                    · have p6797_0 := h6797c.1
                                      have p6797_1 := h6797c.2.1
                                      have p6797_2 := h6797c.2.2.1
                                      have p6797_3 := h6797c.2.2.2
                                      linarith only [h6631, hlam, p6797_1]
                                    · have p6797_0 := h6797c.1
                                      have p6797_1 := h6797c.2.1
                                      have p6797_2 := h6797c.2.2.1
                                      have p6797_3 := h6797c.2.2.2
                                      linarith only [h6419, hlam, p6797_0]
                                    · have p6797_0 := h6797c.1
                                      have p6797_1 := h6797c.2.1
                                      have p6797_2 := h6797c.2.2.1
                                      have p6797_3 := h6797c.2.2.2
                                      linarith only [h4, h6419, h6427, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6797_1]
                                    · have p6797_0 := h6797c.1
                                      have p6797_1 := h6797c.2.1
                                      have p6797_2 := h6797c.2.2.1
                                      have p6797_3 := h6797c.2.2.2
                                      linarith only [h6629, hlam, p6797_0]
                                    · have p6797_0 := h6797c.1
                                      have p6797_1 := h6797c.2.1
                                      have p6797_2 := h6797c.2.2.1
                                      have p6797_3 := h6797c.2.2.2
                                      rcases p6797_3 (m.d 0 3) (by simp) with h6833 | h6833
                                      · rcases p6797_3 (m.d 1 3) (by simp) with h6834 | h6834
                                        · linarith only [h6428, h6834, hlam]
                                        · linarith only [h6427, h6834, hlam]
                                      · linarith only [h6418, h6833, hlam]
                                    · have p6797_0 := h6797c.1
                                      have p6797_1 := h6797c.2.1
                                      have p6797_2 := h6797c.2.2.1
                                      have p6797_3 := h6797c.2.2.2
                                      linarith only [hlam, p6797_0]
                        · linarith only [h6660, hlam, p6633_0]
                      · have p6633_0 := h6633c.1
                        have p6633_1 := h6633c.2.1
                        have p6633_2 := h6633c.2.2.1
                        have p6633_3 := h6633c.2.2.2
                        linarith only [h0, hlam, p6633_0]
                      · have p6633_0 := h6633c.1
                        have p6633_1 := h6633c.2.1
                        have p6633_2 := h6633c.2.2.1
                        have p6633_3 := h6633c.2.2.2
                        linarith only [hlam, p6633_0]
                      · have p6633_0 := h6633c.1
                        have p6633_1 := h6633c.2.1
                        have p6633_2 := h6633c.2.2.1
                        have p6633_3 := h6633c.2.2.2
                        linarith only [h6421, hlam, p6633_0]
                      · have p6633_0 := h6633c.1
                        have p6633_1 := h6633c.2.1
                        have p6633_2 := h6633c.2.2.1
                        have p6633_3 := h6633c.2.2.2
                        linarith only [h6423, hlam, p6633_0]
                      · have p6633_0 := h6633c.1
                        have p6633_1 := h6633c.2.1
                        have p6633_2 := h6633c.2.2.1
                        have p6633_3 := h6633c.2.2.2
                        linarith only [h6425, hlam, p6633_0]
                      · have p6633_0 := h6633c.1
                        have p6633_1 := h6633c.2.1
                        have p6633_2 := h6633c.2.2.1
                        have p6633_3 := h6633c.2.2.2
                        linarith only [h1, hlam, p6633_0]
                      · have p6633_0 := h6633c.1
                        have p6633_1 := h6633c.2.1
                        have p6633_2 := h6633c.2.2.1
                        have p6633_3 := h6633c.2.2.2
                        linarith only [h5543, h6420, h6428, h6628, h6631, hc12, hc23, hlam, hphi, p6633_1]
                      · have p6633_0 := h6633c.1
                        have p6633_1 := h6633c.2.1
                        have p6633_2 := h6633c.2.2.1
                        have p6633_3 := h6633c.2.2.2
                        linarith only [hlam, p6633_0]
                      · have p6633_0 := h6633c.1
                        have p6633_1 := h6633c.2.1
                        have p6633_2 := h6633c.2.2.1
                        have p6633_3 := h6633c.2.2.2
                        linarith only [h5543, h6420, h6423, h6428, h6628, h6631, hc12, hc23, hlam, hphi, p6633_1]
                      · have p6633_0 := h6633c.1
                        have p6633_1 := h6633c.2.1
                        have p6633_2 := h6633c.2.2.1
                        have p6633_3 := h6633c.2.2.2
                        linarith only [h6428, hlam, p6633_1]
                      · have p6633_0 := h6633c.1
                        have p6633_1 := h6633c.2.1
                        have p6633_2 := h6633c.2.2.1
                        have p6633_3 := h6633c.2.2.2
                        linarith only [h2, hlam, p6633_0]
                      · have p6633_0 := h6633c.1
                        have p6633_1 := h6633c.2.1
                        have p6633_2 := h6633c.2.2.1
                        have p6633_3 := h6633c.2.2.2
                        linarith only [h5543, h6420, h6427, h6428, h6628, h6631, hc12, hc23, hlam, hphi, p6633_1]
                      · have p6633_0 := h6633c.1
                        have p6633_1 := h6633c.2.1
                        have p6633_2 := h6633c.2.2.1
                        have p6633_3 := h6633c.2.2.2
                        linarith only [h6427, hlam, p6633_0]
                      · have p6633_0 := h6633c.1
                        have p6633_1 := h6633c.2.1
                        have p6633_2 := h6633c.2.2.1
                        have p6633_3 := h6633c.2.2.2
                        linarith only [hlam, p6633_0]
                      · have p6633_0 := h6633c.1
                        have p6633_1 := h6633c.2.1
                        have p6633_2 := h6633c.2.2.1
                        have p6633_3 := h6633c.2.2.2
                        linarith only [h6626, hlam, p6633_1]
                      · have p6633_0 := h6633c.1
                        have p6633_1 := h6633c.2.1
                        have p6633_2 := h6633c.2.2.1
                        have p6633_3 := h6633c.2.2.2
                        linarith only [h3, hlam, p6633_0]
                      · have p6633_0 := h6633c.1
                        have p6633_1 := h6633c.2.1
                        have p6633_2 := h6633c.2.2.1
                        have p6633_3 := h6633c.2.2.2
                        linarith only [h5543, h6420, h6428, h6628, h6631, hc12, hc23, hlam, hphi, p6633_1]
                      · have p6633_0 := h6633c.1
                        have p6633_1 := h6633c.2.1
                        have p6633_2 := h6633c.2.2.1
                        have p6633_3 := h6633c.2.2.2
                        linarith only [h5543, h6420, h6421, h6428, h6628, h6631, hc12, hc23, hlam, hphi, p6633_1]
                      · have p6633_0 := h6633c.1
                        have p6633_1 := h6633c.2.1
                        have p6633_2 := h6633c.2.2.1
                        have p6633_3 := h6633c.2.2.2
                        linarith only [h5543, h6420, h6423, h6428, h6628, h6631, hc12, hc23, hlam, hphi, p6633_1]
                      · have p6633_0 := h6633c.1
                        have p6633_1 := h6633c.2.1
                        have p6633_2 := h6633c.2.2.1
                        have p6633_3 := h6633c.2.2.2
                        linarith only [hlam, p6633_0]
                  · linarith only [h5543, h6420, h6630, hlam]
                · linarith only [h4, h6419, h6629, hlam]
              · linarith only [h4, h6427, h6428, h6628, hc03, hc35, hlam, hphi]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h6863 | h6863
          · linarith only [h6418, h6427, h6863, hc03, hlam, hphi, ht0b, ht5b, u5ehi3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h6865 | h6865
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6866 | h6866
              · rcases m.htr 2 3 5 (by decide) (by decide) with h6867 | h6867
                · rcases m.htr 2 4 5 (by decide) (by decide) with h6868 | h6868
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6869 | h6869
                    · rcases h1bigk with h6870c | h6870c | h6870c | h6870c | h6870c | h6870c | h6870c | h6870c | h6870c | h6870c | h6870c | h6870c | h6870c | h6870c | h6870c | h6870c | h6870c | h6870c | h6870c | h6870c | h6870c | h6870c | h6870c | h6870c | h6870c
                      · have p6870_0 := h6870c.1
                        have p6870_1 := h6870c.2.1
                        have p6870_2 := h6870c.2.2.1
                        have p6870_3 := h6870c.2.2.2
                        linarith only [hlam, p6870_0]
                      · have p6870_0 := h6870c.1
                        have p6870_1 := h6870c.2.1
                        have p6870_2 := h6870c.2.2.1
                        have p6870_3 := h6870c.2.2.2
                        rcases p6870_3 (m.d 0 1) (by simp) with h6872 | h6872
                        · rcases p6870_3 (m.d 1 2) (by simp) with h6873 | h6873
                          · linarith only [h6873, hlam, p6870_0]
                          · rcases p6870_3 (m.d 1 3) (by simp) with h6875 | h6875
                            · linarith only [h1, h6875, hlam]
                            · linarith only [h6421, h6875, hlam]
                        · linarith only [h6872, hlam, p6870_0]
                      · have p6870_0 := h6870c.1
                        have p6870_1 := h6870c.2.1
                        have p6870_2 := h6870c.2.2.1
                        have p6870_3 := h6870c.2.2.2
                        rcases p6870_3 (m.d 0 1) (by simp) with h6879 | h6879
                        · rcases p6870_3 (m.d 1 2) (by simp) with h6880 | h6880
                          · linarith only [h0, h6880, hlam]
                          · rcases p6870_3 (m.d 1 3) (by simp) with h6882 | h6882
                            · linarith only [h6882, hlam, p6870_0]
                            · rcases p6870_3 (m.d 1 4) (by simp) with h6884 | h6884
                              · linarith only [h2, h6884, hlam]
                              · linarith only [h6427, h6884, hlam]
                        · linarith only [h6879, hlam, p6870_0]
                      · have p6870_0 := h6870c.1
                        have p6870_1 := h6870c.2.1
                        have p6870_2 := h6870c.2.2.1
                        have p6870_3 := h6870c.2.2.2
                        linarith only [h6865, hc01, hlam, hphi, ht0b, ht5b, p6870_1, u5ehi4]
                      · have p6870_0 := h6870c.1
                        have p6870_1 := h6870c.2.1
                        have p6870_2 := h6870c.2.2.1
                        have p6870_3 := h6870c.2.2.2
                        rcases p6870_3 (m.d 0 1) (by simp) with h6889 | h6889
                        · rcases p6870_3 (m.d 1 2) (by simp) with h6890 | h6890
                          · linarith only [h0, h6890, hlam]
                          · rcases p6870_3 (m.d 1 3) (by simp) with h6892 | h6892
                            · linarith only [h1, h6892, hlam]
                            · rcases p6870_3 (m.d 1 4) (by simp) with h6894 | h6894
                              · linarith only [h2, h6894, hlam]
                              · linarith only [h6865, h6894, hlam]
                        · linarith only [h6889, hlam, p6870_0]
                      · have p6870_0 := h6870c.1
                        have p6870_1 := h6870c.2.1
                        have p6870_2 := h6870c.2.2.1
                        have p6870_3 := h6870c.2.2.2
                        linarith only [h0, hlam, p6870_0]
                      · have p6870_0 := h6870c.1
                        have p6870_1 := h6870c.2.1
                        have p6870_2 := h6870c.2.2.1
                        have p6870_3 := h6870c.2.2.2
                        linarith only [hlam, p6870_0]
                      · have p6870_0 := h6870c.1
                        have p6870_1 := h6870c.2.1
                        have p6870_2 := h6870c.2.2.1
                        have p6870_3 := h6870c.2.2.2
                        linarith only [h6421, hlam, p6870_0]
                      · have p6870_0 := h6870c.1
                        have p6870_1 := h6870c.2.1
                        have p6870_2 := h6870c.2.2.1
                        have p6870_3 := h6870c.2.2.2
                        linarith only [h6423, hlam, p6870_0]
                      · have p6870_0 := h6870c.1
                        have p6870_1 := h6870c.2.1
                        have p6870_2 := h6870c.2.2.1
                        have p6870_3 := h6870c.2.2.2
                        linarith only [h6425, hlam, p6870_0]
                      · have p6870_0 := h6870c.1
                        have p6870_1 := h6870c.2.1
                        have p6870_2 := h6870c.2.2.1
                        have p6870_3 := h6870c.2.2.2
                        linarith only [h1, hlam, p6870_0]
                      · have p6870_0 := h6870c.1
                        have p6870_1 := h6870c.2.1
                        have p6870_2 := h6870c.2.2.1
                        have p6870_3 := h6870c.2.2.2
                        linarith only [h5543, h6419, h6420, h6863, hc12, hc24, hlam, hphi, p6870_1]
                      · have p6870_0 := h6870c.1
                        have p6870_1 := h6870c.2.1
                        have p6870_2 := h6870c.2.2.1
                        have p6870_3 := h6870c.2.2.2
                        linarith only [hlam, p6870_0]
                      · have p6870_0 := h6870c.1
                        have p6870_1 := h6870c.2.1
                        have p6870_2 := h6870c.2.2.1
                        have p6870_3 := h6870c.2.2.2
                        linarith only [h6427, hlam, p6870_1]
                      · have p6870_0 := h6870c.1
                        have p6870_1 := h6870c.2.1
                        have p6870_2 := h6870c.2.2.1
                        have p6870_3 := h6870c.2.2.2
                        linarith only [h6863, hlam, p6870_1]
                      · have p6870_0 := h6870c.1
                        have p6870_1 := h6870c.2.1
                        have p6870_2 := h6870c.2.2.1
                        have p6870_3 := h6870c.2.2.2
                        linarith only [h2, hlam, p6870_0]
                      · have p6870_0 := h6870c.1
                        have p6870_1 := h6870c.2.1
                        have p6870_2 := h6870c.2.2.1
                        have p6870_3 := h6870c.2.2.2
                        linarith only [h4, h6418, h6427, hc12, hc23, hlam, hphi, p6870_1]
                      · have p6870_0 := h6870c.1
                        have p6870_1 := h6870c.2.1
                        have p6870_2 := h6870c.2.2.1
                        have p6870_3 := h6870c.2.2.2
                        linarith only [h4, h6418, h6421, h6427, hc12, hc23, hlam, hphi, p6870_1]
                      · have p6870_0 := h6870c.1
                        have p6870_1 := h6870c.2.1
                        have p6870_2 := h6870c.2.2.1
                        have p6870_3 := h6870c.2.2.2
                        linarith only [hlam, p6870_0]
                      · have p6870_0 := h6870c.1
                        have p6870_1 := h6870c.2.1
                        have p6870_2 := h6870c.2.2.1
                        have p6870_3 := h6870c.2.2.2
                        linarith only [h4, h6418, h6427, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p6870_1, u5ehi1]
                      · have p6870_0 := h6870c.1
                        have p6870_1 := h6870c.2.1
                        have p6870_2 := h6870c.2.2.1
                        have p6870_3 := h6870c.2.2.2
                        linarith only [h3, hlam, p6870_0]
                      · have p6870_0 := h6870c.1
                        have p6870_1 := h6870c.2.1
                        have p6870_2 := h6870c.2.2.1
                        have p6870_3 := h6870c.2.2.2
                        linarith only [h4, h6419, h6863, hc12, hc23, hlam, hphi, p6870_1]
                      · have p6870_0 := h6870c.1
                        have p6870_1 := h6870c.2.1
                        have p6870_2 := h6870c.2.2.1
                        have p6870_3 := h6870c.2.2.2
                        linarith only [h4, h6419, h6421, h6863, hc12, hc23, hlam, hphi, p6870_1]
                      · have p6870_0 := h6870c.1
                        have p6870_1 := h6870c.2.1
                        have p6870_2 := h6870c.2.2.1
                        have p6870_3 := h6870c.2.2.2
                        linarith only [h6865, hlam, p6870_0]
                      · have p6870_0 := h6870c.1
                        have p6870_1 := h6870c.2.1
                        have p6870_2 := h6870c.2.2.1
                        have p6870_3 := h6870c.2.2.2
                        linarith only [hlam, p6870_0]
                    · linarith only [h6427, h6865, h6869, hlam]
                  · linarith only [h0, h4, h5543, h6418, h6427, h6865, h6868, hc12, hc23, hlam, hphi]
                · linarith only [h4, h6419, h6867, hlam]
              · linarith only [h4, h6418, h6866, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6922 | h6922
              · rcases m.htr 2 3 5 (by decide) (by decide) with h6923 | h6923
                · rcases m.htr 2 4 5 (by decide) (by decide) with h6924 | h6924
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6925 | h6925
                    · linarith only [h4, h6418, h6423, h6865, h6925, hc12, hc23, hlam, hphi]
                    · linarith only [h4, h6418, h6420, h6421, h6427, h6925, hc12, hc23, hlam, hphi]
                  · linarith only [h5543, h6420, h6924, hlam]
                · linarith only [h4, h6419, h6923, hlam]
              · linarith only [h4, h6418, h6922, hlam]

set_option maxHeartbeats 6218000 in
set_option maxHeartbeats 6218000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s11_x0_x0_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg5543 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg6343 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h6418 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6419 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h6420 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h6931 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5543 := hg5543
  have h6343 := hg6343
  linarith only [h0, h4, h6419, h6931, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]

set_option maxHeartbeats 6218000 in
set_option maxHeartbeats 6218000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s11_x0_x0_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg5543 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg6343 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h6418 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6419 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h6420 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h6931 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h6933 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5543 := hg5543
  have h6343 := hg6343
  linarith only [h0, h5543, h6933, hlam]

set_option maxHeartbeats 6218000 in
set_option maxHeartbeats 6218000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s11_x0_x0_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg5543 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg6343 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h6418 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6419 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h6420 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h6931 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h6933 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h6935 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5543 := hg5543
  have h6343 := hg6343
  linarith only [h0, h6343, h6935, hlam]

end R2N4
