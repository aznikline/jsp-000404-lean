import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_22S17

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7952000 in
set_option maxHeartbeats 7952000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s1 m hb0 hb2 hb3 hb5 h0 h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h3491 | h3491
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3492 | h3492
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3493 | h3493
        · linarith only [h0, h1, h3493, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h3495 | h3495
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3496 | h3496
            · rcases m.htr 0 3 4 (by decide) (by decide) with h3497 | h3497
              · rcases m.htr 0 3 5 (by decide) (by decide) with h3498 | h3498
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3499 | h3499
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3500 | h3500
                    · linarith only [h3493, h3495, h3499, h3500, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3502 | h3502
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h3503 | h3503
                        · linarith only [h0, h1, h3503, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                        · linarith only [h0, h1, h3496, h3500, h3503, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h3495, h3500, h3502, hc12, hc23, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3507 | h3507
                    · linarith only [h0, h3493, h3496, h3499, h3507, hc01, hlam, hphi, u0ehi3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3509 | h3509
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h3510 | h3510
                        · linarith only [h0, h1, h3507, h3510, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                        · linarith only [h0, h1, h3496, h3507, h3510, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h3495, h3507, h3509, hc12, hc23, hlam, hphi]
                · linarith only [h1, h3492, h3498, hlam]
              · linarith only [h1, h3491, h3497, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h3516 | h3516
              · rcases m.htr 0 3 5 (by decide) (by decide) with h3517 | h3517
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3518 | h3518
                  · linarith only [h3495, h3496, h3518, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3520 | h3520
                    · linarith only [h0, h3493, h3495, h3520, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3522 | h3522
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h3523 | h3523
                        · linarith only [h0, h1, h3495, h3496, h3520, h3523, hc23, hlam, hphi, ht01, ht12, u0ehi3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h3525 | h3525
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h3526 | h3526
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h3527 | h3527
                              · linarith only [h3518, h3527, hc14, hlam, hphi, ht01, u0ehi3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h3529 | h3529
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h3530 | h3530
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3531 | h3531
                                    · linarith only [h3518, h3531, hc24, hlam, hphi, ht01, ht12, u0ehi3]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3533 | h3533
                                      · linarith only [h3495, h3496, h3531, h3533, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                                      · rcases h2bigk with h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c | h3535c
                                        · have p3535_0 := h3535c.1
                                          have p3535_1 := h3535c.2.1
                                          have p3535_2 := h3535c.2.2.1
                                          have p3535_3 := h3535c.2.2.2
                                          linarith only [hlam, p3535_0]
                                        · have p3535_0 := h3535c.1
                                          have p3535_1 := h3535c.2.1
                                          have p3535_2 := h3535c.2.2.1
                                          have p3535_3 := h3535c.2.2.2
                                          linarith only [h3496, h3531, hc12, hc45, hlam, hphi, ht23, ht34, p3535_1]
                                        · have p3535_0 := h3535c.1
                                          have p3535_1 := h3535c.2.1
                                          have p3535_2 := h3535c.2.2.1
                                          have p3535_3 := h3535c.2.2.2
                                          linarith only [h3493, hlam, p3535_0]
                                        · have p3535_0 := h3535c.1
                                          have p3535_1 := h3535c.2.1
                                          have p3535_2 := h3535c.2.2.1
                                          have p3535_3 := h3535c.2.2.2
                                          linarith only [h3496, h3529, h3531, hc34, hc45, hlam, hphi, p3535_1]
                                        · have p3535_0 := h3535c.1
                                          have p3535_1 := h3535c.2.1
                                          have p3535_2 := h3535c.2.2.1
                                          have p3535_3 := h3535c.2.2.2
                                          linarith only [h3496, hlam, p3535_0]
                                        · have p3535_0 := h3535c.1
                                          have p3535_1 := h3535c.2.1
                                          have p3535_2 := h3535c.2.2.1
                                          have p3535_3 := h3535c.2.2.2
                                          linarith only [h0, hlam, p3535_0]
                                        · have p3535_0 := h3535c.1
                                          have p3535_1 := h3535c.2.1
                                          have p3535_2 := h3535c.2.2.1
                                          have p3535_3 := h3535c.2.2.2
                                          linarith only [hlam, p3535_0]
                                        · have p3535_0 := h3535c.1
                                          have p3535_1 := h3535c.2.1
                                          have p3535_2 := h3535c.2.2.1
                                          have p3535_3 := h3535c.2.2.2
                                          linarith only [h3520, hlam, p3535_0]
                                        · have p3535_0 := h3535c.1
                                          have p3535_1 := h3535c.2.1
                                          have p3535_2 := h3535c.2.2.1
                                          have p3535_3 := h3535c.2.2.2
                                          linarith only [h0, h1, h3520, h3529, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3535_1]
                                        · have p3535_0 := h3535c.1
                                          have p3535_1 := h3535c.2.1
                                          have p3535_2 := h3535c.2.2.1
                                          have p3535_3 := h3535c.2.2.2
                                          linarith only [h3523, hlam, p3535_0]
                                        · have p3535_0 := h3535c.1
                                          have p3535_1 := h3535c.2.1
                                          have p3535_2 := h3535c.2.2.1
                                          have p3535_3 := h3535c.2.2.2
                                          linarith only [h3495, hc23, hlam, hphi, ht01, ht12, p3535_1, u0ehi3]
                                        · have p3535_0 := h3535c.1
                                          have p3535_1 := h3535c.2.1
                                          have p3535_2 := h3535c.2.2.1
                                          have p3535_3 := h3535c.2.2.2
                                          rcases p3535_3 (m.d 0 2) (by simp) with h3547 | h3547
                                          · linarith only [h3493, h3547, hlam]
                                          · linarith only [h0, h3547, hlam]
                                        · have p3535_0 := h3535c.1
                                          have p3535_1 := h3535c.2.1
                                          have p3535_2 := h3535c.2.2.1
                                          have p3535_3 := h3535c.2.2.2
                                          linarith only [hlam, p3535_0]
                                        · have p3535_0 := h3535c.1
                                          have p3535_1 := h3535c.2.1
                                          have p3535_2 := h3535c.2.2.1
                                          have p3535_3 := h3535c.2.2.2
                                          linarith only [h1, h3492, h3520, h3522, h3523, hlam, p3535_2]
                                        · have p3535_0 := h3535c.1
                                          have p3535_1 := h3535c.2.1
                                          have p3535_2 := h3535c.2.2.1
                                          have p3535_3 := h3535c.2.2.2
                                          linarith only [h3495, h3496, hc23, hlam, hphi, ht01, ht12, p3535_1, u0ehi3]
                                        · have p3535_0 := h3535c.1
                                          have p3535_1 := h3535c.2.1
                                          have p3535_2 := h3535c.2.2.1
                                          have p3535_3 := h3535c.2.2.2
                                          linarith only [h3495, hlam, p3535_0]
                                        · have p3535_0 := h3535c.1
                                          have p3535_1 := h3535c.2.1
                                          have p3535_2 := h3535c.2.2.1
                                          have p3535_3 := h3535c.2.2.2
                                          linarith only [h3522, hlam, p3535_0]
                                        · have p3535_0 := h3535c.1
                                          have p3535_1 := h3535c.2.1
                                          have p3535_2 := h3535c.2.2.1
                                          have p3535_3 := h3535c.2.2.2
                                          linarith only [h3529, hlam, p3535_1]
                                        · have p3535_0 := h3535c.1
                                          have p3535_1 := h3535c.2.1
                                          have p3535_2 := h3535c.2.2.1
                                          have p3535_3 := h3535c.2.2.2
                                          linarith only [hlam, p3535_0]
                                        · have p3535_0 := h3535c.1
                                          have p3535_1 := h3535c.2.1
                                          have p3535_2 := h3535c.2.2.1
                                          have p3535_3 := h3535c.2.2.2
                                          linarith only [h3531, hlam, p3535_1]
                                        · have p3535_0 := h3535c.1
                                          have p3535_1 := h3535c.2.1
                                          have p3535_2 := h3535c.2.2.1
                                          have p3535_3 := h3535c.2.2.2
                                          linarith only [h3495, h3531, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p3535_1, u0ehi3]
                                        · have p3535_0 := h3535c.1
                                          have p3535_1 := h3535c.2.1
                                          have p3535_2 := h3535c.2.2.1
                                          have p3535_3 := h3535c.2.2.2
                                          linarith only [h3522, h3531, hc24, hc45, hlam, hphi, p3535_1]
                                        · have p3535_0 := h3535c.1
                                          have p3535_1 := h3535c.2.1
                                          have p3535_2 := h3535c.2.2.1
                                          have p3535_3 := h3535c.2.2.2
                                          linarith only [h3530, hlam, p3535_1]
                                        · have p3535_0 := h3535c.1
                                          have p3535_1 := h3535c.2.1
                                          have p3535_2 := h3535c.2.2.1
                                          have p3535_3 := h3535c.2.2.2
                                          rcases p3535_3 (m.d 0 2) (by simp) with h3561 | h3561
                                          · linarith only [h3496, h3561, hlam]
                                          · linarith only [h3495, h3561, hlam]
                                        · have p3535_0 := h3535c.1
                                          have p3535_1 := h3535c.2.1
                                          have p3535_2 := h3535c.2.2.1
                                          have p3535_3 := h3535c.2.2.2
                                          linarith only [hlam, p3535_0]
                                  · linarith only [h1, h3492, h3520, h3526, h3530, hlam]
                                · linarith only [h1, h3492, h3520, h3522, h3523, h3529, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h1, h3492, h3522, h3523, h3526, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h1, h3492, h3522, h3523, h3525, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h3495, h3496, h3522, hc12, hc25, hlam, hphi]
                · linarith only [h1, h3492, h3517, hlam]
              · linarith only [h1, h3491, h3516, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3572 | h3572
            · rcases m.htr 0 3 4 (by decide) (by decide) with h3573 | h3573
              · rcases m.htr 0 3 5 (by decide) (by decide) with h3574 | h3574
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3575 | h3575
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3576 | h3576
                    · linarith only [h0, h3493, h3572, h3576, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3578 | h3578
                      · linarith only [h0, h1, h3495, h3572, h3576, h3578, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h3580 | h3580
                        · linarith only [h1, h3491, h3576, h3578, h3580, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                        · linarith only [h3495, h3572, h3580, hc12, hc24, hlam, hphi]
                  · linarith only [h3495, h3572, h3575, hlam]
                · linarith only [h0, h1, h3572, h3574, hlam]
              · linarith only [h1, h3491, h3573, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h3586 | h3586
              · rcases m.htr 0 3 5 (by decide) (by decide) with h3587 | h3587
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3588 | h3588
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3589 | h3589
                    · linarith only [h0, h1, h3493, h3589, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3591 | h3591
                      · linarith only [h0, h1, h3495, h3589, h3591, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h3593 | h3593
                        · linarith only [h1, h3491, h3572, h3589, h3591, h3593, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h3595 | h3595
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h3596 | h3596
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h3597 | h3597
                              · linarith only [h1, h3491, h3589, h3597, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                              · linarith only [h1, h3491, h3588, h3589, h3591, h3597, hc12, hc23, hlam, hphi]
                            · linarith only [h1, h3491, h3588, h3596, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                          · linarith only [h1, h3491, h3572, h3588, h3595, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3602 | h3602
                    · linarith only [h3493, h3602, hc12, hlam, hphi, ht01, u0ehi1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3604 | h3604
                      · linarith only [h0, h3495, h3604, hc01, hlam, hphi, u0ehi1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h3606 | h3606
                        · linarith only [h1, h3491, h3572, h3602, h3604, h3606, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h3608 | h3608
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h3609 | h3609
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h3610 | h3610
                              · linarith only [h1, h3491, h3588, h3602, h3610, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h3612 | h3612
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h3613 | h3613
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3614 | h3614
                                    · linarith only [h3495, h3588, h3614, hc24, hlam, hphi, ht01, ht12, u0ehi1]
                                    · linarith only [h3495, h3614, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                                  · linarith only [h1, h3492, h3602, h3609, h3613, hlam]
                                · linarith only [h1, h3492, h3602, h3608, h3610, h3612, hlam]
                            · linarith only [h1, h3492, h3609, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                          · linarith only [h1, h3492, h3586, h3588, h3608, hc05, hlam, hphi, ht0b, ht5b, u5ehi1]
                · linarith only [h1, h3492, h3587, hlam]
              · linarith only [h1, h3491, h3586, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3623 | h3623
        · linarith only [h0, h1, h3623, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h3625 | h3625
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3626 | h3626
            · linarith only [h0, h3492, h3626, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h3628 | h3628
              · rcases m.htr 0 3 5 (by decide) (by decide) with h3629 | h3629
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3630 | h3630
                  · linarith only [h0, h3492, h3625, h3630, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3632 | h3632
                    · linarith only [h3623, h3632, hc12, hlam, hphi, ht01, u0ehi1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3634 | h3634
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h3635 | h3635
                        · linarith only [h0, h1, h3625, h3626, h3632, h3635, hc23, hlam, hphi, ht01, ht12, u0ehi3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h3637 | h3637
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h3638 | h3638
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h3639 | h3639
                              · linarith only [h3491, h3492, h3630, h3632, h3638, h3639, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                              · linarith only [h0, h3492, h3634, h3639, hc24, hc45, hlam, hphi]
                            · linarith only [h1, h3629, h3638, hlam]
                          · linarith only [h0, h1, h3634, h3637, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h1, h3625, h3632, h3634, hc12, hc23, hlam, hphi]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3645 | h3645
                  · linarith only [h1, h3491, h3629, h3645, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3647 | h3647
                    · linarith only [h3623, h3647, hc12, hlam, hphi, ht01, u0ehi1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3649 | h3649
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h3650 | h3650
                        · linarith only [h0, h1, h3650, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h3652 | h3652
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h3653 | h3653
                            · linarith only [h0, h1, h3629, h3647, h3653, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h1, h3649, h3653, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1, h3649, h3652, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h3623, h3625, h3649, hc12, hc23, hlam, hphi]
              · linarith only [h1, h3491, h3628, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3659 | h3659
            · linarith only [h3491, h3492, h3625, h3659, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h3661 | h3661
              · rcases m.htr 0 3 5 (by decide) (by decide) with h3662 | h3662
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3663 | h3663
                  · linarith only [h3491, h3492, h3663, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3665 | h3665
                    · linarith only [h0, h1, h3623, h3665, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3667 | h3667
                      · linarith only [h0, h1, h3625, h3665, h3667, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h3669 | h3669
                        · linarith only [h1, h3491, h3659, h3665, h3667, h3669, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h3671 | h3671
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h3672 | h3672
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h3673 | h3673
                              · linarith only [h3491, h3492, h3663, h3665, h3672, h3673, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h3675 | h3675
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h3676 | h3676
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3677 | h3677
                                    · linarith only [h3491, h3492, h3667, h3673, h3677, hc12, hc24, hlam, hphi]
                                    · linarith only [h3625, h3677, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                                  · linarith only [h3491, h3492, h3625, h3665, h3672, h3676, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                                · linarith only [h3491, h3492, h3665, h3671, h3672, h3675, hlam]
                            · linarith only [h1, h3491, h3625, h3662, h3672, hc03, hlam, hphi, u0ehi1]
                          · linarith only [h1, h3491, h3625, h3671, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3684 | h3684
                  · linarith only [h1, h3491, h3662, h3684, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3686 | h3686
                    · linarith only [h0, h1, h3662, h3686, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3688 | h3688
                      · linarith only [h0, h1, h3625, h3662, h3688, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h3690 | h3690
                        · linarith only [h1, h3491, h3662, h3688, h3690, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h3692 | h3692
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h3693 | h3693
                            · linarith only [h1, h3491, h3662, h3686, h3688, h3693, hc12, hc23, hlam, hphi]
                            · linarith only [h1, h3491, h3625, h3693, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                          · linarith only [h1, h3491, h3625, h3692, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
              · linarith only [h1, h3491, h3661, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3698 | h3698
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3699 | h3699
        · linarith only [h0, h1, h3699, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h3701 | h3701
          · linarith only [h0, h3491, h3701, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3703 | h3703
            · rcases m.htr 0 3 4 (by decide) (by decide) with h3704 | h3704
              · rcases m.htr 0 3 5 (by decide) (by decide) with h3705 | h3705
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3706 | h3706
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3707 | h3707
                    · linarith only [h3699, h3703, h3707, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3709 | h3709
                      · linarith only [h0, h3701, h3703, h3709, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h3711 | h3711
                        · linarith only [h0, h1, h3707, h3711, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                        · linarith only [h0, h1, h3703, h3707, h3711, hc12, hc23, hlam, hphi]
                  · linarith only [h0, h3491, h3703, h3706, hlam]
                · linarith only [h0, h3491, h3703, h3704, h3705, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h3716 | h3716
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3717 | h3717
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3718 | h3718
                    · linarith only [h0, h1, h3704, h3718, hc23, hc34, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3720 | h3720
                      · linarith only [h0, h1, h3701, h3704, h3720, hc02, hc34, hlam, hphi, ht23]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h3722 | h3722
                        · linarith only [h0, h1, h3704, h3722, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · linarith only [h0, h1, h3703, h3704, h3722, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h1, h3698, h3704, h3717, hlam]
                · linarith only [h0, h1, h3703, h3716, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h3727 | h3727
              · rcases m.htr 0 3 5 (by decide) (by decide) with h3728 | h3728
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3729 | h3729
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3730 | h3730
                    · linarith only [h0, h1, h3699, h3730, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3732 | h3732
                      · linarith only [h0, h1, h3701, h3730, h3732, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h3734 | h3734
                        · linarith only [h0, h1, h3703, h3730, h3734, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h3736 | h3736
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h3737 | h3737
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h3738 | h3738
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h3739 | h3739
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h3740 | h3740
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3741 | h3741
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3742 | h3742
                                      · rcases h2bigk with h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c | h3743c
                                        · have p3743_0 := h3743c.1
                                          have p3743_1 := h3743c.2.1
                                          have p3743_2 := h3743c.2.2.1
                                          have p3743_3 := h3743c.2.2.2
                                          linarith only [hlam, p3743_0]
                                        · have p3743_0 := h3743c.1
                                          have p3743_1 := h3743c.2.1
                                          have p3743_2 := h3743c.2.2.1
                                          have p3743_3 := h3743c.2.2.2
                                          linarith only [h3703, hc12, hc25, hlam, hphi, p3743_1]
                                        · have p3743_0 := h3743c.1
                                          have p3743_1 := h3743c.2.1
                                          have p3743_2 := h3743c.2.2.1
                                          have p3743_3 := h3743c.2.2.2
                                          linarith only [h3699, hlam, p3743_0]
                                        · have p3743_0 := h3743c.1
                                          have p3743_1 := h3743c.2.1
                                          have p3743_2 := h3743c.2.2.1
                                          have p3743_3 := h3743c.2.2.2
                                          linarith only [h3701, hlam, p3743_0]
                                        · have p3743_0 := h3743c.1
                                          have p3743_1 := h3743c.2.1
                                          have p3743_2 := h3743c.2.2.1
                                          have p3743_3 := h3743c.2.2.2
                                          linarith only [h3703, hlam, p3743_0]
                                        · have p3743_0 := h3743c.1
                                          have p3743_1 := h3743c.2.1
                                          have p3743_2 := h3743c.2.2.1
                                          have p3743_3 := h3743c.2.2.2
                                          linarith only [h0, hlam, p3743_0]
                                        · have p3743_0 := h3743c.1
                                          have p3743_1 := h3743c.2.1
                                          have p3743_2 := h3743c.2.2.1
                                          have p3743_3 := h3743c.2.2.2
                                          linarith only [hlam, p3743_0]
                                        · have p3743_0 := h3743c.1
                                          have p3743_1 := h3743c.2.1
                                          have p3743_2 := h3743c.2.2.1
                                          have p3743_3 := h3743c.2.2.2
                                          linarith only [h3730, hlam, p3743_0]
                                        · have p3743_0 := h3743c.1
                                          have p3743_1 := h3743c.2.1
                                          have p3743_2 := h3743c.2.2.1
                                          have p3743_3 := h3743c.2.2.2
                                          linarith only [h3732, hlam, p3743_0]
                                        · have p3743_0 := h3743c.1
                                          have p3743_1 := h3743c.2.1
                                          have p3743_2 := h3743c.2.2.1
                                          have p3743_3 := h3743c.2.2.2
                                          linarith only [h3734, hlam, p3743_0]
                                        · have p3743_0 := h3743c.1
                                          have p3743_1 := h3743c.2.1
                                          have p3743_2 := h3743c.2.2.1
                                          have p3743_3 := h3743c.2.2.2
                                          linarith only [hc23, hlam, hphi, ht01, ht12, p3743_1, u0ehi1]
                                        · have p3743_0 := h3743c.1
                                          have p3743_1 := h3743c.2.1
                                          have p3743_2 := h3743c.2.2.1
                                          have p3743_3 := h3743c.2.2.2
                                          rcases p3743_3 (m.d 0 2) (by simp) with h3755 | h3755
                                          · linarith only [h3699, h3755, hlam]
                                          · linarith only [h0, h3755, hlam]
                                        · have p3743_0 := h3743c.1
                                          have p3743_1 := h3743c.2.1
                                          have p3743_2 := h3743c.2.2.1
                                          have p3743_3 := h3743c.2.2.2
                                          linarith only [hlam, p3743_0]
                                        · have p3743_0 := h3743c.1
                                          have p3743_1 := h3743c.2.1
                                          have p3743_2 := h3743c.2.2.1
                                          have p3743_3 := h3743c.2.2.2
                                          linarith only [h3701, hc23, hlam, hphi, ht01, ht12, p3743_1, u0ehi1]
                                        · have p3743_0 := h3743c.1
                                          have p3743_1 := h3743c.2.1
                                          have p3743_2 := h3743c.2.2.1
                                          have p3743_3 := h3743c.2.2.2
                                          linarith only [h3703, hc23, hlam, hphi, ht01, ht12, p3743_1, u0ehi1]
                                        · have p3743_0 := h3743c.1
                                          have p3743_1 := h3743c.2.1
                                          have p3743_2 := h3743c.2.2.1
                                          have p3743_3 := h3743c.2.2.2
                                          linarith only [hc24, hlam, hphi, ht01, ht12, p3743_1, u0ehi1]
                                        · have p3743_0 := h3743c.1
                                          have p3743_1 := h3743c.2.1
                                          have p3743_2 := h3743c.2.2.1
                                          have p3743_3 := h3743c.2.2.2
                                          rcases p3743_3 (m.d 0 2) (by simp) with h3762 | h3762
                                          · linarith only [h3701, h3762, hlam]
                                          · linarith only [h0, h3762, hlam]
                                        · have p3743_0 := h3743c.1
                                          have p3743_1 := h3743c.2.1
                                          have p3743_2 := h3743c.2.2.1
                                          have p3743_3 := h3743c.2.2.2
                                          linarith only [h3739, hlam, p3743_1]
                                        · have p3743_0 := h3743c.1
                                          have p3743_1 := h3743c.2.1
                                          have p3743_2 := h3743c.2.2.1
                                          have p3743_3 := h3743c.2.2.2
                                          linarith only [hlam, p3743_0]
                                        · have p3743_0 := h3743c.1
                                          have p3743_1 := h3743c.2.1
                                          have p3743_2 := h3743c.2.2.1
                                          have p3743_3 := h3743c.2.2.2
                                          linarith only [h3703, h3739, hc23, hlam, hphi, ht01, ht12, p3743_1, u0ehi1]
                                        · have p3743_0 := h3743c.1
                                          have p3743_1 := h3743c.2.1
                                          have p3743_2 := h3743c.2.2.1
                                          have p3743_3 := h3743c.2.2.2
                                          linarith only [hc25, hlam, hphi, ht01, ht12, p3743_1, u0ehi1]
                                        · have p3743_0 := h3743c.1
                                          have p3743_1 := h3743c.2.1
                                          have p3743_2 := h3743c.2.2.1
                                          have p3743_3 := h3743c.2.2.2
                                          rcases p3743_3 (m.d 0 2) (by simp) with h3769 | h3769
                                          · linarith only [h3703, h3769, hlam]
                                          · linarith only [h0, h3769, hlam]
                                        · have p3743_0 := h3743c.1
                                          have p3743_1 := h3743c.2.1
                                          have p3743_2 := h3743c.2.2.1
                                          have p3743_3 := h3743c.2.2.2
                                          linarith only [h3740, hlam, p3743_1]
                                        · have p3743_0 := h3743c.1
                                          have p3743_1 := h3743c.2.1
                                          have p3743_2 := h3743c.2.2.1
                                          have p3743_3 := h3743c.2.2.2
                                          linarith only [h3741, hlam, p3743_0]
                                        · have p3743_0 := h3743c.1
                                          have p3743_1 := h3743c.2.1
                                          have p3743_2 := h3743c.2.2.1
                                          have p3743_3 := h3743c.2.2.2
                                          linarith only [hlam, p3743_0]
                                      · rcases h2bigk with h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [hlam, p3775_0]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [h0, h3491, h3730, h3736, hc12, hc23, hlam, hphi, p3775_1]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [h3699, hlam, p3775_0]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [h3701, hlam, p3775_0]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [h3703, hlam, p3775_0]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [h0, hlam, p3775_0]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [hlam, p3775_0]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [h3730, hlam, p3775_0]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [h3732, hlam, p3775_0]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [h3734, hlam, p3775_0]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [hc23, hlam, hphi, ht01, ht12, p3775_1, u0ehi1]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          rcases p3775_3 (m.d 0 2) (by simp) with h3787 | h3787
                                          · linarith only [h3699, h3787, hlam]
                                          · linarith only [h0, h3787, hlam]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [hlam, p3775_0]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [h3701, hc23, hlam, hphi, ht01, ht12, p3775_1, u0ehi1]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [h3703, hc23, hlam, hphi, ht01, ht12, p3775_1, u0ehi1]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [hc24, hlam, hphi, ht01, ht12, p3775_1, u0ehi1]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          rcases p3775_3 (m.d 0 2) (by simp) with h3794 | h3794
                                          · linarith only [h3701, h3794, hlam]
                                          · linarith only [h0, h3794, hlam]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [h3739, hlam, p3775_1]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [hlam, p3775_0]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [h3703, h3739, hc23, hlam, hphi, ht01, ht12, p3775_1, u0ehi1]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [hc25, hlam, hphi, ht01, ht12, p3775_1, u0ehi1]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          rcases p3775_3 (m.d 0 2) (by simp) with h3801 | h3801
                                          · linarith only [h3703, h3801, hlam]
                                          · linarith only [h0, h3801, hlam]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [h3740, hlam, p3775_1]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [h3741, hlam, p3775_0]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [hlam, p3775_0]
                                    · linarith only [h3491, h3698, h3701, h3730, h3736, h3738, h3741, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                                  · linarith only [h3491, h3698, h3730, h3736, h3740, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                                · linarith only [h3491, h3698, h3730, h3736, h3739, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                              · linarith only [h3491, h3698, h3737, h3738, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                            · linarith only [h3491, h3698, h3736, h3737, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                          · linarith only [h1, h3727, h3736, hlam]
                  · linarith only [h3491, h3698, h3729, hlam]
                · linarith only [h1, h3698, h3728, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h3815 | h3815
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3816 | h3816
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3817 | h3817
                    · linarith only [h3699, h3817, hc12, hlam, hphi, ht01, u0ehi1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3819 | h3819
                      · linarith only [h0, h3701, h3819, hc01, hlam, hphi, u0ehi1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h3821 | h3821
                        · linarith only [h0, h1, h3727, h3821, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h3823 | h3823
                          · linarith only [h1, h3698, h3727, h3817, h3821, h3823, hc12, hc23, hlam, hphi]
                          · linarith only [h1, h3698, h3703, h3823, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                  · linarith only [h3491, h3698, h3816, hlam]
                · linarith only [h1, h3698, h3815, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3828 | h3828
        · linarith only [h0, h1, h3828, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h3830 | h3830
          · linarith only [h0, h3491, h3830, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3832 | h3832
            · linarith only [h0, h3698, h3832, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h3834 | h3834
              · rcases m.htr 0 3 5 (by decide) (by decide) with h3835 | h3835
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3836 | h3836
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3837 | h3837
                    · linarith only [h3828, h3837, hc12, hlam, hphi, ht01, u0ehi1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3839 | h3839
                      · linarith only [h0, h3830, h3839, hc01, hlam, hphi, u0ehi1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h3841 | h3841
                        · linarith only [h0, h1, h3832, h3837, h3841, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h3843 | h3843
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h3844 | h3844
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h3845 | h3845
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h3846 | h3846
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h3847 | h3847
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3848 | h3848
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3849 | h3849
                                      · rcases h2bigk with h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c | h3850c
                                        · have p3850_0 := h3850c.1
                                          have p3850_1 := h3850c.2.1
                                          have p3850_2 := h3850c.2.2.1
                                          have p3850_3 := h3850c.2.2.2
                                          linarith only [hlam, p3850_0]
                                        · have p3850_0 := h3850c.1
                                          have p3850_1 := h3850c.2.1
                                          have p3850_2 := h3850c.2.2.1
                                          have p3850_3 := h3850c.2.2.2
                                          linarith only [h0, h3698, h3837, h3843, h3845, hc12, hc23, hlam, hphi, p3850_1]
                                        · have p3850_0 := h3850c.1
                                          have p3850_1 := h3850c.2.1
                                          have p3850_2 := h3850c.2.2.1
                                          have p3850_3 := h3850c.2.2.2
                                          linarith only [h3828, hlam, p3850_0]
                                        · have p3850_0 := h3850c.1
                                          have p3850_1 := h3850c.2.1
                                          have p3850_2 := h3850c.2.2.1
                                          have p3850_3 := h3850c.2.2.2
                                          linarith only [h3830, hlam, p3850_0]
                                        · have p3850_0 := h3850c.1
                                          have p3850_1 := h3850c.2.1
                                          have p3850_2 := h3850c.2.2.1
                                          have p3850_3 := h3850c.2.2.2
                                          linarith only [h3832, hlam, p3850_0]
                                        · have p3850_0 := h3850c.1
                                          have p3850_1 := h3850c.2.1
                                          have p3850_2 := h3850c.2.2.1
                                          have p3850_3 := h3850c.2.2.2
                                          linarith only [h0, hlam, p3850_0]
                                        · have p3850_0 := h3850c.1
                                          have p3850_1 := h3850c.2.1
                                          have p3850_2 := h3850c.2.2.1
                                          have p3850_3 := h3850c.2.2.2
                                          linarith only [hlam, p3850_0]
                                        · have p3850_0 := h3850c.1
                                          have p3850_1 := h3850c.2.1
                                          have p3850_2 := h3850c.2.2.1
                                          have p3850_3 := h3850c.2.2.2
                                          linarith only [h3837, hlam, p3850_0]
                                        · have p3850_0 := h3850c.1
                                          have p3850_1 := h3850c.2.1
                                          have p3850_2 := h3850c.2.2.1
                                          have p3850_3 := h3850c.2.2.2
                                          linarith only [h3839, hlam, p3850_0]
                                        · have p3850_0 := h3850c.1
                                          have p3850_1 := h3850c.2.1
                                          have p3850_2 := h3850c.2.2.1
                                          have p3850_3 := h3850c.2.2.2
                                          linarith only [h3841, hlam, p3850_0]
                                        · have p3850_0 := h3850c.1
                                          have p3850_1 := h3850c.2.1
                                          have p3850_2 := h3850c.2.2.1
                                          have p3850_3 := h3850c.2.2.2
                                          linarith only [hc23, hlam, hphi, ht01, ht12, p3850_1, u0ehi1]
                                        · have p3850_0 := h3850c.1
                                          have p3850_1 := h3850c.2.1
                                          have p3850_2 := h3850c.2.2.1
                                          have p3850_3 := h3850c.2.2.2
                                          rcases p3850_3 (m.d 0 2) (by simp) with h3862 | h3862
                                          · linarith only [h3828, h3862, hlam]
                                          · linarith only [h0, h3862, hlam]
                                        · have p3850_0 := h3850c.1
                                          have p3850_1 := h3850c.2.1
                                          have p3850_2 := h3850c.2.2.1
                                          have p3850_3 := h3850c.2.2.2
                                          linarith only [hlam, p3850_0]
                                        · have p3850_0 := h3850c.1
                                          have p3850_1 := h3850c.2.1
                                          have p3850_2 := h3850c.2.2.1
                                          have p3850_3 := h3850c.2.2.2
                                          linarith only [h3830, hc23, hlam, hphi, ht01, ht12, p3850_1, u0ehi1]
                                        · have p3850_0 := h3850c.1
                                          have p3850_1 := h3850c.2.1
                                          have p3850_2 := h3850c.2.2.1
                                          have p3850_3 := h3850c.2.2.2
                                          linarith only [h3698, h3841, hc01, hc23, hlam, hphi, ht12, p3850_1]
                                        · have p3850_0 := h3850c.1
                                          have p3850_1 := h3850c.2.1
                                          have p3850_2 := h3850c.2.2.1
                                          have p3850_3 := h3850c.2.2.2
                                          linarith only [hc24, hlam, hphi, ht01, ht12, p3850_1, u0ehi1]
                                        · have p3850_0 := h3850c.1
                                          have p3850_1 := h3850c.2.1
                                          have p3850_2 := h3850c.2.2.1
                                          have p3850_3 := h3850c.2.2.2
                                          rcases p3850_3 (m.d 0 2) (by simp) with h3869 | h3869
                                          · linarith only [h3830, h3869, hlam]
                                          · linarith only [h0, h3869, hlam]
                                        · have p3850_0 := h3850c.1
                                          have p3850_1 := h3850c.2.1
                                          have p3850_2 := h3850c.2.2.1
                                          have p3850_3 := h3850c.2.2.2
                                          linarith only [h3846, hlam, p3850_1]
                                        · have p3850_0 := h3850c.1
                                          have p3850_1 := h3850c.2.1
                                          have p3850_2 := h3850c.2.2.1
                                          have p3850_3 := h3850c.2.2.2
                                          linarith only [hlam, p3850_0]
                                        · have p3850_0 := h3850c.1
                                          have p3850_1 := h3850c.2.1
                                          have p3850_2 := h3850c.2.2.1
                                          have p3850_3 := h3850c.2.2.2
                                          linarith only [h0, h3698, h3841, h3846, hc23, hlam, hphi, ht01, ht12, p3850_1, u0ehi1]
                                        · have p3850_0 := h3850c.1
                                          have p3850_1 := h3850c.2.1
                                          have p3850_2 := h3850c.2.2.1
                                          have p3850_3 := h3850c.2.2.2
                                          linarith only [hc25, hlam, hphi, ht01, ht12, p3850_1, u0ehi1]
                                        · have p3850_0 := h3850c.1
                                          have p3850_1 := h3850c.2.1
                                          have p3850_2 := h3850c.2.2.1
                                          have p3850_3 := h3850c.2.2.2
                                          rcases p3850_3 (m.d 0 2) (by simp) with h3876 | h3876
                                          · linarith only [h3832, h3876, hlam]
                                          · linarith only [h0, h3876, hlam]
                                        · have p3850_0 := h3850c.1
                                          have p3850_1 := h3850c.2.1
                                          have p3850_2 := h3850c.2.2.1
                                          have p3850_3 := h3850c.2.2.2
                                          linarith only [h3847, hlam, p3850_1]
                                        · have p3850_0 := h3850c.1
                                          have p3850_1 := h3850c.2.1
                                          have p3850_2 := h3850c.2.2.1
                                          have p3850_3 := h3850c.2.2.2
                                          linarith only [h3848, hlam, p3850_0]
                                        · have p3850_0 := h3850c.1
                                          have p3850_1 := h3850c.2.1
                                          have p3850_2 := h3850c.2.2.1
                                          have p3850_3 := h3850c.2.2.2
                                          linarith only [hlam, p3850_0]
                                      · rcases h2bigk with h3882c | h3882c | h3882c | h3882c | h3882c | h3882c | h3882c | h3882c | h3882c | h3882c | h3882c | h3882c | h3882c | h3882c | h3882c | h3882c | h3882c | h3882c | h3882c | h3882c | h3882c | h3882c | h3882c | h3882c | h3882c
                                        · have p3882_0 := h3882c.1
                                          have p3882_1 := h3882c.2.1
                                          have p3882_2 := h3882c.2.2.1
                                          have p3882_3 := h3882c.2.2.2
                                          linarith only [hlam, p3882_0]
                                        · have p3882_0 := h3882c.1
                                          have p3882_1 := h3882c.2.1
                                          have p3882_2 := h3882c.2.2.1
                                          have p3882_3 := h3882c.2.2.2
                                          linarith only [h0, h1, h3837, hc12, hc23, hlam, hphi, p3882_1]
                                        · have p3882_0 := h3882c.1
                                          have p3882_1 := h3882c.2.1
                                          have p3882_2 := h3882c.2.2.1
                                          have p3882_3 := h3882c.2.2.2
                                          linarith only [h3828, hlam, p3882_0]
                                        · have p3882_0 := h3882c.1
                                          have p3882_1 := h3882c.2.1
                                          have p3882_2 := h3882c.2.2.1
                                          have p3882_3 := h3882c.2.2.2
                                          linarith only [h3830, hlam, p3882_0]
                                        · have p3882_0 := h3882c.1
                                          have p3882_1 := h3882c.2.1
                                          have p3882_2 := h3882c.2.2.1
                                          have p3882_3 := h3882c.2.2.2
                                          linarith only [h3832, hlam, p3882_0]
                                        · have p3882_0 := h3882c.1
                                          have p3882_1 := h3882c.2.1
                                          have p3882_2 := h3882c.2.2.1
                                          have p3882_3 := h3882c.2.2.2
                                          linarith only [h0, hlam, p3882_0]
                                        · have p3882_0 := h3882c.1
                                          have p3882_1 := h3882c.2.1
                                          have p3882_2 := h3882c.2.2.1
                                          have p3882_3 := h3882c.2.2.2
                                          linarith only [hlam, p3882_0]
                                        · have p3882_0 := h3882c.1
                                          have p3882_1 := h3882c.2.1
                                          have p3882_2 := h3882c.2.2.1
                                          have p3882_3 := h3882c.2.2.2
                                          linarith only [h3837, hlam, p3882_0]
                                        · have p3882_0 := h3882c.1
                                          have p3882_1 := h3882c.2.1
                                          have p3882_2 := h3882c.2.2.1
                                          have p3882_3 := h3882c.2.2.2
                                          linarith only [h3839, hlam, p3882_0]
                                        · have p3882_0 := h3882c.1
                                          have p3882_1 := h3882c.2.1
                                          have p3882_2 := h3882c.2.2.1
                                          have p3882_3 := h3882c.2.2.2
                                          linarith only [h3841, hlam, p3882_0]
                                        · have p3882_0 := h3882c.1
                                          have p3882_1 := h3882c.2.1
                                          have p3882_2 := h3882c.2.2.1
                                          have p3882_3 := h3882c.2.2.2
                                          linarith only [hc23, hlam, hphi, ht01, ht12, p3882_1, u0ehi1]
                                        · have p3882_0 := h3882c.1
                                          have p3882_1 := h3882c.2.1
                                          have p3882_2 := h3882c.2.2.1
                                          have p3882_3 := h3882c.2.2.2
                                          rcases p3882_3 (m.d 0 2) (by simp) with h3894 | h3894
                                          · linarith only [h3828, h3894, hlam]
                                          · linarith only [h0, h3894, hlam]
                                        · have p3882_0 := h3882c.1
                                          have p3882_1 := h3882c.2.1
                                          have p3882_2 := h3882c.2.2.1
                                          have p3882_3 := h3882c.2.2.2
                                          linarith only [hlam, p3882_0]
                                        · have p3882_0 := h3882c.1
                                          have p3882_1 := h3882c.2.1
                                          have p3882_2 := h3882c.2.2.1
                                          have p3882_3 := h3882c.2.2.2
                                          linarith only [h3698, h3841, h3848, hc01, hc23, hlam, hphi, ht12, p3882_1]
                                        · have p3882_0 := h3882c.1
                                          have p3882_1 := h3882c.2.1
                                          have p3882_2 := h3882c.2.2.1
                                          have p3882_3 := h3882c.2.2.2
                                          linarith only [h0, h3698, h3841, hc23, hlam, hphi, ht01, ht12, p3882_1, u0ehi1]
                                        · have p3882_0 := h3882c.1
                                          have p3882_1 := h3882c.2.1
                                          have p3882_2 := h3882c.2.2.1
                                          have p3882_3 := h3882c.2.2.2
                                          linarith only [hc24, hlam, hphi, ht01, ht12, p3882_1, u0ehi1]
                                        · have p3882_0 := h3882c.1
                                          have p3882_1 := h3882c.2.1
                                          have p3882_2 := h3882c.2.2.1
                                          have p3882_3 := h3882c.2.2.2
                                          rcases p3882_3 (m.d 0 2) (by simp) with h3901 | h3901
                                          · linarith only [h3830, h3901, hlam]
                                          · linarith only [h0, h3901, hlam]
                                        · have p3882_0 := h3882c.1
                                          have p3882_1 := h3882c.2.1
                                          have p3882_2 := h3882c.2.2.1
                                          have p3882_3 := h3882c.2.2.2
                                          linarith only [h3846, hlam, p3882_1]
                                        · have p3882_0 := h3882c.1
                                          have p3882_1 := h3882c.2.1
                                          have p3882_2 := h3882c.2.2.1
                                          have p3882_3 := h3882c.2.2.2
                                          linarith only [hlam, p3882_0]
                                        · have p3882_0 := h3882c.1
                                          have p3882_1 := h3882c.2.1
                                          have p3882_2 := h3882c.2.2.1
                                          have p3882_3 := h3882c.2.2.2
                                          linarith only [h0, h3698, h3841, h3846, hc23, hlam, hphi, ht01, ht12, p3882_1, u0ehi1]
                                        · have p3882_0 := h3882c.1
                                          have p3882_1 := h3882c.2.1
                                          have p3882_2 := h3882c.2.2.1
                                          have p3882_3 := h3882c.2.2.2
                                          linarith only [hc25, hlam, hphi, ht01, ht12, p3882_1, u0ehi1]
                                        · have p3882_0 := h3882c.1
                                          have p3882_1 := h3882c.2.1
                                          have p3882_2 := h3882c.2.2.1
                                          have p3882_3 := h3882c.2.2.2
                                          rcases p3882_3 (m.d 0 2) (by simp) with h3908 | h3908
                                          · linarith only [h3832, h3908, hlam]
                                          · linarith only [h0, h3908, hlam]
                                        · have p3882_0 := h3882c.1
                                          have p3882_1 := h3882c.2.1
                                          have p3882_2 := h3882c.2.2.1
                                          have p3882_3 := h3882c.2.2.2
                                          linarith only [h3847, hlam, p3882_1]
                                        · have p3882_0 := h3882c.1
                                          have p3882_1 := h3882c.2.1
                                          have p3882_2 := h3882c.2.2.1
                                          have p3882_3 := h3882c.2.2.2
                                          linarith only [h3848, hlam, p3882_0]
                                        · have p3882_0 := h3882c.1
                                          have p3882_1 := h3882c.2.1
                                          have p3882_2 := h3882c.2.2.1
                                          have p3882_3 := h3882c.2.2.2
                                          linarith only [hlam, p3882_0]
                                    · linarith only [h3830, h3836, h3848, hc05, hlam, hphi, u0ehi1]
                                  · linarith only [h0, h1, h3837, h3847, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                                · linarith only [h0, h3698, h3837, h3843, h3845, h3846, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                              · linarith only [h0, h3491, h3834, h3836, h3845, hc03, hlam, hphi, u0ehi1]
                            · linarith only [h1, h3835, h3844, hlam]
                          · linarith only [h1, h3834, h3843, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3920 | h3920
                    · linarith only [h0, h3491, h3836, h3920, hc23, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3922 | h3922
                      · linarith only [h0, h3491, h3836, h3922, hc24, hc45, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h3924 | h3924
                        · linarith only [h0, h3491, h3836, h3924, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h3926 | h3926
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h3927 | h3927
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h3928 | h3928
                              · linarith only [h0, h3491, h3836, h3922, h3928, hc12, hc24, hlam, hphi]
                              · linarith only [h0, h3491, h3928, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                            · linarith only [h0, h1, h3927, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                          · linarith only [h1, h3834, h3926, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3933 | h3933
                  · linarith only [h3834, h3835, h3933, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3935 | h3935
                    · linarith only [h0, h3491, h3933, h3935, hc23, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3937 | h3937
                      · linarith only [h0, h3491, h3933, h3937, hc24, hc45, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h3939 | h3939
                        · linarith only [h0, h3491, h3933, h3939, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h3941 | h3941
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h3942 | h3942
                            · linarith only [h0, h3491, h3834, h3835, h3942, hc13, hlam, hphi, ht01, u0ehi1]
                            · linarith only [h0, h1, h3942, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                          · linarith only [h0, h1, h3834, h3941, hc03, hlam, hphi, u0ehi1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h3946 | h3946
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3947 | h3947
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3948 | h3948
                    · linarith only [h0, h3491, h3828, h3948, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3950 | h3950
                      · linarith only [h0, h3698, h3830, h3834, h3946, h3950, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h3952 | h3952
                        · linarith only [h0, h3698, h3834, h3946, h3952, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h3954 | h3954
                          · linarith only [h0, h3698, h3834, h3946, h3948, h3954, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h3954, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                  · linarith only [h3834, h3946, h3947, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h3958 | h3958
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3959 | h3959
                    · linarith only [h0, h1, h3946, h3959, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3961 | h3961
                      · linarith only [h0, h3830, h3961, hc01, hlam, hphi, u0ehi1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h3963 | h3963
                        · linarith only [h0, h1, h3946, h3963, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h3965 | h3965
                          · linarith only [h0, h1, h3834, h3959, h3965, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h3965, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h3968 | h3968
                    · linarith only [h0, h3491, h3958, h3968, hc23, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h3970 | h3970
                      · linarith only [h0, h1, h3834, h3958, h3970, hc24, hc45, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h3972 | h3972
                        · linarith only [h0, h1, h3834, h3958, h3972, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h3974 | h3974
                          · linarith only [h0, h1, h3834, h3968, h3974, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h3974, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]

end R2N4
