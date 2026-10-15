import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_25S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7740000 in
set_option maxHeartbeats 7740000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_s0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_10_12_23_L_R_L_I_H_I_s1 m hb0 hb2 hb3 h0 h1
  · rcases m.htr 0 2 3 (by decide) (by decide) with h3565 | h3565
    · linarith only [h0, h1, h3565, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3567 | h3567
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3568 | h3568
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3569 | h3569
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3570 | h3570
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3571 | h3571
              · linarith only [h3565, h3571, hc12, hlam, hphi, ht01, u0ehi1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3573 | h3573
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3574 | h3574
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3575 | h3575
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3576 | h3576
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3577 | h3577
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3578 | h3578
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3579 | h3579
                            · linarith only [h0, h1, h3571, h3573, h3579, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3581 | h3581
                              · linarith only [h3577, h3579, h3581, hlam]
                              · rcases h2bigk with h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c | h3583c
                                · have p3583_0 := h3583c.1
                                  have p3583_1 := h3583c.2.1
                                  have p3583_2 := h3583c.2.2.1
                                  have p3583_3 := h3583c.2.2.2
                                  linarith only [hlam, p3583_0]
                                · have p3583_0 := h3583c.1
                                  have p3583_1 := h3583c.2.1
                                  have p3583_2 := h3583c.2.2.1
                                  have p3583_3 := h3583c.2.2.2
                                  linarith only [h0, h1, h3571, hc12, hc23, hlam, hphi, p3583_1]
                                · have p3583_0 := h3583c.1
                                  have p3583_1 := h3583c.2.1
                                  have p3583_2 := h3583c.2.2.1
                                  have p3583_3 := h3583c.2.2.2
                                  linarith only [h3565, hlam, p3583_0]
                                · have p3583_0 := h3583c.1
                                  have p3583_1 := h3583c.2.1
                                  have p3583_2 := h3583c.2.2.1
                                  have p3583_3 := h3583c.2.2.2
                                  rcases p3583_3 (m.d 0 2) (by simp) with h3587 | h3587
                                  · rcases p3583_3 (m.d 1 2) (by simp) with h3588 | h3588
                                    · linarith only [h0, h3588, hlam]
                                    · linarith only [h3573, h3588, hlam]
                                  · linarith only [h3587, hlam, p3583_0]
                                · have p3583_0 := h3583c.1
                                  have p3583_1 := h3583c.2.1
                                  have p3583_2 := h3583c.2.2.1
                                  have p3583_3 := h3583c.2.2.2
                                  rcases p3583_3 (m.d 0 2) (by simp) with h3592 | h3592
                                  · rcases p3583_3 (m.d 1 2) (by simp) with h3593 | h3593
                                    · linarith only [h0, h3593, hlam]
                                    · linarith only [h3574, h3593, hlam]
                                  · linarith only [h3592, hlam, p3583_0]
                                · have p3583_0 := h3583c.1
                                  have p3583_1 := h3583c.2.1
                                  have p3583_2 := h3583c.2.2.1
                                  have p3583_3 := h3583c.2.2.2
                                  linarith only [h0, hlam, p3583_0]
                                · have p3583_0 := h3583c.1
                                  have p3583_1 := h3583c.2.1
                                  have p3583_2 := h3583c.2.2.1
                                  have p3583_3 := h3583c.2.2.2
                                  linarith only [hlam, p3583_0]
                                · have p3583_0 := h3583c.1
                                  have p3583_1 := h3583c.2.1
                                  have p3583_2 := h3583c.2.2.1
                                  have p3583_3 := h3583c.2.2.2
                                  linarith only [h3571, hlam, p3583_0]
                                · have p3583_0 := h3583c.1
                                  have p3583_1 := h3583c.2.1
                                  have p3583_2 := h3583c.2.2.1
                                  have p3583_3 := h3583c.2.2.2
                                  linarith only [h0, h1, h3571, h3577, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3583_1]
                                · have p3583_0 := h3583c.1
                                  have p3583_1 := h3583c.2.1
                                  have p3583_2 := h3583c.2.2.1
                                  have p3583_3 := h3583c.2.2.2
                                  linarith only [h0, h1, h3571, h3577, h3579, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3583_1]
                                · have p3583_0 := h3583c.1
                                  have p3583_1 := h3583c.2.1
                                  have p3583_2 := h3583c.2.2.1
                                  have p3583_3 := h3583c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht01, ht12, p3583_1, u0ehi1]
                                · have p3583_0 := h3583c.1
                                  have p3583_1 := h3583c.2.1
                                  have p3583_2 := h3583c.2.2.1
                                  have p3583_3 := h3583c.2.2.2
                                  rcases p3583_3 (m.d 0 2) (by simp) with h3603 | h3603
                                  · linarith only [h3565, h3603, hlam]
                                  · linarith only [h0, h3603, hlam]
                                · have p3583_0 := h3583c.1
                                  have p3583_1 := h3583c.2.1
                                  have p3583_2 := h3583c.2.2.1
                                  have p3583_3 := h3583c.2.2.2
                                  linarith only [hlam, p3583_0]
                                · have p3583_0 := h3583c.1
                                  have p3583_1 := h3583c.2.1
                                  have p3583_2 := h3583c.2.2.1
                                  have p3583_3 := h3583c.2.2.2
                                  linarith only [h0, h1, h3571, h3573, hlam, p3583_2]
                                · have p3583_0 := h3583c.1
                                  have p3583_1 := h3583c.2.1
                                  have p3583_2 := h3583c.2.2.1
                                  have p3583_3 := h3583c.2.2.2
                                  linarith only [h0, h1, h3571, h3574, hlam, p3583_2]
                                · have p3583_0 := h3583c.1
                                  have p3583_1 := h3583c.2.1
                                  have p3583_2 := h3583c.2.2.1
                                  have p3583_3 := h3583c.2.2.2
                                  linarith only [h3567, hlam, p3583_0]
                                · have p3583_0 := h3583c.1
                                  have p3583_1 := h3583c.2.1
                                  have p3583_2 := h3583c.2.2.1
                                  have p3583_3 := h3583c.2.2.2
                                  linarith only [h3573, hlam, p3583_0]
                                · have p3583_0 := h3583c.1
                                  have p3583_1 := h3583c.2.1
                                  have p3583_2 := h3583c.2.2.1
                                  have p3583_3 := h3583c.2.2.2
                                  linarith only [h3577, hlam, p3583_1]
                                · have p3583_0 := h3583c.1
                                  have p3583_1 := h3583c.2.1
                                  have p3583_2 := h3583c.2.2.1
                                  have p3583_3 := h3583c.2.2.2
                                  linarith only [hlam, p3583_0]
                                · have p3583_0 := h3583c.1
                                  have p3583_1 := h3583c.2.1
                                  have p3583_2 := h3583c.2.2.1
                                  have p3583_3 := h3583c.2.2.2
                                  linarith only [h3579, hlam, p3583_1]
                                · have p3583_0 := h3583c.1
                                  have p3583_1 := h3583c.2.1
                                  have p3583_2 := h3583c.2.2.1
                                  have p3583_3 := h3583c.2.2.2
                                  linarith only [h3568, hlam, p3583_0]
                                · have p3583_0 := h3583c.1
                                  have p3583_1 := h3583c.2.1
                                  have p3583_2 := h3583c.2.2.1
                                  have p3583_3 := h3583c.2.2.2
                                  linarith only [h3574, hlam, p3583_0]
                                · have p3583_0 := h3583c.1
                                  have p3583_1 := h3583c.2.1
                                  have p3583_2 := h3583c.2.2.1
                                  have p3583_3 := h3583c.2.2.2
                                  linarith only [h3578, hlam, p3583_1]
                                · have p3583_0 := h3583c.1
                                  have p3583_1 := h3583c.2.1
                                  have p3583_2 := h3583c.2.2.1
                                  have p3583_3 := h3583c.2.2.2
                                  linarith only [h0, h1, h3571, h3574, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3583_1]
                                · have p3583_0 := h3583c.1
                                  have p3583_1 := h3583c.2.1
                                  have p3583_2 := h3583c.2.2.1
                                  have p3583_3 := h3583c.2.2.2
                                  linarith only [hlam, p3583_0]
                          · linarith only [h0, h1, h3571, h3578, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h3571, h3577, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h1, h3568, h3576, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi4]
                    · linarith only [h0, h1, h3568, h3575, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi4]
                  · linarith only [h0, h1, h3568, h3573, h3574, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h0, h1, h3567, h3571, h3573, hc12, hc23, hlam, hphi]
            · linarith only [h0, h1, h3568, h3570, hlam]
          · linarith only [h0, h1, h3567, h3569, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3627 | h3627
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3628 | h3628
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3629 | h3629
              · linarith only [h3565, h3629, hc12, hlam, hphi, ht01, u0ehi1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3631 | h3631
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3632 | h3632
                  · linarith only [h0, h3567, h3568, h3632, hc01, hlam, hphi, u0ehi3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3634 | h3634
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3635 | h3635
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3636 | h3636
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3637 | h3637
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3638 | h3638
                            · linarith only [h0, h1, h3629, h3631, h3638, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3640 | h3640
                              · linarith only [h0, h1, h3567, h3568, h3629, h3631, h3636, h3638, h3640, hc23, hlam, hphi, ht01, ht12, u0ehi3]
                              · rcases h2bigk with h3642c | h3642c | h3642c | h3642c | h3642c | h3642c | h3642c | h3642c | h3642c | h3642c | h3642c | h3642c | h3642c | h3642c | h3642c | h3642c | h3642c | h3642c | h3642c | h3642c | h3642c | h3642c | h3642c | h3642c | h3642c
                                · have p3642_0 := h3642c.1
                                  have p3642_1 := h3642c.2.1
                                  have p3642_2 := h3642c.2.2.1
                                  have p3642_3 := h3642c.2.2.2
                                  linarith only [hlam, p3642_0]
                                · have p3642_0 := h3642c.1
                                  have p3642_1 := h3642c.2.1
                                  have p3642_2 := h3642c.2.2.1
                                  have p3642_3 := h3642c.2.2.2
                                  linarith only [h3568, h3638, hc12, hc45, hlam, hphi, ht23, ht34, p3642_1]
                                · have p3642_0 := h3642c.1
                                  have p3642_1 := h3642c.2.1
                                  have p3642_2 := h3642c.2.2.1
                                  have p3642_3 := h3642c.2.2.2
                                  linarith only [h3565, hlam, p3642_0]
                                · have p3642_0 := h3642c.1
                                  have p3642_1 := h3642c.2.1
                                  have p3642_2 := h3642c.2.2.1
                                  have p3642_3 := h3642c.2.2.2
                                  linarith only [h3568, h3636, h3638, hc34, hc45, hlam, hphi, p3642_1]
                                · have p3642_0 := h3642c.1
                                  have p3642_1 := h3642c.2.1
                                  have p3642_2 := h3642c.2.2.1
                                  have p3642_3 := h3642c.2.2.2
                                  linarith only [h3568, hlam, p3642_0]
                                · have p3642_0 := h3642c.1
                                  have p3642_1 := h3642c.2.1
                                  have p3642_2 := h3642c.2.2.1
                                  have p3642_3 := h3642c.2.2.2
                                  linarith only [h0, hlam, p3642_0]
                                · have p3642_0 := h3642c.1
                                  have p3642_1 := h3642c.2.1
                                  have p3642_2 := h3642c.2.2.1
                                  have p3642_3 := h3642c.2.2.2
                                  linarith only [hlam, p3642_0]
                                · have p3642_0 := h3642c.1
                                  have p3642_1 := h3642c.2.1
                                  have p3642_2 := h3642c.2.2.1
                                  have p3642_3 := h3642c.2.2.2
                                  linarith only [h3629, hlam, p3642_0]
                                · have p3642_0 := h3642c.1
                                  have p3642_1 := h3642c.2.1
                                  have p3642_2 := h3642c.2.2.1
                                  have p3642_3 := h3642c.2.2.2
                                  linarith only [h0, h1, h3567, h3568, h3629, h3636, h3638, hc23, hc34, hc45, hlam, hphi, ht01, ht12, p3642_1, u0ehi3]
                                · have p3642_0 := h3642c.1
                                  have p3642_1 := h3642c.2.1
                                  have p3642_2 := h3642c.2.2.1
                                  have p3642_3 := h3642c.2.2.2
                                  linarith only [h3632, hlam, p3642_0]
                                · have p3642_0 := h3642c.1
                                  have p3642_1 := h3642c.2.1
                                  have p3642_2 := h3642c.2.2.1
                                  have p3642_3 := h3642c.2.2.2
                                  linarith only [h3567, hc23, hlam, hphi, ht01, ht12, p3642_1, u0ehi3]
                                · have p3642_0 := h3642c.1
                                  have p3642_1 := h3642c.2.1
                                  have p3642_2 := h3642c.2.2.1
                                  have p3642_3 := h3642c.2.2.2
                                  rcases p3642_3 (m.d 0 2) (by simp) with h3654 | h3654
                                  · linarith only [h3565, h3654, hlam]
                                  · linarith only [h0, h3654, hlam]
                                · have p3642_0 := h3642c.1
                                  have p3642_1 := h3642c.2.1
                                  have p3642_2 := h3642c.2.2.1
                                  have p3642_3 := h3642c.2.2.2
                                  linarith only [hlam, p3642_0]
                                · have p3642_0 := h3642c.1
                                  have p3642_1 := h3642c.2.1
                                  have p3642_2 := h3642c.2.2.1
                                  have p3642_3 := h3642c.2.2.2
                                  linarith only [h0, h1, h3629, h3631, hlam, p3642_2]
                                · have p3642_0 := h3642c.1
                                  have p3642_1 := h3642c.2.1
                                  have p3642_2 := h3642c.2.2.1
                                  have p3642_3 := h3642c.2.2.2
                                  linarith only [h3567, h3568, hc23, hlam, hphi, ht01, ht12, p3642_1, u0ehi3]
                                · have p3642_0 := h3642c.1
                                  have p3642_1 := h3642c.2.1
                                  have p3642_2 := h3642c.2.2.1
                                  have p3642_3 := h3642c.2.2.2
                                  linarith only [h3567, hlam, p3642_0]
                                · have p3642_0 := h3642c.1
                                  have p3642_1 := h3642c.2.1
                                  have p3642_2 := h3642c.2.2.1
                                  have p3642_3 := h3642c.2.2.2
                                  linarith only [h3631, hlam, p3642_0]
                                · have p3642_0 := h3642c.1
                                  have p3642_1 := h3642c.2.1
                                  have p3642_2 := h3642c.2.2.1
                                  have p3642_3 := h3642c.2.2.2
                                  linarith only [h3636, hlam, p3642_1]
                                · have p3642_0 := h3642c.1
                                  have p3642_1 := h3642c.2.1
                                  have p3642_2 := h3642c.2.2.1
                                  have p3642_3 := h3642c.2.2.2
                                  linarith only [hlam, p3642_0]
                                · have p3642_0 := h3642c.1
                                  have p3642_1 := h3642c.2.1
                                  have p3642_2 := h3642c.2.2.1
                                  have p3642_3 := h3642c.2.2.2
                                  linarith only [h3638, hlam, p3642_1]
                                · have p3642_0 := h3642c.1
                                  have p3642_1 := h3642c.2.1
                                  have p3642_2 := h3642c.2.2.1
                                  have p3642_3 := h3642c.2.2.2
                                  linarith only [h3567, h3638, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p3642_1, u0ehi3]
                                · have p3642_0 := h3642c.1
                                  have p3642_1 := h3642c.2.1
                                  have p3642_2 := h3642c.2.2.1
                                  have p3642_3 := h3642c.2.2.2
                                  linarith only [h3631, h3638, hc24, hc45, hlam, hphi, p3642_1]
                                · have p3642_0 := h3642c.1
                                  have p3642_1 := h3642c.2.1
                                  have p3642_2 := h3642c.2.2.1
                                  have p3642_3 := h3642c.2.2.2
                                  linarith only [h3637, hlam, p3642_1]
                                · have p3642_0 := h3642c.1
                                  have p3642_1 := h3642c.2.1
                                  have p3642_2 := h3642c.2.2.1
                                  have p3642_3 := h3642c.2.2.2
                                  rcases p3642_3 (m.d 0 2) (by simp) with h3668 | h3668
                                  · linarith only [h3568, h3668, hlam]
                                  · linarith only [h3567, h3668, hlam]
                                · have p3642_0 := h3642c.1
                                  have p3642_1 := h3642c.2.1
                                  have p3642_2 := h3642c.2.2.1
                                  have p3642_3 := h3642c.2.2.2
                                  linarith only [hlam, p3642_0]
                          · linarith only [h0, h1, h3629, h3631, h3635, h3636, h3637, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h1, h3629, h3631, h3636, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h1, h3628, h3631, h3635, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h1, h3631, h3634, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h3567, h3568, h3631, hc12, hc25, hlam, hphi]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3677 | h3677
              · linarith only [h0, h1, h3628, h3677, hc23, hc35, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3679 | h3679
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3680 | h3680
                  · linarith only [h0, h1, h3568, h3628, h3680, hc02, hc35, hlam, hphi, ht23]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3682 | h3682
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3683 | h3683
                      · linarith only [h0, h1, h3628, h3677, h3683, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h3679, h3683, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h1, h3679, h3682, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h3567, h3568, h3679, hc12, hc25, hlam, hphi]
          · linarith only [h0, h1, h3567, h3627, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3689 | h3689
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3690 | h3690
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3691 | h3691
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3692 | h3692
              · linarith only [h0, h1, h3565, h3690, h3692, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3694 | h3694
                · linarith only [h0, h1, h3567, h3692, h3694, hc02, hc23, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3696 | h3696
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3697 | h3697
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3698 | h3698
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3699 | h3699
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3700 | h3700
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3701 | h3701
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3702 | h3702
                              · rcases h2bigk with h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c | h3703c
                                · have p3703_0 := h3703c.1
                                  have p3703_1 := h3703c.2.1
                                  have p3703_2 := h3703c.2.2.1
                                  have p3703_3 := h3703c.2.2.2
                                  linarith only [hlam, p3703_0]
                                · have p3703_0 := h3703c.1
                                  have p3703_1 := h3703c.2.1
                                  have p3703_2 := h3703c.2.2.1
                                  have p3703_3 := h3703c.2.2.2
                                  linarith only [h3567, hc12, hc24, hlam, hphi, p3703_1]
                                · have p3703_0 := h3703c.1
                                  have p3703_1 := h3703c.2.1
                                  have p3703_2 := h3703c.2.2.1
                                  have p3703_3 := h3703c.2.2.2
                                  linarith only [h3565, hlam, p3703_0]
                                · have p3703_0 := h3703c.1
                                  have p3703_1 := h3703c.2.1
                                  have p3703_2 := h3703c.2.2.1
                                  have p3703_3 := h3703c.2.2.2
                                  linarith only [h3567, hlam, p3703_0]
                                · have p3703_0 := h3703c.1
                                  have p3703_1 := h3703c.2.1
                                  have p3703_2 := h3703c.2.2.1
                                  have p3703_3 := h3703c.2.2.2
                                  rcases p3703_3 (m.d 0 2) (by simp) with h3708 | h3708
                                  · rcases p3703_3 (m.d 1 2) (by simp) with h3709 | h3709
                                    · linarith only [h0, h3709, hlam]
                                    · linarith only [h3696, h3709, hlam]
                                  · linarith only [h3708, hlam, p3703_0]
                                · have p3703_0 := h3703c.1
                                  have p3703_1 := h3703c.2.1
                                  have p3703_2 := h3703c.2.2.1
                                  have p3703_3 := h3703c.2.2.2
                                  linarith only [h0, hlam, p3703_0]
                                · have p3703_0 := h3703c.1
                                  have p3703_1 := h3703c.2.1
                                  have p3703_2 := h3703c.2.2.1
                                  have p3703_3 := h3703c.2.2.2
                                  linarith only [hlam, p3703_0]
                                · have p3703_0 := h3703c.1
                                  have p3703_1 := h3703c.2.1
                                  have p3703_2 := h3703c.2.2.1
                                  have p3703_3 := h3703c.2.2.2
                                  linarith only [h3692, hlam, p3703_0]
                                · have p3703_0 := h3703c.1
                                  have p3703_1 := h3703c.2.1
                                  have p3703_2 := h3703c.2.2.1
                                  have p3703_3 := h3703c.2.2.2
                                  linarith only [h3694, hlam, p3703_0]
                                · have p3703_0 := h3703c.1
                                  have p3703_1 := h3703c.2.1
                                  have p3703_2 := h3703c.2.2.1
                                  have p3703_3 := h3703c.2.2.2
                                  linarith only [h0, h1, h3692, h3700, h3702, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3703_1]
                                · have p3703_0 := h3703c.1
                                  have p3703_1 := h3703c.2.1
                                  have p3703_2 := h3703c.2.2.1
                                  have p3703_3 := h3703c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht01, ht12, p3703_1, u0ehi1]
                                · have p3703_0 := h3703c.1
                                  have p3703_1 := h3703c.2.1
                                  have p3703_2 := h3703c.2.2.1
                                  have p3703_3 := h3703c.2.2.2
                                  rcases p3703_3 (m.d 0 2) (by simp) with h3719 | h3719
                                  · linarith only [h3565, h3719, hlam]
                                  · linarith only [h0, h3719, hlam]
                                · have p3703_0 := h3703c.1
                                  have p3703_1 := h3703c.2.1
                                  have p3703_2 := h3703c.2.2.1
                                  have p3703_3 := h3703c.2.2.2
                                  linarith only [hlam, p3703_0]
                                · have p3703_0 := h3703c.1
                                  have p3703_1 := h3703c.2.1
                                  have p3703_2 := h3703c.2.2.1
                                  have p3703_3 := h3703c.2.2.2
                                  linarith only [h3567, h3689, hc23, hlam, hphi, ht01, ht12, p3703_1, u0ehi4]
                                · have p3703_0 := h3703c.1
                                  have p3703_1 := h3703c.2.1
                                  have p3703_2 := h3703c.2.2.1
                                  have p3703_3 := h3703c.2.2.2
                                  linarith only [h0, h1, h3692, h3696, hlam, p3703_2]
                                · have p3703_0 := h3703c.1
                                  have p3703_1 := h3703c.2.1
                                  have p3703_2 := h3703c.2.2.1
                                  have p3703_3 := h3703c.2.2.2
                                  linarith only [h3689, hc24, hlam, hphi, ht01, ht12, p3703_1, u0ehi4]
                                · have p3703_0 := h3703c.1
                                  have p3703_1 := h3703c.2.1
                                  have p3703_2 := h3703c.2.2.1
                                  have p3703_3 := h3703c.2.2.2
                                  rcases p3703_3 (m.d 0 2) (by simp) with h3726 | h3726
                                  · linarith only [h3567, h3726, hlam]
                                  · linarith only [h0, h3726, hlam]
                                · have p3703_0 := h3703c.1
                                  have p3703_1 := h3703c.2.1
                                  have p3703_2 := h3703c.2.2.1
                                  have p3703_3 := h3703c.2.2.2
                                  linarith only [h3699, hlam, p3703_1]
                                · have p3703_0 := h3703c.1
                                  have p3703_1 := h3703c.2.1
                                  have p3703_2 := h3703c.2.2.1
                                  have p3703_3 := h3703c.2.2.2
                                  linarith only [hlam, p3703_0]
                                · have p3703_0 := h3703c.1
                                  have p3703_1 := h3703c.2.1
                                  have p3703_2 := h3703c.2.2.1
                                  have p3703_3 := h3703c.2.2.2
                                  rcases p3703_3 (m.d 0 2) (by simp) with h3731 | h3731
                                  · linarith only [h3567, h3731, hlam]
                                  · linarith only [h3689, h3731, hlam]
                                · have p3703_0 := h3703c.1
                                  have p3703_1 := h3703c.2.1
                                  have p3703_2 := h3703c.2.2.1
                                  have p3703_3 := h3703c.2.2.2
                                  linarith only [h3689, hlam, p3703_0]
                                · have p3703_0 := h3703c.1
                                  have p3703_1 := h3703c.2.1
                                  have p3703_2 := h3703c.2.2.1
                                  have p3703_3 := h3703c.2.2.2
                                  linarith only [h3696, hlam, p3703_0]
                                · have p3703_0 := h3703c.1
                                  have p3703_1 := h3703c.2.1
                                  have p3703_2 := h3703c.2.2.1
                                  have p3703_3 := h3703c.2.2.2
                                  linarith only [h3700, hlam, p3703_1]
                                · have p3703_0 := h3703c.1
                                  have p3703_1 := h3703c.2.1
                                  have p3703_2 := h3703c.2.2.1
                                  have p3703_3 := h3703c.2.2.2
                                  linarith only [h3701, hlam, p3703_0]
                                · have p3703_0 := h3703c.1
                                  have p3703_1 := h3703c.2.1
                                  have p3703_2 := h3703c.2.2.1
                                  have p3703_3 := h3703c.2.2.2
                                  linarith only [hlam, p3703_0]
                              · linarith only [h0, h1, h3692, h3696, h3701, h3702, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h3567, h3689, h3701, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi4]
                          · linarith only [h0, h1, h3692, h3700, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h3692, h3699, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h1, h3689, h3698, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi4]
                    · linarith only [h0, h1, h3689, h3690, h3697, hc03, hlam, hphi, u0ehi4]
                  · linarith only [h3567, h3689, h3696, hc12, hc24, hlam, hphi]
            · linarith only [h0, h1, h3689, h3691, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3747 | h3747
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3748 | h3748
              · linarith only [h0, h1, h3690, h3748, hc23, hc34, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3750 | h3750
                · linarith only [h0, h1, h3567, h3690, h3750, hc02, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3752 | h3752
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3753 | h3753
                    · linarith only [h0, h1, h3690, h3748, h3753, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h3689, h3753, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi4]
                  · linarith only [h3567, h3689, h3752, hc12, hc24, hlam, hphi]
            · linarith only [h0, h1, h3689, h3747, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3758 | h3758
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3759 | h3759
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3760 | h3760
              · linarith only [h0, h3565, h3760, hc01, hlam, hphi, u0ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3762 | h3762
                · linarith only [h0, h1, h3567, h3760, h3762, hc02, hc23, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3764 | h3764
                  · linarith only [h0, h1, h3689, h3760, h3764, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3766 | h3766
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3767 | h3767
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3768 | h3768
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3769 | h3769
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3770 | h3770
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3771 | h3771
                              · rcases h2bigk with h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c | h3772c
                                · have p3772_0 := h3772c.1
                                  have p3772_1 := h3772c.2.1
                                  have p3772_2 := h3772c.2.2.1
                                  have p3772_3 := h3772c.2.2.2
                                  linarith only [hlam, p3772_0]
                                · have p3772_0 := h3772c.1
                                  have p3772_1 := h3772c.2.1
                                  have p3772_2 := h3772c.2.2.1
                                  have p3772_3 := h3772c.2.2.2
                                  linarith only [h3689, h3770, hc12, hc24, hlam, hphi, p3772_1]
                                · have p3772_0 := h3772c.1
                                  have p3772_1 := h3772c.2.1
                                  have p3772_2 := h3772c.2.2.1
                                  have p3772_3 := h3772c.2.2.2
                                  linarith only [h3565, hlam, p3772_0]
                                · have p3772_0 := h3772c.1
                                  have p3772_1 := h3772c.2.1
                                  have p3772_2 := h3772c.2.2.1
                                  have p3772_3 := h3772c.2.2.2
                                  linarith only [h3567, hlam, p3772_0]
                                · have p3772_0 := h3772c.1
                                  have p3772_1 := h3772c.2.1
                                  have p3772_2 := h3772c.2.2.1
                                  have p3772_3 := h3772c.2.2.2
                                  linarith only [h3689, hlam, p3772_0]
                                · have p3772_0 := h3772c.1
                                  have p3772_1 := h3772c.2.1
                                  have p3772_2 := h3772c.2.2.1
                                  have p3772_3 := h3772c.2.2.2
                                  linarith only [h0, hlam, p3772_0]
                                · have p3772_0 := h3772c.1
                                  have p3772_1 := h3772c.2.1
                                  have p3772_2 := h3772c.2.2.1
                                  have p3772_3 := h3772c.2.2.2
                                  linarith only [hlam, p3772_0]
                                · have p3772_0 := h3772c.1
                                  have p3772_1 := h3772c.2.1
                                  have p3772_2 := h3772c.2.2.1
                                  have p3772_3 := h3772c.2.2.2
                                  linarith only [h3760, hlam, p3772_0]
                                · have p3772_0 := h3772c.1
                                  have p3772_1 := h3772c.2.1
                                  have p3772_2 := h3772c.2.2.1
                                  have p3772_3 := h3772c.2.2.2
                                  linarith only [h3762, hlam, p3772_0]
                                · have p3772_0 := h3772c.1
                                  have p3772_1 := h3772c.2.1
                                  have p3772_2 := h3772c.2.2.1
                                  have p3772_3 := h3772c.2.2.2
                                  linarith only [h3764, hlam, p3772_0]
                                · have p3772_0 := h3772c.1
                                  have p3772_1 := h3772c.2.1
                                  have p3772_2 := h3772c.2.2.1
                                  have p3772_3 := h3772c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht01, ht12, p3772_1, u0ehi1]
                                · have p3772_0 := h3772c.1
                                  have p3772_1 := h3772c.2.1
                                  have p3772_2 := h3772c.2.2.1
                                  have p3772_3 := h3772c.2.2.2
                                  rcases p3772_3 (m.d 0 2) (by simp) with h3784 | h3784
                                  · linarith only [h3565, h3784, hlam]
                                  · linarith only [h0, h3784, hlam]
                                · have p3772_0 := h3772c.1
                                  have p3772_1 := h3772c.2.1
                                  have p3772_2 := h3772c.2.2.1
                                  have p3772_3 := h3772c.2.2.2
                                  linarith only [hlam, p3772_0]
                                · have p3772_0 := h3772c.1
                                  have p3772_1 := h3772c.2.1
                                  have p3772_2 := h3772c.2.2.1
                                  have p3772_3 := h3772c.2.2.2
                                  linarith only [h3567, hc23, hlam, hphi, ht01, ht12, p3772_1, u0ehi1]
                                · have p3772_0 := h3772c.1
                                  have p3772_1 := h3772c.2.1
                                  have p3772_2 := h3772c.2.2.1
                                  have p3772_3 := h3772c.2.2.2
                                  linarith only [h3689, hc23, hlam, hphi, ht01, ht12, p3772_1, u0ehi1]
                                · have p3772_0 := h3772c.1
                                  have p3772_1 := h3772c.2.1
                                  have p3772_2 := h3772c.2.2.1
                                  have p3772_3 := h3772c.2.2.2
                                  linarith only [hc24, hlam, hphi, ht01, ht12, p3772_1, u0ehi1]
                                · have p3772_0 := h3772c.1
                                  have p3772_1 := h3772c.2.1
                                  have p3772_2 := h3772c.2.2.1
                                  have p3772_3 := h3772c.2.2.2
                                  rcases p3772_3 (m.d 0 2) (by simp) with h3791 | h3791
                                  · linarith only [h3567, h3791, hlam]
                                  · linarith only [h0, h3791, hlam]
                                · have p3772_0 := h3772c.1
                                  have p3772_1 := h3772c.2.1
                                  have p3772_2 := h3772c.2.2.1
                                  have p3772_3 := h3772c.2.2.2
                                  linarith only [h3768, hlam, p3772_1]
                                · have p3772_0 := h3772c.1
                                  have p3772_1 := h3772c.2.1
                                  have p3772_2 := h3772c.2.2.1
                                  have p3772_3 := h3772c.2.2.2
                                  linarith only [hlam, p3772_0]
                                · have p3772_0 := h3772c.1
                                  have p3772_1 := h3772c.2.1
                                  have p3772_2 := h3772c.2.2.1
                                  have p3772_3 := h3772c.2.2.2
                                  linarith only [h3689, h3768, hc23, hlam, hphi, ht01, ht12, p3772_1, u0ehi1]
                                · have p3772_0 := h3772c.1
                                  have p3772_1 := h3772c.2.1
                                  have p3772_2 := h3772c.2.2.1
                                  have p3772_3 := h3772c.2.2.2
                                  linarith only [hc25, hlam, hphi, ht01, ht12, p3772_1, u0ehi1]
                                · have p3772_0 := h3772c.1
                                  have p3772_1 := h3772c.2.1
                                  have p3772_2 := h3772c.2.2.1
                                  have p3772_3 := h3772c.2.2.2
                                  rcases p3772_3 (m.d 0 2) (by simp) with h3798 | h3798
                                  · linarith only [h3689, h3798, hlam]
                                  · linarith only [h0, h3798, hlam]
                                · have p3772_0 := h3772c.1
                                  have p3772_1 := h3772c.2.1
                                  have p3772_2 := h3772c.2.2.1
                                  have p3772_3 := h3772c.2.2.2
                                  linarith only [h3769, hlam, p3772_1]
                                · have p3772_0 := h3772c.1
                                  have p3772_1 := h3772c.2.1
                                  have p3772_2 := h3772c.2.2.1
                                  have p3772_3 := h3772c.2.2.2
                                  linarith only [h3770, hlam, p3772_0]
                                · have p3772_0 := h3772c.1
                                  have p3772_1 := h3772c.2.1
                                  have p3772_2 := h3772c.2.2.1
                                  have p3772_3 := h3772c.2.2.2
                                  linarith only [hlam, p3772_0]
                              · rcases h2bigk with h3804c | h3804c | h3804c | h3804c | h3804c | h3804c | h3804c | h3804c | h3804c | h3804c | h3804c | h3804c | h3804c | h3804c | h3804c | h3804c | h3804c | h3804c | h3804c | h3804c | h3804c | h3804c | h3804c | h3804c | h3804c
                                · have p3804_0 := h3804c.1
                                  have p3804_1 := h3804c.2.1
                                  have p3804_2 := h3804c.2.2.1
                                  have p3804_3 := h3804c.2.2.2
                                  linarith only [hlam, p3804_0]
                                · have p3804_0 := h3804c.1
                                  have p3804_1 := h3804c.2.1
                                  have p3804_2 := h3804c.2.2.1
                                  have p3804_3 := h3804c.2.2.2
                                  linarith only [h0, h1, h3760, hc12, hc23, hlam, hphi, p3804_1]
                                · have p3804_0 := h3804c.1
                                  have p3804_1 := h3804c.2.1
                                  have p3804_2 := h3804c.2.2.1
                                  have p3804_3 := h3804c.2.2.2
                                  linarith only [h3565, hlam, p3804_0]
                                · have p3804_0 := h3804c.1
                                  have p3804_1 := h3804c.2.1
                                  have p3804_2 := h3804c.2.2.1
                                  have p3804_3 := h3804c.2.2.2
                                  linarith only [h3567, hlam, p3804_0]
                                · have p3804_0 := h3804c.1
                                  have p3804_1 := h3804c.2.1
                                  have p3804_2 := h3804c.2.2.1
                                  have p3804_3 := h3804c.2.2.2
                                  linarith only [h3689, hlam, p3804_0]
                                · have p3804_0 := h3804c.1
                                  have p3804_1 := h3804c.2.1
                                  have p3804_2 := h3804c.2.2.1
                                  have p3804_3 := h3804c.2.2.2
                                  linarith only [h0, hlam, p3804_0]
                                · have p3804_0 := h3804c.1
                                  have p3804_1 := h3804c.2.1
                                  have p3804_2 := h3804c.2.2.1
                                  have p3804_3 := h3804c.2.2.2
                                  linarith only [hlam, p3804_0]
                                · have p3804_0 := h3804c.1
                                  have p3804_1 := h3804c.2.1
                                  have p3804_2 := h3804c.2.2.1
                                  have p3804_3 := h3804c.2.2.2
                                  linarith only [h3760, hlam, p3804_0]
                                · have p3804_0 := h3804c.1
                                  have p3804_1 := h3804c.2.1
                                  have p3804_2 := h3804c.2.2.1
                                  have p3804_3 := h3804c.2.2.2
                                  linarith only [h3762, hlam, p3804_0]
                                · have p3804_0 := h3804c.1
                                  have p3804_1 := h3804c.2.1
                                  have p3804_2 := h3804c.2.2.1
                                  have p3804_3 := h3804c.2.2.2
                                  linarith only [h3764, hlam, p3804_0]
                                · have p3804_0 := h3804c.1
                                  have p3804_1 := h3804c.2.1
                                  have p3804_2 := h3804c.2.2.1
                                  have p3804_3 := h3804c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht01, ht12, p3804_1, u0ehi1]
                                · have p3804_0 := h3804c.1
                                  have p3804_1 := h3804c.2.1
                                  have p3804_2 := h3804c.2.2.1
                                  have p3804_3 := h3804c.2.2.2
                                  rcases p3804_3 (m.d 0 2) (by simp) with h3816 | h3816
                                  · linarith only [h3565, h3816, hlam]
                                  · linarith only [h0, h3816, hlam]
                                · have p3804_0 := h3804c.1
                                  have p3804_1 := h3804c.2.1
                                  have p3804_2 := h3804c.2.2.1
                                  have p3804_3 := h3804c.2.2.2
                                  linarith only [hlam, p3804_0]
                                · have p3804_0 := h3804c.1
                                  have p3804_1 := h3804c.2.1
                                  have p3804_2 := h3804c.2.2.1
                                  have p3804_3 := h3804c.2.2.2
                                  linarith only [h3567, hc23, hlam, hphi, ht01, ht12, p3804_1, u0ehi1]
                                · have p3804_0 := h3804c.1
                                  have p3804_1 := h3804c.2.1
                                  have p3804_2 := h3804c.2.2.1
                                  have p3804_3 := h3804c.2.2.2
                                  linarith only [h3689, hc23, hlam, hphi, ht01, ht12, p3804_1, u0ehi1]
                                · have p3804_0 := h3804c.1
                                  have p3804_1 := h3804c.2.1
                                  have p3804_2 := h3804c.2.2.1
                                  have p3804_3 := h3804c.2.2.2
                                  linarith only [hc24, hlam, hphi, ht01, ht12, p3804_1, u0ehi1]
                                · have p3804_0 := h3804c.1
                                  have p3804_1 := h3804c.2.1
                                  have p3804_2 := h3804c.2.2.1
                                  have p3804_3 := h3804c.2.2.2
                                  rcases p3804_3 (m.d 0 2) (by simp) with h3823 | h3823
                                  · linarith only [h3567, h3823, hlam]
                                  · linarith only [h0, h3823, hlam]
                                · have p3804_0 := h3804c.1
                                  have p3804_1 := h3804c.2.1
                                  have p3804_2 := h3804c.2.2.1
                                  have p3804_3 := h3804c.2.2.2
                                  linarith only [h3768, hlam, p3804_1]
                                · have p3804_0 := h3804c.1
                                  have p3804_1 := h3804c.2.1
                                  have p3804_2 := h3804c.2.2.1
                                  have p3804_3 := h3804c.2.2.2
                                  linarith only [hlam, p3804_0]
                                · have p3804_0 := h3804c.1
                                  have p3804_1 := h3804c.2.1
                                  have p3804_2 := h3804c.2.2.1
                                  have p3804_3 := h3804c.2.2.2
                                  linarith only [h3689, h3768, hc23, hlam, hphi, ht01, ht12, p3804_1, u0ehi1]
                                · have p3804_0 := h3804c.1
                                  have p3804_1 := h3804c.2.1
                                  have p3804_2 := h3804c.2.2.1
                                  have p3804_3 := h3804c.2.2.2
                                  linarith only [hc25, hlam, hphi, ht01, ht12, p3804_1, u0ehi1]
                                · have p3804_0 := h3804c.1
                                  have p3804_1 := h3804c.2.1
                                  have p3804_2 := h3804c.2.2.1
                                  have p3804_3 := h3804c.2.2.2
                                  rcases p3804_3 (m.d 0 2) (by simp) with h3830 | h3830
                                  · linarith only [h3689, h3830, hlam]
                                  · linarith only [h0, h3830, hlam]
                                · have p3804_0 := h3804c.1
                                  have p3804_1 := h3804c.2.1
                                  have p3804_2 := h3804c.2.2.1
                                  have p3804_3 := h3804c.2.2.2
                                  linarith only [h3769, hlam, p3804_1]
                                · have p3804_0 := h3804c.1
                                  have p3804_1 := h3804c.2.1
                                  have p3804_2 := h3804c.2.2.1
                                  have p3804_3 := h3804c.2.2.2
                                  linarith only [h3770, hlam, p3804_0]
                                · have p3804_0 := h3804c.1
                                  have p3804_1 := h3804c.2.1
                                  have p3804_2 := h3804c.2.2.1
                                  have p3804_3 := h3804c.2.2.2
                                  linarith only [hlam, p3804_0]
                            · linarith only [h3567, h3770, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                          · linarith only [h1, h3760, h3769, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                        · linarith only [h1, h3760, h3768, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                      · linarith only [h0, h1, h3759, h3767, hc05, hlam, hphi, u0ehi1]
                    · linarith only [h0, h1, h3766, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3841 | h3841
              · linarith only [h0, h1, h3759, h3841, hc23, hc35, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3843 | h3843
                · linarith only [h0, h1, h3567, h3759, h3843, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3845 | h3845
                  · linarith only [h0, h1, h3689, h3759, h3845, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3847 | h3847
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h3848 | h3848
                      · linarith only [h0, h1, h3759, h3841, h3848, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h3848, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                    · linarith only [h0, h1, h3758, h3847, hc03, hlam, hphi, u0ehi1]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3852 | h3852
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3853 | h3853
              · linarith only [h0, h1, h3758, h3853, hc23, hc34, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3855 | h3855
                · linarith only [h0, h1, h3567, h3758, h3855, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3857 | h3857
                  · linarith only [h0, h1, h3689, h3758, h3857, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3859 | h3859
                    · linarith only [h0, h1, h3758, h3853, h3859, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h3859, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3862 | h3862
              · linarith only [h0, h1, h3852, h3862, hc23, hc35, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3864 | h3864
                · linarith only [h0, h1, h3567, h3852, h3864, hc02, hc35, hlam, hphi, ht23]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3866 | h3866
                  · linarith only [h0, h1, h3689, h3852, h3866, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3868 | h3868
                    · linarith only [h0, h1, h3758, h3862, h3868, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h3868, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]

set_option maxHeartbeats 11532000 in
set_option maxHeartbeats 11532000 in
theorem r1l7_10_12_23_L_R_L_I_H_I_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  exact r1l7_10_12_23_L_R_L_I_H_I_s0 m hb0 hb2 hb3 h0

end R2N4
