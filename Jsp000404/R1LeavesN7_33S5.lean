import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_33S3
import Jsp000404.R1LeavesN7_33S4

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8870000 in
theorem r1l7_11_13_25_L_I_L_R_H_I_x1_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2319 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2512 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2736 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2841 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h3585 | h3585
  · rcases m.htr 0 3 4 (by decide) (by decide) with h3586 | h3586
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3587 | h3587
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3588 | h3588
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3589 | h3589
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3590 | h3590
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3591 | h3591
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3592 | h3592
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3593 | h3593
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3594 | h3594
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3595 | h3595
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3596 | h3596
                        · linarith only [h2841, h3585, h3589, h3596, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                        · linarith only [h2841, h3586, h3596, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h2841, h3585, h3586, h3587, h3595, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · linarith only [h2512, h3588, h3594, hlam]
                  · linarith only [h2841, h3585, h3587, h3589, h3593, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h2841, h3586, h3589, h3592, hlam]
              · linarith only [h2841, h3585, h3589, h3591, hlam]
            · linarith only [h2841, h3589, h3590, hc02, hc24, hlam, hphi]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3605 | h3605
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3606 | h3606
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3607 | h3607
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3608 | h3608
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3609 | h3609
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3610 | h3610
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3611 | h3611
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3612 | h3612
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3613 | h3613
                            · rcases h1bigk with h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c | h3614c
                              · have p3614_0 := h3614c.1
                                have p3614_1 := h3614c.2.1
                                have p3614_2 := h3614c.2.2.1
                                have p3614_3 := h3614c.2.2.2
                                linarith only [hlam, p3614_0]
                              · have p3614_0 := h3614c.1
                                have p3614_1 := h3614c.2.1
                                have p3614_2 := h3614c.2.2.1
                                have p3614_3 := h3614c.2.2.2
                                linarith only [h0, hlam, p3614_0]
                              · have p3614_0 := h3614c.1
                                have p3614_1 := h3614c.2.1
                                have p3614_2 := h3614c.2.2.1
                                have p3614_3 := h3614c.2.2.2
                                linarith only [h2319, hlam, p3614_0]
                              · have p3614_0 := h3614c.1
                                have p3614_1 := h3614c.2.1
                                have p3614_2 := h3614c.2.2.1
                                have p3614_3 := h3614c.2.2.2
                                linarith only [h2512, hlam, p3614_0]
                              · have p3614_0 := h3614c.1
                                have p3614_1 := h3614c.2.1
                                have p3614_2 := h3614c.2.2.1
                                have p3614_3 := h3614c.2.2.2
                                linarith only [h2736, hlam, p3614_0]
                              · have p3614_0 := h3614c.1
                                have p3614_1 := h3614c.2.1
                                have p3614_2 := h3614c.2.2.1
                                have p3614_3 := h3614c.2.2.2
                                linarith only [h3589, hc01, hc23, hlam, hphi, ht12, p3614_1]
                              · have p3614_0 := h3614c.1
                                have p3614_1 := h3614c.2.1
                                have p3614_2 := h3614c.2.2.1
                                have p3614_3 := h3614c.2.2.2
                                linarith only [hlam, p3614_0]
                              · have p3614_0 := h3614c.1
                                have p3614_1 := h3614c.2.1
                                have p3614_2 := h3614c.2.2.1
                                have p3614_3 := h3614c.2.2.2
                                linarith only [h3589, hlam, p3614_0]
                              · have p3614_0 := h3614c.1
                                have p3614_1 := h3614c.2.1
                                have p3614_2 := h3614c.2.2.1
                                have p3614_3 := h3614c.2.2.2
                                linarith only [h2512, h3589, hc01, hc23, hlam, hphi, ht12, p3614_1]
                              · have p3614_0 := h3614c.1
                                have p3614_1 := h3614c.2.1
                                have p3614_2 := h3614c.2.2.1
                                have p3614_3 := h3614c.2.2.2
                                linarith only [h2736, h3589, hc01, hc23, hlam, hphi, ht12, p3614_1]
                              · have p3614_0 := h3614c.1
                                have p3614_1 := h3614c.2.1
                                have p3614_2 := h3614c.2.2.1
                                have p3614_3 := h3614c.2.2.2
                                rcases p3614_3 (m.d 0 1) (by simp) with h3625 | h3625
                                · linarith only [h3625, hlam, p3614_0]
                                · rcases p3614_3 (m.d 1 2) (by simp) with h3627 | h3627
                                  · linarith only [h3589, h3627, hlam]
                                  · linarith only [h0, h3627, hlam]
                              · have p3614_0 := h3614c.1
                                have p3614_1 := h3614c.2.1
                                have p3614_2 := h3614c.2.2.1
                                have p3614_3 := h3614c.2.2.2
                                linarith only [h0, hc01, hc13, hlam, hphi, p3614_1]
                              · have p3614_0 := h3614c.1
                                have p3614_1 := h3614c.2.1
                                have p3614_2 := h3614c.2.2.1
                                have p3614_3 := h3614c.2.2.2
                                linarith only [hlam, p3614_0]
                              · have p3614_0 := h3614c.1
                                have p3614_1 := h3614c.2.1
                                have p3614_2 := h3614c.2.2.1
                                have p3614_3 := h3614c.2.2.2
                                linarith only [h2736, h3589, h3609, hc01, hc23, hlam, hphi, ht12, p3614_1]
                              · have p3614_0 := h3614c.1
                                have p3614_1 := h3614c.2.1
                                have p3614_2 := h3614c.2.2.1
                                have p3614_3 := h3614c.2.2.2
                                linarith only [h2736, h3589, hc01, hc23, hlam, hphi, ht12, p3614_1]
                              · have p3614_0 := h3614c.1
                                have p3614_1 := h3614c.2.1
                                have p3614_2 := h3614c.2.2.1
                                have p3614_3 := h3614c.2.2.2
                                linarith only [h3589, h3605, hc01, hc23, hlam, hphi, ht12, p3614_1]
                              · have p3614_0 := h3614c.1
                                have p3614_1 := h3614c.2.1
                                have p3614_2 := h3614c.2.2.1
                                have p3614_3 := h3614c.2.2.2
                                linarith only [h3605, hlam, p3614_1]
                              · have p3614_0 := h3614c.1
                                have p3614_1 := h3614c.2.1
                                have p3614_2 := h3614c.2.2.1
                                have p3614_3 := h3614c.2.2.2
                                linarith only [h3607, hlam, p3614_0]
                              · have p3614_0 := h3614c.1
                                have p3614_1 := h3614c.2.1
                                have p3614_2 := h3614c.2.2.1
                                have p3614_3 := h3614c.2.2.2
                                linarith only [hlam, p3614_0]
                              · have p3614_0 := h3614c.1
                                have p3614_1 := h3614c.2.1
                                have p3614_2 := h3614c.2.2.1
                                have p3614_3 := h3614c.2.2.2
                                linarith only [h2736, h3589, h3605, hc01, hc23, hlam, hphi, ht12, p3614_1]
                              · have p3614_0 := h3614c.1
                                have p3614_1 := h3614c.2.1
                                have p3614_2 := h3614c.2.2.1
                                have p3614_3 := h3614c.2.2.2
                                linarith only [h3589, h3606, hc01, hc23, hlam, hphi, ht12, p3614_1]
                              · have p3614_0 := h3614c.1
                                have p3614_1 := h3614c.2.1
                                have p3614_2 := h3614c.2.2.1
                                have p3614_3 := h3614c.2.2.2
                                linarith only [h3606, hlam, p3614_1]
                              · have p3614_0 := h3614c.1
                                have p3614_1 := h3614c.2.1
                                have p3614_2 := h3614c.2.2.1
                                have p3614_3 := h3614c.2.2.2
                                linarith only [h3608, hlam, p3614_0]
                              · have p3614_0 := h3614c.1
                                have p3614_1 := h3614c.2.1
                                have p3614_2 := h3614c.2.2.1
                                have p3614_3 := h3614c.2.2.2
                                linarith only [h3609, hlam, p3614_0]
                              · have p3614_0 := h3614c.1
                                have p3614_1 := h3614c.2.1
                                have p3614_2 := h3614c.2.2.1
                                have p3614_3 := h3614c.2.2.2
                                linarith only [hlam, p3614_0]
                            · linarith only [h2512, h3588, h3589, h3605, h3613, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h2512, h3588, h3589, h3605, h3610, h3612, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h3589, h3611, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h2736, h3586, h3589, h3605, h3609, h3610, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                    · linarith only [h2512, h3588, h3609, hlam]
                  · linarith only [h0, h2319, h3585, h3587, h3589, h3608, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h2319, h3586, h3607, hlam]
              · linarith only [h0, h3585, h3606, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3652 | h3652
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3653 | h3653
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3654 | h3654
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3655 | h3655
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3656 | h3656
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3657 | h3657
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3658 | h3658
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3659 | h3659
                            · rcases h1bigk with h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c | h3660c
                              · have p3660_0 := h3660c.1
                                have p3660_1 := h3660c.2.1
                                have p3660_2 := h3660c.2.2.1
                                have p3660_3 := h3660c.2.2.2
                                linarith only [hlam, p3660_0]
                              · have p3660_0 := h3660c.1
                                have p3660_1 := h3660c.2.1
                                have p3660_2 := h3660c.2.2.1
                                have p3660_3 := h3660c.2.2.2
                                linarith only [h0, hlam, p3660_0]
                              · have p3660_0 := h3660c.1
                                have p3660_1 := h3660c.2.1
                                have p3660_2 := h3660c.2.2.1
                                have p3660_3 := h3660c.2.2.2
                                linarith only [h2319, hlam, p3660_0]
                              · have p3660_0 := h3660c.1
                                have p3660_1 := h3660c.2.1
                                have p3660_2 := h3660c.2.2.1
                                have p3660_3 := h3660c.2.2.2
                                linarith only [h2512, hlam, p3660_0]
                              · have p3660_0 := h3660c.1
                                have p3660_1 := h3660c.2.1
                                have p3660_2 := h3660c.2.2.1
                                have p3660_3 := h3660c.2.2.2
                                linarith only [h2736, hlam, p3660_0]
                              · have p3660_0 := h3660c.1
                                have p3660_1 := h3660c.2.1
                                have p3660_2 := h3660c.2.2.1
                                have p3660_3 := h3660c.2.2.2
                                linarith only [h3605, h3656, hc01, hc23, hlam, hphi, ht12, p3660_1]
                              · have p3660_0 := h3660c.1
                                have p3660_1 := h3660c.2.1
                                have p3660_2 := h3660c.2.2.1
                                have p3660_3 := h3660c.2.2.2
                                linarith only [hlam, p3660_0]
                              · have p3660_0 := h3660c.1
                                have p3660_1 := h3660c.2.1
                                have p3660_2 := h3660c.2.2.1
                                have p3660_3 := h3660c.2.2.2
                                linarith only [h3589, hlam, p3660_0]
                              · have p3660_0 := h3660c.1
                                have p3660_1 := h3660c.2.1
                                have p3660_2 := h3660c.2.2.1
                                have p3660_3 := h3660c.2.2.2
                                linarith only [h3605, hlam, p3660_0]
                              · have p3660_0 := h3660c.1
                                have p3660_1 := h3660c.2.1
                                have p3660_2 := h3660c.2.2.1
                                have p3660_3 := h3660c.2.2.2
                                linarith only [h2736, h3605, h3656, hc01, hc23, hlam, hphi, ht12, p3660_1]
                              · have p3660_0 := h3660c.1
                                have p3660_1 := h3660c.2.1
                                have p3660_2 := h3660c.2.2.1
                                have p3660_3 := h3660c.2.2.2
                                rcases p3660_3 (m.d 0 1) (by simp) with h3671 | h3671
                                · linarith only [h3671, hlam, p3660_0]
                                · rcases p3660_3 (m.d 1 2) (by simp) with h3673 | h3673
                                  · linarith only [h3589, h3673, hlam]
                                  · linarith only [h0, h3673, hlam]
                              · have p3660_0 := h3660c.1
                                have p3660_1 := h3660c.2.1
                                have p3660_2 := h3660c.2.2.1
                                have p3660_3 := h3660c.2.2.2
                                linarith only [h0, h3585, h3657, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3660_1, u3ehi4]
                              · have p3660_0 := h3660c.1
                                have p3660_1 := h3660c.2.1
                                have p3660_2 := h3660c.2.2.1
                                have p3660_3 := h3660c.2.2.2
                                linarith only [hlam, p3660_0]
                              · have p3660_0 := h3660c.1
                                have p3660_1 := h3660c.2.1
                                have p3660_2 := h3660c.2.2.1
                                have p3660_3 := h3660c.2.2.2
                                linarith only [h0, h3585, h3589, h3605, h3657, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3660_1, u3ehi4]
                              · have p3660_0 := h3660c.1
                                have p3660_1 := h3660c.2.1
                                have p3660_2 := h3660c.2.2.1
                                have p3660_3 := h3660c.2.2.2
                                linarith only [h2736, h3589, hc01, hc23, hlam, hphi, ht12, p3660_1]
                              · have p3660_0 := h3660c.1
                                have p3660_1 := h3660c.2.1
                                have p3660_2 := h3660c.2.2.1
                                have p3660_3 := h3660c.2.2.2
                                rcases p3660_3 (m.d 0 1) (by simp) with h3680 | h3680
                                · linarith only [h3680, hlam, p3660_0]
                                · rcases p3660_3 (m.d 1 2) (by simp) with h3682 | h3682
                                  · linarith only [h3605, h3682, hlam]
                                  · linarith only [h0, h3682, hlam]
                              · have p3660_0 := h3660c.1
                                have p3660_1 := h3660c.2.1
                                have p3660_2 := h3660c.2.2.1
                                have p3660_3 := h3660c.2.2.2
                                linarith only [h0, h3585, h3657, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3660_1, u3ehi4]
                              · have p3660_0 := h3660c.1
                                have p3660_1 := h3660c.2.1
                                have p3660_2 := h3660c.2.2.1
                                have p3660_3 := h3660c.2.2.2
                                linarith only [h3653, hlam, p3660_0]
                              · have p3660_0 := h3660c.1
                                have p3660_1 := h3660c.2.1
                                have p3660_2 := h3660c.2.2.1
                                have p3660_3 := h3660c.2.2.2
                                linarith only [hlam, p3660_0]
                              · have p3660_0 := h3660c.1
                                have p3660_1 := h3660c.2.1
                                have p3660_2 := h3660c.2.2.1
                                have p3660_3 := h3660c.2.2.2
                                linarith only [h2736, h3589, h3653, hc01, hc23, hlam, hphi, ht12, p3660_1]
                              · have p3660_0 := h3660c.1
                                have p3660_1 := h3660c.2.1
                                have p3660_2 := h3660c.2.2.1
                                have p3660_3 := h3660c.2.2.2
                                linarith only [h3589, h3652, hc01, hc23, hlam, hphi, ht12, p3660_1]
                              · have p3660_0 := h3660c.1
                                have p3660_1 := h3660c.2.1
                                have p3660_2 := h3660c.2.2.1
                                have p3660_3 := h3660c.2.2.2
                                linarith only [h3652, hlam, p3660_1]
                              · have p3660_0 := h3660c.1
                                have p3660_1 := h3660c.2.1
                                have p3660_2 := h3660c.2.2.1
                                have p3660_3 := h3660c.2.2.2
                                linarith only [h3654, hlam, p3660_0]
                              · have p3660_0 := h3660c.1
                                have p3660_1 := h3660c.2.1
                                have p3660_2 := h3660c.2.2.1
                                have p3660_3 := h3660c.2.2.2
                                linarith only [h3655, hlam, p3660_0]
                              · have p3660_0 := h3660c.1
                                have p3660_1 := h3660c.2.1
                                have p3660_2 := h3660c.2.2.1
                                have p3660_3 := h3660c.2.2.2
                                linarith only [hlam, p3660_0]
                            · linarith only [h0, h3585, h3605, h3656, h3658, h3659, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h0, h3588, h3605, h3658, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                        · linarith only [h0, h3605, h3656, h3657, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h2319, h3586, h3589, h3656, hlam]
                    · linarith only [h2512, h2841, h3585, h3588, h3655, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h2319, h3586, h3654, hc35, hlam, hphi, u3ehi3]
                · linarith only [h2319, h3586, h3653, hlam]
              · linarith only [h0, h3585, h3652, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3702 | h3702
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3703 | h3703
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3704 | h3704
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3705 | h3705
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3706 | h3706
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3707 | h3707
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3708 | h3708
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3709 | h3709
                        · linarith only [h2841, h3585, h3702, h3709, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                        · linarith only [h2841, h3586, h3709, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h2841, h3586, h3588, h3705, h3707, h3708, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3713 | h3713
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3714 | h3714
                        · linarith only [h2841, h3585, h3702, h3714, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                        · linarith only [h2841, h3585, h3586, h3588, h3714, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h2841, h3585, h3586, h3588, h3713, hlam]
                  · linarith only [h2841, h3585, h3587, h3702, h3706, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h2841, h3585, h3586, h3588, h3702, h3705, hlam]
              · linarith only [h2841, h3702, h3704, hc02, hc25, hlam, hphi]
            · linarith only [h2841, h3585, h3586, h3588, h3702, h3703, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3722 | h3722
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3723 | h3723
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3724 | h3724
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3725 | h3725
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3726 | h3726
                    · linarith only [h3586, h3588, h3702, h3722, h3726, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3728 | h3728
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3729 | h3729
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3730 | h3730
                          · linarith only [h3702, h3722, h3726, h3730, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3732 | h3732
                            · linarith only [h2512, h3585, h3726, h3728, h3730, h3732, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                            · rcases h1bigk with h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c
                              · have p3734_0 := h3734c.1
                                have p3734_1 := h3734c.2.1
                                have p3734_2 := h3734c.2.2.1
                                have p3734_3 := h3734c.2.2.2
                                linarith only [hlam, p3734_0]
                              · have p3734_0 := h3734c.1
                                have p3734_1 := h3734c.2.1
                                have p3734_2 := h3734c.2.2.1
                                have p3734_3 := h3734c.2.2.2
                                linarith only [h0, hlam, p3734_0]
                              · have p3734_0 := h3734c.1
                                have p3734_1 := h3734c.2.1
                                have p3734_2 := h3734c.2.2.1
                                have p3734_3 := h3734c.2.2.2
                                linarith only [h2319, hlam, p3734_0]
                              · have p3734_0 := h3734c.1
                                have p3734_1 := h3734c.2.1
                                have p3734_2 := h3734c.2.2.1
                                have p3734_3 := h3734c.2.2.2
                                linarith only [h2512, hlam, p3734_0]
                              · have p3734_0 := h3734c.1
                                have p3734_1 := h3734c.2.1
                                have p3734_2 := h3734c.2.2.1
                                have p3734_3 := h3734c.2.2.2
                                linarith only [h2736, hlam, p3734_0]
                              · have p3734_0 := h3734c.1
                                have p3734_1 := h3734c.2.1
                                have p3734_2 := h3734c.2.2.1
                                have p3734_3 := h3734c.2.2.2
                                linarith only [h3702, hc01, hc23, hlam, hphi, ht12, p3734_1]
                              · have p3734_0 := h3734c.1
                                have p3734_1 := h3734c.2.1
                                have p3734_2 := h3734c.2.2.1
                                have p3734_3 := h3734c.2.2.2
                                linarith only [hlam, p3734_0]
                              · have p3734_0 := h3734c.1
                                have p3734_1 := h3734c.2.1
                                have p3734_2 := h3734c.2.2.1
                                have p3734_3 := h3734c.2.2.2
                                linarith only [h3702, hlam, p3734_0]
                              · have p3734_0 := h3734c.1
                                have p3734_1 := h3734c.2.1
                                have p3734_2 := h3734c.2.2.1
                                have p3734_3 := h3734c.2.2.2
                                linarith only [h2512, h3702, hc01, hc23, hlam, hphi, ht12, p3734_1]
                              · have p3734_0 := h3734c.1
                                have p3734_1 := h3734c.2.1
                                have p3734_2 := h3734c.2.2.1
                                have p3734_3 := h3734c.2.2.2
                                linarith only [h2736, h3702, hc01, hc23, hlam, hphi, ht12, p3734_1]
                              · have p3734_0 := h3734c.1
                                have p3734_1 := h3734c.2.1
                                have p3734_2 := h3734c.2.2.1
                                have p3734_3 := h3734c.2.2.2
                                rcases p3734_3 (m.d 0 1) (by simp) with h3745 | h3745
                                · linarith only [h3745, hlam, p3734_0]
                                · rcases p3734_3 (m.d 1 2) (by simp) with h3747 | h3747
                                  · linarith only [h3702, h3747, hlam]
                                  · linarith only [h0, h3747, hlam]
                              · have p3734_0 := h3734c.1
                                have p3734_1 := h3734c.2.1
                                have p3734_2 := h3734c.2.2.1
                                have p3734_3 := h3734c.2.2.2
                                linarith only [h0, h3585, h3702, h3728, h3730, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3734_1, u3ehi3]
                              · have p3734_0 := h3734c.1
                                have p3734_1 := h3734c.2.1
                                have p3734_2 := h3734c.2.2.1
                                have p3734_3 := h3734c.2.2.2
                                linarith only [hlam, p3734_0]
                              · have p3734_0 := h3734c.1
                                have p3734_1 := h3734c.2.1
                                have p3734_2 := h3734c.2.2.1
                                have p3734_3 := h3734c.2.2.2
                                linarith only [h2512, h3702, hc01, hc23, hlam, hphi, ht12, p3734_1]
                              · have p3734_0 := h3734c.1
                                have p3734_1 := h3734c.2.1
                                have p3734_2 := h3734c.2.2.1
                                have p3734_3 := h3734c.2.2.2
                                linarith only [h2512, h3702, h3726, hc01, hc23, hlam, hphi, ht12, p3734_1]
                              · have p3734_0 := h3734c.1
                                have p3734_1 := h3734c.2.1
                                have p3734_2 := h3734c.2.2.1
                                have p3734_3 := h3734c.2.2.2
                                linarith only [h3726, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3734_1]
                              · have p3734_0 := h3734c.1
                                have p3734_1 := h3734c.2.1
                                have p3734_2 := h3734c.2.2.1
                                have p3734_3 := h3734c.2.2.2
                                linarith only [h3722, hlam, p3734_1]
                              · have p3734_0 := h3734c.1
                                have p3734_1 := h3734c.2.1
                                have p3734_2 := h3734c.2.2.1
                                have p3734_3 := h3734c.2.2.2
                                linarith only [h3724, hlam, p3734_0]
                              · have p3734_0 := h3734c.1
                                have p3734_1 := h3734c.2.1
                                have p3734_2 := h3734c.2.2.1
                                have p3734_3 := h3734c.2.2.2
                                linarith only [hlam, p3734_0]
                              · have p3734_0 := h3734c.1
                                have p3734_1 := h3734c.2.1
                                have p3734_2 := h3734c.2.2.1
                                have p3734_3 := h3734c.2.2.2
                                linarith only [h3726, hlam, p3734_1]
                              · have p3734_0 := h3734c.1
                                have p3734_1 := h3734c.2.1
                                have p3734_2 := h3734c.2.2.1
                                have p3734_3 := h3734c.2.2.2
                                linarith only [h3702, h3723, hc01, hc23, hlam, hphi, ht12, p3734_1]
                              · have p3734_0 := h3734c.1
                                have p3734_1 := h3734c.2.1
                                have p3734_2 := h3734c.2.2.1
                                have p3734_3 := h3734c.2.2.2
                                linarith only [h3723, hlam, p3734_1]
                              · have p3734_0 := h3734c.1
                                have p3734_1 := h3734c.2.1
                                have p3734_2 := h3734c.2.2.1
                                have p3734_3 := h3734c.2.2.2
                                linarith only [h3725, hlam, p3734_0]
                              · have p3734_0 := h3734c.1
                                have p3734_1 := h3734c.2.1
                                have p3734_2 := h3734c.2.2.1
                                have p3734_3 := h3734c.2.2.2
                                linarith only [h2512, h3702, h3723, hc01, hc23, hlam, hphi, ht12, p3734_1]
                              · have p3734_0 := h3734c.1
                                have p3734_1 := h3734c.2.1
                                have p3734_2 := h3734c.2.2.1
                                have p3734_3 := h3734c.2.2.2
                                linarith only [hlam, p3734_0]
                        · linarith only [h0, h3702, h3729, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h2736, h3586, h3588, h3702, h3723, h3728, hlam]
                  · linarith only [h2319, h3586, h3725, hc35, hlam, hphi, u3ehi3]
                · linarith only [h2319, h3586, h3724, hlam]
              · linarith only [h0, h3585, h3723, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3769 | h3769
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3770 | h3770
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3771 | h3771
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3772 | h3772
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3773 | h3773
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3774 | h3774
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3775 | h3775
                          · linarith only [h0, h3585, h3586, h3588, h3722, h3773, h3775, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h0, h3585, h3722, h3772, h3775, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h0, h3722, h3773, h3774, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h2319, h3586, h3588, h3702, h3773, hc45, hlam, hphi, ht34, u3ehi0]
                    · linarith only [h3722, h3769, h3772, hlam]
                  · linarith only [h2319, h3587, h3771, hlam]
                · linarith only [h2319, h3586, h3770, hlam]
              · linarith only [h0, h3585, h3769, hlam]
      · linarith only [h3586, h3587, hc35, hlam, hphi, u3ehi3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3785 | h3785
      · linarith only [h3586, h3785, hc34, hlam, hphi, u3ehi4]
      · linarith only [h2841, h3585, h3785, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h3788 | h3788
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3789 | h3789
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3790 | h3790
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3791 | h3791
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3792 | h3792
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3793 | h3793
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3794 | h3794
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3795 | h3795
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3796 | h3796
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3797 | h3797
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3798 | h3798
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3799 | h3799
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3800 | h3800
                            · rcases h1bigk with h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c | h3801c
                              · have p3801_0 := h3801c.1
                                have p3801_1 := h3801c.2.1
                                have p3801_2 := h3801c.2.2.1
                                have p3801_3 := h3801c.2.2.2
                                linarith only [hlam, p3801_0]
                              · have p3801_0 := h3801c.1
                                have p3801_1 := h3801c.2.1
                                have p3801_2 := h3801c.2.2.1
                                have p3801_3 := h3801c.2.2.2
                                linarith only [h0, hlam, p3801_0]
                              · have p3801_0 := h3801c.1
                                have p3801_1 := h3801c.2.1
                                have p3801_2 := h3801c.2.2.1
                                have p3801_3 := h3801c.2.2.2
                                linarith only [h2319, hlam, p3801_0]
                              · have p3801_0 := h3801c.1
                                have p3801_1 := h3801c.2.1
                                have p3801_2 := h3801c.2.2.1
                                have p3801_3 := h3801c.2.2.2
                                linarith only [h2512, hlam, p3801_0]
                              · have p3801_0 := h3801c.1
                                have p3801_1 := h3801c.2.1
                                have p3801_2 := h3801c.2.2.1
                                have p3801_3 := h3801c.2.2.2
                                linarith only [h2736, hlam, p3801_0]
                              · have p3801_0 := h3801c.1
                                have p3801_1 := h3801c.2.1
                                have p3801_2 := h3801c.2.2.1
                                have p3801_3 := h3801c.2.2.2
                                rcases p3801_3 (m.d 0 1) (by simp) with h3807 | h3807
                                · linarith only [h3807, hlam, p3801_0]
                                · rcases p3801_3 (m.d 1 2) (by simp) with h3809 | h3809
                                  · rcases p3801_3 (m.d 1 3) (by simp) with h3810 | h3810
                                    · linarith only [h3791, h3810, hlam]
                                    · linarith only [h2319, h3810, hlam]
                                  · linarith only [h3809, hlam, p3801_0]
                              · have p3801_0 := h3801c.1
                                have p3801_1 := h3801c.2.1
                                have p3801_2 := h3801c.2.2.1
                                have p3801_3 := h3801c.2.2.2
                                linarith only [hlam, p3801_0]
                              · have p3801_0 := h3801c.1
                                have p3801_1 := h3801c.2.1
                                have p3801_2 := h3801c.2.2.1
                                have p3801_3 := h3801c.2.2.2
                                linarith only [h0, h3585, h3793, h3794, h3796, hc01, hc12, hlam, hphi, p3801_1]
                              · have p3801_0 := h3801c.1
                                have p3801_1 := h3801c.2.1
                                have p3801_2 := h3801c.2.2.1
                                have p3801_3 := h3801c.2.2.2
                                linarith only [h2512, hc01, hc12, hlam, hphi, p3801_1]
                              · have p3801_0 := h3801c.1
                                have p3801_1 := h3801c.2.1
                                have p3801_2 := h3801c.2.2.1
                                have p3801_3 := h3801c.2.2.2
                                linarith only [h0, h3585, h3793, hc01, hc12, hlam, hphi, p3801_1]
                              · have p3801_0 := h3801c.1
                                have p3801_1 := h3801c.2.1
                                have p3801_2 := h3801c.2.2.1
                                have p3801_3 := h3801c.2.2.2
                                rcases p3801_3 (m.d 0 1) (by simp) with h3818 | h3818
                                · linarith only [h3818, hlam, p3801_0]
                                · rcases p3801_3 (m.d 1 2) (by simp) with h3820 | h3820
                                  · rcases p3801_3 (m.d 1 3) (by simp) with h3821 | h3821
                                    · rcases p3801_3 (m.d 1 4) (by simp) with h3822 | h3822
                                      · linarith only [h3794, h3822, hlam]
                                      · linarith only [h2512, h3822, hlam]
                                    · linarith only [h3821, hlam, p3801_0]
                                  · linarith only [h0, h3820, hlam]
                              · have p3801_0 := h3801c.1
                                have p3801_1 := h3801c.2.1
                                have p3801_2 := h3801c.2.2.1
                                have p3801_3 := h3801c.2.2.2
                                linarith only [h3791, hlam, p3801_1]
                              · have p3801_0 := h3801c.1
                                have p3801_1 := h3801c.2.1
                                have p3801_2 := h3801c.2.2.1
                                have p3801_3 := h3801c.2.2.2
                                linarith only [hlam, p3801_0]
                              · have p3801_0 := h3801c.1
                                have p3801_1 := h3801c.2.1
                                have p3801_2 := h3801c.2.2.1
                                have p3801_3 := h3801c.2.2.2
                                linarith only [h0, h3585, h3793, h3796, hc01, hc13, hlam, hphi, p3801_1]
                              · have p3801_0 := h3801c.1
                                have p3801_1 := h3801c.2.1
                                have p3801_2 := h3801c.2.2.1
                                have p3801_3 := h3801c.2.2.2
                                linarith only [h0, h3585, h3791, h3793, hc01, hc12, hlam, hphi, p3801_1]
                              · have p3801_0 := h3801c.1
                                have p3801_1 := h3801c.2.1
                                have p3801_2 := h3801c.2.2.1
                                have p3801_3 := h3801c.2.2.2
                                rcases p3801_3 (m.d 0 1) (by simp) with h3831 | h3831
                                · linarith only [h3831, hlam, p3801_0]
                                · rcases p3801_3 (m.d 1 2) (by simp) with h3833 | h3833
                                  · rcases p3801_3 (m.d 1 3) (by simp) with h3834 | h3834
                                    · rcases p3801_3 (m.d 1 4) (by simp) with h3835 | h3835
                                      · rcases p3801_3 (m.d 1 5) (by simp) with h3836 | h3836
                                        · linarith only [h3796, h3836, hlam]
                                        · linarith only [h2736, h3836, hlam]
                                      · linarith only [h3835, hlam, p3801_0]
                                    · linarith only [h2319, h3834, hlam]
                                  · linarith only [h0, h3833, hlam]
                              · have p3801_0 := h3801c.1
                                have p3801_1 := h3801c.2.1
                                have p3801_2 := h3801c.2.2.1
                                have p3801_3 := h3801c.2.2.2
                                linarith only [h3792, hlam, p3801_1]
                              · have p3801_0 := h3801c.1
                                have p3801_1 := h3801c.2.1
                                have p3801_2 := h3801c.2.2.1
                                have p3801_3 := h3801c.2.2.2
                                linarith only [h3794, hlam, p3801_0]
                              · have p3801_0 := h3801c.1
                                have p3801_1 := h3801c.2.1
                                have p3801_2 := h3801c.2.2.1
                                have p3801_3 := h3801c.2.2.2
                                linarith only [hlam, p3801_0]
                              · have p3801_0 := h3801c.1
                                have p3801_1 := h3801c.2.1
                                have p3801_2 := h3801c.2.2.1
                                have p3801_3 := h3801c.2.2.2
                                linarith only [h0, h3585, h3793, hc01, hc14, hlam, hphi, p3801_1]
                              · have p3801_0 := h3801c.1
                                have p3801_1 := h3801c.2.1
                                have p3801_2 := h3801c.2.2.1
                                have p3801_3 := h3801c.2.2.2
                                rcases p3801_3 (m.d 0 1) (by simp) with h3846 | h3846
                                · linarith only [h3846, hlam, p3801_0]
                                · rcases p3801_3 (m.d 1 2) (by simp) with h3848 | h3848
                                  · rcases p3801_3 (m.d 1 3) (by simp) with h3849 | h3849
                                    · rcases p3801_3 (m.d 1 4) (by simp) with h3850 | h3850
                                      · rcases p3801_3 (m.d 1 5) (by simp) with h3851 | h3851
                                        · rcases h5bigk with h3852c | h3852c | h3852c | h3852c | h3852c | h3852c | h3852c | h3852c | h3852c | h3852c | h3852c | h3852c | h3852c | h3852c | h3852c | h3852c | h3852c | h3852c | h3852c | h3852c | h3852c | h3852c | h3852c | h3852c | h3852c
                                          · have p3852_0 := h3852c.1
                                            have p3852_1 := h3852c.2.1
                                            have p3852_2 := h3852c.2.2.1
                                            have p3852_3 := h3852c.2.2.2
                                            linarith only [hlam, p3852_0]
                                          · have p3852_0 := h3852c.1
                                            have p3852_1 := h3852c.2.1
                                            have p3852_2 := h3852c.2.2.1
                                            have p3852_3 := h3852c.2.2.2
                                            linarith only [h2736, hlam, p3852_1]
                                          · have p3852_0 := h3852c.1
                                            have p3852_1 := h3852c.2.1
                                            have p3852_2 := h3852c.2.2.1
                                            have p3852_3 := h3852c.2.2.2
                                            linarith only [h3585, hlam, p3852_0]
                                          · have p3852_0 := h3852c.1
                                            have p3852_1 := h3852c.2.1
                                            have p3852_2 := h3852c.2.2.1
                                            have p3852_3 := h3852c.2.2.2
                                            linarith only [hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p3852_1, u3ehi4]
                                          · have p3852_0 := h3852c.1
                                            have p3852_1 := h3852c.2.1
                                            have p3852_2 := h3852c.2.2.1
                                            have p3852_3 := h3852c.2.2.2
                                            linarith only [h2841, h3788, h3790, h3791, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3852_1]
                                          · have p3852_0 := h3852c.1
                                            have p3852_1 := h3852c.2.1
                                            have p3852_2 := h3852c.2.2.1
                                            have p3852_3 := h3852c.2.2.2
                                            linarith only [h2736, hc01, hc15, hlam, hphi, p3852_1]
                                          · have p3852_0 := h3852c.1
                                            have p3852_1 := h3852c.2.1
                                            have p3852_2 := h3852c.2.2.1
                                            have p3852_3 := h3852c.2.2.2
                                            linarith only [hlam, p3852_0]
                                          · have p3852_0 := h3852c.1
                                            have p3852_1 := h3852c.2.1
                                            have p3852_2 := h3852c.2.2.1
                                            have p3852_3 := h3852c.2.2.2
                                            linarith only [h0, h3585, h3793, hc01, hc12, hlam, hphi, p3852_1]
                                          · have p3852_0 := h3852c.1
                                            have p3852_1 := h3852c.2.1
                                            have p3852_2 := h3852c.2.2.1
                                            have p3852_3 := h3852c.2.2.2
                                            linarith only [h3791, h3795, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3852_1, u3ehi4]
                                          · have p3852_0 := h3852c.1
                                            have p3852_1 := h3852c.2.1
                                            have p3852_2 := h3852c.2.2.1
                                            have p3852_3 := h3852c.2.2.2
                                            rcases p3852_3 (m.d 0 5) (by simp) with h3862 | h3862
                                            · linarith only [h2736, h3862, hlam]
                                            · linarith only [h3790, h3862, hlam]
                                          · have p3852_0 := h3852c.1
                                            have p3852_1 := h3852c.2.1
                                            have p3852_2 := h3852c.2.2.1
                                            have p3852_3 := h3852c.2.2.2
                                            linarith only [h3789, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3852_1, u3ehi4]
                                          · have p3852_0 := h3852c.1
                                            have p3852_1 := h3852c.2.1
                                            have p3852_2 := h3852c.2.2.1
                                            have p3852_3 := h3852c.2.2.2
                                            linarith only [h3793, hlam, p3852_1]
                                          · have p3852_0 := h3852c.1
                                            have p3852_1 := h3852c.2.1
                                            have p3852_2 := h3852c.2.2.1
                                            have p3852_3 := h3852c.2.2.2
                                            linarith only [hlam, p3852_0]
                                          · have p3852_0 := h3852c.1
                                            have p3852_1 := h3852c.2.1
                                            have p3852_2 := h3852c.2.2.1
                                            have p3852_3 := h3852c.2.2.2
                                            linarith only [h3798, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3852_1, u3ehi4]
                                          · have p3852_0 := h3852c.1
                                            have p3852_1 := h3852c.2.1
                                            have p3852_2 := h3852c.2.2.1
                                            have p3852_3 := h3852c.2.2.2
                                            linarith only [h3791, h3797, h3799, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3852_1]
                                          · have p3852_0 := h3852c.1
                                            have p3852_1 := h3852c.2.1
                                            have p3852_2 := h3852c.2.2.1
                                            have p3852_3 := h3852c.2.2.2
                                            linarith only [h3789, hlam, p3852_0]
                                          · have p3852_0 := h3852c.1
                                            have p3852_1 := h3852c.2.1
                                            have p3852_2 := h3852c.2.2.1
                                            have p3852_3 := h3852c.2.2.2
                                            linarith only [h3795, hlam, p3852_0]
                                          · have p3852_0 := h3852c.1
                                            have p3852_1 := h3852c.2.1
                                            have p3852_2 := h3852c.2.2.1
                                            have p3852_3 := h3852c.2.2.2
                                            linarith only [h3798, hlam, p3852_0]
                                          · have p3852_0 := h3852c.1
                                            have p3852_1 := h3852c.2.1
                                            have p3852_2 := h3852c.2.2.1
                                            have p3852_3 := h3852c.2.2.2
                                            linarith only [hlam, p3852_0]
                                          · have p3852_0 := h3852c.1
                                            have p3852_1 := h3852c.2.1
                                            have p3852_2 := h3852c.2.2.1
                                            have p3852_3 := h3852c.2.2.2
                                            linarith only [h3788, h3800, hc03, hc45, hlam, hphi, ht0b, ht5b, p3852_1]
                                          · have p3852_0 := h3852c.1
                                            have p3852_1 := h3852c.2.1
                                            have p3852_2 := h3852c.2.2.1
                                            have p3852_3 := h3852c.2.2.2
                                            linarith only [h3790, hlam, p3852_0]
                                          · have p3852_0 := h3852c.1
                                            have p3852_1 := h3852c.2.1
                                            have p3852_2 := h3852c.2.2.1
                                            have p3852_3 := h3852c.2.2.2
                                            linarith only [h3796, hlam, p3852_0]
                                          · have p3852_0 := h3852c.1
                                            have p3852_1 := h3852c.2.1
                                            have p3852_2 := h3852c.2.2.1
                                            have p3852_3 := h3852c.2.2.2
                                            linarith only [h3799, hlam, p3852_0]
                                          · have p3852_0 := h3852c.1
                                            have p3852_1 := h3852c.2.1
                                            have p3852_2 := h3852c.2.2.1
                                            have p3852_3 := h3852c.2.2.2
                                            linarith only [h3800, hlam, p3852_0]
                                          · have p3852_0 := h3852c.1
                                            have p3852_1 := h3852c.2.1
                                            have p3852_2 := h3852c.2.2.1
                                            have p3852_3 := h3852c.2.2.2
                                            linarith only [hlam, p3852_0]
                                        · linarith only [h3851, hlam, p3801_0]
                                      · linarith only [h2512, h3850, hlam]
                                    · linarith only [h2319, h3849, hlam]
                                  · linarith only [h0, h3848, hlam]
                              · have p3801_0 := h3801c.1
                                have p3801_1 := h3801c.2.1
                                have p3801_2 := h3801c.2.2.1
                                have p3801_3 := h3801c.2.2.2
                                linarith only [h3793, hlam, p3801_1]
                              · have p3801_0 := h3801c.1
                                have p3801_1 := h3801c.2.1
                                have p3801_2 := h3801c.2.2.1
                                have p3801_3 := h3801c.2.2.2
                                linarith only [h3795, hlam, p3801_0]
                              · have p3801_0 := h3801c.1
                                have p3801_1 := h3801c.2.1
                                have p3801_2 := h3801c.2.2.1
                                have p3801_3 := h3801c.2.2.2
                                linarith only [h3796, hlam, p3801_0]
                              · have p3801_0 := h3801c.1
                                have p3801_1 := h3801c.2.1
                                have p3801_2 := h3801c.2.2.1
                                have p3801_3 := h3801c.2.2.2
                                linarith only [hlam, p3801_0]
                            · linarith only [h2841, h3788, h3790, h3791, h3800, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h2841, h3788, h3790, h3791, h3797, h3799, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h2841, h3788, h3798, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h2841, h3789, h3797, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h2512, h3790, h3796, hlam]
                  · linarith only [h2841, h3789, h3791, h3795, hlam]
                · linarith only [h2841, h3788, h3791, h3794, hlam]
              · linarith only [h2841, h3789, h3791, h3793, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
            · linarith only [h2841, h3789, h3791, h3792, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3897 | h3897
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3898 | h3898
              · linarith only [h0, h3585, h3791, h3898, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3900 | h3900
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3901 | h3901
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3902 | h3902
                    · linarith only [h3897, h3898, h3902, hlam]
                    · linarith only [h2319, h2512, h3788, h3790, h3902, hc01, hc13, hlam, hphi]
                  · linarith only [h2319, h3788, h3901, hc35, hlam, hphi, u3ehi3]
                · linarith only [h2319, h3788, h3900, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3907 | h3907
              · linarith only [h0, h3585, h3897, h3907, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3909 | h3909
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3910 | h3910
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3911 | h3911
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3912 | h3912
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3913 | h3913
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3914 | h3914
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3915 | h3915
                            · rcases h1bigk with h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c
                              · have p3916_0 := h3916c.1
                                have p3916_1 := h3916c.2.1
                                have p3916_2 := h3916c.2.2.1
                                have p3916_3 := h3916c.2.2.2
                                linarith only [hlam, p3916_0]
                              · have p3916_0 := h3916c.1
                                have p3916_1 := h3916c.2.1
                                have p3916_2 := h3916c.2.2.1
                                have p3916_3 := h3916c.2.2.2
                                linarith only [h0, hlam, p3916_0]
                              · have p3916_0 := h3916c.1
                                have p3916_1 := h3916c.2.1
                                have p3916_2 := h3916c.2.2.1
                                have p3916_3 := h3916c.2.2.2
                                linarith only [h2319, hlam, p3916_0]
                              · have p3916_0 := h3916c.1
                                have p3916_1 := h3916c.2.1
                                have p3916_2 := h3916c.2.2.1
                                have p3916_3 := h3916c.2.2.2
                                linarith only [h2512, hlam, p3916_0]
                              · have p3916_0 := h3916c.1
                                have p3916_1 := h3916c.2.1
                                have p3916_2 := h3916c.2.2.1
                                have p3916_3 := h3916c.2.2.2
                                linarith only [h2736, hlam, p3916_0]
                              · have p3916_0 := h3916c.1
                                have p3916_1 := h3916c.2.1
                                have p3916_2 := h3916c.2.2.1
                                have p3916_3 := h3916c.2.2.2
                                linarith only [h3907, h3912, h3914, hc01, hc23, hlam, hphi, ht12, p3916_1]
                              · have p3916_0 := h3916c.1
                                have p3916_1 := h3916c.2.1
                                have p3916_2 := h3916c.2.2.1
                                have p3916_3 := h3916c.2.2.2
                                linarith only [hlam, p3916_0]
                              · have p3916_0 := h3916c.1
                                have p3916_1 := h3916c.2.1
                                have p3916_2 := h3916c.2.2.1
                                have p3916_3 := h3916c.2.2.2
                                linarith only [h3791, hlam, p3916_0]
                              · have p3916_0 := h3916c.1
                                have p3916_1 := h3916c.2.1
                                have p3916_2 := h3916c.2.2.1
                                have p3916_3 := h3916c.2.2.2
                                linarith only [h3897, hlam, p3916_0]
                              · have p3916_0 := h3916c.1
                                have p3916_1 := h3916c.2.1
                                have p3916_2 := h3916c.2.2.1
                                have p3916_3 := h3916c.2.2.2
                                linarith only [h3907, hlam, p3916_0]
                              · have p3916_0 := h3916c.1
                                have p3916_1 := h3916c.2.1
                                have p3916_2 := h3916c.2.2.1
                                have p3916_3 := h3916c.2.2.2
                                rcases p3916_3 (m.d 0 1) (by simp) with h3927 | h3927
                                · linarith only [h3927, hlam, p3916_0]
                                · rcases p3916_3 (m.d 1 2) (by simp) with h3929 | h3929
                                  · linarith only [h3791, h3929, hlam]
                                  · linarith only [h0, h3929, hlam]
                              · have p3916_0 := h3916c.1
                                have p3916_1 := h3916c.2.1
                                have p3916_2 := h3916c.2.2.1
                                have p3916_3 := h3916c.2.2.2
                                linarith only [h0, hc01, hc13, hlam, hphi, p3916_1]
                              · have p3916_0 := h3916c.1
                                have p3916_1 := h3916c.2.1
                                have p3916_2 := h3916c.2.2.1
                                have p3916_3 := h3916c.2.2.2
                                linarith only [hlam, p3916_0]
                              · have p3916_0 := h3916c.1
                                have p3916_1 := h3916c.2.1
                                have p3916_2 := h3916c.2.2.1
                                have p3916_3 := h3916c.2.2.2
                                linarith only [h2512, h3791, hc01, hc23, hlam, hphi, ht12, p3916_1]
                              · have p3916_0 := h3916c.1
                                have p3916_1 := h3916c.2.1
                                have p3916_2 := h3916c.2.2.1
                                have p3916_3 := h3916c.2.2.2
                                linarith only [h2736, h3791, hc01, hc23, hlam, hphi, ht12, p3916_1]
                              · have p3916_0 := h3916c.1
                                have p3916_1 := h3916c.2.1
                                have p3916_2 := h3916c.2.2.1
                                have p3916_3 := h3916c.2.2.2
                                rcases p3916_3 (m.d 0 1) (by simp) with h3936 | h3936
                                · linarith only [h3936, hlam, p3916_0]
                                · rcases p3916_3 (m.d 1 2) (by simp) with h3938 | h3938
                                  · linarith only [h3897, h3938, hlam]
                                  · linarith only [h0, h3938, hlam]
                              · have p3916_0 := h3916c.1
                                have p3916_1 := h3916c.2.1
                                have p3916_2 := h3916c.2.2.1
                                have p3916_3 := h3916c.2.2.2
                                linarith only [h0, hc01, hc14, hlam, hphi, p3916_1]
                              · have p3916_0 := h3916c.1
                                have p3916_1 := h3916c.2.1
                                have p3916_2 := h3916c.2.2.1
                                have p3916_3 := h3916c.2.2.2
                                linarith only [h3909, hlam, p3916_0]
                              · have p3916_0 := h3916c.1
                                have p3916_1 := h3916c.2.1
                                have p3916_2 := h3916c.2.2.1
                                have p3916_3 := h3916c.2.2.2
                                linarith only [hlam, p3916_0]
                              · have p3916_0 := h3916c.1
                                have p3916_1 := h3916c.2.1
                                have p3916_2 := h3916c.2.2.1
                                have p3916_3 := h3916c.2.2.2
                                linarith only [h2736, h3897, h3912, hc01, hc23, hlam, hphi, ht12, p3916_1]
                              · have p3916_0 := h3916c.1
                                have p3916_1 := h3916c.2.1
                                have p3916_2 := h3916c.2.2.1
                                have p3916_3 := h3916c.2.2.2
                                rcases p3916_3 (m.d 0 1) (by simp) with h3945 | h3945
                                · linarith only [h3945, hlam, p3916_0]
                                · rcases p3916_3 (m.d 1 2) (by simp) with h3947 | h3947
                                  · linarith only [h3907, h3947, hlam]
                                  · linarith only [h0, h3947, hlam]
                              · have p3916_0 := h3916c.1
                                have p3916_1 := h3916c.2.1
                                have p3916_2 := h3916c.2.2.1
                                have p3916_3 := h3916c.2.2.2
                                linarith only [h0, hc01, hc15, hlam, hphi, p3916_1]
                              · have p3916_0 := h3916c.1
                                have p3916_1 := h3916c.2.1
                                have p3916_2 := h3916c.2.2.1
                                have p3916_3 := h3916c.2.2.2
                                linarith only [h3910, hlam, p3916_0]
                              · have p3916_0 := h3916c.1
                                have p3916_1 := h3916c.2.1
                                have p3916_2 := h3916c.2.2.1
                                have p3916_3 := h3916c.2.2.2
                                linarith only [h3911, hlam, p3916_0]
                              · have p3916_0 := h3916c.1
                                have p3916_1 := h3916c.2.1
                                have p3916_2 := h3916c.2.2.1
                                have p3916_3 := h3916c.2.2.2
                                linarith only [hlam, p3916_0]
                            · rcases h1bigk with h3954c | h3954c | h3954c | h3954c | h3954c | h3954c | h3954c | h3954c | h3954c | h3954c | h3954c | h3954c | h3954c | h3954c | h3954c | h3954c | h3954c | h3954c | h3954c | h3954c | h3954c | h3954c | h3954c | h3954c | h3954c
                              · have p3954_0 := h3954c.1
                                have p3954_1 := h3954c.2.1
                                have p3954_2 := h3954c.2.2.1
                                have p3954_3 := h3954c.2.2.2
                                linarith only [hlam, p3954_0]
                              · have p3954_0 := h3954c.1
                                have p3954_1 := h3954c.2.1
                                have p3954_2 := h3954c.2.2.1
                                have p3954_3 := h3954c.2.2.2
                                linarith only [h0, hlam, p3954_0]
                              · have p3954_0 := h3954c.1
                                have p3954_1 := h3954c.2.1
                                have p3954_2 := h3954c.2.2.1
                                have p3954_3 := h3954c.2.2.2
                                linarith only [h2319, hlam, p3954_0]
                              · have p3954_0 := h3954c.1
                                have p3954_1 := h3954c.2.1
                                have p3954_2 := h3954c.2.2.1
                                have p3954_3 := h3954c.2.2.2
                                linarith only [h2512, hlam, p3954_0]
                              · have p3954_0 := h3954c.1
                                have p3954_1 := h3954c.2.1
                                have p3954_2 := h3954c.2.2.1
                                have p3954_3 := h3954c.2.2.2
                                linarith only [h2736, hlam, p3954_0]
                              · have p3954_0 := h3954c.1
                                have p3954_1 := h3954c.2.1
                                have p3954_2 := h3954c.2.2.1
                                have p3954_3 := h3954c.2.2.2
                                linarith only [h3791, hc01, hc23, hlam, hphi, ht12, p3954_1]
                              · have p3954_0 := h3954c.1
                                have p3954_1 := h3954c.2.1
                                have p3954_2 := h3954c.2.2.1
                                have p3954_3 := h3954c.2.2.2
                                linarith only [hlam, p3954_0]
                              · have p3954_0 := h3954c.1
                                have p3954_1 := h3954c.2.1
                                have p3954_2 := h3954c.2.2.1
                                have p3954_3 := h3954c.2.2.2
                                linarith only [h3791, hlam, p3954_0]
                              · have p3954_0 := h3954c.1
                                have p3954_1 := h3954c.2.1
                                have p3954_2 := h3954c.2.2.1
                                have p3954_3 := h3954c.2.2.2
                                linarith only [h3897, hlam, p3954_0]
                              · have p3954_0 := h3954c.1
                                have p3954_1 := h3954c.2.1
                                have p3954_2 := h3954c.2.2.1
                                have p3954_3 := h3954c.2.2.2
                                linarith only [h3907, hlam, p3954_0]
                              · have p3954_0 := h3954c.1
                                have p3954_1 := h3954c.2.1
                                have p3954_2 := h3954c.2.2.1
                                have p3954_3 := h3954c.2.2.2
                                rcases p3954_3 (m.d 0 1) (by simp) with h3965 | h3965
                                · linarith only [h3965, hlam, p3954_0]
                                · rcases p3954_3 (m.d 1 2) (by simp) with h3967 | h3967
                                  · linarith only [h3791, h3967, hlam]
                                  · linarith only [h0, h3967, hlam]
                              · have p3954_0 := h3954c.1
                                have p3954_1 := h3954c.2.1
                                have p3954_2 := h3954c.2.2.1
                                have p3954_3 := h3954c.2.2.2
                                linarith only [h0, h3791, hc01, hc23, hlam, hphi, ht12, p3954_1]
                              · have p3954_0 := h3954c.1
                                have p3954_1 := h3954c.2.1
                                have p3954_2 := h3954c.2.2.1
                                have p3954_3 := h3954c.2.2.2
                                linarith only [hlam, p3954_0]
                              · have p3954_0 := h3954c.1
                                have p3954_1 := h3954c.2.1
                                have p3954_2 := h3954c.2.2.1
                                have p3954_3 := h3954c.2.2.2
                                linarith only [h2512, h3790, h3791, h3915, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3954_1, u3ehi3]
                              · have p3954_0 := h3954c.1
                                have p3954_1 := h3954c.2.1
                                have p3954_2 := h3954c.2.2.1
                                have p3954_3 := h3954c.2.2.2
                                linarith only [h2736, h3791, hc01, hc23, hlam, hphi, ht12, p3954_1]
                              · have p3954_0 := h3954c.1
                                have p3954_1 := h3954c.2.1
                                have p3954_2 := h3954c.2.2.1
                                have p3954_3 := h3954c.2.2.2
                                rcases p3954_3 (m.d 0 1) (by simp) with h3974 | h3974
                                · linarith only [h3974, hlam, p3954_0]
                                · rcases p3954_3 (m.d 1 2) (by simp) with h3976 | h3976
                                  · linarith only [h3897, h3976, hlam]
                                  · linarith only [h0, h3976, hlam]
                              · have p3954_0 := h3954c.1
                                have p3954_1 := h3954c.2.1
                                have p3954_2 := h3954c.2.2.1
                                have p3954_3 := h3954c.2.2.2
                                linarith only [h0, hc01, hc14, hlam, hphi, p3954_1]
                              · have p3954_0 := h3954c.1
                                have p3954_1 := h3954c.2.1
                                have p3954_2 := h3954c.2.2.1
                                have p3954_3 := h3954c.2.2.2
                                linarith only [h3909, hlam, p3954_0]
                              · have p3954_0 := h3954c.1
                                have p3954_1 := h3954c.2.1
                                have p3954_2 := h3954c.2.2.1
                                have p3954_3 := h3954c.2.2.2
                                linarith only [hlam, p3954_0]
                              · have p3954_0 := h3954c.1
                                have p3954_1 := h3954c.2.1
                                have p3954_2 := h3954c.2.2.1
                                have p3954_3 := h3954c.2.2.2
                                linarith only [h2736, h3897, h3912, hc01, hc23, hlam, hphi, ht12, p3954_1]
                              · have p3954_0 := h3954c.1
                                have p3954_1 := h3954c.2.1
                                have p3954_2 := h3954c.2.2.1
                                have p3954_3 := h3954c.2.2.2
                                rcases p3954_3 (m.d 0 1) (by simp) with h3983 | h3983
                                · linarith only [h3983, hlam, p3954_0]
                                · rcases p3954_3 (m.d 1 2) (by simp) with h3985 | h3985
                                  · linarith only [h3907, h3985, hlam]
                                  · linarith only [h0, h3985, hlam]
                              · have p3954_0 := h3954c.1
                                have p3954_1 := h3954c.2.1
                                have p3954_2 := h3954c.2.2.1
                                have p3954_3 := h3954c.2.2.2
                                linarith only [h0, hc01, hc15, hlam, hphi, p3954_1]
                              · have p3954_0 := h3954c.1
                                have p3954_1 := h3954c.2.1
                                have p3954_2 := h3954c.2.2.1
                                have p3954_3 := h3954c.2.2.2
                                linarith only [h3910, hlam, p3954_0]
                              · have p3954_0 := h3954c.1
                                have p3954_1 := h3954c.2.1
                                have p3954_2 := h3954c.2.2.1
                                have p3954_3 := h3954c.2.2.2
                                linarith only [h3911, hlam, p3954_0]
                              · have p3954_0 := h3954c.1
                                have p3954_1 := h3954c.2.1
                                have p3954_2 := h3954c.2.2.1
                                have p3954_3 := h3954c.2.2.2
                                linarith only [hlam, p3954_0]
                          · linarith only [h2512, h3790, h3897, h3914, hlam]
                        · linarith only [h0, h3789, h3897, h3912, h3913, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                      · linarith only [h2319, h3788, h3791, h3912, hlam]
                    · linarith only [h2512, h3790, h3911, hlam]
                  · linarith only [h2319, h3789, h3910, hlam]
                · linarith only [h2319, h3788, h3909, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3998 | h3998
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3999 | h3999
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4000 | h4000
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4001 | h4001
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4002 | h4002
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4003 | h4003
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4004 | h4004
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4005 | h4005
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4006 | h4006
                          · linarith only [h3788, h3790, h3998, h4004, h4006, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4008 | h4008
                            · linarith only [h2841, h3788, h3998, h4006, h4008, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases h1bigk with h4010c | h4010c | h4010c | h4010c | h4010c | h4010c | h4010c | h4010c | h4010c | h4010c | h4010c | h4010c | h4010c | h4010c | h4010c | h4010c | h4010c | h4010c | h4010c | h4010c | h4010c | h4010c | h4010c | h4010c | h4010c
                              · have p4010_0 := h4010c.1
                                have p4010_1 := h4010c.2.1
                                have p4010_2 := h4010c.2.2.1
                                have p4010_3 := h4010c.2.2.2
                                linarith only [hlam, p4010_0]
                              · have p4010_0 := h4010c.1
                                have p4010_1 := h4010c.2.1
                                have p4010_2 := h4010c.2.2.1
                                have p4010_3 := h4010c.2.2.2
                                linarith only [h0, hlam, p4010_0]
                              · have p4010_0 := h4010c.1
                                have p4010_1 := h4010c.2.1
                                have p4010_2 := h4010c.2.2.1
                                have p4010_3 := h4010c.2.2.2
                                linarith only [h2319, hlam, p4010_0]
                              · have p4010_0 := h4010c.1
                                have p4010_1 := h4010c.2.1
                                have p4010_2 := h4010c.2.2.1
                                have p4010_3 := h4010c.2.2.2
                                linarith only [h2512, hlam, p4010_0]
                              · have p4010_0 := h4010c.1
                                have p4010_1 := h4010c.2.1
                                have p4010_2 := h4010c.2.2.1
                                have p4010_3 := h4010c.2.2.2
                                linarith only [h2736, hlam, p4010_0]
                              · have p4010_0 := h4010c.1
                                have p4010_1 := h4010c.2.1
                                have p4010_2 := h4010c.2.2.1
                                have p4010_3 := h4010c.2.2.2
                                rcases p4010_3 (m.d 0 1) (by simp) with h4016 | h4016
                                · linarith only [h4016, hlam, p4010_0]
                                · rcases p4010_3 (m.d 1 2) (by simp) with h4018 | h4018
                                  · rcases p4010_3 (m.d 1 3) (by simp) with h4019 | h4019
                                    · linarith only [h3998, h4019, hlam]
                                    · linarith only [h2319, h4019, hlam]
                                  · linarith only [h4018, hlam, p4010_0]
                              · have p4010_0 := h4010c.1
                                have p4010_1 := h4010c.2.1
                                have p4010_2 := h4010c.2.2.1
                                have p4010_3 := h4010c.2.2.2
                                linarith only [hlam, p4010_0]
                              · have p4010_0 := h4010c.1
                                have p4010_1 := h4010c.2.1
                                have p4010_2 := h4010c.2.2.1
                                have p4010_3 := h4010c.2.2.2
                                linarith only [h2319, hc01, hc12, hlam, hphi, p4010_1]
                              · have p4010_0 := h4010c.1
                                have p4010_1 := h4010c.2.1
                                have p4010_2 := h4010c.2.2.1
                                have p4010_3 := h4010c.2.2.2
                                linarith only [h2512, hc01, hc12, hlam, hphi, p4010_1]
                              · have p4010_0 := h4010c.1
                                have p4010_1 := h4010c.2.1
                                have p4010_2 := h4010c.2.2.1
                                have p4010_3 := h4010c.2.2.2
                                linarith only [h3788, h3790, h4003, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4010_1, u3ehi3]
                              · have p4010_0 := h4010c.1
                                have p4010_1 := h4010c.2.1
                                have p4010_2 := h4010c.2.2.1
                                have p4010_3 := h4010c.2.2.2
                                rcases p4010_3 (m.d 0 1) (by simp) with h4027 | h4027
                                · linarith only [h4027, hlam, p4010_0]
                                · rcases p4010_3 (m.d 1 2) (by simp) with h4029 | h4029
                                  · rcases p4010_3 (m.d 1 3) (by simp) with h4030 | h4030
                                    · rcases p4010_3 (m.d 1 4) (by simp) with h4031 | h4031
                                      · linarith only [h4001, h4031, hlam]
                                      · linarith only [h2512, h4031, hlam]
                                    · linarith only [h4030, hlam, p4010_0]
                                  · linarith only [h0, h4029, hlam]
                              · have p4010_0 := h4010c.1
                                have p4010_1 := h4010c.2.1
                                have p4010_2 := h4010c.2.2.1
                                have p4010_3 := h4010c.2.2.2
                                linarith only [h3998, hlam, p4010_1]
                              · have p4010_0 := h4010c.1
                                have p4010_1 := h4010c.2.1
                                have p4010_2 := h4010c.2.2.1
                                have p4010_3 := h4010c.2.2.2
                                linarith only [hlam, p4010_0]
                              · have p4010_0 := h4010c.1
                                have p4010_1 := h4010c.2.1
                                have p4010_2 := h4010c.2.2.1
                                have p4010_3 := h4010c.2.2.2
                                linarith only [h3788, h3790, h4003, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4010_1, u3ehi3]
                              · have p4010_0 := h4010c.1
                                have p4010_1 := h4010c.2.1
                                have p4010_2 := h4010c.2.2.1
                                have p4010_3 := h4010c.2.2.2
                                linarith only [h3788, h3790, h3998, h4003, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4010_1, u3ehi3]
                              · have p4010_0 := h4010c.1
                                have p4010_1 := h4010c.2.1
                                have p4010_2 := h4010c.2.2.1
                                have p4010_3 := h4010c.2.2.2
                                rcases p4010_3 (m.d 0 1) (by simp) with h4040 | h4040
                                · linarith only [h4040, hlam, p4010_0]
                                · rcases p4010_3 (m.d 1 2) (by simp) with h4042 | h4042
                                  · rcases p4010_3 (m.d 1 3) (by simp) with h4043 | h4043
                                    · rcases p4010_3 (m.d 1 4) (by simp) with h4044 | h4044
                                      · rcases p4010_3 (m.d 1 5) (by simp) with h4045 | h4045
                                        · linarith only [h4003, h4045, hlam]
                                        · linarith only [h2736, h4045, hlam]
                                      · linarith only [h4044, hlam, p4010_0]
                                    · linarith only [h2319, h4043, hlam]
                                  · linarith only [h0, h4042, hlam]
                              · have p4010_0 := h4010c.1
                                have p4010_1 := h4010c.2.1
                                have p4010_2 := h4010c.2.2.1
                                have p4010_3 := h4010c.2.2.2
                                linarith only [h3999, hlam, p4010_1]
                              · have p4010_0 := h4010c.1
                                have p4010_1 := h4010c.2.1
                                have p4010_2 := h4010c.2.2.1
                                have p4010_3 := h4010c.2.2.2
                                linarith only [h4001, hlam, p4010_0]
                              · have p4010_0 := h4010c.1
                                have p4010_1 := h4010c.2.1
                                have p4010_2 := h4010c.2.2.1
                                have p4010_3 := h4010c.2.2.2
                                linarith only [hlam, p4010_0]
                              · have p4010_0 := h4010c.1
                                have p4010_1 := h4010c.2.1
                                have p4010_2 := h4010c.2.2.1
                                have p4010_3 := h4010c.2.2.2
                                linarith only [h3788, h3790, h4003, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4010_1, u3ehi3]
                              · have p4010_0 := h4010c.1
                                have p4010_1 := h4010c.2.1
                                have p4010_2 := h4010c.2.2.1
                                have p4010_3 := h4010c.2.2.2
                                rcases p4010_3 (m.d 0 1) (by simp) with h4055 | h4055
                                · linarith only [h4055, hlam, p4010_0]
                                · rcases p4010_3 (m.d 1 2) (by simp) with h4057 | h4057
                                  · rcases p4010_3 (m.d 1 3) (by simp) with h4058 | h4058
                                    · rcases p4010_3 (m.d 1 4) (by simp) with h4059 | h4059
                                      · rcases p4010_3 (m.d 1 5) (by simp) with h4060 | h4060
                                        · rcases h5bigk with h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c | h4061c
                                          · have p4061_0 := h4061c.1
                                            have p4061_1 := h4061c.2.1
                                            have p4061_2 := h4061c.2.2.1
                                            have p4061_3 := h4061c.2.2.2
                                            linarith only [hlam, p4061_0]
                                          · have p4061_0 := h4061c.1
                                            have p4061_1 := h4061c.2.1
                                            have p4061_2 := h4061c.2.2.1
                                            have p4061_3 := h4061c.2.2.2
                                            linarith only [h2736, hlam, p4061_1]
                                          · have p4061_0 := h4061c.1
                                            have p4061_1 := h4061c.2.1
                                            have p4061_2 := h4061c.2.2.1
                                            have p4061_3 := h4061c.2.2.2
                                            linarith only [h3585, hlam, p4061_0]
                                          · have p4061_0 := h4061c.1
                                            have p4061_1 := h4061c.2.1
                                            have p4061_2 := h4061c.2.2.1
                                            have p4061_3 := h4061c.2.2.2
                                            linarith only [h4008, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p4061_1, u3ehi3]
                                          · have p4061_0 := h4061c.1
                                            have p4061_1 := h4061c.2.1
                                            have p4061_2 := h4061c.2.2.1
                                            have p4061_3 := h4061c.2.2.2
                                            linarith only [h3790, hlam, p4061_1]
                                          · have p4061_0 := h4061c.1
                                            have p4061_1 := h4061c.2.1
                                            have p4061_2 := h4061c.2.2.1
                                            have p4061_3 := h4061c.2.2.2
                                            linarith only [h2736, hc01, hc15, hlam, hphi, p4061_1]
                                          · have p4061_0 := h4061c.1
                                            have p4061_1 := h4061c.2.1
                                            have p4061_2 := h4061c.2.2.1
                                            have p4061_3 := h4061c.2.2.2
                                            linarith only [hlam, p4061_0]
                                          · have p4061_0 := h4061c.1
                                            have p4061_1 := h4061c.2.1
                                            have p4061_2 := h4061c.2.2.1
                                            have p4061_3 := h4061c.2.2.2
                                            linarith only [h0, h3585, h4000, hc01, hc12, hlam, hphi, p4061_1]
                                          · have p4061_0 := h4061c.1
                                            have p4061_1 := h4061c.2.1
                                            have p4061_2 := h4061c.2.2.1
                                            have p4061_3 := h4061c.2.2.2
                                            linarith only [h3998, h4002, h4008, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4061_1, u3ehi3]
                                          · have p4061_0 := h4061c.1
                                            have p4061_1 := h4061c.2.1
                                            have p4061_2 := h4061c.2.2.1
                                            have p4061_3 := h4061c.2.2.2
                                            linarith only [h3788, h3790, h3998, h4001, h4003, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4061_1, u3ehi3]
                                          · have p4061_0 := h4061c.1
                                            have p4061_1 := h4061c.2.1
                                            have p4061_2 := h4061c.2.2.1
                                            have p4061_3 := h4061c.2.2.2
                                            linarith only [h3789, h4008, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4061_1, u3ehi3]
                                          · have p4061_0 := h4061c.1
                                            have p4061_1 := h4061c.2.1
                                            have p4061_2 := h4061c.2.2.1
                                            have p4061_3 := h4061c.2.2.2
                                            linarith only [h4000, hlam, p4061_1]
                                          · have p4061_0 := h4061c.1
                                            have p4061_1 := h4061c.2.1
                                            have p4061_2 := h4061c.2.2.1
                                            have p4061_3 := h4061c.2.2.2
                                            linarith only [hlam, p4061_0]
                                          · have p4061_0 := h4061c.1
                                            have p4061_1 := h4061c.2.1
                                            have p4061_2 := h4061c.2.2.1
                                            have p4061_3 := h4061c.2.2.2
                                            linarith only [h3998, h4005, h4008, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4061_1, u3ehi3]
                                          · have p4061_0 := h4061c.1
                                            have p4061_1 := h4061c.2.1
                                            have p4061_2 := h4061c.2.2.1
                                            have p4061_3 := h4061c.2.2.2
                                            linarith only [h4006, hlam, p4061_1]
                                          · have p4061_0 := h4061c.1
                                            have p4061_1 := h4061c.2.1
                                            have p4061_2 := h4061c.2.2.1
                                            have p4061_3 := h4061c.2.2.2
                                            linarith only [h3789, hlam, p4061_0]
                                          · have p4061_0 := h4061c.1
                                            have p4061_1 := h4061c.2.1
                                            have p4061_2 := h4061c.2.2.1
                                            have p4061_3 := h4061c.2.2.2
                                            linarith only [h4002, hlam, p4061_0]
                                          · have p4061_0 := h4061c.1
                                            have p4061_1 := h4061c.2.1
                                            have p4061_2 := h4061c.2.2.1
                                            have p4061_3 := h4061c.2.2.2
                                            linarith only [h4005, hlam, p4061_0]
                                          · have p4061_0 := h4061c.1
                                            have p4061_1 := h4061c.2.1
                                            have p4061_2 := h4061c.2.2.1
                                            have p4061_3 := h4061c.2.2.2
                                            linarith only [hlam, p4061_0]
                                          · have p4061_0 := h4061c.1
                                            have p4061_1 := h4061c.2.1
                                            have p4061_2 := h4061c.2.2.1
                                            have p4061_3 := h4061c.2.2.2
                                            linarith only [h4008, hlam, p4061_1]
                                          · have p4061_0 := h4061c.1
                                            have p4061_1 := h4061c.2.1
                                            have p4061_2 := h4061c.2.2.1
                                            have p4061_3 := h4061c.2.2.2
                                            linarith only [h3789, h4008, hc45, hlam, hphi, ht34, p4061_1, u3ehi3]
                                          · have p4061_0 := h4061c.1
                                            have p4061_1 := h4061c.2.1
                                            have p4061_2 := h4061c.2.2.1
                                            have p4061_3 := h4061c.2.2.2
                                            linarith only [h4003, hlam, p4061_0]
                                          · have p4061_0 := h4061c.1
                                            have p4061_1 := h4061c.2.1
                                            have p4061_2 := h4061c.2.2.1
                                            have p4061_3 := h4061c.2.2.2
                                            linarith only [h3998, h4001, h4003, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p4061_1]
                                          · have p4061_0 := h4061c.1
                                            have p4061_1 := h4061c.2.1
                                            have p4061_2 := h4061c.2.2.1
                                            have p4061_3 := h4061c.2.2.2
                                            linarith only [h3998, h4001, h4003, h4008, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4061_1, u3ehi3]
                                          · have p4061_0 := h4061c.1
                                            have p4061_1 := h4061c.2.1
                                            have p4061_2 := h4061c.2.2.1
                                            have p4061_3 := h4061c.2.2.2
                                            linarith only [hlam, p4061_0]
                                        · linarith only [h4060, hlam, p4010_0]
                                      · linarith only [h2512, h4059, hlam]
                                    · linarith only [h2319, h4058, hlam]
                                  · linarith only [h0, h4057, hlam]
                              · have p4010_0 := h4010c.1
                                have p4010_1 := h4010c.2.1
                                have p4010_2 := h4010c.2.2.1
                                have p4010_3 := h4010c.2.2.2
                                linarith only [h4000, hlam, p4010_1]
                              · have p4010_0 := h4010c.1
                                have p4010_1 := h4010c.2.1
                                have p4010_2 := h4010c.2.2.1
                                have p4010_3 := h4010c.2.2.2
                                linarith only [h4002, hlam, p4010_0]
                              · have p4010_0 := h4010c.1
                                have p4010_1 := h4010c.2.1
                                have p4010_2 := h4010c.2.2.1
                                have p4010_3 := h4010c.2.2.2
                                linarith only [h4003, hlam, p4010_0]
                              · have p4010_0 := h4010c.1
                                have p4010_1 := h4010c.2.1
                                have p4010_2 := h4010c.2.2.1
                                have p4010_3 := h4010c.2.2.2
                                linarith only [hlam, p4010_0]
                        · linarith only [h0, h2319, h2841, h3789, h3998, h4005, hc01, hc12, hlam, hphi]
                      · linarith only [h2841, h3789, h4004, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4097 | h4097
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4098 | h4098
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4099 | h4099
                          · linarith only [h2512, h4003, h4099, hc01, hc24, hlam, hphi, ht12]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4101 | h4101
                            · linarith only [h2512, h3788, h4003, h4101, hlam]
                            · rcases h1bigk with h4103c | h4103c | h4103c | h4103c | h4103c | h4103c | h4103c | h4103c | h4103c | h4103c | h4103c | h4103c | h4103c | h4103c | h4103c | h4103c | h4103c | h4103c | h4103c | h4103c | h4103c | h4103c | h4103c | h4103c | h4103c
                              · have p4103_0 := h4103c.1
                                have p4103_1 := h4103c.2.1
                                have p4103_2 := h4103c.2.2.1
                                have p4103_3 := h4103c.2.2.2
                                linarith only [hlam, p4103_0]
                              · have p4103_0 := h4103c.1
                                have p4103_1 := h4103c.2.1
                                have p4103_2 := h4103c.2.2.1
                                have p4103_3 := h4103c.2.2.2
                                linarith only [h0, hlam, p4103_0]
                              · have p4103_0 := h4103c.1
                                have p4103_1 := h4103c.2.1
                                have p4103_2 := h4103c.2.2.1
                                have p4103_3 := h4103c.2.2.2
                                linarith only [h2319, hlam, p4103_0]
                              · have p4103_0 := h4103c.1
                                have p4103_1 := h4103c.2.1
                                have p4103_2 := h4103c.2.2.1
                                have p4103_3 := h4103c.2.2.2
                                linarith only [h2512, hlam, p4103_0]
                              · have p4103_0 := h4103c.1
                                have p4103_1 := h4103c.2.1
                                have p4103_2 := h4103c.2.2.1
                                have p4103_3 := h4103c.2.2.2
                                linarith only [h2736, hlam, p4103_0]
                              · have p4103_0 := h4103c.1
                                have p4103_1 := h4103c.2.1
                                have p4103_2 := h4103c.2.2.1
                                have p4103_3 := h4103c.2.2.2
                                rcases p4103_3 (m.d 0 1) (by simp) with h4109 | h4109
                                · linarith only [h4109, hlam, p4103_0]
                                · rcases p4103_3 (m.d 1 2) (by simp) with h4111 | h4111
                                  · rcases p4103_3 (m.d 1 3) (by simp) with h4112 | h4112
                                    · linarith only [h3998, h4112, hlam]
                                    · linarith only [h2319, h4112, hlam]
                                  · linarith only [h4111, hlam, p4103_0]
                              · have p4103_0 := h4103c.1
                                have p4103_1 := h4103c.2.1
                                have p4103_2 := h4103c.2.2.1
                                have p4103_3 := h4103c.2.2.2
                                linarith only [hlam, p4103_0]
                              · have p4103_0 := h4103c.1
                                have p4103_1 := h4103c.2.1
                                have p4103_2 := h4103c.2.2.1
                                have p4103_3 := h4103c.2.2.2
                                linarith only [h2319, hc01, hc12, hlam, hphi, p4103_1]
                              · have p4103_0 := h4103c.1
                                have p4103_1 := h4103c.2.1
                                have p4103_2 := h4103c.2.2.1
                                have p4103_3 := h4103c.2.2.2
                                linarith only [h2512, hc01, hc12, hlam, hphi, p4103_1]
                              · have p4103_0 := h4103c.1
                                have p4103_1 := h4103c.2.1
                                have p4103_2 := h4103c.2.2.1
                                have p4103_3 := h4103c.2.2.2
                                linarith only [h2736, hc01, hc12, hlam, hphi, p4103_1]
                              · have p4103_0 := h4103c.1
                                have p4103_1 := h4103c.2.1
                                have p4103_2 := h4103c.2.2.1
                                have p4103_3 := h4103c.2.2.2
                                rcases p4103_3 (m.d 0 1) (by simp) with h4120 | h4120
                                · linarith only [h4120, hlam, p4103_0]
                                · rcases p4103_3 (m.d 1 2) (by simp) with h4122 | h4122
                                  · rcases p4103_3 (m.d 1 3) (by simp) with h4123 | h4123
                                    · rcases p4103_3 (m.d 1 4) (by simp) with h4124 | h4124
                                      · linarith only [h4001, h4124, hlam]
                                      · linarith only [h2512, h4124, hlam]
                                    · linarith only [h4123, hlam, p4103_0]
                                  · linarith only [h0, h4122, hlam]
                              · have p4103_0 := h4103c.1
                                have p4103_1 := h4103c.2.1
                                have p4103_2 := h4103c.2.2.1
                                have p4103_3 := h4103c.2.2.2
                                linarith only [h3998, hlam, p4103_1]
                              · have p4103_0 := h4103c.1
                                have p4103_1 := h4103c.2.1
                                have p4103_2 := h4103c.2.2.1
                                have p4103_3 := h4103c.2.2.2
                                linarith only [hlam, p4103_0]
                              · have p4103_0 := h4103c.1
                                have p4103_1 := h4103c.2.1
                                have p4103_2 := h4103c.2.2.1
                                have p4103_3 := h4103c.2.2.2
                                linarith only [h2512, hc01, hc13, hlam, hphi, p4103_1]
                              · have p4103_0 := h4103c.1
                                have p4103_1 := h4103c.2.1
                                have p4103_2 := h4103c.2.2.1
                                have p4103_3 := h4103c.2.2.2
                                linarith only [h2736, h3998, hc01, hc12, hlam, hphi, p4103_1]
                              · have p4103_0 := h4103c.1
                                have p4103_1 := h4103c.2.1
                                have p4103_2 := h4103c.2.2.1
                                have p4103_3 := h4103c.2.2.2
                                linarith only [h2841, h3789, h3998, h4003, h4101, hc01, hc12, hc45, hlam, hphi, ht34, p4103_1, u3ehi3]
                              · have p4103_0 := h4103c.1
                                have p4103_1 := h4103c.2.1
                                have p4103_2 := h4103c.2.2.1
                                have p4103_3 := h4103c.2.2.2
                                linarith only [h3999, hlam, p4103_1]
                              · have p4103_0 := h4103c.1
                                have p4103_1 := h4103c.2.1
                                have p4103_2 := h4103c.2.2.1
                                have p4103_3 := h4103c.2.2.2
                                linarith only [h4001, hlam, p4103_0]
                              · have p4103_0 := h4103c.1
                                have p4103_1 := h4103c.2.1
                                have p4103_2 := h4103c.2.2.1
                                have p4103_3 := h4103c.2.2.2
                                linarith only [hlam, p4103_0]
                              · have p4103_0 := h4103c.1
                                have p4103_1 := h4103c.2.1
                                have p4103_2 := h4103c.2.2.1
                                have p4103_3 := h4103c.2.2.2
                                linarith only [h4003, hlam, p4103_1]
                              · have p4103_0 := h4103c.1
                                have p4103_1 := h4103c.2.1
                                have p4103_2 := h4103c.2.2.1
                                have p4103_3 := h4103c.2.2.2
                                rcases p4103_3 (m.d 0 1) (by simp) with h4138 | h4138
                                · linarith only [h4138, hlam, p4103_0]
                                · rcases p4103_3 (m.d 1 2) (by simp) with h4140 | h4140
                                  · rcases p4103_3 (m.d 1 3) (by simp) with h4141 | h4141
                                    · rcases p4103_3 (m.d 1 4) (by simp) with h4142 | h4142
                                      · linarith only [h4003, h4142, hlam]
                                      · linarith only [h2512, h4142, hlam]
                                    · linarith only [h2319, h4141, hlam]
                                  · linarith only [h0, h4140, hlam]
                              · have p4103_0 := h4103c.1
                                have p4103_1 := h4103c.2.1
                                have p4103_2 := h4103c.2.2.1
                                have p4103_3 := h4103c.2.2.2
                                linarith only [h4000, hlam, p4103_1]
                              · have p4103_0 := h4103c.1
                                have p4103_1 := h4103c.2.1
                                have p4103_2 := h4103c.2.2.1
                                have p4103_3 := h4103c.2.2.2
                                linarith only [h4002, hlam, p4103_0]
                              · have p4103_0 := h4103c.1
                                have p4103_1 := h4103c.2.1
                                have p4103_2 := h4103c.2.2.1
                                have p4103_3 := h4103c.2.2.2
                                linarith only [h2512, hc01, hc15, hlam, hphi, p4103_1]
                              · have p4103_0 := h4103c.1
                                have p4103_1 := h4103c.2.1
                                have p4103_2 := h4103c.2.2.1
                                have p4103_3 := h4103c.2.2.2
                                linarith only [hlam, p4103_0]
                        · linarith only [h2841, h3789, h4098, hlam]
                      · linarith only [h2841, h3789, h4097, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h2841, h3789, h3998, h4002, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h2841, h3788, h3998, h4001, hlam]
              · linarith only [h2841, h3788, h3998, h4000, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
            · linarith only [h2841, h3788, h3998, h3999, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4157 | h4157
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4158 | h4158
              · linarith only [h0, h3585, h3998, h4158, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4160 | h4160
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4161 | h4161
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4162 | h4162
                    · linarith only [h3788, h3790, h3998, h4157, h4162, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4164 | h4164
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4165 | h4165
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4166 | h4166
                          · linarith only [h4157, h4158, h4162, h4165, h4166, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h4157, h4158, h4164, h4166, hc45, hlam, hphi, ht34, u3ehi3]
                        · linarith only [h0, h2319, h2841, h3789, h4165, hc01, hc13, hlam, hphi]
                      · linarith only [h2319, h3788, h3998, h4164, hlam]
                  · linarith only [h2319, h3789, h4161, hlam]
                · linarith only [h2319, h3789, h4160, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4173 | h4173
              · linarith only [h0, h3585, h3998, h4173, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4175 | h4175
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4176 | h4176
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4177 | h4177
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4178 | h4178
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4179 | h4179
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4180 | h4180
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4181 | h4181
                            · linarith only [h3788, h3790, h4181, hlam]
                            · rcases h1bigk with h4183c | h4183c | h4183c | h4183c | h4183c | h4183c | h4183c | h4183c | h4183c | h4183c | h4183c | h4183c | h4183c | h4183c | h4183c | h4183c | h4183c | h4183c | h4183c | h4183c | h4183c | h4183c | h4183c | h4183c | h4183c
                              · have p4183_0 := h4183c.1
                                have p4183_1 := h4183c.2.1
                                have p4183_2 := h4183c.2.2.1
                                have p4183_3 := h4183c.2.2.2
                                linarith only [hlam, p4183_0]
                              · have p4183_0 := h4183c.1
                                have p4183_1 := h4183c.2.1
                                have p4183_2 := h4183c.2.2.1
                                have p4183_3 := h4183c.2.2.2
                                linarith only [h0, hlam, p4183_0]
                              · have p4183_0 := h4183c.1
                                have p4183_1 := h4183c.2.1
                                have p4183_2 := h4183c.2.2.1
                                have p4183_3 := h4183c.2.2.2
                                linarith only [h2319, hlam, p4183_0]
                              · have p4183_0 := h4183c.1
                                have p4183_1 := h4183c.2.1
                                have p4183_2 := h4183c.2.2.1
                                have p4183_3 := h4183c.2.2.2
                                linarith only [h2512, hlam, p4183_0]
                              · have p4183_0 := h4183c.1
                                have p4183_1 := h4183c.2.1
                                have p4183_2 := h4183c.2.2.1
                                have p4183_3 := h4183c.2.2.2
                                linarith only [h2736, hlam, p4183_0]
                              · have p4183_0 := h4183c.1
                                have p4183_1 := h4183c.2.1
                                have p4183_2 := h4183c.2.2.1
                                have p4183_3 := h4183c.2.2.2
                                linarith only [h4173, hc01, hc25, hlam, hphi, ht12, p4183_1]
                              · have p4183_0 := h4183c.1
                                have p4183_1 := h4183c.2.1
                                have p4183_2 := h4183c.2.2.1
                                have p4183_3 := h4183c.2.2.2
                                linarith only [hlam, p4183_0]
                              · have p4183_0 := h4183c.1
                                have p4183_1 := h4183c.2.1
                                have p4183_2 := h4183c.2.2.1
                                have p4183_3 := h4183c.2.2.2
                                linarith only [h3998, hlam, p4183_0]
                              · have p4183_0 := h4183c.1
                                have p4183_1 := h4183c.2.1
                                have p4183_2 := h4183c.2.2.1
                                have p4183_3 := h4183c.2.2.2
                                linarith only [h4157, hlam, p4183_0]
                              · have p4183_0 := h4183c.1
                                have p4183_1 := h4183c.2.1
                                have p4183_2 := h4183c.2.2.1
                                have p4183_3 := h4183c.2.2.2
                                linarith only [h4173, hlam, p4183_0]
                              · have p4183_0 := h4183c.1
                                have p4183_1 := h4183c.2.1
                                have p4183_2 := h4183c.2.2.1
                                have p4183_3 := h4183c.2.2.2
                                rcases p4183_3 (m.d 0 1) (by simp) with h4194 | h4194
                                · linarith only [h4194, hlam, p4183_0]
                                · rcases p4183_3 (m.d 1 2) (by simp) with h4196 | h4196
                                  · linarith only [h3998, h4196, hlam]
                                  · linarith only [h0, h4196, hlam]
                              · have p4183_0 := h4183c.1
                                have p4183_1 := h4183c.2.1
                                have p4183_2 := h4183c.2.2.1
                                have p4183_3 := h4183c.2.2.2
                                linarith only [h0, h3998, hc01, hc23, hlam, hphi, ht12, p4183_1]
                              · have p4183_0 := h4183c.1
                                have p4183_1 := h4183c.2.1
                                have p4183_2 := h4183c.2.2.1
                                have p4183_3 := h4183c.2.2.2
                                linarith only [hlam, p4183_0]
                              · have p4183_0 := h4183c.1
                                have p4183_1 := h4183c.2.1
                                have p4183_2 := h4183c.2.2.1
                                have p4183_3 := h4183c.2.2.2
                                linarith only [h3790, h3998, h4177, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4183_1]
                              · have p4183_0 := h4183c.1
                                have p4183_1 := h4183c.2.1
                                have p4183_2 := h4183c.2.2.1
                                have p4183_3 := h4183c.2.2.2
                                linarith only [h2736, h3998, hc01, hc23, hlam, hphi, ht12, p4183_1]
                              · have p4183_0 := h4183c.1
                                have p4183_1 := h4183c.2.1
                                have p4183_2 := h4183c.2.2.1
                                have p4183_3 := h4183c.2.2.2
                                rcases p4183_3 (m.d 0 1) (by simp) with h4203 | h4203
                                · linarith only [h4203, hlam, p4183_0]
                                · rcases p4183_3 (m.d 1 2) (by simp) with h4205 | h4205
                                  · linarith only [h4157, h4205, hlam]
                                  · linarith only [h0, h4205, hlam]
                              · have p4183_0 := h4183c.1
                                have p4183_1 := h4183c.2.1
                                have p4183_2 := h4183c.2.2.1
                                have p4183_3 := h4183c.2.2.2
                                linarith only [h0, hc01, hc14, hlam, hphi, p4183_1]
                              · have p4183_0 := h4183c.1
                                have p4183_1 := h4183c.2.1
                                have p4183_2 := h4183c.2.2.1
                                have p4183_3 := h4183c.2.2.2
                                linarith only [h4175, hlam, p4183_0]
                              · have p4183_0 := h4183c.1
                                have p4183_1 := h4183c.2.1
                                have p4183_2 := h4183c.2.2.1
                                have p4183_3 := h4183c.2.2.2
                                linarith only [hlam, p4183_0]
                              · have p4183_0 := h4183c.1
                                have p4183_1 := h4183c.2.1
                                have p4183_2 := h4183c.2.2.1
                                have p4183_3 := h4183c.2.2.2
                                linarith only [h3788, h3790, h4157, h4177, h4178, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4183_1, u3ehi3]
                              · have p4183_0 := h4183c.1
                                have p4183_1 := h4183c.2.1
                                have p4183_2 := h4183c.2.2.1
                                have p4183_3 := h4183c.2.2.2
                                rcases p4183_3 (m.d 0 1) (by simp) with h4212 | h4212
                                · linarith only [h4212, hlam, p4183_0]
                                · rcases p4183_3 (m.d 1 2) (by simp) with h4214 | h4214
                                  · linarith only [h4173, h4214, hlam]
                                  · linarith only [h0, h4214, hlam]
                              · have p4183_0 := h4183c.1
                                have p4183_1 := h4183c.2.1
                                have p4183_2 := h4183c.2.2.1
                                have p4183_3 := h4183c.2.2.2
                                linarith only [h0, hc01, hc15, hlam, hphi, p4183_1]
                              · have p4183_0 := h4183c.1
                                have p4183_1 := h4183c.2.1
                                have p4183_2 := h4183c.2.2.1
                                have p4183_3 := h4183c.2.2.2
                                linarith only [h4176, hlam, p4183_0]
                              · have p4183_0 := h4183c.1
                                have p4183_1 := h4183c.2.1
                                have p4183_2 := h4183c.2.2.1
                                have p4183_3 := h4183c.2.2.2
                                linarith only [h4177, hlam, p4183_0]
                              · have p4183_0 := h4183c.1
                                have p4183_1 := h4183c.2.1
                                have p4183_2 := h4183c.2.2.1
                                have p4183_3 := h4183c.2.2.2
                                linarith only [hlam, p4183_0]
                          · linarith only [h0, h4157, h4180, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h3789, h3790, h3998, h4175, h4177, h4179, hlam]
                      · linarith only [h3788, h3790, h3998, h4175, h4177, h4178, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4224 | h4224
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4225 | h4225
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4226 | h4226
                          · linarith only [h0, h4157, h4177, h4226, hc01, hc24, hlam, hphi, ht12]
                          · linarith only [h0, h4157, h4226, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h2319, h3789, h3998, h4225, hlam]
                      · linarith only [h2319, h3789, h3998, h4224, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h2319, h3789, h4176, hlam]
                · linarith only [h2319, h3788, h3790, h4175, hc45, hlam, hphi, ht34, u3ehi0]
      · linarith only [h3788, h3789, hc35, hlam, hphi, u3ehi3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4234 | h4234
      · linarith only [h3788, h4234, hc34, hlam, hphi, u3ehi4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4236 | h4236
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4237 | h4237
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4238 | h4238
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4239 | h4239
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4240 | h4240
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4241 | h4241
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4242 | h4242
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4243 | h4243
                      · linarith only [h3788, h4237, h4243, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h0, h2841, h4237, h4240, h4243, hc01, hc12, hlam, hphi]
                    · linarith only [h2512, h4236, h4242, hlam]
                  · linarith only [h4240, h4241, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4248 | h4248
                  · linarith only [h4240, h4248, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4250 | h4250
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4251 | h4251
                      · linarith only [h2319, h4240, h4251, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4253 | h4253
                        · linarith only [h4237, h4248, h4253, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4255 | h4255
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4256 | h4256
                            · rcases h1bigk with h4257c | h4257c | h4257c | h4257c | h4257c | h4257c | h4257c | h4257c | h4257c | h4257c | h4257c | h4257c | h4257c | h4257c | h4257c | h4257c | h4257c | h4257c | h4257c | h4257c | h4257c | h4257c | h4257c | h4257c | h4257c
                              · have p4257_0 := h4257c.1
                                have p4257_1 := h4257c.2.1
                                have p4257_2 := h4257c.2.2.1
                                have p4257_3 := h4257c.2.2.2
                                linarith only [hlam, p4257_0]
                              · have p4257_0 := h4257c.1
                                have p4257_1 := h4257c.2.1
                                have p4257_2 := h4257c.2.2.1
                                have p4257_3 := h4257c.2.2.2
                                linarith only [h0, hlam, p4257_0]
                              · have p4257_0 := h4257c.1
                                have p4257_1 := h4257c.2.1
                                have p4257_2 := h4257c.2.2.1
                                have p4257_3 := h4257c.2.2.2
                                linarith only [h2319, hlam, p4257_0]
                              · have p4257_0 := h4257c.1
                                have p4257_1 := h4257c.2.1
                                have p4257_2 := h4257c.2.2.1
                                have p4257_3 := h4257c.2.2.2
                                linarith only [h2512, hlam, p4257_0]
                              · have p4257_0 := h4257c.1
                                have p4257_1 := h4257c.2.1
                                have p4257_2 := h4257c.2.2.1
                                have p4257_3 := h4257c.2.2.2
                                linarith only [h2736, hlam, p4257_0]
                              · have p4257_0 := h4257c.1
                                have p4257_1 := h4257c.2.1
                                have p4257_2 := h4257c.2.2.1
                                have p4257_3 := h4257c.2.2.2
                                rcases p4257_3 (m.d 0 1) (by simp) with h4263 | h4263
                                · linarith only [h4263, hlam, p4257_0]
                                · rcases p4257_3 (m.d 1 2) (by simp) with h4265 | h4265
                                  · rcases p4257_3 (m.d 1 3) (by simp) with h4266 | h4266
                                    · linarith only [h4237, h4266, hlam]
                                    · linarith only [h2319, h4266, hlam]
                                  · linarith only [h4265, hlam, p4257_0]
                              · have p4257_0 := h4257c.1
                                have p4257_1 := h4257c.2.1
                                have p4257_2 := h4257c.2.2.1
                                have p4257_3 := h4257c.2.2.2
                                linarith only [hlam, p4257_0]
                              · have p4257_0 := h4257c.1
                                have p4257_1 := h4257c.2.1
                                have p4257_2 := h4257c.2.2.1
                                have p4257_3 := h4257c.2.2.2
                                linarith only [h0, h2841, h4237, hc01, hc12, hlam, hphi, p4257_1]
                              · have p4257_0 := h4257c.1
                                have p4257_1 := h4257c.2.1
                                have p4257_2 := h4257c.2.2.1
                                have p4257_3 := h4257c.2.2.2
                                linarith only [h2512, hc01, hc12, hlam, hphi, p4257_1]
                              · have p4257_0 := h4257c.1
                                have p4257_1 := h4257c.2.1
                                have p4257_2 := h4257c.2.2.1
                                have p4257_3 := h4257c.2.2.2
                                linarith only [h2736, hc01, hc12, hlam, hphi, p4257_1]
                              · have p4257_0 := h4257c.1
                                have p4257_1 := h4257c.2.1
                                have p4257_2 := h4257c.2.2.1
                                have p4257_3 := h4257c.2.2.2
                                linarith only [h4248, h4256, hc01, hc34, hlam, hphi, ht12, ht23, p4257_1]
                              · have p4257_0 := h4257c.1
                                have p4257_1 := h4257c.2.1
                                have p4257_2 := h4257c.2.2.1
                                have p4257_3 := h4257c.2.2.2
                                linarith only [h4237, hlam, p4257_1]
                              · have p4257_0 := h4257c.1
                                have p4257_1 := h4257c.2.1
                                have p4257_2 := h4257c.2.2.1
                                have p4257_3 := h4257c.2.2.2
                                linarith only [hlam, p4257_0]
                              · have p4257_0 := h4257c.1
                                have p4257_1 := h4257c.2.1
                                have p4257_2 := h4257c.2.2.1
                                have p4257_3 := h4257c.2.2.2
                                linarith only [h4240, hlam, p4257_1]
                              · have p4257_0 := h4257c.1
                                have p4257_1 := h4257c.2.1
                                have p4257_2 := h4257c.2.2.1
                                have p4257_3 := h4257c.2.2.2
                                linarith only [h4248, hlam, p4257_1]
                              · have p4257_0 := h4257c.1
                                have p4257_1 := h4257c.2.1
                                have p4257_2 := h4257c.2.2.1
                                have p4257_3 := h4257c.2.2.2
                                rcases p4257_3 (m.d 0 1) (by simp) with h4279 | h4279
                                · linarith only [h4279, hlam, p4257_0]
                                · rcases p4257_3 (m.d 1 2) (by simp) with h4281 | h4281
                                  · rcases p4257_3 (m.d 1 3) (by simp) with h4282 | h4282
                                    · linarith only [h4240, h4282, hlam]
                                    · linarith only [h2319, h4282, hlam]
                                  · linarith only [h0, h4281, hlam]
                              · have p4257_0 := h4257c.1
                                have p4257_1 := h4257c.2.1
                                have p4257_2 := h4257c.2.2.1
                                have p4257_3 := h4257c.2.2.2
                                linarith only [h4238, hlam, p4257_1]
                              · have p4257_0 := h4257c.1
                                have p4257_1 := h4257c.2.1
                                have p4257_2 := h4257c.2.2.1
                                have p4257_3 := h4257c.2.2.2
                                linarith only [h0, h2841, h4237, hc01, hc14, hlam, hphi, p4257_1]
                              · have p4257_0 := h4257c.1
                                have p4257_1 := h4257c.2.1
                                have p4257_2 := h4257c.2.2.1
                                have p4257_3 := h4257c.2.2.2
                                linarith only [hlam, p4257_0]
                              · have p4257_0 := h4257c.1
                                have p4257_1 := h4257c.2.1
                                have p4257_2 := h4257c.2.2.1
                                have p4257_3 := h4257c.2.2.2
                                linarith only [h0, h2841, h4237, h4240, h4248, hc01, hc34, hlam, hphi, ht12, ht23, p4257_1]
                              · have p4257_0 := h4257c.1
                                have p4257_1 := h4257c.2.1
                                have p4257_2 := h4257c.2.2.1
                                have p4257_3 := h4257c.2.2.2
                                rcases p4257_3 (m.d 0 1) (by simp) with h4290 | h4290
                                · linarith only [h4290, hlam, p4257_0]
                                · rcases p4257_3 (m.d 1 2) (by simp) with h4292 | h4292
                                  · rcases p4257_3 (m.d 1 3) (by simp) with h4293 | h4293
                                    · linarith only [h4248, h4293, hlam]
                                    · linarith only [h2319, h4293, hlam]
                                  · linarith only [h0, h4292, hlam]
                              · have p4257_0 := h4257c.1
                                have p4257_1 := h4257c.2.1
                                have p4257_2 := h4257c.2.2.1
                                have p4257_3 := h4257c.2.2.2
                                linarith only [h4239, hlam, p4257_1]
                              · have p4257_0 := h4257c.1
                                have p4257_1 := h4257c.2.1
                                have p4257_2 := h4257c.2.2.1
                                have p4257_3 := h4257c.2.2.2
                                linarith only [h0, h2841, h4237, hc01, hc15, hlam, hphi, p4257_1]
                              · have p4257_0 := h4257c.1
                                have p4257_1 := h4257c.2.1
                                have p4257_2 := h4257c.2.2.1
                                have p4257_3 := h4257c.2.2.2
                                linarith only [h4250, hlam, p4257_0]
                              · have p4257_0 := h4257c.1
                                have p4257_1 := h4257c.2.1
                                have p4257_2 := h4257c.2.2.1
                                have p4257_3 := h4257c.2.2.2
                                linarith only [hlam, p4257_0]
                            · linarith only [h2512, h4240, h4255, h4256, hc01, hc24, hlam, hphi, ht12]
                          · linarith only [h0, h2512, h2841, h4236, h4251, h4255, hc01, hc14, hlam, hphi]
                    · linarith only [h2512, h4236, h4250, hlam]
              · linarith only [h0, h2841, h4237, h4239, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h2841, h4237, h4238, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4306 | h4306
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4307 | h4307
              · linarith only [h0, h3585, h4237, h4307, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4309 | h4309
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4310 | h4310
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4311 | h4311
                    · linarith only [h4306, h4307, h4311, hlam]
                    · linarith only [h3788, h4236, h4309, h4311, hlam]
                  · linarith only [h3788, h4309, h4310, hc35, hlam, hphi, u3ehi0]
                · linarith only [h4237, h4306, h4309, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4316 | h4316
              · linarith only [h0, h3585, h4306, h4316, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4318 | h4318
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4319 | h4319
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4320 | h4320
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4321 | h4321
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4322 | h4322
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4323 | h4323
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4324 | h4324
                            · rcases h1bigk with h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c
                              · have p4325_0 := h4325c.1
                                have p4325_1 := h4325c.2.1
                                have p4325_2 := h4325c.2.2.1
                                have p4325_3 := h4325c.2.2.2
                                linarith only [hlam, p4325_0]
                              · have p4325_0 := h4325c.1
                                have p4325_1 := h4325c.2.1
                                have p4325_2 := h4325c.2.2.1
                                have p4325_3 := h4325c.2.2.2
                                linarith only [h0, hlam, p4325_0]
                              · have p4325_0 := h4325c.1
                                have p4325_1 := h4325c.2.1
                                have p4325_2 := h4325c.2.2.1
                                have p4325_3 := h4325c.2.2.2
                                linarith only [h2319, hlam, p4325_0]
                              · have p4325_0 := h4325c.1
                                have p4325_1 := h4325c.2.1
                                have p4325_2 := h4325c.2.2.1
                                have p4325_3 := h4325c.2.2.2
                                linarith only [h2512, hlam, p4325_0]
                              · have p4325_0 := h4325c.1
                                have p4325_1 := h4325c.2.1
                                have p4325_2 := h4325c.2.2.1
                                have p4325_3 := h4325c.2.2.2
                                linarith only [h2736, hlam, p4325_0]
                              · have p4325_0 := h4325c.1
                                have p4325_1 := h4325c.2.1
                                have p4325_2 := h4325c.2.2.1
                                have p4325_3 := h4325c.2.2.2
                                linarith only [h4316, h4321, h4323, hc01, hc23, hlam, hphi, ht12, p4325_1]
                              · have p4325_0 := h4325c.1
                                have p4325_1 := h4325c.2.1
                                have p4325_2 := h4325c.2.2.1
                                have p4325_3 := h4325c.2.2.2
                                linarith only [hlam, p4325_0]
                              · have p4325_0 := h4325c.1
                                have p4325_1 := h4325c.2.1
                                have p4325_2 := h4325c.2.2.1
                                have p4325_3 := h4325c.2.2.2
                                linarith only [h4237, hlam, p4325_0]
                              · have p4325_0 := h4325c.1
                                have p4325_1 := h4325c.2.1
                                have p4325_2 := h4325c.2.2.1
                                have p4325_3 := h4325c.2.2.2
                                linarith only [h4306, hlam, p4325_0]
                              · have p4325_0 := h4325c.1
                                have p4325_1 := h4325c.2.1
                                have p4325_2 := h4325c.2.2.1
                                have p4325_3 := h4325c.2.2.2
                                linarith only [h4316, hlam, p4325_0]
                              · have p4325_0 := h4325c.1
                                have p4325_1 := h4325c.2.1
                                have p4325_2 := h4325c.2.2.1
                                have p4325_3 := h4325c.2.2.2
                                rcases p4325_3 (m.d 0 1) (by simp) with h4336 | h4336
                                · linarith only [h4336, hlam, p4325_0]
                                · rcases p4325_3 (m.d 1 2) (by simp) with h4338 | h4338
                                  · linarith only [h4237, h4338, hlam]
                                  · linarith only [h0, h4338, hlam]
                              · have p4325_0 := h4325c.1
                                have p4325_1 := h4325c.2.1
                                have p4325_2 := h4325c.2.2.1
                                have p4325_3 := h4325c.2.2.2
                                linarith only [h0, h4237, hc01, hc23, hlam, hphi, ht12, p4325_1]
                              · have p4325_0 := h4325c.1
                                have p4325_1 := h4325c.2.1
                                have p4325_2 := h4325c.2.2.1
                                have p4325_3 := h4325c.2.2.2
                                linarith only [hlam, p4325_0]
                              · have p4325_0 := h4325c.1
                                have p4325_1 := h4325c.2.1
                                have p4325_2 := h4325c.2.2.1
                                have p4325_3 := h4325c.2.2.2
                                linarith only [h4234, h4237, h4319, h4320, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4325_1, u3ehi0]
                              · have p4325_0 := h4325c.1
                                have p4325_1 := h4325c.2.1
                                have p4325_2 := h4325c.2.2.1
                                have p4325_3 := h4325c.2.2.2
                                linarith only [h4234, h4237, h4319, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4325_1, u3ehi0]
                              · have p4325_0 := h4325c.1
                                have p4325_1 := h4325c.2.1
                                have p4325_2 := h4325c.2.2.1
                                have p4325_3 := h4325c.2.2.2
                                rcases p4325_3 (m.d 0 1) (by simp) with h4345 | h4345
                                · linarith only [h4345, hlam, p4325_0]
                                · rcases p4325_3 (m.d 1 2) (by simp) with h4347 | h4347
                                  · linarith only [h4306, h4347, hlam]
                                  · linarith only [h0, h4347, hlam]
                              · have p4325_0 := h4325c.1
                                have p4325_1 := h4325c.2.1
                                have p4325_2 := h4325c.2.2.1
                                have p4325_3 := h4325c.2.2.2
                                linarith only [h0, hc01, hc14, hlam, hphi, p4325_1]
                              · have p4325_0 := h4325c.1
                                have p4325_1 := h4325c.2.1
                                have p4325_2 := h4325c.2.2.1
                                have p4325_3 := h4325c.2.2.2
                                linarith only [h4318, hlam, p4325_0]
                              · have p4325_0 := h4325c.1
                                have p4325_1 := h4325c.2.1
                                have p4325_2 := h4325c.2.2.1
                                have p4325_3 := h4325c.2.2.2
                                linarith only [hlam, p4325_0]
                              · have p4325_0 := h4325c.1
                                have p4325_1 := h4325c.2.1
                                have p4325_2 := h4325c.2.2.1
                                have p4325_3 := h4325c.2.2.2
                                linarith only [h4234, h4306, h4319, h4321, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4325_1, u3ehi0]
                              · have p4325_0 := h4325c.1
                                have p4325_1 := h4325c.2.1
                                have p4325_2 := h4325c.2.2.1
                                have p4325_3 := h4325c.2.2.2
                                rcases p4325_3 (m.d 0 1) (by simp) with h4354 | h4354
                                · linarith only [h4354, hlam, p4325_0]
                                · rcases p4325_3 (m.d 1 2) (by simp) with h4356 | h4356
                                  · linarith only [h4316, h4356, hlam]
                                  · linarith only [h0, h4356, hlam]
                              · have p4325_0 := h4325c.1
                                have p4325_1 := h4325c.2.1
                                have p4325_2 := h4325c.2.2.1
                                have p4325_3 := h4325c.2.2.2
                                linarith only [h0, hc01, hc15, hlam, hphi, p4325_1]
                              · have p4325_0 := h4325c.1
                                have p4325_1 := h4325c.2.1
                                have p4325_2 := h4325c.2.2.1
                                have p4325_3 := h4325c.2.2.2
                                linarith only [h4319, hlam, p4325_0]
                              · have p4325_0 := h4325c.1
                                have p4325_1 := h4325c.2.1
                                have p4325_2 := h4325c.2.2.1
                                have p4325_3 := h4325c.2.2.2
                                linarith only [h4320, hlam, p4325_0]
                              · have p4325_0 := h4325c.1
                                have p4325_1 := h4325c.2.1
                                have p4325_2 := h4325c.2.2.1
                                have p4325_3 := h4325c.2.2.2
                                linarith only [hlam, p4325_0]
                            · linarith only [h3788, h4236, h4324, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                          · linarith only [h2512, h3788, h4236, h4306, h4323, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h4237, h4318, h4322, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h4237, h4318, h4321, hlam]
                    · linarith only [h2512, h3788, h4236, h4237, h4318, h4320, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h3788, h4318, h4319, hc35, hlam, hphi, u3ehi0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4369 | h4369
                  · linarith only [h4318, h4369, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4371 | h4371
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4372 | h4372
                      · linarith only [h2319, h4318, h4372, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h4237, h4372, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h2512, h4236, h4371, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4376 | h4376
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4377 | h4377
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4378 | h4378
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4379 | h4379
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4380 | h4380
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4381 | h4381
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4382 | h4382
                      · linarith only [h3788, h4376, h4382, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h0, h2841, h4379, h4382, hc01, hc13, hlam, hphi]
                    · linarith only [h3788, h4379, h4381, hc45, hlam, hphi, ht34, u3ehi0]
                  · linarith only [h3788, h4379, h4380, hc35, hlam, hphi, u3ehi0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4387 | h4387
                  · linarith only [h4379, h4387, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4389 | h4389
                    · linarith only [h3788, h4236, h4379, h4389, hc34, hlam, hphi, u3ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4391 | h4391
                      · linarith only [h4376, h4387, h4391, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4393 | h4393
                        · linarith only [h4376, h4387, h4393, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4395 | h4395
                          · linarith only [h4377, h4389, h4395, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4397 | h4397
                            · linarith only [h0, h2841, h4376, h4379, h4389, h4397, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h3788, h4397, hc45, hlam, hphi, ht34, u3ehi0]
              · linarith only [h0, h2841, h4376, h4378, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h2841, h4376, h4377, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4402 | h4402
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4403 | h4403
              · linarith only [h0, h3585, h4376, h4403, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4405 | h4405
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4406 | h4406
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4407 | h4407
                    · linarith only [h3788, h4236, h4376, h4402, h4407, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                    · linarith only [h3788, h4405, h4407, hc45, hlam, hphi, ht34, u3ehi0]
                  · linarith only [h3788, h4376, h4402, h4405, h4406, hc35, hlam, hphi, u3ehi0]
                · linarith only [h4376, h4402, h4405, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4412 | h4412
              · linarith only [h0, h3585, h4402, h4412, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4414 | h4414
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4415 | h4415
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4416 | h4416
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4417 | h4417
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4418 | h4418
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4419 | h4419
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4420 | h4420
                            · linarith only [h3788, h4236, h4420, hc34, hlam, hphi, u3ehi0]
                            · linarith only [h3788, h4416, h4420, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                          · linarith only [h4402, h4416, h4419, hlam]
                        · linarith only [h2512, h4236, h4402, h4416, h4417, h4418, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h3788, h4236, h4376, h4414, h4416, h4417, hc34, hlam, hphi, u3ehi0]
                    · linarith only [h3788, h4414, h4416, hc45, hlam, hphi, ht34, u3ehi0]
                  · linarith only [h3788, h4414, h4415, hc35, hlam, hphi, u3ehi0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4428 | h4428
                  · linarith only [h4414, h4428, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4430 | h4430
                    · linarith only [h3788, h4236, h4414, h4430, hc34, hlam, hphi, u3ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4432 | h4432
                      · linarith only [h0, h4376, h4414, h4432, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h4376, h4432, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 8870000 in
theorem r1l7_11_13_25_L_I_L_R_H_I_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2319 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2512 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2736 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h2841 | h2841
  · exact r1l7_11_13_25_L_I_L_R_H_I_x1_x1_x1_x1_x0 m hb1 hb3 hb5 h0 h2319 h2512 h2736 h2841
  · exact r1l7_11_13_25_L_I_L_R_H_I_x1_x1_x1_x1_x1 m hb1 hb3 hb5 h0 h2319 h2512 h2736 h2841

set_option maxHeartbeats 8870000 in
theorem r1l7_11_13_25_L_I_L_R_H_I_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2319 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2512 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2736 | h2736
  · exact r1l7_11_13_25_L_I_L_R_H_I_x1_x1_x1_x0 m hb1 hb3 hb5 h0 h2319 h2512 h2736
  · exact r1l7_11_13_25_L_I_L_R_H_I_x1_x1_x1_x1 m hb1 hb3 hb5 h0 h2319 h2512 h2736

set_option maxHeartbeats 8870000 in
theorem r1l7_11_13_25_L_I_L_R_H_I_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2319 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2512 | h2512
  · exact r1l7_11_13_25_L_I_L_R_H_I_x1_x1_x0 m hb1 hb3 hb5 h0 h2319 h2512
  · exact r1l7_11_13_25_L_I_L_R_H_I_x1_x1_x1 m hb1 hb3 hb5 h0 h2319 h2512

set_option maxHeartbeats 8870000 in
theorem r1l7_11_13_25_L_I_L_R_H_I_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h2319 | h2319
  · exact r1l7_11_13_25_L_I_L_R_H_I_x1_x0 m hb1 hb3 hb5 h0 h2319
  · exact r1l7_11_13_25_L_I_L_R_H_I_x1_x1 m hb1 hb3 hb5 h0 h2319

end R2N4
