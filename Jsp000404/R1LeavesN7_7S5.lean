import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_7S4

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7772000 in
set_option maxHeartbeats 7772000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s7 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s8 m hb1 hb3 hb5 h0 h1 h2 h3 h4 h5 h6 h7 h8
  · rcases m.htr 0 4 5 (by decide) (by decide) with h3598 | h3598
    · linarith only [h3598, h7, h8, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3600 | h3600
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3601 | h3601
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3602 | h3602
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3603 | h3603
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3604 | h3604
              · linarith only [h1, h3604, h8, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3606 | h3606
                · linarith only [h2, h3598, h3606, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3608 | h3608
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3609 | h3609
                    · linarith only [h1, h3600, h3609, h8, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3611 | h3611
                      · linarith only [h2, h3598, h3601, h3611, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3613 | h3613
                        · linarith only [h3598, h3602, h3608, h3609, h3613, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases h1bigk with h3615c | h3615c | h3615c | h3615c | h3615c | h3615c | h3615c | h3615c | h3615c | h3615c | h3615c | h3615c | h3615c | h3615c | h3615c | h3615c | h3615c | h3615c | h3615c | h3615c | h3615c | h3615c | h3615c | h3615c | h3615c
                          · have p3615_0 := h3615c.1
                            have p3615_1 := h3615c.2.1
                            have p3615_2 := h3615c.2.2.1
                            have p3615_3 := h3615c.2.2.2
                            linarith only [hlam, p3615_0]
                          · have p3615_0 := h3615c.1
                            have p3615_1 := h3615c.2.1
                            have p3615_2 := h3615c.2.2.1
                            have p3615_3 := h3615c.2.2.2
                            linarith only [h3602, hc01, hlam, hphi, ht0b, ht5b, p3615_1, u5ehi2]
                          · have p3615_0 := h3615c.1
                            have p3615_1 := h3615c.2.1
                            have p3615_2 := h3615c.2.2.1
                            have p3615_3 := h3615c.2.2.2
                            rcases p3615_3 (m.d 0 1) (by simp) with h3618 | h3618
                            · rcases p3615_3 (m.d 1 2) (by simp) with h3619 | h3619
                              · linarith only [h0, h3619, hlam]
                              · linarith only [h3600, h3619, hlam]
                            · linarith only [h3618, hlam, p3615_0]
                          · have p3615_0 := h3615c.1
                            have p3615_1 := h3615c.2.1
                            have p3615_2 := h3615c.2.2.1
                            have p3615_3 := h3615c.2.2.2
                            rcases p3615_3 (m.d 0 1) (by simp) with h3623 | h3623
                            · rcases p3615_3 (m.d 1 2) (by simp) with h3624 | h3624
                              · linarith only [h0, h3624, hlam]
                              · linarith only [h3601, h3624, hlam]
                            · linarith only [h3623, hlam, p3615_0]
                          · have p3615_0 := h3615c.1
                            have p3615_1 := h3615c.2.1
                            have p3615_2 := h3615c.2.2.1
                            have p3615_3 := h3615c.2.2.2
                            rcases p3615_3 (m.d 0 1) (by simp) with h3628 | h3628
                            · rcases p3615_3 (m.d 1 2) (by simp) with h3629 | h3629
                              · linarith only [h0, h3629, hlam]
                              · linarith only [h3602, h3629, hlam]
                            · linarith only [h3628, hlam, p3615_0]
                          · have p3615_0 := h3615c.1
                            have p3615_1 := h3615c.2.1
                            have p3615_2 := h3615c.2.2.1
                            have p3615_3 := h3615c.2.2.2
                            linarith only [h0, hlam, p3615_0]
                          · have p3615_0 := h3615c.1
                            have p3615_1 := h3615c.2.1
                            have p3615_2 := h3615c.2.2.1
                            have p3615_3 := h3615c.2.2.2
                            linarith only [hlam, p3615_0]
                          · have p3615_0 := h3615c.1
                            have p3615_1 := h3615c.2.1
                            have p3615_2 := h3615c.2.2.1
                            have p3615_3 := h3615c.2.2.2
                            linarith only [h0, h3600, h3608, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3615_1]
                          · have p3615_0 := h3615c.1
                            have p3615_1 := h3615c.2.1
                            have p3615_2 := h3615c.2.2.1
                            have p3615_3 := h3615c.2.2.2
                            rcases p3615_3 (m.d 0 1) (by simp) with h3636 | h3636
                            · rcases p3615_3 (m.d 1 2) (by simp) with h3637 | h3637
                              · rcases p3615_3 (m.d 1 3) (by simp) with h3638 | h3638
                                · linarith only [h3600, h3638, hlam]
                                · linarith only [h3603, h3638, hlam]
                              · linarith only [h3601, h3637, hlam]
                            · linarith only [h2, h3636, hlam]
                          · have p3615_0 := h3615c.1
                            have p3615_1 := h3615c.2.1
                            have p3615_2 := h3615c.2.2.1
                            have p3615_3 := h3615c.2.2.2
                            linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p3615_1, u5ehi1]
                          · have p3615_0 := h3615c.1
                            have p3615_1 := h3615c.2.1
                            have p3615_2 := h3615c.2.2.1
                            have p3615_3 := h3615c.2.2.2
                            linarith only [h1, hlam, p3615_0]
                          · have p3615_0 := h3615c.1
                            have p3615_1 := h3615c.2.1
                            have p3615_2 := h3615c.2.2.1
                            have p3615_3 := h3615c.2.2.2
                            linarith only [h3600, hlam, p3615_1]
                          · have p3615_0 := h3615c.1
                            have p3615_1 := h3615c.2.1
                            have p3615_2 := h3615c.2.2.1
                            have p3615_3 := h3615c.2.2.2
                            linarith only [hlam, p3615_0]
                          · have p3615_0 := h3615c.1
                            have p3615_1 := h3615c.2.1
                            have p3615_2 := h3615c.2.2.1
                            have p3615_3 := h3615c.2.2.2
                            linarith only [h1, h3613, h8, hc14, hc45, hlam, hphi, p3615_1]
                          · have p3615_0 := h3615c.1
                            have p3615_1 := h3615c.2.1
                            have p3615_2 := h3615c.2.2.1
                            have p3615_3 := h3615c.2.2.2
                            linarith only [h3604, hlam, p3615_1]
                          · have p3615_0 := h3615c.1
                            have p3615_1 := h3615c.2.1
                            have p3615_2 := h3615c.2.2.1
                            have p3615_3 := h3615c.2.2.2
                            linarith only [h2, hlam, p3615_0]
                          · have p3615_0 := h3615c.1
                            have p3615_1 := h3615c.2.1
                            have p3615_2 := h3615c.2.2.1
                            have p3615_3 := h3615c.2.2.2
                            linarith only [h3601, hlam, p3615_1]
                          · have p3615_0 := h3615c.1
                            have p3615_1 := h3615c.2.1
                            have p3615_2 := h3615c.2.2.1
                            have p3615_3 := h3615c.2.2.2
                            linarith only [h3603, hlam, p3615_0]
                          · have p3615_0 := h3615c.1
                            have p3615_1 := h3615c.2.1
                            have p3615_2 := h3615c.2.2.1
                            have p3615_3 := h3615c.2.2.2
                            linarith only [hlam, p3615_0]
                          · have p3615_0 := h3615c.1
                            have p3615_1 := h3615c.2.1
                            have p3615_2 := h3615c.2.2.1
                            have p3615_3 := h3615c.2.2.2
                            linarith only [h3606, hlam, p3615_1]
                          · have p3615_0 := h3615c.1
                            have p3615_1 := h3615c.2.1
                            have p3615_2 := h3615c.2.2.1
                            have p3615_3 := h3615c.2.2.2
                            linarith only [h3, hlam, p3615_0]
                          · have p3615_0 := h3615c.1
                            have p3615_1 := h3615c.2.1
                            have p3615_2 := h3615c.2.2.1
                            have p3615_3 := h3615c.2.2.2
                            linarith only [h3602, hlam, p3615_1]
                          · have p3615_0 := h3615c.1
                            have p3615_1 := h3615c.2.1
                            have p3615_2 := h3615c.2.2.1
                            have p3615_3 := h3615c.2.2.2
                            linarith only [h3, h3600, h3608, h3613, h8, hc34, hc45, hlam, hphi, p3615_1]
                          · have p3615_0 := h3615c.1
                            have p3615_1 := h3615c.2.1
                            have p3615_2 := h3615c.2.2.1
                            have p3615_3 := h3615c.2.2.2
                            rcases p3615_3 (m.d 0 1) (by simp) with h3657 | h3657
                            · rcases p3615_3 (m.d 1 2) (by simp) with h3658 | h3658
                              · rcases p3615_3 (m.d 1 3) (by simp) with h3659 | h3659
                                · linarith only [h3604, h3659, hlam]
                                · linarith only [h3603, h3659, hlam]
                              · linarith only [h3601, h3658, hlam]
                            · linarith only [h2, h3657, hlam]
                          · have p3615_0 := h3615c.1
                            have p3615_1 := h3615c.2.1
                            have p3615_2 := h3615c.2.2.1
                            have p3615_3 := h3615c.2.2.2
                            linarith only [hlam, p3615_0]
                  · linarith only [h3608, h7, h8, hc23, hc35, hlam, hphi]
            · linarith only [h3600, h3603, h7, h8, hc23, hc35, hlam, hphi]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3667 | h3667
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3668 | h3668
              · linarith only [h0, h3600, h3602, h3668, h6, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3670 | h3670
                · linarith only [h2, h3598, h3670, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3672 | h3672
                  · linarith only [h0, h3600, h3602, h3672, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h3672, h7, h8, hc23, hc35, hlam, hphi]
            · linarith only [h3667, h7, h8, hc13, hc35, hlam, hphi]
        · linarith only [h3598, h3600, h3601, h5, hc23, hc45, hlam, hphi, ht34]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3677 | h3677
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3678 | h3678
          · linarith only [h3600, h3678, h4, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3680 | h3680
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3681 | h3681
              · linarith only [h3600, h3677, h3681, h4, h8, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3683 | h3683
                · linarith only [h3598, h3600, h3677, h3683, h4, h8, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3685 | h3685
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3686 | h3686
                    · linarith only [h3686, h4, h8, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3688 | h3688
                      · linarith only [h2, h3598, h3677, h3688, h7, h8, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3690 | h3690
                        · linarith only [h3598, h3600, h3677, h3685, h3690, h4, h8, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h3600, h3677, h3690, h4, h8, hc24, hc45, hlam, hphi]
                  · linarith only [h3600, h3677, h3685, h7, h8, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
            · linarith only [h3600, h3677, h3680, h7, h8, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3695 | h3695
          · linarith only [h3598, h3677, h3695, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3697 | h3697
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3698 | h3698
              · linarith only [h1, h3698, h8, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3700 | h3700
                · linarith only [h2, h3598, h3677, h3700, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3702 | h3702
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3703 | h3703
                    · linarith only [h3677, h3703, h5, h7, h8, hc12, hc23, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3705 | h3705
                      · linarith only [h3598, h3705, h5, h7, h8, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3707 | h3707
                        · linarith only [h3598, h3677, h3707, h5, hc12, hc34, hlam, hphi, ht23]
                        · rcases h1bigk with h3709c | h3709c | h3709c | h3709c | h3709c | h3709c | h3709c | h3709c | h3709c | h3709c | h3709c | h3709c | h3709c | h3709c | h3709c | h3709c | h3709c | h3709c | h3709c | h3709c | h3709c | h3709c | h3709c | h3709c | h3709c
                          · have p3709_0 := h3709c.1
                            have p3709_1 := h3709c.2.1
                            have p3709_2 := h3709c.2.2.1
                            have p3709_3 := h3709c.2.2.2
                            linarith only [hlam, p3709_0]
                          · have p3709_0 := h3709c.1
                            have p3709_1 := h3709c.2.1
                            have p3709_2 := h3709c.2.2.1
                            have p3709_3 := h3709c.2.2.2
                            rcases p3709_3 (m.d 0 1) (by simp) with h3711 | h3711
                            · rcases p3709_3 (m.d 1 2) (by simp) with h3712 | h3712
                              · linarith only [h3712, hlam, p3709_0]
                              · rcases p3709_3 (m.d 1 3) (by simp) with h3714 | h3714
                                · linarith only [h1, h3714, hlam]
                                · linarith only [h3600, h3714, hlam]
                            · linarith only [h3711, hlam, p3709_0]
                          · have p3709_0 := h3709c.1
                            have p3709_1 := h3709c.2.1
                            have p3709_2 := h3709c.2.2.1
                            have p3709_3 := h3709c.2.2.2
                            rcases p3709_3 (m.d 0 1) (by simp) with h3718 | h3718
                            · rcases p3709_3 (m.d 1 2) (by simp) with h3719 | h3719
                              · linarith only [h0, h3719, hlam]
                              · rcases p3709_3 (m.d 1 3) (by simp) with h3721 | h3721
                                · linarith only [h3721, hlam, p3709_0]
                                · rcases p3709_3 (m.d 1 4) (by simp) with h3723 | h3723
                                  · linarith only [h2, h3723, hlam]
                                  · rcases p3709_3 (m.d 1 5) (by simp) with h3725 | h3725
                                    · linarith only [h3, h3725, hlam]
                                    · linarith only [h3698, h3725, hlam]
                            · linarith only [h3718, hlam, p3709_0]
                          · have p3709_0 := h3709c.1
                            have p3709_1 := h3709c.2.1
                            have p3709_2 := h3709c.2.2.1
                            have p3709_3 := h3709c.2.2.2
                            rcases p3709_3 (m.d 0 1) (by simp) with h3729 | h3729
                            · rcases p3709_3 (m.d 1 2) (by simp) with h3730 | h3730
                              · linarith only [h0, h3730, hlam]
                              · rcases p3709_3 (m.d 1 3) (by simp) with h3732 | h3732
                                · linarith only [h1, h3732, hlam]
                                · linarith only [h3697, h3732, hlam]
                            · linarith only [h3729, hlam, p3709_0]
                          · have p3709_0 := h3709c.1
                            have p3709_1 := h3709c.2.1
                            have p3709_2 := h3709c.2.2.1
                            have p3709_3 := h3709c.2.2.2
                            rcases p3709_3 (m.d 0 1) (by simp) with h3736 | h3736
                            · rcases p3709_3 (m.d 1 2) (by simp) with h3737 | h3737
                              · linarith only [h0, h3737, hlam]
                              · rcases p3709_3 (m.d 1 3) (by simp) with h3739 | h3739
                                · linarith only [h1, h3739, hlam]
                                · rcases p3709_3 (m.d 1 4) (by simp) with h3741 | h3741
                                  · linarith only [h2, h3741, hlam]
                                  · rcases p3709_3 (m.d 1 5) (by simp) with h3743 | h3743
                                    · linarith only [h3743, hlam, p3709_0]
                                    · rcases h1emax with h3745 | h3745 | h3745 | h3745 | h3745
                                      · linarith only [h3698, h3745, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3709_1]
                                      · rcases h3bigk with h3747c | h3747c | h3747c | h3747c | h3747c | h3747c | h3747c | h3747c | h3747c | h3747c | h3747c | h3747c | h3747c | h3747c | h3747c | h3747c | h3747c | h3747c | h3747c | h3747c | h3747c | h3747c | h3747c | h3747c | h3747c
                                        · have p3747_0 := h3747c.1
                                          have p3747_1 := h3747c.2.1
                                          have p3747_2 := h3747c.2.2.1
                                          have p3747_3 := h3747c.2.2.2
                                          linarith only [hlam, p3747_0]
                                        · have p3747_0 := h3747c.1
                                          have p3747_1 := h3747c.2.1
                                          have p3747_2 := h3747c.2.2.1
                                          have p3747_3 := h3747c.2.2.2
                                          linarith only [h3697, h8, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3747_1]
                                        · have p3747_0 := h3747c.1
                                          have p3747_1 := h3747c.2.1
                                          have p3747_2 := h3747c.2.2.1
                                          have p3747_3 := h3747c.2.2.2
                                          linarith only [h3677, h3702, h3707, h8, hc12, hc45, hlam, hphi, ht23, ht34, p3747_1]
                                        · have p3747_0 := h3747c.1
                                          have p3747_1 := h3747c.2.1
                                          have p3747_2 := h3747c.2.2.1
                                          have p3747_3 := h3747c.2.2.2
                                          linarith only [h3707, h8, hc34, hc45, hlam, hphi, p3747_1]
                                        · have p3747_0 := h3747c.1
                                          have p3747_1 := h3747c.2.1
                                          have p3747_2 := h3747c.2.2.1
                                          have p3747_3 := h3747c.2.2.2
                                          linarith only [h8, hlam, p3747_0]
                                        · have p3747_0 := h3747c.1
                                          have p3747_1 := h3747c.2.1
                                          have p3747_2 := h3747c.2.2.1
                                          have p3747_3 := h3747c.2.2.2
                                          linarith only [h1, hlam, p3747_0]
                                        · have p3747_0 := h3747c.1
                                          have p3747_1 := h3747c.2.1
                                          have p3747_2 := h3747c.2.2.1
                                          have p3747_3 := h3747c.2.2.2
                                          linarith only [hlam, p3747_0]
                                        · have p3747_0 := h3747c.1
                                          have p3747_1 := h3747c.2.1
                                          have p3747_2 := h3747c.2.2.1
                                          have p3747_3 := h3747c.2.2.2
                                          linarith only [h3600, hlam, p3747_1]
                                        · have p3747_0 := h3747c.1
                                          have p3747_1 := h3747c.2.1
                                          have p3747_2 := h3747c.2.2.1
                                          have p3747_3 := h3747c.2.2.2
                                          linarith only [h3698, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3709_1, p3747_1]
                                        · have p3747_0 := h3747c.1
                                          have p3747_1 := h3747c.2.1
                                          have p3747_2 := h3747c.2.2.1
                                          have p3747_3 := h3747c.2.2.2
                                          linarith only [h3698, hlam, p3747_0]
                                        · have p3747_0 := h3747c.1
                                          have p3747_1 := h3747c.2.1
                                          have p3747_2 := h3747c.2.2.1
                                          have p3747_3 := h3747c.2.2.2
                                          linarith only [h4, hlam, p3747_0]
                                        · have p3747_0 := h3747c.1
                                          have p3747_1 := h3747c.2.1
                                          have p3747_2 := h3747c.2.2.1
                                          have p3747_3 := h3747c.2.2.2
                                          linarith only [h3707, h4, h8, hc13, hc45, hlam, hphi, ht34, p3747_1]
                                        · have p3747_0 := h3747c.1
                                          have p3747_1 := h3747c.2.1
                                          have p3747_2 := h3747c.2.2.1
                                          have p3747_3 := h3747c.2.2.2
                                          linarith only [hlam, p3747_0]
                                        · have p3747_0 := h3747c.1
                                          have p3747_1 := h3747c.2.1
                                          have p3747_2 := h3747c.2.2.1
                                          have p3747_3 := h3747c.2.2.2
                                          linarith only [h3707, h4, h8, hc34, hc45, hlam, hphi, p3747_1]
                                        · have p3747_0 := h3747c.1
                                          have p3747_1 := h3747c.2.1
                                          have p3747_2 := h3747c.2.2.1
                                          have p3747_3 := h3747c.2.2.2
                                          linarith only [h3703, hlam, p3747_0]
                                        · have p3747_0 := h3747c.1
                                          have p3747_1 := h3747c.2.1
                                          have p3747_2 := h3747c.2.2.1
                                          have p3747_3 := h3747c.2.2.2
                                          linarith only [h7, hlam, p3747_0]
                                        · have p3747_0 := h3747c.1
                                          have p3747_1 := h3747c.2.1
                                          have p3747_2 := h3747c.2.2.1
                                          have p3747_3 := h3747c.2.2.2
                                          linarith only [h3697, hlam, p3747_0]
                                        · have p3747_0 := h3747c.1
                                          have p3747_1 := h3747c.2.1
                                          have p3747_2 := h3747c.2.2.1
                                          have p3747_3 := h3747c.2.2.2
                                          linarith only [h3702, hlam, p3747_0]
                                        · have p3747_0 := h3747c.1
                                          have p3747_1 := h3747c.2.1
                                          have p3747_2 := h3747c.2.2.1
                                          have p3747_3 := h3747c.2.2.2
                                          linarith only [hlam, p3747_0]
                                        · have p3747_0 := h3747c.1
                                          have p3747_1 := h3747c.2.1
                                          have p3747_2 := h3747c.2.2.1
                                          have p3747_3 := h3747c.2.2.2
                                          linarith only [h3707, hlam, p3747_1]
                                        · have p3747_0 := h3747c.1
                                          have p3747_1 := h3747c.2.1
                                          have p3747_2 := h3747c.2.2.1
                                          have p3747_3 := h3747c.2.2.2
                                          linarith only [h1, h3697, h3707, hc34, hc45, hlam, hphi, p3747_1]
                                        · have p3747_0 := h3747c.1
                                          have p3747_1 := h3747c.2.1
                                          have p3747_2 := h3747c.2.2.1
                                          have p3747_3 := h3747c.2.2.2
                                          linarith only [h3697, h3707, hc34, hc45, hlam, hphi, p3747_1]
                                        · have p3747_0 := h3747c.1
                                          have p3747_1 := h3747c.2.1
                                          have p3747_2 := h3747c.2.2.1
                                          have p3747_3 := h3747c.2.2.2
                                          linarith only [h3600, h3707, hc12, hc45, hlam, hphi, ht23, ht34, p3747_1]
                                        · have p3747_0 := h3747c.1
                                          have p3747_1 := h3747c.2.1
                                          have p3747_2 := h3747c.2.2.1
                                          have p3747_3 := h3747c.2.2.2
                                          rcases p3747_3 (m.d 0 3) (by simp) with h3771 | h3771
                                          · linarith only [h3771, h8, hlam]
                                          · linarith only [h3771, h7, hlam]
                                        · have p3747_0 := h3747c.1
                                          have p3747_1 := h3747c.2.1
                                          have p3747_2 := h3747c.2.2.1
                                          have p3747_3 := h3747c.2.2.2
                                          linarith only [hlam, p3747_0]
                                      · rcases h3bigk with h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c | h3775c
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [hlam, p3775_0]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [h3697, h3707, h8, hc34, hc45, hlam, hphi, p3775_1]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [h3677, h3702, h3707, h8, hc12, hc45, hlam, hphi, ht23, ht34, p3775_1]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [h3707, h8, hc34, hc45, hlam, hphi, p3775_1]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [h8, hlam, p3775_0]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [h1, hlam, p3775_0]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [hlam, p3775_0]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [h3600, hlam, p3775_1]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [h1, h3707, h8, hc34, hc45, hlam, hphi, p3775_1]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [h3698, hlam, p3775_0]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [h4, hlam, p3775_0]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [h3707, h4, h8, hc13, hc45, hlam, hphi, ht34, p3775_1]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [hlam, p3775_0]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [h3707, h4, h8, hc34, hc45, hlam, hphi, p3775_1]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [h3703, hlam, p3775_0]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [h7, hlam, p3775_0]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [h3697, hlam, p3775_0]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [h3702, hlam, p3775_0]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [hlam, p3775_0]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [h3707, hlam, p3775_1]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [h1, h3697, h3707, hc34, hc45, hlam, hphi, p3775_1]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [h3697, h3707, hc34, hc45, hlam, hphi, p3775_1]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [h3600, h3707, hc12, hc45, hlam, hphi, ht23, ht34, p3775_1]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          rcases p3775_3 (m.d 0 3) (by simp) with h3799 | h3799
                                          · linarith only [h3799, h8, hlam]
                                          · linarith only [h3799, h7, hlam]
                                        · have p3775_0 := h3775c.1
                                          have p3775_1 := h3775c.2.1
                                          have p3775_2 := h3775c.2.2.1
                                          have p3775_3 := h3775c.2.2.2
                                          linarith only [hlam, p3775_0]
                                      · rcases h3bigk with h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c | h3803c
                                        · have p3803_0 := h3803c.1
                                          have p3803_1 := h3803c.2.1
                                          have p3803_2 := h3803c.2.2.1
                                          have p3803_3 := h3803c.2.2.2
                                          linarith only [hlam, p3803_0]
                                        · have p3803_0 := h3803c.1
                                          have p3803_1 := h3803c.2.1
                                          have p3803_2 := h3803c.2.2.1
                                          have p3803_3 := h3803c.2.2.2
                                          linarith only [h3697, h3707, h8, hc34, hc45, hlam, hphi, p3803_1]
                                        · have p3803_0 := h3803c.1
                                          have p3803_1 := h3803c.2.1
                                          have p3803_2 := h3803c.2.2.1
                                          have p3803_3 := h3803c.2.2.2
                                          linarith only [h3677, h3702, h3707, h8, hc12, hc45, hlam, hphi, ht23, ht34, p3803_1]
                                        · have p3803_0 := h3803c.1
                                          have p3803_1 := h3803c.2.1
                                          have p3803_2 := h3803c.2.2.1
                                          have p3803_3 := h3803c.2.2.2
                                          linarith only [h3707, h8, hc34, hc45, hlam, hphi, p3803_1]
                                        · have p3803_0 := h3803c.1
                                          have p3803_1 := h3803c.2.1
                                          have p3803_2 := h3803c.2.2.1
                                          have p3803_3 := h3803c.2.2.2
                                          linarith only [h8, hlam, p3803_0]
                                        · have p3803_0 := h3803c.1
                                          have p3803_1 := h3803c.2.1
                                          have p3803_2 := h3803c.2.2.1
                                          have p3803_3 := h3803c.2.2.2
                                          linarith only [h1, hlam, p3803_0]
                                        · have p3803_0 := h3803c.1
                                          have p3803_1 := h3803c.2.1
                                          have p3803_2 := h3803c.2.2.1
                                          have p3803_3 := h3803c.2.2.2
                                          linarith only [hlam, p3803_0]
                                        · have p3803_0 := h3803c.1
                                          have p3803_1 := h3803c.2.1
                                          have p3803_2 := h3803c.2.2.1
                                          have p3803_3 := h3803c.2.2.2
                                          linarith only [h3600, hlam, p3803_1]
                                        · have p3803_0 := h3803c.1
                                          have p3803_1 := h3803c.2.1
                                          have p3803_2 := h3803c.2.2.1
                                          have p3803_3 := h3803c.2.2.2
                                          linarith only [h1, h3707, h8, hc34, hc45, hlam, hphi, p3803_1]
                                        · have p3803_0 := h3803c.1
                                          have p3803_1 := h3803c.2.1
                                          have p3803_2 := h3803c.2.2.1
                                          have p3803_3 := h3803c.2.2.2
                                          linarith only [h3698, hlam, p3803_0]
                                        · have p3803_0 := h3803c.1
                                          have p3803_1 := h3803c.2.1
                                          have p3803_2 := h3803c.2.2.1
                                          have p3803_3 := h3803c.2.2.2
                                          linarith only [h4, hlam, p3803_0]
                                        · have p3803_0 := h3803c.1
                                          have p3803_1 := h3803c.2.1
                                          have p3803_2 := h3803c.2.2.1
                                          have p3803_3 := h3803c.2.2.2
                                          linarith only [h3707, h4, h8, hc13, hc45, hlam, hphi, ht34, p3803_1]
                                        · have p3803_0 := h3803c.1
                                          have p3803_1 := h3803c.2.1
                                          have p3803_2 := h3803c.2.2.1
                                          have p3803_3 := h3803c.2.2.2
                                          linarith only [hlam, p3803_0]
                                        · have p3803_0 := h3803c.1
                                          have p3803_1 := h3803c.2.1
                                          have p3803_2 := h3803c.2.2.1
                                          have p3803_3 := h3803c.2.2.2
                                          linarith only [h3707, h4, h8, hc34, hc45, hlam, hphi, p3803_1]
                                        · have p3803_0 := h3803c.1
                                          have p3803_1 := h3803c.2.1
                                          have p3803_2 := h3803c.2.2.1
                                          have p3803_3 := h3803c.2.2.2
                                          linarith only [h3703, hlam, p3803_0]
                                        · have p3803_0 := h3803c.1
                                          have p3803_1 := h3803c.2.1
                                          have p3803_2 := h3803c.2.2.1
                                          have p3803_3 := h3803c.2.2.2
                                          linarith only [h7, hlam, p3803_0]
                                        · have p3803_0 := h3803c.1
                                          have p3803_1 := h3803c.2.1
                                          have p3803_2 := h3803c.2.2.1
                                          have p3803_3 := h3803c.2.2.2
                                          linarith only [h3697, hlam, p3803_0]
                                        · have p3803_0 := h3803c.1
                                          have p3803_1 := h3803c.2.1
                                          have p3803_2 := h3803c.2.2.1
                                          have p3803_3 := h3803c.2.2.2
                                          linarith only [h3702, hlam, p3803_0]
                                        · have p3803_0 := h3803c.1
                                          have p3803_1 := h3803c.2.1
                                          have p3803_2 := h3803c.2.2.1
                                          have p3803_3 := h3803c.2.2.2
                                          linarith only [hlam, p3803_0]
                                        · have p3803_0 := h3803c.1
                                          have p3803_1 := h3803c.2.1
                                          have p3803_2 := h3803c.2.2.1
                                          have p3803_3 := h3803c.2.2.2
                                          linarith only [h3707, hlam, p3803_1]
                                        · have p3803_0 := h3803c.1
                                          have p3803_1 := h3803c.2.1
                                          have p3803_2 := h3803c.2.2.1
                                          have p3803_3 := h3803c.2.2.2
                                          linarith only [h1, h3697, h3707, hc34, hc45, hlam, hphi, p3803_1]
                                        · have p3803_0 := h3803c.1
                                          have p3803_1 := h3803c.2.1
                                          have p3803_2 := h3803c.2.2.1
                                          have p3803_3 := h3803c.2.2.2
                                          linarith only [h3697, h3707, hc34, hc45, hlam, hphi, p3803_1]
                                        · have p3803_0 := h3803c.1
                                          have p3803_1 := h3803c.2.1
                                          have p3803_2 := h3803c.2.2.1
                                          have p3803_3 := h3803c.2.2.2
                                          linarith only [h3600, h3707, hc12, hc45, hlam, hphi, ht23, ht34, p3803_1]
                                        · have p3803_0 := h3803c.1
                                          have p3803_1 := h3803c.2.1
                                          have p3803_2 := h3803c.2.2.1
                                          have p3803_3 := h3803c.2.2.2
                                          rcases p3803_3 (m.d 0 3) (by simp) with h3827 | h3827
                                          · linarith only [h3827, h8, hlam]
                                          · linarith only [h3827, h7, hlam]
                                        · have p3803_0 := h3803c.1
                                          have p3803_1 := h3803c.2.1
                                          have p3803_2 := h3803c.2.2.1
                                          have p3803_3 := h3803c.2.2.2
                                          linarith only [hlam, p3803_0]
                                      · rcases h3bigk with h3831c | h3831c | h3831c | h3831c | h3831c | h3831c | h3831c | h3831c | h3831c | h3831c | h3831c | h3831c | h3831c | h3831c | h3831c | h3831c | h3831c | h3831c | h3831c | h3831c | h3831c | h3831c | h3831c | h3831c | h3831c
                                        · have p3831_0 := h3831c.1
                                          have p3831_1 := h3831c.2.1
                                          have p3831_2 := h3831c.2.2.1
                                          have p3831_3 := h3831c.2.2.2
                                          linarith only [hlam, p3831_0]
                                        · have p3831_0 := h3831c.1
                                          have p3831_1 := h3831c.2.1
                                          have p3831_2 := h3831c.2.2.1
                                          have p3831_3 := h3831c.2.2.2
                                          linarith only [h3697, h3707, h8, hc34, hc45, hlam, hphi, p3831_1]
                                        · have p3831_0 := h3831c.1
                                          have p3831_1 := h3831c.2.1
                                          have p3831_2 := h3831c.2.2.1
                                          have p3831_3 := h3831c.2.2.2
                                          linarith only [h3677, h3702, h3707, h8, hc12, hc45, hlam, hphi, ht23, ht34, p3831_1]
                                        · have p3831_0 := h3831c.1
                                          have p3831_1 := h3831c.2.1
                                          have p3831_2 := h3831c.2.2.1
                                          have p3831_3 := h3831c.2.2.2
                                          linarith only [h3707, h8, hc34, hc45, hlam, hphi, p3831_1]
                                        · have p3831_0 := h3831c.1
                                          have p3831_1 := h3831c.2.1
                                          have p3831_2 := h3831c.2.2.1
                                          have p3831_3 := h3831c.2.2.2
                                          linarith only [h8, hlam, p3831_0]
                                        · have p3831_0 := h3831c.1
                                          have p3831_1 := h3831c.2.1
                                          have p3831_2 := h3831c.2.2.1
                                          have p3831_3 := h3831c.2.2.2
                                          linarith only [h1, hlam, p3831_0]
                                        · have p3831_0 := h3831c.1
                                          have p3831_1 := h3831c.2.1
                                          have p3831_2 := h3831c.2.2.1
                                          have p3831_3 := h3831c.2.2.2
                                          linarith only [hlam, p3831_0]
                                        · have p3831_0 := h3831c.1
                                          have p3831_1 := h3831c.2.1
                                          have p3831_2 := h3831c.2.2.1
                                          have p3831_3 := h3831c.2.2.2
                                          linarith only [h3600, hlam, p3831_1]
                                        · have p3831_0 := h3831c.1
                                          have p3831_1 := h3831c.2.1
                                          have p3831_2 := h3831c.2.2.1
                                          have p3831_3 := h3831c.2.2.2
                                          linarith only [h1, h3707, h8, hc34, hc45, hlam, hphi, p3831_1]
                                        · have p3831_0 := h3831c.1
                                          have p3831_1 := h3831c.2.1
                                          have p3831_2 := h3831c.2.2.1
                                          have p3831_3 := h3831c.2.2.2
                                          linarith only [h3698, hlam, p3831_0]
                                        · have p3831_0 := h3831c.1
                                          have p3831_1 := h3831c.2.1
                                          have p3831_2 := h3831c.2.2.1
                                          have p3831_3 := h3831c.2.2.2
                                          linarith only [h4, hlam, p3831_0]
                                        · have p3831_0 := h3831c.1
                                          have p3831_1 := h3831c.2.1
                                          have p3831_2 := h3831c.2.2.1
                                          have p3831_3 := h3831c.2.2.2
                                          linarith only [h3707, h4, h8, hc13, hc45, hlam, hphi, ht34, p3831_1]
                                        · have p3831_0 := h3831c.1
                                          have p3831_1 := h3831c.2.1
                                          have p3831_2 := h3831c.2.2.1
                                          have p3831_3 := h3831c.2.2.2
                                          linarith only [hlam, p3831_0]
                                        · have p3831_0 := h3831c.1
                                          have p3831_1 := h3831c.2.1
                                          have p3831_2 := h3831c.2.2.1
                                          have p3831_3 := h3831c.2.2.2
                                          linarith only [h3707, h4, h8, hc34, hc45, hlam, hphi, p3831_1]
                                        · have p3831_0 := h3831c.1
                                          have p3831_1 := h3831c.2.1
                                          have p3831_2 := h3831c.2.2.1
                                          have p3831_3 := h3831c.2.2.2
                                          linarith only [h3703, hlam, p3831_0]
                                        · have p3831_0 := h3831c.1
                                          have p3831_1 := h3831c.2.1
                                          have p3831_2 := h3831c.2.2.1
                                          have p3831_3 := h3831c.2.2.2
                                          linarith only [h7, hlam, p3831_0]
                                        · have p3831_0 := h3831c.1
                                          have p3831_1 := h3831c.2.1
                                          have p3831_2 := h3831c.2.2.1
                                          have p3831_3 := h3831c.2.2.2
                                          linarith only [h3697, hlam, p3831_0]
                                        · have p3831_0 := h3831c.1
                                          have p3831_1 := h3831c.2.1
                                          have p3831_2 := h3831c.2.2.1
                                          have p3831_3 := h3831c.2.2.2
                                          linarith only [h3702, hlam, p3831_0]
                                        · have p3831_0 := h3831c.1
                                          have p3831_1 := h3831c.2.1
                                          have p3831_2 := h3831c.2.2.1
                                          have p3831_3 := h3831c.2.2.2
                                          linarith only [hlam, p3831_0]
                                        · have p3831_0 := h3831c.1
                                          have p3831_1 := h3831c.2.1
                                          have p3831_2 := h3831c.2.2.1
                                          have p3831_3 := h3831c.2.2.2
                                          linarith only [h3707, hlam, p3831_1]
                                        · have p3831_0 := h3831c.1
                                          have p3831_1 := h3831c.2.1
                                          have p3831_2 := h3831c.2.2.1
                                          have p3831_3 := h3831c.2.2.2
                                          linarith only [h1, h3697, h3707, hc34, hc45, hlam, hphi, p3831_1]
                                        · have p3831_0 := h3831c.1
                                          have p3831_1 := h3831c.2.1
                                          have p3831_2 := h3831c.2.2.1
                                          have p3831_3 := h3831c.2.2.2
                                          linarith only [h3697, h3707, hc34, hc45, hlam, hphi, p3831_1]
                                        · have p3831_0 := h3831c.1
                                          have p3831_1 := h3831c.2.1
                                          have p3831_2 := h3831c.2.2.1
                                          have p3831_3 := h3831c.2.2.2
                                          linarith only [h3600, h3707, hc12, hc45, hlam, hphi, ht23, ht34, p3831_1]
                                        · have p3831_0 := h3831c.1
                                          have p3831_1 := h3831c.2.1
                                          have p3831_2 := h3831c.2.2.1
                                          have p3831_3 := h3831c.2.2.2
                                          rcases p3831_3 (m.d 0 3) (by simp) with h3855 | h3855
                                          · linarith only [h3855, h8, hlam]
                                          · linarith only [h3855, h7, hlam]
                                        · have p3831_0 := h3831c.1
                                          have p3831_1 := h3831c.2.1
                                          have p3831_2 := h3831c.2.2.1
                                          have p3831_3 := h3831c.2.2.2
                                          linarith only [hlam, p3831_0]
                            · linarith only [h3736, hlam, p3709_0]
                          · have p3709_0 := h3709c.1
                            have p3709_1 := h3709c.2.1
                            have p3709_2 := h3709c.2.2.1
                            have p3709_3 := h3709c.2.2.2
                            linarith only [h0, hlam, p3709_0]
                          · have p3709_0 := h3709c.1
                            have p3709_1 := h3709c.2.1
                            have p3709_2 := h3709c.2.2.1
                            have p3709_3 := h3709c.2.2.2
                            linarith only [hlam, p3709_0]
                          · have p3709_0 := h3709c.1
                            have p3709_1 := h3709c.2.1
                            have p3709_2 := h3709c.2.2.1
                            have p3709_3 := h3709c.2.2.2
                            linarith only [h3600, hlam, p3709_0]
                          · have p3709_0 := h3709c.1
                            have p3709_1 := h3709c.2.1
                            have p3709_2 := h3709c.2.2.1
                            have p3709_3 := h3709c.2.2.2
                            linarith only [h3677, hlam, p3709_0]
                          · have p3709_0 := h3709c.1
                            have p3709_1 := h3709c.2.1
                            have p3709_2 := h3709c.2.2.1
                            have p3709_3 := h3709c.2.2.2
                            linarith only [h3695, hlam, p3709_0]
                          · have p3709_0 := h3709c.1
                            have p3709_1 := h3709c.2.1
                            have p3709_2 := h3709c.2.2.1
                            have p3709_3 := h3709c.2.2.2
                            linarith only [h1, hlam, p3709_0]
                          · have p3709_0 := h3709c.1
                            have p3709_1 := h3709c.2.1
                            have p3709_2 := h3709c.2.2.1
                            have p3709_3 := h3709c.2.2.2
                            linarith only [h1, h3707, h8, hc12, hc45, hlam, hphi, ht23, ht34, p3709_1]
                          · have p3709_0 := h3709c.1
                            have p3709_1 := h3709c.2.1
                            have p3709_2 := h3709c.2.2.1
                            have p3709_3 := h3709c.2.2.2
                            linarith only [hlam, p3709_0]
                          · have p3709_0 := h3709c.1
                            have p3709_1 := h3709c.2.1
                            have p3709_2 := h3709c.2.2.1
                            have p3709_3 := h3709c.2.2.2
                            linarith only [h1, h3677, h3707, h8, hc12, hc45, hlam, hphi, ht23, ht34, p3709_1]
                          · have p3709_0 := h3709c.1
                            have p3709_1 := h3709c.2.1
                            have p3709_2 := h3709c.2.2.1
                            have p3709_3 := h3709c.2.2.2
                            linarith only [h3698, hlam, p3709_1]
                          · have p3709_0 := h3709c.1
                            have p3709_1 := h3709c.2.1
                            have p3709_2 := h3709c.2.2.1
                            have p3709_3 := h3709c.2.2.2
                            linarith only [h2, hlam, p3709_0]
                          · have p3709_0 := h3709c.1
                            have p3709_1 := h3709c.2.1
                            have p3709_2 := h3709c.2.2.1
                            have p3709_3 := h3709c.2.2.2
                            linarith only [h2, h3707, h7, h8, hc12, hc45, hlam, hphi, ht23, ht34, p3709_1]
                          · have p3709_0 := h3709c.1
                            have p3709_1 := h3709c.2.1
                            have p3709_2 := h3709c.2.2.1
                            have p3709_3 := h3709c.2.2.2
                            linarith only [h3697, hlam, p3709_0]
                          · have p3709_0 := h3709c.1
                            have p3709_1 := h3709c.2.1
                            have p3709_2 := h3709c.2.2.1
                            have p3709_3 := h3709c.2.2.2
                            linarith only [hlam, p3709_0]
                          · have p3709_0 := h3709c.1
                            have p3709_1 := h3709c.2.1
                            have p3709_2 := h3709c.2.2.1
                            have p3709_3 := h3709c.2.2.2
                            linarith only [h3700, hlam, p3709_1]
                          · have p3709_0 := h3709c.1
                            have p3709_1 := h3709c.2.1
                            have p3709_2 := h3709c.2.2.1
                            have p3709_3 := h3709c.2.2.2
                            linarith only [h3, hlam, p3709_0]
                          · have p3709_0 := h3709c.1
                            have p3709_1 := h3709c.2.1
                            have p3709_2 := h3709c.2.2.1
                            have p3709_3 := h3709c.2.2.2
                            rcases p3709_3 (m.d 0 1) (by simp) with h3876 | h3876
                            · rcases p3709_3 (m.d 1 2) (by simp) with h3877 | h3877
                              · linarith only [h3695, h3877, hlam]
                              · rcases p3709_3 (m.d 1 3) (by simp) with h3879 | h3879
                                · linarith only [h3698, h3879, hlam]
                                · linarith only [h3600, h3879, hlam]
                            · linarith only [h0, h3876, hlam]
                          · have p3709_0 := h3709c.1
                            have p3709_1 := h3709c.2.1
                            have p3709_2 := h3709c.2.2.1
                            have p3709_3 := h3709c.2.2.2
                            linarith only [h3, h3697, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3709_1]
                          · have p3709_0 := h3709c.1
                            have p3709_1 := h3709c.2.1
                            have p3709_2 := h3709c.2.2.1
                            have p3709_3 := h3709c.2.2.2
                            rcases p3709_3 (m.d 0 1) (by simp) with h3884 | h3884
                            · rcases p3709_3 (m.d 1 2) (by simp) with h3885 | h3885
                              · linarith only [h3695, h3885, hlam]
                              · rcases p3709_3 (m.d 1 3) (by simp) with h3887 | h3887
                                · linarith only [h3698, h3887, hlam]
                                · linarith only [h3697, h3887, hlam]
                            · linarith only [h2, h3884, hlam]
                          · have p3709_0 := h3709c.1
                            have p3709_1 := h3709c.2.1
                            have p3709_2 := h3709c.2.2.1
                            have p3709_3 := h3709c.2.2.2
                            linarith only [hlam, p3709_0]
                  · linarith only [h1, h3697, h3702, h8, hc23, hc35, hlam, hphi]
            · linarith only [h3697, h7, h8, hc13, hc35, hlam, hphi]

set_option maxHeartbeats 10184000 in
set_option maxHeartbeats 10184000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s6_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  exact r1l7_11_13_25_L_I_L_I_M_IR_s7 m hb1 hb3 hb5 h0 h1 h2 h3 h4 h5 h6 h7

set_option maxHeartbeats 10184000 in
set_option maxHeartbeats 10184000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s6_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h3894 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 4 5 (by decide) (by decide) with h3895 | h3895
  · rcases m.htr 1 2 3 (by decide) (by decide) with h3896 | h3896
    · rcases m.htr 1 2 4 (by decide) (by decide) with h3897 | h3897
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3898 | h3898
        · rcases m.htr 1 3 4 (by decide) (by decide) with h3899 | h3899
          · linarith only [h3894, h3899, h7, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h3901 | h3901
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3902 | h3902
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3903 | h3903
                · linarith only [h1, h3901, h3903, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3905 | h3905
                  · linarith only [h0, h3897, h3903, h3905, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · linarith only [h1, h3901, h3905, h7, hc23, hc34, hlam, hphi]
              · linarith only [h3895, h3899, h3901, h3902, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
            · linarith only [h3894, h3901, h7, hc13, hc34, hlam, hphi]
        · linarith only [h3894, h3896, h3898, h6, h7, hc23, hc34, hlam, hphi]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3911 | h3911
        · linarith only [h0, h3897, h3911, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
        · linarith only [h3894, h3896, h3911, h6, h7, hc23, hc34, hlam, hphi]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h3914 | h3914
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3915 | h3915
        · linarith only [h0, h3896, h3915, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h3917 | h3917
          · linarith only [h3894, h3914, h3915, h3917, h6, h7, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
          · linarith only [h3896, h3914, h3917, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3920 | h3920
        · linarith only [h3896, h3920, h4, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h3922 | h3922
          · linarith only [h3896, h3922, h4, h7, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h3924 | h3924
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3925 | h3925
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3926 | h3926
                · linarith only [h3926, h4, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3928 | h3928
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3929 | h3929
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3930 | h3930
                      · rcases h1bigk with h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c | h3931c
                        · have p3931_0 := h3931c.1
                          have p3931_1 := h3931c.2.1
                          have p3931_2 := h3931c.2.2.1
                          have p3931_3 := h3931c.2.2.2
                          linarith only [hlam, p3931_0]
                        · have p3931_0 := h3931c.1
                          have p3931_1 := h3931c.2.1
                          have p3931_2 := h3931c.2.2.1
                          have p3931_3 := h3931c.2.2.2
                          rcases p3931_3 (m.d 0 1) (by simp) with h3933 | h3933
                          · rcases p3931_3 (m.d 1 2) (by simp) with h3934 | h3934
                            · linarith only [h3934, hlam, p3931_0]
                            · rcases p3931_3 (m.d 1 3) (by simp) with h3936 | h3936
                              · linarith only [h1, h3936, hlam]
                              · linarith only [h3896, h3936, hlam]
                          · linarith only [h3933, hlam, p3931_0]
                        · have p3931_0 := h3931c.1
                          have p3931_1 := h3931c.2.1
                          have p3931_2 := h3931c.2.2.1
                          have p3931_3 := h3931c.2.2.2
                          linarith only [h3924, h3930, hc01, hlam, hphi, ht0b, ht5b, p3931_1, u5ehi4]
                        · have p3931_0 := h3931c.1
                          have p3931_1 := h3931c.2.1
                          have p3931_2 := h3931c.2.2.1
                          have p3931_3 := h3931c.2.2.2
                          linarith only [h3922, h3924, h3930, hc01, hlam, hphi, ht0b, ht5b, p3931_1, u5ehi4]
                        · have p3931_0 := h3931c.1
                          have p3931_1 := h3931c.2.1
                          have p3931_2 := h3931c.2.2.1
                          have p3931_3 := h3931c.2.2.2
                          rcases p3931_3 (m.d 0 1) (by simp) with h3942 | h3942
                          · rcases p3931_3 (m.d 1 2) (by simp) with h3943 | h3943
                            · linarith only [h0, h3943, hlam]
                            · rcases p3931_3 (m.d 1 3) (by simp) with h3945 | h3945
                              · linarith only [h1, h3945, hlam]
                              · linarith only [h3924, h3945, hlam]
                          · linarith only [h3942, hlam, p3931_0]
                        · have p3931_0 := h3931c.1
                          have p3931_1 := h3931c.2.1
                          have p3931_2 := h3931c.2.2.1
                          have p3931_3 := h3931c.2.2.2
                          linarith only [h0, hlam, p3931_0]
                        · have p3931_0 := h3931c.1
                          have p3931_1 := h3931c.2.1
                          have p3931_2 := h3931c.2.2.1
                          have p3931_3 := h3931c.2.2.2
                          linarith only [hlam, p3931_0]
                        · have p3931_0 := h3931c.1
                          have p3931_1 := h3931c.2.1
                          have p3931_2 := h3931c.2.2.1
                          have p3931_3 := h3931c.2.2.2
                          linarith only [h3896, hlam, p3931_0]
                        · have p3931_0 := h3931c.1
                          have p3931_1 := h3931c.2.1
                          have p3931_2 := h3931c.2.2.1
                          have p3931_3 := h3931c.2.2.2
                          linarith only [h3914, hlam, p3931_0]
                        · have p3931_0 := h3931c.1
                          have p3931_1 := h3931c.2.1
                          have p3931_2 := h3931c.2.2.1
                          have p3931_3 := h3931c.2.2.2
                          linarith only [h3920, hlam, p3931_0]
                        · have p3931_0 := h3931c.1
                          have p3931_1 := h3931c.2.1
                          have p3931_2 := h3931c.2.2.1
                          have p3931_3 := h3931c.2.2.2
                          linarith only [h1, hlam, p3931_0]
                        · have p3931_0 := h3931c.1
                          have p3931_1 := h3931c.2.1
                          have p3931_2 := h3931c.2.2.1
                          have p3931_3 := h3931c.2.2.2
                          linarith only [h1, h7, hc12, hc34, hlam, hphi, ht23, p3931_1]
                        · have p3931_0 := h3931c.1
                          have p3931_1 := h3931c.2.1
                          have p3931_2 := h3931c.2.2.1
                          have p3931_3 := h3931c.2.2.2
                          linarith only [hlam, p3931_0]
                        · have p3931_0 := h3931c.1
                          have p3931_1 := h3931c.2.1
                          have p3931_2 := h3931c.2.2.1
                          have p3931_3 := h3931c.2.2.2
                          linarith only [h3922, hlam, p3931_1]
                        · have p3931_0 := h3931c.1
                          have p3931_1 := h3931c.2.1
                          have p3931_2 := h3931c.2.2.1
                          have p3931_3 := h3931c.2.2.2
                          linarith only [h3896, h4, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3931_1, u5ehi1]
                        · have p3931_0 := h3931c.1
                          have p3931_1 := h3931c.2.1
                          have p3931_2 := h3931c.2.2.1
                          have p3931_3 := h3931c.2.2.2
                          linarith only [h2, hlam, p3931_0]
                        · have p3931_0 := h3931c.1
                          have p3931_1 := h3931c.2.1
                          have p3931_2 := h3931c.2.2.1
                          have p3931_3 := h3931c.2.2.2
                          rcases p3931_3 (m.d 0 1) (by simp) with h3960 | h3960
                          · rcases p3931_3 (m.d 1 2) (by simp) with h3961 | h3961
                            · linarith only [h3914, h3961, hlam]
                            · rcases p3931_3 (m.d 1 3) (by simp) with h3963 | h3963
                              · linarith only [h3922, h3963, hlam]
                              · linarith only [h3896, h3963, hlam]
                          · linarith only [h0, h3960, hlam]
                        · have p3931_0 := h3931c.1
                          have p3931_1 := h3931c.2.1
                          have p3931_2 := h3931c.2.2.1
                          have p3931_3 := h3931c.2.2.2
                          linarith only [h0, h3914, h3924, h3930, h5, hc01, hlam, hphi, ht0b, ht5b, p3931_1, u5ehi4]
                        · have p3931_0 := h3931c.1
                          have p3931_1 := h3931c.2.1
                          have p3931_2 := h3931c.2.2.1
                          have p3931_3 := h3931c.2.2.2
                          linarith only [hlam, p3931_0]
                        · have p3931_0 := h3931c.1
                          have p3931_1 := h3931c.2.1
                          have p3931_2 := h3931c.2.2.1
                          have p3931_3 := h3931c.2.2.2
                          linarith only [h0, h3914, h3924, h3930, h5, hc01, hlam, hphi, ht0b, ht5b, p3931_1, u5ehi4]
                        · have p3931_0 := h3931c.1
                          have p3931_1 := h3931c.2.1
                          have p3931_2 := h3931c.2.2.1
                          have p3931_3 := h3931c.2.2.2
                          linarith only [h3, hlam, p3931_0]
                        · have p3931_0 := h3931c.1
                          have p3931_1 := h3931c.2.1
                          have p3931_2 := h3931c.2.2.1
                          have p3931_3 := h3931c.2.2.2
                          linarith only [h3, h3894, h7, hc12, hc34, hlam, hphi, ht23, p3931_1]
                        · have p3931_0 := h3931c.1
                          have p3931_1 := h3931c.2.1
                          have p3931_2 := h3931c.2.2.1
                          have p3931_3 := h3931c.2.2.2
                          linarith only [h3924, hlam, p3931_0]
                        · have p3931_0 := h3931c.1
                          have p3931_1 := h3931c.2.1
                          have p3931_2 := h3931c.2.2.1
                          have p3931_3 := h3931c.2.2.2
                          linarith only [h3925, hlam, p3931_0]
                        · have p3931_0 := h3931c.1
                          have p3931_1 := h3931c.2.1
                          have p3931_2 := h3931c.2.2.1
                          have p3931_3 := h3931c.2.2.2
                          linarith only [hlam, p3931_0]
                      · linarith only [h1, h3924, h3930, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                    · linarith only [h3894, h3895, h3914, h3929, h7, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h3896, h3924, h3928, hlam]
              · linarith only [h3895, h3922, h3924, h3925, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
            · linarith only [h3894, h3924, h7, hc13, hc34, hlam, hphi]
  · linarith only [h3894, h3895, h7, hlam]

end R2N4
