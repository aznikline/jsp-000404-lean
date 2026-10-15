import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_31S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5048000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_R_s0_x1_x1_x1_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2249 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2576 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2850 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2852 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2853 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2854 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2855 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 5 (by decide) (by decide) with h3686 | h3686
  · linarith only [h2855, h3686, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h3688 | h3688
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3689 | h3689
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3690 | h3690
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3691 | h3691
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3692 | h3692
            · linarith only [h2855, h3688, h3689, h3692, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3694 | h3694
              · linarith only [h2852, h3686, h3692, h3694, hc23, hc34, hlam, hphi]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3696 | h3696
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3697 | h3697
                  · linarith only [h2576, h3688, h3692, h3697, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3699 | h3699
                    · linarith only [h2249, h2852, h3692, h3699, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3701 | h3701
                      · linarith only [h0, h2853, h3701, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3703 | h3703
                        · rcases h0bigk with h3704c | h3704c | h3704c | h3704c | h3704c | h3704c | h3704c | h3704c | h3704c | h3704c | h3704c | h3704c | h3704c | h3704c | h3704c | h3704c | h3704c | h3704c | h3704c | h3704c | h3704c | h3704c | h3704c | h3704c | h3704c
                          · have p3704_0 := h3704c.1
                            have p3704_1 := h3704c.2.1
                            have p3704_2 := h3704c.2.2.1
                            have p3704_3 := h3704c.2.2.2
                            linarith only [hlam, p3704_0]
                          · have p3704_0 := h3704c.1
                            have p3704_1 := h3704c.2.1
                            have p3704_2 := h3704c.2.2.1
                            have p3704_3 := h3704c.2.2.2
                            linarith only [h0, hlam, p3704_1]
                          · have p3704_0 := h3704c.1
                            have p3704_1 := h3704c.2.1
                            have p3704_2 := h3704c.2.2.1
                            have p3704_3 := h3704c.2.2.2
                            linarith only [h2249, hlam, p3704_0]
                          · have p3704_0 := h3704c.1
                            have p3704_1 := h3704c.2.1
                            have p3704_2 := h3704c.2.2.1
                            have p3704_3 := h3704c.2.2.2
                            linarith only [h2576, hlam, p3704_1]
                          · have p3704_0 := h3704c.1
                            have p3704_1 := h3704c.2.1
                            have p3704_2 := h3704c.2.2.1
                            have p3704_3 := h3704c.2.2.2
                            linarith only [h2850, hlam, p3704_1]
                          · have p3704_0 := h3704c.1
                            have p3704_1 := h3704c.2.1
                            have p3704_2 := h3704c.2.2.1
                            have p3704_3 := h3704c.2.2.2
                            rcases p3704_3 (m.d 0 1) (by simp) with h3710 | h3710
                            · linarith only [h0, h3710, hlam]
                            · rcases p3704_3 (m.d 0 2) (by simp) with h3712 | h3712
                              · rcases p3704_3 (m.d 0 3) (by simp) with h3713 | h3713
                                · linarith only [h2852, h3713, hlam]
                                · linarith only [h2249, h3713, hlam]
                              · linarith only [h0, h3712, hlam]
                          · have p3704_0 := h3704c.1
                            have p3704_1 := h3704c.2.1
                            have p3704_2 := h3704c.2.2.1
                            have p3704_3 := h3704c.2.2.2
                            linarith only [hlam, p3704_0]
                          · have p3704_0 := h3704c.1
                            have p3704_1 := h3704c.2.1
                            have p3704_2 := h3704c.2.2.1
                            have p3704_3 := h3704c.2.2.2
                            rcases p3704_3 (m.d 0 1) (by simp) with h3718 | h3718
                            · linarith only [h0, h3718, hlam]
                            · rcases p3704_3 (m.d 0 2) (by simp) with h3720 | h3720
                              · rcases p3704_3 (m.d 0 3) (by simp) with h3721 | h3721
                                · linarith only [h2852, h3721, hlam]
                                · rcases p3704_3 (m.d 0 4) (by simp) with h3723 | h3723
                                  · linarith only [h2853, h3723, hlam]
                                  · linarith only [h2855, h3723, hlam]
                              · linarith only [h2852, h3720, hlam]
                          · have p3704_0 := h3704c.1
                            have p3704_1 := h3704c.2.1
                            have p3704_2 := h3704c.2.2.1
                            have p3704_3 := h3704c.2.2.2
                            linarith only [h0, h3688, h3701, hc12, hlam, hphi, ht01, ht0b, ht5b, p3704_1, u5ehi2]
                          · have p3704_0 := h3704c.1
                            have p3704_1 := h3704c.2.1
                            have p3704_2 := h3704c.2.2.1
                            have p3704_3 := h3704c.2.2.2
                            linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p3704_1, u5ehi0]
                          · have p3704_0 := h3704c.1
                            have p3704_1 := h3704c.2.1
                            have p3704_2 := h3704c.2.2.1
                            have p3704_3 := h3704c.2.2.2
                            linarith only [h2249, h3694, h3703, hc01, hc34, hlam, hphi, ht12, ht23, p3704_1]
                          · have p3704_0 := h3704c.1
                            have p3704_1 := h3704c.2.1
                            have p3704_2 := h3704c.2.2.1
                            have p3704_3 := h3704c.2.2.2
                            linarith only [h2852, hlam, p3704_1]
                          · have p3704_0 := h3704c.1
                            have p3704_1 := h3704c.2.1
                            have p3704_2 := h3704c.2.2.1
                            have p3704_3 := h3704c.2.2.2
                            linarith only [hlam, p3704_0]
                          · have p3704_0 := h3704c.1
                            have p3704_1 := h3704c.2.1
                            have p3704_2 := h3704c.2.2.1
                            have p3704_3 := h3704c.2.2.2
                            linarith only [h2855, hlam, p3704_1]
                          · have p3704_0 := h3704c.1
                            have p3704_1 := h3704c.2.1
                            have p3704_2 := h3704c.2.2.1
                            have p3704_3 := h3704c.2.2.2
                            linarith only [h3686, hlam, p3704_1]
                          · have p3704_0 := h3704c.1
                            have p3704_1 := h3704c.2.1
                            have p3704_2 := h3704c.2.2.1
                            have p3704_3 := h3704c.2.2.2
                            rcases p3704_3 (m.d 0 1) (by simp) with h3734 | h3734
                            · linarith only [h2576, h3734, hlam]
                            · rcases p3704_3 (m.d 0 2) (by simp) with h3736 | h3736
                              · rcases p3704_3 (m.d 0 3) (by simp) with h3737 | h3737
                                · linarith only [h2855, h3737, hlam]
                                · linarith only [h2249, h3737, hlam]
                              · linarith only [h0, h3736, hlam]
                          · have p3704_0 := h3704c.1
                            have p3704_1 := h3704c.2.1
                            have p3704_2 := h3704c.2.2.1
                            have p3704_3 := h3704c.2.2.2
                            linarith only [h2853, hlam, p3704_0]
                          · have p3704_0 := h3704c.1
                            have p3704_1 := h3704c.2.1
                            have p3704_2 := h3704c.2.2.1
                            have p3704_3 := h3704c.2.2.2
                            rcases p3704_3 (m.d 0 1) (by simp) with h3742 | h3742
                            · linarith only [h2576, h3742, hlam]
                            · rcases p3704_3 (m.d 0 2) (by simp) with h3744 | h3744
                              · rcases p3704_3 (m.d 0 3) (by simp) with h3745 | h3745
                                · linarith only [h2855, h3745, hlam]
                                · rcases p3704_3 (m.d 0 4) (by simp) with h3747 | h3747
                                  · rcases p3704_3 (m.d 0 5) (by simp) with h3748 | h3748
                                    · linarith only [h3688, h3748, hlam]
                                    · linarith only [h3686, h3748, hlam]
                                  · linarith only [h2855, h3747, hlam]
                              · linarith only [h2852, h3744, hlam]
                          · have p3704_0 := h3704c.1
                            have p3704_1 := h3704c.2.1
                            have p3704_2 := h3704c.2.2.1
                            have p3704_3 := h3704c.2.2.2
                            linarith only [hlam, p3704_0]
                          · have p3704_0 := h3704c.1
                            have p3704_1 := h3704c.2.1
                            have p3704_2 := h3704c.2.2.1
                            have p3704_3 := h3704c.2.2.2
                            linarith only [h3688, h3701, hc04, hlam, hphi, ht0b, ht5b, p3704_1, u5ehi2]
                          · have p3704_0 := h3704c.1
                            have p3704_1 := h3704c.2.1
                            have p3704_2 := h3704c.2.2.1
                            have p3704_3 := h3704c.2.2.2
                            rcases p3704_3 (m.d 0 1) (by simp) with h3755 | h3755
                            · linarith only [h2850, h3755, hlam]
                            · rcases p3704_3 (m.d 0 2) (by simp) with h3757 | h3757
                              · rcases p3704_3 (m.d 0 3) (by simp) with h3758 | h3758
                                · linarith only [h3686, h3758, hlam]
                                · linarith only [h2249, h3758, hlam]
                              · linarith only [h0, h3757, hlam]
                          · have p3704_0 := h3704c.1
                            have p3704_1 := h3704c.2.1
                            have p3704_2 := h3704c.2.2.1
                            have p3704_3 := h3704c.2.2.2
                            linarith only [h2854, hlam, p3704_1]
                          · have p3704_0 := h3704c.1
                            have p3704_1 := h3704c.2.1
                            have p3704_2 := h3704c.2.2.1
                            have p3704_3 := h3704c.2.2.2
                            rcases p3704_3 (m.d 0 1) (by simp) with h3763 | h3763
                            · linarith only [h2850, h3763, hlam]
                            · rcases p3704_3 (m.d 0 2) (by simp) with h3765 | h3765
                              · rcases p3704_3 (m.d 0 3) (by simp) with h3766 | h3766
                                · linarith only [h3686, h3766, hlam]
                                · rcases p3704_3 (m.d 0 4) (by simp) with h3768 | h3768
                                  · rcases p3704_3 (m.d 0 5) (by simp) with h3769 | h3769
                                    · rcases h2bigk with h3770c | h3770c | h3770c | h3770c | h3770c | h3770c | h3770c | h3770c | h3770c | h3770c | h3770c | h3770c | h3770c | h3770c | h3770c | h3770c | h3770c | h3770c | h3770c | h3770c | h3770c | h3770c | h3770c | h3770c | h3770c
                                      · have p3770_0 := h3770c.1
                                        have p3770_1 := h3770c.2.1
                                        have p3770_2 := h3770c.2.2.1
                                        have p3770_3 := h3770c.2.2.2
                                        linarith only [hlam, p3770_0]
                                      · have p3770_0 := h3770c.1
                                        have p3770_1 := h3770c.2.1
                                        have p3770_2 := h3770c.2.2.1
                                        have p3770_3 := h3770c.2.2.2
                                        linarith only [h0, hlam, p3770_1]
                                      · have p3770_0 := h3770c.1
                                        have p3770_1 := h3770c.2.1
                                        have p3770_2 := h3770c.2.2.1
                                        have p3770_3 := h3770c.2.2.2
                                        rcases p3770_3 (m.d 0 2) (by simp) with h3773 | h3773
                                        · rcases p3770_3 (m.d 1 2) (by simp) with h3774 | h3774
                                          · rcases p3770_3 (m.d 2 3) (by simp) with h3775 | h3775
                                            · linarith only [h3775, hlam, p3770_0]
                                            · rcases p3770_3 (m.d 2 4) (by simp) with h3777 | h3777
                                              · linarith only [h2853, h3777, hlam]
                                              · linarith only [h3697, h3777, hlam]
                                          · linarith only [h3689, h3774, hlam]
                                        · linarith only [h3773, hlam, p3770_0]
                                      · have p3770_0 := h3770c.1
                                        have p3770_1 := h3770c.2.1
                                        have p3770_2 := h3770c.2.2.1
                                        have p3770_3 := h3770c.2.2.2
                                        rcases p3770_3 (m.d 0 2) (by simp) with h3782 | h3782
                                        · rcases p3770_3 (m.d 1 2) (by simp) with h3783 | h3783
                                          · rcases p3770_3 (m.d 2 3) (by simp) with h3784 | h3784
                                            · linarith only [h2852, h3784, hlam]
                                            · rcases p3770_3 (m.d 2 4) (by simp) with h3786 | h3786
                                              · linarith only [h3786, hlam, p3770_0]
                                              · rcases p3770_3 (m.d 2 5) (by simp) with h3788 | h3788
                                                · linarith only [h2854, h3788, hlam]
                                                · linarith only [h3701, h3788, hlam]
                                          · linarith only [h3690, h3783, hlam]
                                        · linarith only [h3782, hlam, p3770_0]
                                      · have p3770_0 := h3770c.1
                                        have p3770_1 := h3770c.2.1
                                        have p3770_2 := h3770c.2.2.1
                                        have p3770_3 := h3770c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p3770_1, u5ehi2]
                                      · have p3770_0 := h3770c.1
                                        have p3770_1 := h3770c.2.1
                                        have p3770_2 := h3770c.2.2.1
                                        have p3770_3 := h3770c.2.2.2
                                        linarith only [h2854, hc12, hlam, hphi, ht01, ht0b, ht5b, p3770_1, u5ehi2]
                                      · have p3770_0 := h3770c.1
                                        have p3770_1 := h3770c.2.1
                                        have p3770_2 := h3770c.2.2.1
                                        have p3770_3 := h3770c.2.2.2
                                        linarith only [hlam, p3770_0]
                                      · have p3770_0 := h3770c.1
                                        have p3770_1 := h3770c.2.1
                                        have p3770_2 := h3770c.2.2.1
                                        have p3770_3 := h3770c.2.2.2
                                        rcases p3770_3 (m.d 0 2) (by simp) with h3796 | h3796
                                        · linarith only [h0, h3796, hlam]
                                        · linarith only [h2852, h3796, hlam]
                                      · have p3770_0 := h3770c.1
                                        have p3770_1 := h3770c.2.1
                                        have p3770_2 := h3770c.2.2.1
                                        have p3770_3 := h3770c.2.2.2
                                        rcases p3770_3 (m.d 0 2) (by simp) with h3799 | h3799
                                        · linarith only [h0, h3799, hlam]
                                        · linarith only [h2853, h3799, hlam]
                                      · have p3770_0 := h3770c.1
                                        have p3770_1 := h3770c.2.1
                                        have p3770_2 := h3770c.2.2.1
                                        have p3770_3 := h3770c.2.2.2
                                        linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p3770_1, u5ehi2]
                                      · have p3770_0 := h3770c.1
                                        have p3770_1 := h3770c.2.1
                                        have p3770_2 := h3770c.2.2.1
                                        have p3770_3 := h3770c.2.2.2
                                        linarith only [h2852, hlam, p3770_0]
                                      · have p3770_0 := h3770c.1
                                        have p3770_1 := h3770c.2.1
                                        have p3770_2 := h3770c.2.2.1
                                        have p3770_3 := h3770c.2.2.2
                                        linarith only [h3689, hlam, p3770_0]
                                      · have p3770_0 := h3770c.1
                                        have p3770_1 := h3770c.2.1
                                        have p3770_2 := h3770c.2.2.1
                                        have p3770_3 := h3770c.2.2.2
                                        linarith only [hlam, p3770_0]
                                      · have p3770_0 := h3770c.1
                                        have p3770_1 := h3770c.2.1
                                        have p3770_2 := h3770c.2.2.1
                                        have p3770_3 := h3770c.2.2.2
                                        linarith only [h3697, hlam, p3770_0]
                                      · have p3770_0 := h3770c.1
                                        have p3770_1 := h3770c.2.1
                                        have p3770_2 := h3770c.2.2.1
                                        have p3770_3 := h3770c.2.2.2
                                        linarith only [h3699, hlam, p3770_0]
                                      · have p3770_0 := h3770c.1
                                        have p3770_1 := h3770c.2.1
                                        have p3770_2 := h3770c.2.2.1
                                        have p3770_3 := h3770c.2.2.2
                                        linarith only [h2853, hlam, p3770_0]
                                      · have p3770_0 := h3770c.1
                                        have p3770_1 := h3770c.2.1
                                        have p3770_2 := h3770c.2.2.1
                                        have p3770_3 := h3770c.2.2.2
                                        linarith only [h3690, hlam, p3770_0]
                                      · have p3770_0 := h3770c.1
                                        have p3770_1 := h3770c.2.1
                                        have p3770_2 := h3770c.2.2.1
                                        have p3770_3 := h3770c.2.2.2
                                        linarith only [h2853, h3688, h3701, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3770_1]
                                      · have p3770_0 := h3770c.1
                                        have p3770_1 := h3770c.2.1
                                        have p3770_2 := h3770c.2.2.1
                                        have p3770_3 := h3770c.2.2.2
                                        linarith only [hlam, p3770_0]
                                      · have p3770_0 := h3770c.1
                                        have p3770_1 := h3770c.2.1
                                        have p3770_2 := h3770c.2.2.1
                                        have p3770_3 := h3770c.2.2.2
                                        linarith only [h3701, hlam, p3770_1]
                                      · have p3770_0 := h3770c.1
                                        have p3770_1 := h3770c.2.1
                                        have p3770_2 := h3770c.2.2.1
                                        have p3770_3 := h3770c.2.2.2
                                        linarith only [h2854, hlam, p3770_0]
                                      · have p3770_0 := h3770c.1
                                        have p3770_1 := h3770c.2.1
                                        have p3770_2 := h3770c.2.2.1
                                        have p3770_3 := h3770c.2.2.2
                                        linarith only [h3691, hlam, p3770_0]
                                      · have p3770_0 := h3770c.1
                                        have p3770_1 := h3770c.2.1
                                        have p3770_2 := h3770c.2.2.1
                                        have p3770_3 := h3770c.2.2.2
                                        linarith only [h2576, h3688, h3692, h3701, hc23, hc34, hlam, hphi, p3770_1]
                                      · have p3770_0 := h3770c.1
                                        have p3770_1 := h3770c.2.1
                                        have p3770_2 := h3770c.2.2.1
                                        have p3770_3 := h3770c.2.2.2
                                        linarith only [h2576, h3688, h3692, h3697, h3701, hc23, hc34, hlam, hphi, p3770_1]
                                      · have p3770_0 := h3770c.1
                                        have p3770_1 := h3770c.2.1
                                        have p3770_2 := h3770c.2.2.1
                                        have p3770_3 := h3770c.2.2.2
                                        linarith only [hlam, p3770_0]
                                    · linarith only [h3686, h3769, hlam]
                                  · linarith only [h2855, h3768, hlam]
                              · linarith only [h2852, h3765, hlam]
                          · have p3704_0 := h3704c.1
                            have p3704_1 := h3704c.2.1
                            have p3704_2 := h3704c.2.2.1
                            have p3704_3 := h3704c.2.2.2
                            linarith only [h3688, hlam, p3704_1]
                          · have p3704_0 := h3704c.1
                            have p3704_1 := h3704c.2.1
                            have p3704_2 := h3704c.2.2.1
                            have p3704_3 := h3704c.2.2.2
                            linarith only [hlam, p3704_0]
                        · linarith only [h2576, h3688, h3692, h3703, hlam]
                · linarith only [h2576, h3688, h3696, hlam]
          · linarith only [h0, h2853, h3688, h3691, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
        · linarith only [h0, h2853, h3688, h3690, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
      · linarith only [h0, h2853, h3688, h3689, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3828 | h3828
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3829 | h3829
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3830 | h3830
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3831 | h3831
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3832 | h3832
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3833 | h3833
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3834 | h3834
                  · linarith only [h0, h2249, h2852, h2855, h3834, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3836 | h3836
                    · linarith only [h2852, h2854, h2855, h3686, h3836, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3838 | h3838
                      · linarith only [h2853, h3688, h3838, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3840 | h3840
                        · linarith only [h3828, h3831, h3840, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                        · linarith only [h2249, h2855, h3828, h3831, h3833, h3840, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3843 | h3843
                  · linarith only [h2852, h2855, h3843, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3845 | h3845
                    · linarith only [h2852, h2854, h2855, h3686, h3845, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3847 | h3847
                      · linarith only [h2853, h2855, h3831, h3833, h3847, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3849 | h3849
                        · linarith only [h3831, h3833, h3849, hlam]
                        · rcases h0bigk with h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c | h3851c
                          · have p3851_0 := h3851c.1
                            have p3851_1 := h3851c.2.1
                            have p3851_2 := h3851c.2.2.1
                            have p3851_3 := h3851c.2.2.2
                            linarith only [hlam, p3851_0]
                          · have p3851_0 := h3851c.1
                            have p3851_1 := h3851c.2.1
                            have p3851_2 := h3851c.2.2.1
                            have p3851_3 := h3851c.2.2.2
                            linarith only [h0, hlam, p3851_1]
                          · have p3851_0 := h3851c.1
                            have p3851_1 := h3851c.2.1
                            have p3851_2 := h3851c.2.2.1
                            have p3851_3 := h3851c.2.2.2
                            linarith only [h2249, hlam, p3851_0]
                          · have p3851_0 := h3851c.1
                            have p3851_1 := h3851c.2.1
                            have p3851_2 := h3851c.2.2.1
                            have p3851_3 := h3851c.2.2.2
                            linarith only [h2576, hlam, p3851_1]
                          · have p3851_0 := h3851c.1
                            have p3851_1 := h3851c.2.1
                            have p3851_2 := h3851c.2.2.1
                            have p3851_3 := h3851c.2.2.2
                            linarith only [h2850, hlam, p3851_1]
                          · have p3851_0 := h3851c.1
                            have p3851_1 := h3851c.2.1
                            have p3851_2 := h3851c.2.2.1
                            have p3851_3 := h3851c.2.2.2
                            rcases p3851_3 (m.d 0 1) (by simp) with h3857 | h3857
                            · linarith only [h0, h3857, hlam]
                            · rcases p3851_3 (m.d 0 2) (by simp) with h3859 | h3859
                              · rcases p3851_3 (m.d 0 3) (by simp) with h3860 | h3860
                                · linarith only [h2852, h3860, hlam]
                                · linarith only [h2249, h3860, hlam]
                              · linarith only [h0, h3859, hlam]
                          · have p3851_0 := h3851c.1
                            have p3851_1 := h3851c.2.1
                            have p3851_2 := h3851c.2.2.1
                            have p3851_3 := h3851c.2.2.2
                            linarith only [hlam, p3851_0]
                          · have p3851_0 := h3851c.1
                            have p3851_1 := h3851c.2.1
                            have p3851_2 := h3851c.2.2.1
                            have p3851_3 := h3851c.2.2.2
                            rcases p3851_3 (m.d 0 1) (by simp) with h3865 | h3865
                            · linarith only [h0, h3865, hlam]
                            · rcases p3851_3 (m.d 0 2) (by simp) with h3867 | h3867
                              · rcases p3851_3 (m.d 0 3) (by simp) with h3868 | h3868
                                · linarith only [h2852, h3868, hlam]
                                · rcases p3851_3 (m.d 0 4) (by simp) with h3870 | h3870
                                  · linarith only [h2853, h3870, hlam]
                                  · linarith only [h2855, h3870, hlam]
                              · linarith only [h2852, h3867, hlam]
                          · have p3851_0 := h3851c.1
                            have p3851_1 := h3851c.2.1
                            have p3851_2 := h3851c.2.2.1
                            have p3851_3 := h3851c.2.2.2
                            rcases p3851_3 (m.d 0 1) (by simp) with h3874 | h3874
                            · linarith only [h0, h3874, hlam]
                            · rcases p3851_3 (m.d 0 2) (by simp) with h3876 | h3876
                              · rcases p3851_3 (m.d 0 3) (by simp) with h3877 | h3877
                                · linarith only [h2852, h3877, hlam]
                                · rcases p3851_3 (m.d 0 4) (by simp) with h3879 | h3879
                                  · linarith only [h2853, h3879, hlam]
                                  · rcases p3851_3 (m.d 0 5) (by simp) with h3881 | h3881
                                    · linarith only [h2854, h3881, hlam]
                                    · linarith only [h3688, h3881, hlam]
                              · linarith only [h2853, h3876, hlam]
                          · have p3851_0 := h3851c.1
                            have p3851_1 := h3851c.2.1
                            have p3851_2 := h3851c.2.2.1
                            have p3851_3 := h3851c.2.2.2
                            linarith only [h0, h2854, hc12, hlam, hphi, ht01, ht0b, ht5b, p3851_1, u5ehi2]
                          · have p3851_0 := h3851c.1
                            have p3851_1 := h3851c.2.1
                            have p3851_2 := h3851c.2.2.1
                            have p3851_3 := h3851c.2.2.2
                            linarith only [h2855, h3832, h3849, hc01, hc13, hlam, hphi, p3851_1]
                          · have p3851_0 := h3851c.1
                            have p3851_1 := h3851c.2.1
                            have p3851_2 := h3851c.2.2.1
                            have p3851_3 := h3851c.2.2.2
                            linarith only [h2852, hlam, p3851_1]
                          · have p3851_0 := h3851c.1
                            have p3851_1 := h3851c.2.1
                            have p3851_2 := h3851c.2.2.1
                            have p3851_3 := h3851c.2.2.2
                            linarith only [hlam, p3851_0]
                          · have p3851_0 := h3851c.1
                            have p3851_1 := h3851c.2.1
                            have p3851_2 := h3851c.2.2.1
                            have p3851_3 := h3851c.2.2.2
                            linarith only [h2855, hlam, p3851_1]
                          · have p3851_0 := h3851c.1
                            have p3851_1 := h3851c.2.1
                            have p3851_2 := h3851c.2.2.1
                            have p3851_3 := h3851c.2.2.2
                            linarith only [h3686, hlam, p3851_1]
                          · have p3851_0 := h3851c.1
                            have p3851_1 := h3851c.2.1
                            have p3851_2 := h3851c.2.2.1
                            have p3851_3 := h3851c.2.2.2
                            linarith only [h2576, h3833, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3851_1]
                          · have p3851_0 := h3851c.1
                            have p3851_1 := h3851c.2.1
                            have p3851_2 := h3851c.2.2.1
                            have p3851_3 := h3851c.2.2.2
                            linarith only [h2853, hlam, p3851_0]
                          · have p3851_0 := h3851c.1
                            have p3851_1 := h3851c.2.1
                            have p3851_2 := h3851c.2.2.1
                            have p3851_3 := h3851c.2.2.2
                            linarith only [h2576, h3833, hc03, hc45, hlam, hphi, ht34, p3851_1]
                          · have p3851_0 := h3851c.1
                            have p3851_1 := h3851c.2.1
                            have p3851_2 := h3851c.2.2.1
                            have p3851_3 := h3851c.2.2.2
                            linarith only [hlam, p3851_0]
                          · have p3851_0 := h3851c.1
                            have p3851_1 := h3851c.2.1
                            have p3851_2 := h3851c.2.2.1
                            have p3851_3 := h3851c.2.2.2
                            linarith only [h3688, hlam, p3851_0]
                          · have p3851_0 := h3851c.1
                            have p3851_1 := h3851c.2.1
                            have p3851_2 := h3851c.2.2.1
                            have p3851_3 := h3851c.2.2.2
                            linarith only [h3686, h3832, hc01, hc13, hlam, hphi, p3851_1]
                          · have p3851_0 := h3851c.1
                            have p3851_1 := h3851c.2.1
                            have p3851_2 := h3851c.2.2.1
                            have p3851_3 := h3851c.2.2.2
                            linarith only [h2854, hlam, p3851_1]
                          · have p3851_0 := h3851c.1
                            have p3851_1 := h3851c.2.1
                            have p3851_2 := h3851c.2.2.1
                            have p3851_3 := h3851c.2.2.2
                            linarith only [h2249, h3686, h3832, hc01, hc13, hlam, hphi, p3851_1]
                          · have p3851_0 := h3851c.1
                            have p3851_1 := h3851c.2.1
                            have p3851_2 := h3851c.2.2.1
                            have p3851_3 := h3851c.2.2.2
                            linarith only [h2576, h3686, h3832, hc01, hc13, hlam, hphi, p3851_1]
                          · have p3851_0 := h3851c.1
                            have p3851_1 := h3851c.2.1
                            have p3851_2 := h3851c.2.2.1
                            have p3851_3 := h3851c.2.2.2
                            linarith only [hlam, p3851_0]
              · linarith only [h2249, h2855, h3831, h3832, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3902 | h3902
              · linarith only [h3831, h3902, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3904 | h3904
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3905 | h3905
                  · linarith only [h3688, h3831, h3904, h3905, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3907 | h3907
                    · linarith only [h2249, h3902, h3907, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3909 | h3909
                      · linarith only [h2853, h3688, h3909, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3911 | h3911
                        · rcases h0bigk with h3912c | h3912c | h3912c | h3912c | h3912c | h3912c | h3912c | h3912c | h3912c | h3912c | h3912c | h3912c | h3912c | h3912c | h3912c | h3912c | h3912c | h3912c | h3912c | h3912c | h3912c | h3912c | h3912c | h3912c | h3912c
                          · have p3912_0 := h3912c.1
                            have p3912_1 := h3912c.2.1
                            have p3912_2 := h3912c.2.2.1
                            have p3912_3 := h3912c.2.2.2
                            linarith only [hlam, p3912_0]
                          · have p3912_0 := h3912c.1
                            have p3912_1 := h3912c.2.1
                            have p3912_2 := h3912c.2.2.1
                            have p3912_3 := h3912c.2.2.2
                            linarith only [h0, hlam, p3912_1]
                          · have p3912_0 := h3912c.1
                            have p3912_1 := h3912c.2.1
                            have p3912_2 := h3912c.2.2.1
                            have p3912_3 := h3912c.2.2.2
                            linarith only [h2249, hlam, p3912_0]
                          · have p3912_0 := h3912c.1
                            have p3912_1 := h3912c.2.1
                            have p3912_2 := h3912c.2.2.1
                            have p3912_3 := h3912c.2.2.2
                            linarith only [h2576, hlam, p3912_1]
                          · have p3912_0 := h3912c.1
                            have p3912_1 := h3912c.2.1
                            have p3912_2 := h3912c.2.2.1
                            have p3912_3 := h3912c.2.2.2
                            linarith only [h2850, hlam, p3912_1]
                          · have p3912_0 := h3912c.1
                            have p3912_1 := h3912c.2.1
                            have p3912_2 := h3912c.2.2.1
                            have p3912_3 := h3912c.2.2.2
                            rcases p3912_3 (m.d 0 1) (by simp) with h3918 | h3918
                            · linarith only [h0, h3918, hlam]
                            · rcases p3912_3 (m.d 0 2) (by simp) with h3920 | h3920
                              · rcases p3912_3 (m.d 0 3) (by simp) with h3921 | h3921
                                · linarith only [h2852, h3921, hlam]
                                · linarith only [h2249, h3921, hlam]
                              · linarith only [h0, h3920, hlam]
                          · have p3912_0 := h3912c.1
                            have p3912_1 := h3912c.2.1
                            have p3912_2 := h3912c.2.2.1
                            have p3912_3 := h3912c.2.2.2
                            linarith only [hlam, p3912_0]
                          · have p3912_0 := h3912c.1
                            have p3912_1 := h3912c.2.1
                            have p3912_2 := h3912c.2.2.1
                            have p3912_3 := h3912c.2.2.2
                            rcases p3912_3 (m.d 0 1) (by simp) with h3926 | h3926
                            · linarith only [h0, h3926, hlam]
                            · rcases p3912_3 (m.d 0 2) (by simp) with h3928 | h3928
                              · rcases p3912_3 (m.d 0 3) (by simp) with h3929 | h3929
                                · linarith only [h2852, h3929, hlam]
                                · rcases p3912_3 (m.d 0 4) (by simp) with h3931 | h3931
                                  · linarith only [h2853, h3931, hlam]
                                  · linarith only [h2855, h3931, hlam]
                              · linarith only [h2852, h3928, hlam]
                          · have p3912_0 := h3912c.1
                            have p3912_1 := h3912c.2.1
                            have p3912_2 := h3912c.2.2.1
                            have p3912_3 := h3912c.2.2.2
                            rcases p3912_3 (m.d 0 1) (by simp) with h3935 | h3935
                            · linarith only [h0, h3935, hlam]
                            · rcases p3912_3 (m.d 0 2) (by simp) with h3937 | h3937
                              · rcases p3912_3 (m.d 0 3) (by simp) with h3938 | h3938
                                · linarith only [h2852, h3938, hlam]
                                · rcases p3912_3 (m.d 0 4) (by simp) with h3940 | h3940
                                  · linarith only [h2853, h3940, hlam]
                                  · rcases p3912_3 (m.d 0 5) (by simp) with h3942 | h3942
                                    · linarith only [h2854, h3942, hlam]
                                    · linarith only [h3688, h3942, hlam]
                              · linarith only [h2853, h3937, hlam]
                          · have p3912_0 := h3912c.1
                            have p3912_1 := h3912c.2.1
                            have p3912_2 := h3912c.2.2.1
                            have p3912_3 := h3912c.2.2.2
                            linarith only [h0, h2854, hc12, hlam, hphi, ht01, ht0b, ht5b, p3912_1, u5ehi2]
                          · have p3912_0 := h3912c.1
                            have p3912_1 := h3912c.2.1
                            have p3912_2 := h3912c.2.2.1
                            have p3912_3 := h3912c.2.2.2
                            linarith only [h2855, h3688, h3831, h3904, hc01, hc34, hlam, hphi, ht12, ht23, p3912_1]
                          · have p3912_0 := h3912c.1
                            have p3912_1 := h3912c.2.1
                            have p3912_2 := h3912c.2.2.1
                            have p3912_3 := h3912c.2.2.2
                            linarith only [h2852, hlam, p3912_1]
                          · have p3912_0 := h3912c.1
                            have p3912_1 := h3912c.2.1
                            have p3912_2 := h3912c.2.2.1
                            have p3912_3 := h3912c.2.2.2
                            linarith only [hlam, p3912_0]
                          · have p3912_0 := h3912c.1
                            have p3912_1 := h3912c.2.1
                            have p3912_2 := h3912c.2.2.1
                            have p3912_3 := h3912c.2.2.2
                            linarith only [h2855, hlam, p3912_1]
                          · have p3912_0 := h3912c.1
                            have p3912_1 := h3912c.2.1
                            have p3912_2 := h3912c.2.2.1
                            have p3912_3 := h3912c.2.2.2
                            linarith only [h3686, hlam, p3912_1]
                          · have p3912_0 := h3912c.1
                            have p3912_1 := h3912c.2.1
                            have p3912_2 := h3912c.2.2.1
                            have p3912_3 := h3912c.2.2.2
                            linarith only [h3688, h3831, h3904, hc01, hc34, hlam, hphi, ht12, ht23, p3912_1]
                          · have p3912_0 := h3912c.1
                            have p3912_1 := h3912c.2.1
                            have p3912_2 := h3912c.2.2.1
                            have p3912_3 := h3912c.2.2.2
                            linarith only [h2853, hlam, p3912_0]
                          · have p3912_0 := h3912c.1
                            have p3912_1 := h3912c.2.1
                            have p3912_2 := h3912c.2.2.1
                            have p3912_3 := h3912c.2.2.2
                            linarith only [h3688, h3831, h3904, hc03, hc34, hlam, hphi, p3912_1]
                          · have p3912_0 := h3912c.1
                            have p3912_1 := h3912c.2.1
                            have p3912_2 := h3912c.2.2.1
                            have p3912_3 := h3912c.2.2.2
                            linarith only [hlam, p3912_0]
                          · have p3912_0 := h3912c.1
                            have p3912_1 := h3912c.2.1
                            have p3912_2 := h3912c.2.2.1
                            have p3912_3 := h3912c.2.2.2
                            linarith only [h3688, hlam, p3912_0]
                          · have p3912_0 := h3912c.1
                            have p3912_1 := h3912c.2.1
                            have p3912_2 := h3912c.2.2.1
                            have p3912_3 := h3912c.2.2.2
                            linarith only [h3688, h3831, h3904, hc01, hc34, hlam, hphi, ht12, ht23, p3912_1]
                          · have p3912_0 := h3912c.1
                            have p3912_1 := h3912c.2.1
                            have p3912_2 := h3912c.2.2.1
                            have p3912_3 := h3912c.2.2.2
                            linarith only [h2854, hlam, p3912_1]
                          · have p3912_0 := h3912c.1
                            have p3912_1 := h3912c.2.1
                            have p3912_2 := h3912c.2.2.1
                            have p3912_3 := h3912c.2.2.2
                            linarith only [h2249, h3688, h3831, h3904, hc01, hc34, hlam, hphi, ht12, ht23, p3912_1]
                          · have p3912_0 := h3912c.1
                            have p3912_1 := h3912c.2.1
                            have p3912_2 := h3912c.2.2.1
                            have p3912_3 := h3912c.2.2.2
                            linarith only [h2576, h3688, h3831, h3904, hc01, hc34, hlam, hphi, ht12, ht23, p3912_1]
                          · have p3912_0 := h3912c.1
                            have p3912_1 := h3912c.2.1
                            have p3912_2 := h3912c.2.2.1
                            have p3912_3 := h3912c.2.2.2
                            linarith only [hlam, p3912_0]
                        · linarith only [h3831, h3904, h3911, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3963 | h3963
                  · linarith only [h2852, h2855, h3963, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3965 | h3965
                    · linarith only [h2249, h3902, h3965, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3967 | h3967
                      · linarith only [h2576, h2853, h3904, h3967, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3969 | h3969
                        · linarith only [h2249, h3831, h3904, h3969, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h2249, h3831, h3969, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · linarith only [h0, h2854, h3830, hlam]
        · linarith only [h0, h2854, h3829, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
      · linarith only [h0, h2854, h3828, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]

set_option maxHeartbeats 5048000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_R_s0_x1_x1_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2249 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2576 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2850 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2852 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2853 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2854 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 4 (by decide) (by decide) with h2855 | h2855
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_R_s0_x1_x1_x1_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 h2249 h2576 h2850 h2852 h2853 h2854 h2855
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_R_s0_x1_x1_x1_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 h2249 h2576 h2850 h2852 h2853 h2854 h2855

set_option maxHeartbeats 5048000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_R_s0_x1_x1_x1_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2249 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2576 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2850 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2852 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2853 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2854 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 4 (by decide) (by decide) with h3975 | h3975
  · rcases m.htr 0 3 5 (by decide) (by decide) with h3976 | h3976
    · linarith only [h2852, h2854, h3976, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3978 | h3978
      · linarith only [h2852, h2854, h3975, h3978, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3980 | h3980
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3981 | h3981
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3982 | h3982
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3983 | h3983
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3984 | h3984
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3985 | h3985
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3986 | h3986
                    · linarith only [h2852, h2854, h3982, h3986, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h2852, h2854, h3975, h3982, h3986, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3989 | h3989
                    · linarith only [h2852, h2854, h3982, h3989, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h2852, h2854, h3975, h3982, h3989, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3992 | h3992
                  · linarith only [h3978, h3983, h3984, h3992, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3994 | h3994
                    · linarith only [h2852, h2854, h3982, h3994, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h2852, h2854, h3975, h3982, h3994, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h2249, h2852, h2854, h3975, h3982, h3983, hc01, hc12, hlam, hphi]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3998 | h3998
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3999 | h3999
                · linarith only [h3975, h3976, h3980, h3982, h3999, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h4001 | h4001
                  · linarith only [h3978, h3981, h3982, h4001, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4003 | h4003
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h4004 | h4004
                      · linarith only [h2852, h4004, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4006 | h4006
                        · linarith only [h0, h2850, h2853, h3982, h4001, h4004, h4006, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                        · linarith only [h0, h2852, h3982, h4003, h4006, hc34, hc45, hlam, hphi]
                    · linarith only [h3975, h3976, h4003, hc23, hc35, hlam, hphi]
              · linarith only [h2249, h3975, h3998, hlam]
          · linarith only [h0, h2853, h3981, hlam]
        · linarith only [h0, h2852, h3980, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h4013 | h4013
    · linarith only [h3975, h4013, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h4015 | h4015
      · linarith only [h2853, h2854, h4015, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4017 | h4017
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4018 | h4018
          · rcases m.htr 1 2 5 (by decide) (by decide) with h4019 | h4019
            · rcases m.htr 1 3 4 (by decide) (by decide) with h4020 | h4020
              · rcases m.htr 1 3 5 (by decide) (by decide) with h4021 | h4021
                · rcases m.htr 1 4 5 (by decide) (by decide) with h4022 | h4022
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4023 | h4023
                    · linarith only [h2852, h2854, h3975, h4019, h4023, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h4025 | h4025
                      · linarith only [h2853, h2854, h4013, h4019, h4023, h4025, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4027 | h4027
                        · linarith only [h2853, h2854, h4017, h4021, h4025, h4027, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4029 | h4029
                          · linarith only [h2853, h2854, h4023, h4027, h4029, hc23, hc34, hlam, hphi]
                          · linarith only [h2249, h3975, h4017, h4020, h4022, h4029, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4032 | h4032
                    · linarith only [h2249, h2852, h2854, h3975, h4019, h4032, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h4034 | h4034
                      · linarith only [h2853, h2854, h4019, h4032, h4034, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4036 | h4036
                        · linarith only [h2249, h2853, h2854, h3975, h4017, h4020, h4021, h4022, h4034, h4036, hc01, hc12, hlam, hphi]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4038 | h4038
                          · linarith only [h4020, h4022, h4038, hlam]
                          · rcases h0bigk with h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c
                            · have p4040_0 := h4040c.1
                              have p4040_1 := h4040c.2.1
                              have p4040_2 := h4040c.2.2.1
                              have p4040_3 := h4040c.2.2.2
                              linarith only [hlam, p4040_0]
                            · have p4040_0 := h4040c.1
                              have p4040_1 := h4040c.2.1
                              have p4040_2 := h4040c.2.2.1
                              have p4040_3 := h4040c.2.2.2
                              linarith only [h0, hlam, p4040_1]
                            · have p4040_0 := h4040c.1
                              have p4040_1 := h4040c.2.1
                              have p4040_2 := h4040c.2.2.1
                              have p4040_3 := h4040c.2.2.2
                              linarith only [h2249, hlam, p4040_0]
                            · have p4040_0 := h4040c.1
                              have p4040_1 := h4040c.2.1
                              have p4040_2 := h4040c.2.2.1
                              have p4040_3 := h4040c.2.2.2
                              linarith only [h2576, hlam, p4040_1]
                            · have p4040_0 := h4040c.1
                              have p4040_1 := h4040c.2.1
                              have p4040_2 := h4040c.2.2.1
                              have p4040_3 := h4040c.2.2.2
                              linarith only [h2850, hlam, p4040_1]
                            · have p4040_0 := h4040c.1
                              have p4040_1 := h4040c.2.1
                              have p4040_2 := h4040c.2.2.1
                              have p4040_3 := h4040c.2.2.2
                              linarith only [h2854, h4017, h4021, h4034, hc01, hc12, hlam, hphi, p4040_1]
                            · have p4040_0 := h4040c.1
                              have p4040_1 := h4040c.2.1
                              have p4040_2 := h4040c.2.2.1
                              have p4040_3 := h4040c.2.2.2
                              linarith only [hlam, p4040_0]
                            · have p4040_0 := h4040c.1
                              have p4040_1 := h4040c.2.1
                              have p4040_2 := h4040c.2.2.1
                              have p4040_3 := h4040c.2.2.2
                              linarith only [h2249, h2854, h4017, h4021, h4034, hc01, hc12, hlam, hphi, p4040_1]
                            · have p4040_0 := h4040c.1
                              have p4040_1 := h4040c.2.1
                              have p4040_2 := h4040c.2.2.1
                              have p4040_3 := h4040c.2.2.2
                              linarith only [h2854, h4017, h4021, h4034, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4040_1]
                            · have p4040_0 := h4040c.1
                              have p4040_1 := h4040c.2.1
                              have p4040_2 := h4040c.2.2.1
                              have p4040_3 := h4040c.2.2.2
                              linarith only [h2854, hlam, p4040_0]
                            · have p4040_0 := h4040c.1
                              have p4040_1 := h4040c.2.1
                              have p4040_2 := h4040c.2.2.1
                              have p4040_3 := h4040c.2.2.2
                              linarith only [h3975, h4020, hc01, hc14, hlam, hphi, p4040_1]
                            · have p4040_0 := h4040c.1
                              have p4040_1 := h4040c.2.1
                              have p4040_2 := h4040c.2.2.1
                              have p4040_3 := h4040c.2.2.2
                              linarith only [h2852, hlam, p4040_1]
                            · have p4040_0 := h4040c.1
                              have p4040_1 := h4040c.2.1
                              have p4040_2 := h4040c.2.2.1
                              have p4040_3 := h4040c.2.2.2
                              linarith only [hlam, p4040_0]
                            · have p4040_0 := h4040c.1
                              have p4040_1 := h4040c.2.1
                              have p4040_2 := h4040c.2.2.1
                              have p4040_3 := h4040c.2.2.2
                              linarith only [h3975, hlam, p4040_1]
                            · have p4040_0 := h4040c.1
                              have p4040_1 := h4040c.2.1
                              have p4040_2 := h4040c.2.2.1
                              have p4040_3 := h4040c.2.2.2
                              linarith only [h4013, hlam, p4040_1]
                            · have p4040_0 := h4040c.1
                              have p4040_1 := h4040c.2.1
                              have p4040_2 := h4040c.2.2.1
                              have p4040_3 := h4040c.2.2.2
                              linarith only [h2576, h2853, h2854, h4017, h4021, h4022, h4032, h4034, hc01, hc12, hc23, hc45, hlam, hphi, ht34, p4040_1]
                            · have p4040_0 := h4040c.1
                              have p4040_1 := h4040c.2.1
                              have p4040_2 := h4040c.2.2.1
                              have p4040_3 := h4040c.2.2.2
                              linarith only [h2853, hlam, p4040_0]
                            · have p4040_0 := h4040c.1
                              have p4040_1 := h4040c.2.1
                              have p4040_2 := h4040c.2.2.1
                              have p4040_3 := h4040c.2.2.2
                              linarith only [h2853, h2854, h4017, h4021, h4034, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4040_1]
                            · have p4040_0 := h4040c.1
                              have p4040_1 := h4040c.2.1
                              have p4040_2 := h4040c.2.2.1
                              have p4040_3 := h4040c.2.2.2
                              linarith only [hlam, p4040_0]
                            · have p4040_0 := h4040c.1
                              have p4040_1 := h4040c.2.1
                              have p4040_2 := h4040c.2.2.1
                              have p4040_3 := h4040c.2.2.2
                              linarith only [h4015, hlam, p4040_0]
                            · have p4040_0 := h4040c.1
                              have p4040_1 := h4040c.2.1
                              have p4040_2 := h4040c.2.2.1
                              have p4040_3 := h4040c.2.2.2
                              linarith only [h2854, h4017, h4021, h4034, hc01, hc12, hlam, hphi, p4040_1]
                            · have p4040_0 := h4040c.1
                              have p4040_1 := h4040c.2.1
                              have p4040_2 := h4040c.2.2.1
                              have p4040_3 := h4040c.2.2.2
                              linarith only [h2853, h2854, h4017, h4021, h4032, h4034, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4040_1]
                            · have p4040_0 := h4040c.1
                              have p4040_1 := h4040c.2.1
                              have p4040_2 := h4040c.2.2.1
                              have p4040_3 := h4040c.2.2.2
                              linarith only [h2249, h2854, h4017, h4021, h4034, hc01, hc12, hlam, hphi, p4040_1]
                            · have p4040_0 := h4040c.1
                              have p4040_1 := h4040c.2.1
                              have p4040_2 := h4040c.2.2.1
                              have p4040_3 := h4040c.2.2.2
                              linarith only [h2576, h2854, h4017, h4021, h4034, hc01, hc12, hlam, hphi, p4040_1]
                            · have p4040_0 := h4040c.1
                              have p4040_1 := h4040c.2.1
                              have p4040_2 := h4040c.2.2.1
                              have p4040_3 := h4040c.2.2.2
                              linarith only [hlam, p4040_0]
                · linarith only [h2249, h3975, h4020, h4021, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h4067 | h4067
                · linarith only [h4020, h4067, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h4069 | h4069
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4070 | h4070
                    · linarith only [h2852, h2854, h4019, h4020, h4070, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h4072 | h4072
                      · linarith only [h2853, h2854, h4019, h4067, h4070, h4072, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4074 | h4074
                        · linarith only [h2853, h2854, h4015, h4019, h4074, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                        · linarith only [h2853, h2854, h4020, h4069, h4070, h4074, hc23, hc34, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4077 | h4077
                    · linarith only [h2852, h2854, h4019, h4077, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h4079 | h4079
                      · linarith only [h2853, h2854, h4019, h4067, h4077, h4079, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4081 | h4081
                        · linarith only [h2853, h2854, h4019, h4069, h4081, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4083 | h4083
                          · linarith only [h2249, h4020, h4069, h4083, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h2249, h4020, h4083, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h4086 | h4086
              · linarith only [h2249, h3975, h4017, h4019, h4086, hc01, hc25, hlam, hphi, ht12]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h4088 | h4088
                · linarith only [h4018, h4019, h4086, h4088, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h4090 | h4090
                  · linarith only [h4018, h4019, h4090, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4092 | h4092
                    · linarith only [h0, h2852, h4019, h4086, h4092, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h4094 | h4094
                      · linarith only [h2852, h2854, h4088, h4094, hc05, hlam, hphi, ht0b, ht5b, u5ehi1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4096 | h4096
                        · linarith only [h2853, h4096, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4098 | h4098
                          · linarith only [h0, h4019, h4096, h4098, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h2249, h4086, h4098, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · linarith only [h0, h2853, h4018, hlam]
        · linarith only [h0, h2852, h4017, hlam]

set_option maxHeartbeats 5048000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_R_s0_x1_x1_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2249 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2576 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2850 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2852 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2853 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 5 (by decide) (by decide) with h2854 | h2854
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_R_s0_x1_x1_x1_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 h2249 h2576 h2850 h2852 h2853 h2854
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_R_s0_x1_x1_x1_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 h2249 h2576 h2850 h2852 h2853 h2854

set_option maxHeartbeats 5048000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_R_s0_x1_x1_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2249 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2576 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2850 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2852 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2853 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 5 (by decide) (by decide) with h4103 | h4103
  · linarith only [h2853, h4103, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h4105 | h4105
    · linarith only [h2852, h2853, h4105, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4107 | h4107
      · linarith only [h2852, h2853, h4107, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4109 | h4109
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4110 | h4110
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4111 | h4111
            · linarith only [h2853, h4109, h4111, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4113 | h4113
              · linarith only [h4103, h4111, h4113, hc02, hc24, hlam, hphi]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4115 | h4115
                · linarith only [h4105, h4109, h4115, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4117 | h4117
                  · linarith only [h4107, h4115, h4117, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4119 | h4119
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4120 | h4120
                      · linarith only [h0, h2852, h4111, h4115, h4120, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4122 | h4122
                        · linarith only [h2850, h2852, h4103, h4117, h4122, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4124 | h4124
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4125 | h4125
                            · rcases h0bigk with h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c
                              · have p4126_0 := h4126c.1
                                have p4126_1 := h4126c.2.1
                                have p4126_2 := h4126c.2.2.1
                                have p4126_3 := h4126c.2.2.2
                                linarith only [hlam, p4126_0]
                              · have p4126_0 := h4126c.1
                                have p4126_1 := h4126c.2.1
                                have p4126_2 := h4126c.2.2.1
                                have p4126_3 := h4126c.2.2.2
                                linarith only [h0, hlam, p4126_1]
                              · have p4126_0 := h4126c.1
                                have p4126_1 := h4126c.2.1
                                have p4126_2 := h4126c.2.2.1
                                have p4126_3 := h4126c.2.2.2
                                linarith only [h2249, hlam, p4126_0]
                              · have p4126_0 := h4126c.1
                                have p4126_1 := h4126c.2.1
                                have p4126_2 := h4126c.2.2.1
                                have p4126_3 := h4126c.2.2.2
                                linarith only [h2576, hlam, p4126_1]
                              · have p4126_0 := h4126c.1
                                have p4126_1 := h4126c.2.1
                                have p4126_2 := h4126c.2.2.1
                                have p4126_3 := h4126c.2.2.2
                                linarith only [h2850, hlam, p4126_1]
                              · have p4126_0 := h4126c.1
                                have p4126_1 := h4126c.2.1
                                have p4126_2 := h4126c.2.2.1
                                have p4126_3 := h4126c.2.2.2
                                linarith only [h0, h4113, h4120, h4124, hc01, hc34, hlam, hphi, ht12, ht23, p4126_1]
                              · have p4126_0 := h4126c.1
                                have p4126_1 := h4126c.2.1
                                have p4126_2 := h4126c.2.2.1
                                have p4126_3 := h4126c.2.2.2
                                linarith only [hlam, p4126_0]
                              · have p4126_0 := h4126c.1
                                have p4126_1 := h4126c.2.1
                                have p4126_2 := h4126c.2.2.1
                                have p4126_3 := h4126c.2.2.2
                                linarith only [h0, h4113, h4120, h4124, hc03, hc34, hlam, hphi, p4126_1]
                              · have p4126_0 := h4126c.1
                                have p4126_1 := h4126c.2.1
                                have p4126_2 := h4126c.2.2.1
                                have p4126_3 := h4126c.2.2.2
                                linarith only [h2853, hlam, p4126_1]
                              · have p4126_0 := h4126c.1
                                have p4126_1 := h4126c.2.1
                                have p4126_2 := h4126c.2.2.1
                                have p4126_3 := h4126c.2.2.2
                                linarith only [h4103, hlam, p4126_0]
                              · have p4126_0 := h4126c.1
                                have p4126_1 := h4126c.2.1
                                have p4126_2 := h4126c.2.2.1
                                have p4126_3 := h4126c.2.2.2
                                linarith only [h2249, h4110, h4113, h4120, h4124, hc01, hc34, hlam, hphi, ht12, ht23, p4126_1]
                              · have p4126_0 := h4126c.1
                                have p4126_1 := h4126c.2.1
                                have p4126_2 := h4126c.2.2.1
                                have p4126_3 := h4126c.2.2.2
                                linarith only [h2852, hlam, p4126_1]
                              · have p4126_0 := h4126c.1
                                have p4126_1 := h4126c.2.1
                                have p4126_2 := h4126c.2.2.1
                                have p4126_3 := h4126c.2.2.2
                                linarith only [hlam, p4126_0]
                              · have p4126_0 := h4126c.1
                                have p4126_1 := h4126c.2.1
                                have p4126_2 := h4126c.2.2.1
                                have p4126_3 := h4126c.2.2.2
                                linarith only [h4105, hlam, p4126_1]
                              · have p4126_0 := h4126c.1
                                have p4126_1 := h4126c.2.1
                                have p4126_2 := h4126c.2.2.1
                                have p4126_3 := h4126c.2.2.2
                                linarith only [h4107, hlam, p4126_1]
                              · have p4126_0 := h4126c.1
                                have p4126_1 := h4126c.2.1
                                have p4126_2 := h4126c.2.2.1
                                have p4126_3 := h4126c.2.2.2
                                rcases p4126_3 (m.d 0 1) (by simp) with h4142 | h4142
                                · linarith only [h2576, h4142, hlam]
                                · rcases p4126_3 (m.d 0 2) (by simp) with h4144 | h4144
                                  · linarith only [h2853, h4144, hlam]
                                  · linarith only [h0, h4144, hlam]
                              · have p4126_0 := h4126c.1
                                have p4126_1 := h4126c.2.1
                                have p4126_2 := h4126c.2.2.1
                                have p4126_3 := h4126c.2.2.2
                                linarith only [h2852, h2853, h4120, hc23, hc34, hlam, hphi, p4126_1]
                              · have p4126_0 := h4126c.1
                                have p4126_1 := h4126c.2.1
                                have p4126_2 := h4126c.2.2.1
                                have p4126_3 := h4126c.2.2.2
                                rcases p4126_3 (m.d 0 1) (by simp) with h4148 | h4148
                                · linarith only [h2576, h4148, hlam]
                                · rcases p4126_3 (m.d 0 2) (by simp) with h4150 | h4150
                                  · linarith only [h2853, h4150, hlam]
                                  · linarith only [h2852, h4150, hlam]
                              · have p4126_0 := h4126c.1
                                have p4126_1 := h4126c.2.1
                                have p4126_2 := h4126c.2.2.1
                                have p4126_3 := h4126c.2.2.2
                                linarith only [hlam, p4126_0]
                              · have p4126_0 := h4126c.1
                                have p4126_1 := h4126c.2.1
                                have p4126_2 := h4126c.2.2.1
                                have p4126_3 := h4126c.2.2.2
                                linarith only [h2576, h4109, h4111, h4120, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4126_1, u5ehi4]
                              · have p4126_0 := h4126c.1
                                have p4126_1 := h4126c.2.1
                                have p4126_2 := h4126c.2.2.1
                                have p4126_3 := h4126c.2.2.2
                                rcases p4126_3 (m.d 0 1) (by simp) with h4155 | h4155
                                · linarith only [h2850, h4155, hlam]
                                · rcases p4126_3 (m.d 0 2) (by simp) with h4157 | h4157
                                  · linarith only [h4103, h4157, hlam]
                                  · linarith only [h0, h4157, hlam]
                              · have p4126_0 := h4126c.1
                                have p4126_1 := h4126c.2.1
                                have p4126_2 := h4126c.2.2.1
                                have p4126_3 := h4126c.2.2.2
                                linarith only [h2850, h2852, h4113, h4122, hc23, hc35, hlam, hphi, p4126_1]
                              · have p4126_0 := h4126c.1
                                have p4126_1 := h4126c.2.1
                                have p4126_2 := h4126c.2.2.1
                                have p4126_3 := h4126c.2.2.2
                                rcases p4126_3 (m.d 0 1) (by simp) with h4161 | h4161
                                · linarith only [h2850, h4161, hlam]
                                · rcases p4126_3 (m.d 0 2) (by simp) with h4163 | h4163
                                  · linarith only [h4103, h4163, hlam]
                                  · linarith only [h2852, h4163, hlam]
                              · have p4126_0 := h4126c.1
                                have p4126_1 := h4126c.2.1
                                have p4126_2 := h4126c.2.2.1
                                have p4126_3 := h4126c.2.2.2
                                linarith only [h4109, hlam, p4126_1]
                              · have p4126_0 := h4126c.1
                                have p4126_1 := h4126c.2.1
                                have p4126_2 := h4126c.2.2.1
                                have p4126_3 := h4126c.2.2.2
                                linarith only [hlam, p4126_0]
                            · linarith only [h2852, h2853, h4120, h4125, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h2576, h4109, h4111, h4124, hlam]
                    · linarith only [h2576, h4109, h4119, hlam]
          · linarith only [h0, h2852, h4110, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4172 | h4172
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4173 | h4173
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4174 | h4174
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4175 | h4175
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4176 | h4176
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4177 | h4177
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4178 | h4178
                      · linarith only [h2249, h2852, h2853, h4105, h4109, h4175, h4177, h4178, hc01, hc13, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4180 | h4180
                        · linarith only [h2852, h2853, h4107, h4109, h4172, h4175, h4177, h4180, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4182 | h4182
                          · linarith only [h2852, h2853, h4109, h4178, h4182, hc23, hc34, hlam, hphi]
                          · linarith only [h2852, h2853, h4172, h4175, h4177, h4182, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h2852, h2853, h4173, h4177, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h2249, h4105, h4175, h4176, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4187 | h4187
                  · linarith only [h4175, h4187, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4189 | h4189
                    · linarith only [h2852, h2853, h4109, h4175, h4189, hc23, hc34, hlam, hphi]
                    · linarith only [h2852, h2853, h4173, h4189, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h2852, h2853, h4173, h4174, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4193 | h4193
              · linarith only [h4173, h4193, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4195 | h4195
                · linarith only [h2249, h4105, h4172, h4173, h4195, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4197 | h4197
                  · linarith only [h4195, h4197, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4199 | h4199
                    · linarith only [h2852, h2853, h4109, h4195, h4199, hc23, hc34, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4201 | h4201
                      · linarith only [h0, h2852, h4173, h4199, h4201, hc34, hc45, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4203 | h4203
                        · linarith only [h0, h2852, h4173, h4197, h4199, h4203, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4205 | h4205
                          · linarith only [h2249, h4172, h4173, h4199, h4201, h4205, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h2852, h2853, h4205, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h2852, h2853, h4172, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 5048000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_R_s0_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2249 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2576 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2850 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2852 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 4 (by decide) (by decide) with h2853 | h2853
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_R_s0_x1_x1_x1_x0_x0 m hb0 hb2 hb3 hb5 hg0 h2249 h2576 h2850 h2852 h2853
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_R_s0_x1_x1_x1_x0_x1 m hb0 hb2 hb3 hb5 hg0 h2249 h2576 h2850 h2852 h2853

end R2N4
