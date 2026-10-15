import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_28S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6104000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1414 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1728 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg1965 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg1966 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg1967 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1968 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1969 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1414 := hg1414
  have h1728 := hg1728
  have h1965 := hg1965
  have h1966 := hg1966
  have h1967 := hg1967
  rcases m.htr 0 4 5 (by decide) (by decide) with h3682 | h3682
  · linarith only [h1968, h1969, h3682, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h3684 | h3684
    · rcases m.htr 1 2 4 (by decide) (by decide) with h3685 | h3685
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3686 | h3686
        · rcases m.htr 1 3 4 (by decide) (by decide) with h3687 | h3687
          · rcases m.htr 1 3 5 (by decide) (by decide) with h3688 | h3688
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3689 | h3689
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3690 | h3690
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3691 | h3691
                  · linarith only [h0, h1414, h1965, h1969, h3691, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3693 | h3693
                    · linarith only [h1965, h1969, h3682, h3688, h3690, h3693, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3695 | h3695
                      · linarith only [h1965, h1966, h1969, h3682, h3684, h3688, h3690, h3695, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · rcases h0bigk with h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c | h3697c
                        · have p3697_0 := h3697c.1
                          have p3697_1 := h3697c.2.1
                          have p3697_2 := h3697c.2.2.1
                          have p3697_3 := h3697c.2.2.2
                          linarith only [hlam, p3697_0]
                        · have p3697_0 := h3697c.1
                          have p3697_1 := h3697c.2.1
                          have p3697_2 := h3697c.2.2.1
                          have p3697_3 := h3697c.2.2.2
                          linarith only [h0, hlam, p3697_1]
                        · have p3697_0 := h3697c.1
                          have p3697_1 := h3697c.2.1
                          have p3697_2 := h3697c.2.2.1
                          have p3697_3 := h3697c.2.2.2
                          linarith only [h1414, hlam, p3697_0]
                        · have p3697_0 := h3697c.1
                          have p3697_1 := h3697c.2.1
                          have p3697_2 := h3697c.2.2.1
                          have p3697_3 := h3697c.2.2.2
                          linarith only [h0, h1966, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3697_1, u2ehi3]
                        · have p3697_0 := h3697c.1
                          have p3697_1 := h3697c.2.1
                          have p3697_2 := h3697c.2.2.1
                          have p3697_3 := h3697c.2.2.2
                          linarith only [h1728, hlam, p3697_1]
                        · have p3697_0 := h3697c.1
                          have p3697_1 := h3697c.2.1
                          have p3697_2 := h3697c.2.2.1
                          have p3697_3 := h3697c.2.2.2
                          rcases p3697_3 (m.d 0 1) (by simp) with h3703 | h3703
                          · linarith only [h0, h3703, hlam]
                          · rcases p3697_3 (m.d 0 2) (by simp) with h3705 | h3705
                            · rcases p3697_3 (m.d 0 3) (by simp) with h3706 | h3706
                              · linarith only [h1965, h3706, hlam]
                              · linarith only [h1414, h3706, hlam]
                            · linarith only [h0, h3705, hlam]
                        · have p3697_0 := h3697c.1
                          have p3697_1 := h3697c.2.1
                          have p3697_2 := h3697c.2.2.1
                          have p3697_3 := h3697c.2.2.2
                          linarith only [hlam, p3697_0]
                        · have p3697_0 := h3697c.1
                          have p3697_1 := h3697c.2.1
                          have p3697_2 := h3697c.2.2.1
                          have p3697_3 := h3697c.2.2.2
                          rcases p3697_3 (m.d 0 1) (by simp) with h3711 | h3711
                          · linarith only [h0, h3711, hlam]
                          · rcases p3697_3 (m.d 0 2) (by simp) with h3713 | h3713
                            · rcases p3697_3 (m.d 0 3) (by simp) with h3714 | h3714
                              · linarith only [h1965, h3714, hlam]
                              · rcases p3697_3 (m.d 0 4) (by simp) with h3716 | h3716
                                · linarith only [h1966, h3716, hlam]
                                · rcases p3697_3 (m.d 0 5) (by simp) with h3718 | h3718
                                  · linarith only [h1967, h3718, hlam]
                                  · linarith only [h1969, h3718, hlam]
                            · linarith only [h1965, h3713, hlam]
                        · have p3697_0 := h3697c.1
                          have p3697_1 := h3697c.2.1
                          have p3697_2 := h3697c.2.2.1
                          have p3697_3 := h3697c.2.2.2
                          rcases p3697_3 (m.d 0 1) (by simp) with h3722 | h3722
                          · linarith only [h0, h3722, hlam]
                          · rcases p3697_3 (m.d 0 2) (by simp) with h3724 | h3724
                            · rcases p3697_3 (m.d 0 3) (by simp) with h3725 | h3725
                              · linarith only [h1965, h3725, hlam]
                              · linarith only [h1968, h3725, hlam]
                            · linarith only [h1966, h3724, hlam]
                        · have p3697_0 := h3697c.1
                          have p3697_1 := h3697c.2.1
                          have p3697_2 := h3697c.2.2.1
                          have p3697_3 := h3697c.2.2.2
                          rcases p3697_3 (m.d 0 1) (by simp) with h3729 | h3729
                          · linarith only [h0, h3729, hlam]
                          · rcases p3697_3 (m.d 0 2) (by simp) with h3731 | h3731
                            · rcases p3697_3 (m.d 0 3) (by simp) with h3732 | h3732
                              · linarith only [h1965, h3732, hlam]
                              · rcases p3697_3 (m.d 0 4) (by simp) with h3734 | h3734
                                · linarith only [h1966, h3734, hlam]
                                · rcases p3697_3 (m.d 0 5) (by simp) with h3736 | h3736
                                  · linarith only [h1967, h3736, hlam]
                                  · rcases h0emax with h3738 | h3738 | h3738 | h3738 | h3738
                                    · rcases h5bigk with h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c
                                      · have p3739_0 := h3739c.1
                                        have p3739_1 := h3739c.2.1
                                        have p3739_2 := h3739c.2.2.1
                                        have p3739_3 := h3739c.2.2.2
                                        linarith only [hlam, p3739_0]
                                      · have p3739_0 := h3739c.1
                                        have p3739_1 := h3739c.2.1
                                        have p3739_2 := h3739c.2.2.1
                                        have p3739_3 := h3739c.2.2.2
                                        linarith only [h1728, hlam, p3739_1]
                                      · have p3739_0 := h3739c.1
                                        have p3739_1 := h3739c.2.1
                                        have p3739_2 := h3739c.2.2.1
                                        have p3739_3 := h3739c.2.2.2
                                        linarith only [hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3739_1, u2ehi4]
                                      · have p3739_0 := h3739c.1
                                        have p3739_1 := h3739c.2.1
                                        have p3739_2 := h3739c.2.2.1
                                        have p3739_3 := h3739c.2.2.2
                                        linarith only [h1969, hlam, p3739_1]
                                      · have p3739_0 := h3739c.1
                                        have p3739_1 := h3739c.2.1
                                        have p3739_2 := h3739c.2.2.1
                                        have p3739_3 := h3739c.2.2.2
                                        linarith only [h3682, hlam, p3739_1]
                                      · have p3739_0 := h3739c.1
                                        have p3739_1 := h3739c.2.1
                                        have p3739_2 := h3739c.2.2.1
                                        have p3739_3 := h3739c.2.2.2
                                        linarith only [h1728, hc01, hc15, hlam, hphi, p3739_1]
                                      · have p3739_0 := h3739c.1
                                        have p3739_1 := h3739c.2.1
                                        have p3739_2 := h3739c.2.2.1
                                        have p3739_3 := h3739c.2.2.2
                                        linarith only [hlam, p3739_0]
                                      · have p3739_0 := h3739c.1
                                        have p3739_1 := h3739c.2.1
                                        have p3739_2 := h3739c.2.2.1
                                        have p3739_3 := h3739c.2.2.2
                                        linarith only [h3686, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3739_1, u2ehi4]
                                      · have p3739_0 := h3739c.1
                                        have p3739_1 := h3739c.2.1
                                        have p3739_2 := h3739c.2.2.1
                                        have p3739_3 := h3739c.2.2.2
                                        linarith only [h1969, h3684, h3688, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3739_1]
                                      · have p3739_0 := h3739c.1
                                        have p3739_1 := h3739c.2.1
                                        have p3739_2 := h3739c.2.2.1
                                        have p3739_3 := h3739c.2.2.2
                                        linarith only [h1966, h3682, h3684, h3687, h3689, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3739_1, u2ehi3]
                                      · have p3739_0 := h3739c.1
                                        have p3739_1 := h3739c.2.1
                                        have p3739_2 := h3739c.2.2.1
                                        have p3739_3 := h3739c.2.2.2
                                        linarith only [h1967, hlam, p3739_1]
                                      · have p3739_0 := h3739c.1
                                        have p3739_1 := h3739c.2.1
                                        have p3739_2 := h3739c.2.2.1
                                        have p3739_3 := h3739c.2.2.2
                                        linarith only [h3686, hlam, p3739_1]
                                      · have p3739_0 := h3739c.1
                                        have p3739_1 := h3739c.2.1
                                        have p3739_2 := h3739c.2.2.1
                                        have p3739_3 := h3739c.2.2.2
                                        linarith only [hlam, p3739_0]
                                      · have p3739_0 := h3739c.1
                                        have p3739_1 := h3739c.2.1
                                        have p3739_2 := h3739c.2.2.1
                                        have p3739_3 := h3739c.2.2.2
                                        linarith only [h3691, hlam, p3739_1]
                                      · have p3739_0 := h3739c.1
                                        have p3739_1 := h3739c.2.1
                                        have p3739_2 := h3739c.2.2.1
                                        have p3739_3 := h3739c.2.2.2
                                        linarith only [h3693, hlam, p3739_1]
                                      · have p3739_0 := h3739c.1
                                        have p3739_1 := h3739c.2.1
                                        have p3739_2 := h3739c.2.2.1
                                        have p3739_3 := h3739c.2.2.2
                                        linarith only [h1966, h1968, h1969, hc35, hlam, hphi, ht23, p3739_1, u2ehi3]
                                      · have p3739_0 := h3739c.1
                                        have p3739_1 := h3739c.2.1
                                        have p3739_2 := h3739c.2.2.1
                                        have p3739_3 := h3739c.2.2.2
                                        linarith only [h3688, hlam, p3739_0]
                                      · have p3739_0 := h3739c.1
                                        have p3739_1 := h3739c.2.1
                                        have p3739_2 := h3739c.2.2.1
                                        have p3739_3 := h3739c.2.2.2
                                        linarith only [h3684, h3688, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3739_1, u2ehi4]
                                      · have p3739_0 := h3739c.1
                                        have p3739_1 := h3739c.2.1
                                        have p3739_2 := h3739c.2.2.1
                                        have p3739_3 := h3739c.2.2.2
                                        linarith only [hlam, p3739_0]
                                      · have p3739_0 := h3739c.1
                                        have p3739_1 := h3739c.2.1
                                        have p3739_2 := h3739c.2.2.1
                                        have p3739_3 := h3739c.2.2.2
                                        linarith only [h3695, hlam, p3739_1]
                                      · have p3739_0 := h3739c.1
                                        have p3739_1 := h3739c.2.1
                                        have p3739_2 := h3739c.2.2.1
                                        have p3739_3 := h3739c.2.2.2
                                        linarith only [h1966, h1968, h1969, hc45, hlam, hphi, ht23, ht34, p3739_1, u2ehi3]
                                      · have p3739_0 := h3739c.1
                                        have p3739_1 := h3739c.2.1
                                        have p3739_2 := h3739c.2.2.1
                                        have p3739_3 := h3739c.2.2.2
                                        linarith only [h3689, hlam, p3739_0]
                                      · have p3739_0 := h3739c.1
                                        have p3739_1 := h3739c.2.1
                                        have p3739_2 := h3739c.2.2.1
                                        have p3739_3 := h3739c.2.2.2
                                        linarith only [h3684, h3687, h3689, h3690, h3691, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3739_1, u2ehi3]
                                      · have p3739_0 := h3739c.1
                                        have p3739_1 := h3739c.2.1
                                        have p3739_2 := h3739c.2.2.1
                                        have p3739_3 := h3739c.2.2.2
                                        linarith only [h3684, h3687, h3689, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p3739_1]
                                      · have p3739_0 := h3739c.1
                                        have p3739_1 := h3739c.2.1
                                        have p3739_2 := h3739c.2.2.1
                                        have p3739_3 := h3739c.2.2.2
                                        linarith only [hlam, p3739_0]
                                    · linarith only [h1965, h3690, h3738, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                    · rcases h5bigk with h3766c | h3766c | h3766c | h3766c | h3766c | h3766c | h3766c | h3766c | h3766c | h3766c | h3766c | h3766c | h3766c | h3766c | h3766c | h3766c | h3766c | h3766c | h3766c | h3766c | h3766c | h3766c | h3766c | h3766c | h3766c
                                      · have p3766_0 := h3766c.1
                                        have p3766_1 := h3766c.2.1
                                        have p3766_2 := h3766c.2.2.1
                                        have p3766_3 := h3766c.2.2.2
                                        linarith only [hlam, p3766_0]
                                      · have p3766_0 := h3766c.1
                                        have p3766_1 := h3766c.2.1
                                        have p3766_2 := h3766c.2.2.1
                                        have p3766_3 := h3766c.2.2.2
                                        linarith only [h1728, hlam, p3766_1]
                                      · have p3766_0 := h3766c.1
                                        have p3766_1 := h3766c.2.1
                                        have p3766_2 := h3766c.2.2.1
                                        have p3766_3 := h3766c.2.2.2
                                        linarith only [h3690, h3691, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3697_1, p3766_1, u2ehi3]
                                      · have p3766_0 := h3766c.1
                                        have p3766_1 := h3766c.2.1
                                        have p3766_2 := h3766c.2.2.1
                                        have p3766_3 := h3766c.2.2.2
                                        linarith only [h1969, hlam, p3766_1]
                                      · have p3766_0 := h3766c.1
                                        have p3766_1 := h3766c.2.1
                                        have p3766_2 := h3766c.2.2.1
                                        have p3766_3 := h3766c.2.2.2
                                        linarith only [h3682, hlam, p3766_1]
                                      · have p3766_0 := h3766c.1
                                        have p3766_1 := h3766c.2.1
                                        have p3766_2 := h3766c.2.2.1
                                        have p3766_3 := h3766c.2.2.2
                                        linarith only [h1728, h3684, h3687, h3689, hc01, hc12, hlam, hphi, p3766_1]
                                      · have p3766_0 := h3766c.1
                                        have p3766_1 := h3766c.2.1
                                        have p3766_2 := h3766c.2.2.1
                                        have p3766_3 := h3766c.2.2.2
                                        linarith only [hlam, p3766_0]
                                      · have p3766_0 := h3766c.1
                                        have p3766_1 := h3766c.2.1
                                        have p3766_2 := h3766c.2.2.1
                                        have p3766_3 := h3766c.2.2.2
                                        linarith only [h3684, h3687, h3689, h3690, h3691, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3766_1, u2ehi3]
                                      · have p3766_0 := h3766c.1
                                        have p3766_1 := h3766c.2.1
                                        have p3766_2 := h3766c.2.2.1
                                        have p3766_3 := h3766c.2.2.2
                                        linarith only [h1966, h1968, h1969, h3684, h3687, h3689, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3766_1, u2ehi3]
                                      · have p3766_0 := h3766c.1
                                        have p3766_1 := h3766c.2.1
                                        have p3766_2 := h3766c.2.2.1
                                        have p3766_3 := h3766c.2.2.2
                                        linarith only [h1966, h3682, h3684, h3687, h3689, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3766_1, u2ehi3]
                                      · have p3766_0 := h3766c.1
                                        have p3766_1 := h3766c.2.1
                                        have p3766_2 := h3766c.2.2.1
                                        have p3766_3 := h3766c.2.2.2
                                        linarith only [h1967, hlam, p3766_1]
                                      · have p3766_0 := h3766c.1
                                        have p3766_1 := h3766c.2.1
                                        have p3766_2 := h3766c.2.2.1
                                        have p3766_3 := h3766c.2.2.2
                                        linarith only [h3686, hlam, p3766_1]
                                      · have p3766_0 := h3766c.1
                                        have p3766_1 := h3766c.2.1
                                        have p3766_2 := h3766c.2.2.1
                                        have p3766_3 := h3766c.2.2.2
                                        linarith only [hlam, p3766_0]
                                      · have p3766_0 := h3766c.1
                                        have p3766_1 := h3766c.2.1
                                        have p3766_2 := h3766c.2.2.1
                                        have p3766_3 := h3766c.2.2.2
                                        linarith only [h3691, hlam, p3766_1]
                                      · have p3766_0 := h3766c.1
                                        have p3766_1 := h3766c.2.1
                                        have p3766_2 := h3766c.2.2.1
                                        have p3766_3 := h3766c.2.2.2
                                        linarith only [h3693, hlam, p3766_1]
                                      · have p3766_0 := h3766c.1
                                        have p3766_1 := h3766c.2.1
                                        have p3766_2 := h3766c.2.2.1
                                        have p3766_3 := h3766c.2.2.2
                                        linarith only [h1967, h3690, h3691, hc35, hlam, hphi, ht23, p3766_1, u2ehi3]
                                      · have p3766_0 := h3766c.1
                                        have p3766_1 := h3766c.2.1
                                        have p3766_2 := h3766c.2.2.1
                                        have p3766_3 := h3766c.2.2.2
                                        linarith only [h3688, hlam, p3766_0]
                                      · have p3766_0 := h3766c.1
                                        have p3766_1 := h3766c.2.1
                                        have p3766_2 := h3766c.2.2.1
                                        have p3766_3 := h3766c.2.2.2
                                        linarith only [h3684, h3688, h3690, h3691, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3766_1, u2ehi3]
                                      · have p3766_0 := h3766c.1
                                        have p3766_1 := h3766c.2.1
                                        have p3766_2 := h3766c.2.2.1
                                        have p3766_3 := h3766c.2.2.2
                                        linarith only [hlam, p3766_0]
                                      · have p3766_0 := h3766c.1
                                        have p3766_1 := h3766c.2.1
                                        have p3766_2 := h3766c.2.2.1
                                        have p3766_3 := h3766c.2.2.2
                                        linarith only [h3695, hlam, p3766_1]
                                      · have p3766_0 := h3766c.1
                                        have p3766_1 := h3766c.2.1
                                        have p3766_2 := h3766c.2.2.1
                                        have p3766_3 := h3766c.2.2.2
                                        linarith only [h1967, h3690, h3691, hc45, hlam, hphi, ht23, ht34, p3766_1, u2ehi3]
                                      · have p3766_0 := h3766c.1
                                        have p3766_1 := h3766c.2.1
                                        have p3766_2 := h3766c.2.2.1
                                        have p3766_3 := h3766c.2.2.2
                                        linarith only [h3689, hlam, p3766_0]
                                      · have p3766_0 := h3766c.1
                                        have p3766_1 := h3766c.2.1
                                        have p3766_2 := h3766c.2.2.1
                                        have p3766_3 := h3766c.2.2.2
                                        linarith only [h3684, h3687, h3689, h3690, h3691, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3766_1, u2ehi3]
                                      · have p3766_0 := h3766c.1
                                        have p3766_1 := h3766c.2.1
                                        have p3766_2 := h3766c.2.2.1
                                        have p3766_3 := h3766c.2.2.2
                                        linarith only [h3684, h3687, h3689, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p3766_1]
                                      · have p3766_0 := h3766c.1
                                        have p3766_1 := h3766c.2.1
                                        have p3766_2 := h3766c.2.2.1
                                        have p3766_3 := h3766c.2.2.2
                                        linarith only [hlam, p3766_0]
                                    · rcases h5bigk with h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c | h3792c
                                      · have p3792_0 := h3792c.1
                                        have p3792_1 := h3792c.2.1
                                        have p3792_2 := h3792c.2.2.1
                                        have p3792_3 := h3792c.2.2.2
                                        linarith only [hlam, p3792_0]
                                      · have p3792_0 := h3792c.1
                                        have p3792_1 := h3792c.2.1
                                        have p3792_2 := h3792c.2.2.1
                                        have p3792_3 := h3792c.2.2.2
                                        linarith only [h1728, hlam, p3792_1]
                                      · have p3792_0 := h3792c.1
                                        have p3792_1 := h3792c.2.1
                                        have p3792_2 := h3792c.2.2.1
                                        have p3792_3 := h3792c.2.2.2
                                        linarith only [h3690, h3691, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3792_1, u2ehi3]
                                      · have p3792_0 := h3792c.1
                                        have p3792_1 := h3792c.2.1
                                        have p3792_2 := h3792c.2.2.1
                                        have p3792_3 := h3792c.2.2.2
                                        linarith only [h1969, hlam, p3792_1]
                                      · have p3792_0 := h3792c.1
                                        have p3792_1 := h3792c.2.1
                                        have p3792_2 := h3792c.2.2.1
                                        have p3792_3 := h3792c.2.2.2
                                        linarith only [h3682, hlam, p3792_1]
                                      · have p3792_0 := h3792c.1
                                        have p3792_1 := h3792c.2.1
                                        have p3792_2 := h3792c.2.2.1
                                        have p3792_3 := h3792c.2.2.2
                                        linarith only [h1728, h3684, h3687, h3689, hc01, hc12, hlam, hphi, p3792_1]
                                      · have p3792_0 := h3792c.1
                                        have p3792_1 := h3792c.2.1
                                        have p3792_2 := h3792c.2.2.1
                                        have p3792_3 := h3792c.2.2.2
                                        linarith only [hlam, p3792_0]
                                      · have p3792_0 := h3792c.1
                                        have p3792_1 := h3792c.2.1
                                        have p3792_2 := h3792c.2.2.1
                                        have p3792_3 := h3792c.2.2.2
                                        linarith only [h3684, h3687, h3689, h3690, h3691, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3792_1, u2ehi3]
                                      · have p3792_0 := h3792c.1
                                        have p3792_1 := h3792c.2.1
                                        have p3792_2 := h3792c.2.2.1
                                        have p3792_3 := h3792c.2.2.2
                                        linarith only [h1966, h1968, h1969, h3684, h3687, h3689, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3792_1, u2ehi3]
                                      · have p3792_0 := h3792c.1
                                        have p3792_1 := h3792c.2.1
                                        have p3792_2 := h3792c.2.2.1
                                        have p3792_3 := h3792c.2.2.2
                                        linarith only [h1966, h3682, h3684, h3687, h3689, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3792_1, u2ehi3]
                                      · have p3792_0 := h3792c.1
                                        have p3792_1 := h3792c.2.1
                                        have p3792_2 := h3792c.2.2.1
                                        have p3792_3 := h3792c.2.2.2
                                        linarith only [h1967, hlam, p3792_1]
                                      · have p3792_0 := h3792c.1
                                        have p3792_1 := h3792c.2.1
                                        have p3792_2 := h3792c.2.2.1
                                        have p3792_3 := h3792c.2.2.2
                                        linarith only [h3686, hlam, p3792_1]
                                      · have p3792_0 := h3792c.1
                                        have p3792_1 := h3792c.2.1
                                        have p3792_2 := h3792c.2.2.1
                                        have p3792_3 := h3792c.2.2.2
                                        linarith only [hlam, p3792_0]
                                      · have p3792_0 := h3792c.1
                                        have p3792_1 := h3792c.2.1
                                        have p3792_2 := h3792c.2.2.1
                                        have p3792_3 := h3792c.2.2.2
                                        linarith only [h3691, hlam, p3792_1]
                                      · have p3792_0 := h3792c.1
                                        have p3792_1 := h3792c.2.1
                                        have p3792_2 := h3792c.2.2.1
                                        have p3792_3 := h3792c.2.2.2
                                        linarith only [h3693, hlam, p3792_1]
                                      · have p3792_0 := h3792c.1
                                        have p3792_1 := h3792c.2.1
                                        have p3792_2 := h3792c.2.2.1
                                        have p3792_3 := h3792c.2.2.2
                                        linarith only [h1967, h3690, h3691, hc35, hlam, hphi, ht23, p3792_1, u2ehi3]
                                      · have p3792_0 := h3792c.1
                                        have p3792_1 := h3792c.2.1
                                        have p3792_2 := h3792c.2.2.1
                                        have p3792_3 := h3792c.2.2.2
                                        linarith only [h3688, hlam, p3792_0]
                                      · have p3792_0 := h3792c.1
                                        have p3792_1 := h3792c.2.1
                                        have p3792_2 := h3792c.2.2.1
                                        have p3792_3 := h3792c.2.2.2
                                        linarith only [h3684, h3688, h3690, h3691, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3792_1, u2ehi3]
                                      · have p3792_0 := h3792c.1
                                        have p3792_1 := h3792c.2.1
                                        have p3792_2 := h3792c.2.2.1
                                        have p3792_3 := h3792c.2.2.2
                                        linarith only [hlam, p3792_0]
                                      · have p3792_0 := h3792c.1
                                        have p3792_1 := h3792c.2.1
                                        have p3792_2 := h3792c.2.2.1
                                        have p3792_3 := h3792c.2.2.2
                                        linarith only [h3695, hlam, p3792_1]
                                      · have p3792_0 := h3792c.1
                                        have p3792_1 := h3792c.2.1
                                        have p3792_2 := h3792c.2.2.1
                                        have p3792_3 := h3792c.2.2.2
                                        linarith only [h1967, h3690, h3691, hc45, hlam, hphi, ht23, ht34, p3792_1, u2ehi3]
                                      · have p3792_0 := h3792c.1
                                        have p3792_1 := h3792c.2.1
                                        have p3792_2 := h3792c.2.2.1
                                        have p3792_3 := h3792c.2.2.2
                                        linarith only [h3689, hlam, p3792_0]
                                      · have p3792_0 := h3792c.1
                                        have p3792_1 := h3792c.2.1
                                        have p3792_2 := h3792c.2.2.1
                                        have p3792_3 := h3792c.2.2.2
                                        linarith only [h3684, h3687, h3689, h3690, h3691, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3792_1, u2ehi3]
                                      · have p3792_0 := h3792c.1
                                        have p3792_1 := h3792c.2.1
                                        have p3792_2 := h3792c.2.2.1
                                        have p3792_3 := h3792c.2.2.2
                                        linarith only [h3684, h3687, h3689, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p3792_1]
                                      · have p3792_0 := h3792c.1
                                        have p3792_1 := h3792c.2.1
                                        have p3792_2 := h3792c.2.2.1
                                        have p3792_3 := h3792c.2.2.2
                                        linarith only [hlam, p3792_0]
                                    · rcases h5bigk with h3818c | h3818c | h3818c | h3818c | h3818c | h3818c | h3818c | h3818c | h3818c | h3818c | h3818c | h3818c | h3818c | h3818c | h3818c | h3818c | h3818c | h3818c | h3818c | h3818c | h3818c | h3818c | h3818c | h3818c | h3818c
                                      · have p3818_0 := h3818c.1
                                        have p3818_1 := h3818c.2.1
                                        have p3818_2 := h3818c.2.2.1
                                        have p3818_3 := h3818c.2.2.2
                                        linarith only [hlam, p3818_0]
                                      · have p3818_0 := h3818c.1
                                        have p3818_1 := h3818c.2.1
                                        have p3818_2 := h3818c.2.2.1
                                        have p3818_3 := h3818c.2.2.2
                                        linarith only [h1728, hlam, p3818_1]
                                      · have p3818_0 := h3818c.1
                                        have p3818_1 := h3818c.2.1
                                        have p3818_2 := h3818c.2.2.1
                                        have p3818_3 := h3818c.2.2.2
                                        linarith only [h3690, h3691, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3818_1, u2ehi3]
                                      · have p3818_0 := h3818c.1
                                        have p3818_1 := h3818c.2.1
                                        have p3818_2 := h3818c.2.2.1
                                        have p3818_3 := h3818c.2.2.2
                                        linarith only [h1969, hlam, p3818_1]
                                      · have p3818_0 := h3818c.1
                                        have p3818_1 := h3818c.2.1
                                        have p3818_2 := h3818c.2.2.1
                                        have p3818_3 := h3818c.2.2.2
                                        linarith only [h3682, hlam, p3818_1]
                                      · have p3818_0 := h3818c.1
                                        have p3818_1 := h3818c.2.1
                                        have p3818_2 := h3818c.2.2.1
                                        have p3818_3 := h3818c.2.2.2
                                        linarith only [h1728, h3684, h3687, h3689, hc01, hc12, hlam, hphi, p3818_1]
                                      · have p3818_0 := h3818c.1
                                        have p3818_1 := h3818c.2.1
                                        have p3818_2 := h3818c.2.2.1
                                        have p3818_3 := h3818c.2.2.2
                                        linarith only [hlam, p3818_0]
                                      · have p3818_0 := h3818c.1
                                        have p3818_1 := h3818c.2.1
                                        have p3818_2 := h3818c.2.2.1
                                        have p3818_3 := h3818c.2.2.2
                                        linarith only [h3684, h3687, h3689, h3690, h3691, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3818_1, u2ehi3]
                                      · have p3818_0 := h3818c.1
                                        have p3818_1 := h3818c.2.1
                                        have p3818_2 := h3818c.2.2.1
                                        have p3818_3 := h3818c.2.2.2
                                        linarith only [h1966, h1968, h1969, h3684, h3687, h3689, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3818_1, u2ehi3]
                                      · have p3818_0 := h3818c.1
                                        have p3818_1 := h3818c.2.1
                                        have p3818_2 := h3818c.2.2.1
                                        have p3818_3 := h3818c.2.2.2
                                        linarith only [h1966, h3682, h3684, h3687, h3689, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3818_1, u2ehi3]
                                      · have p3818_0 := h3818c.1
                                        have p3818_1 := h3818c.2.1
                                        have p3818_2 := h3818c.2.2.1
                                        have p3818_3 := h3818c.2.2.2
                                        linarith only [h1967, hlam, p3818_1]
                                      · have p3818_0 := h3818c.1
                                        have p3818_1 := h3818c.2.1
                                        have p3818_2 := h3818c.2.2.1
                                        have p3818_3 := h3818c.2.2.2
                                        linarith only [h3686, hlam, p3818_1]
                                      · have p3818_0 := h3818c.1
                                        have p3818_1 := h3818c.2.1
                                        have p3818_2 := h3818c.2.2.1
                                        have p3818_3 := h3818c.2.2.2
                                        linarith only [hlam, p3818_0]
                                      · have p3818_0 := h3818c.1
                                        have p3818_1 := h3818c.2.1
                                        have p3818_2 := h3818c.2.2.1
                                        have p3818_3 := h3818c.2.2.2
                                        linarith only [h3691, hlam, p3818_1]
                                      · have p3818_0 := h3818c.1
                                        have p3818_1 := h3818c.2.1
                                        have p3818_2 := h3818c.2.2.1
                                        have p3818_3 := h3818c.2.2.2
                                        linarith only [h3693, hlam, p3818_1]
                                      · have p3818_0 := h3818c.1
                                        have p3818_1 := h3818c.2.1
                                        have p3818_2 := h3818c.2.2.1
                                        have p3818_3 := h3818c.2.2.2
                                        linarith only [h1967, h3690, h3691, hc35, hlam, hphi, ht23, p3818_1, u2ehi3]
                                      · have p3818_0 := h3818c.1
                                        have p3818_1 := h3818c.2.1
                                        have p3818_2 := h3818c.2.2.1
                                        have p3818_3 := h3818c.2.2.2
                                        linarith only [h3688, hlam, p3818_0]
                                      · have p3818_0 := h3818c.1
                                        have p3818_1 := h3818c.2.1
                                        have p3818_2 := h3818c.2.2.1
                                        have p3818_3 := h3818c.2.2.2
                                        linarith only [h3684, h3688, h3690, h3691, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3818_1, u2ehi3]
                                      · have p3818_0 := h3818c.1
                                        have p3818_1 := h3818c.2.1
                                        have p3818_2 := h3818c.2.2.1
                                        have p3818_3 := h3818c.2.2.2
                                        linarith only [hlam, p3818_0]
                                      · have p3818_0 := h3818c.1
                                        have p3818_1 := h3818c.2.1
                                        have p3818_2 := h3818c.2.2.1
                                        have p3818_3 := h3818c.2.2.2
                                        linarith only [h3695, hlam, p3818_1]
                                      · have p3818_0 := h3818c.1
                                        have p3818_1 := h3818c.2.1
                                        have p3818_2 := h3818c.2.2.1
                                        have p3818_3 := h3818c.2.2.2
                                        linarith only [h1967, h3690, h3691, hc45, hlam, hphi, ht23, ht34, p3818_1, u2ehi3]
                                      · have p3818_0 := h3818c.1
                                        have p3818_1 := h3818c.2.1
                                        have p3818_2 := h3818c.2.2.1
                                        have p3818_3 := h3818c.2.2.2
                                        linarith only [h3689, hlam, p3818_0]
                                      · have p3818_0 := h3818c.1
                                        have p3818_1 := h3818c.2.1
                                        have p3818_2 := h3818c.2.2.1
                                        have p3818_3 := h3818c.2.2.2
                                        linarith only [h3684, h3687, h3689, h3690, h3691, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3818_1, u2ehi3]
                                      · have p3818_0 := h3818c.1
                                        have p3818_1 := h3818c.2.1
                                        have p3818_2 := h3818c.2.2.1
                                        have p3818_3 := h3818c.2.2.2
                                        linarith only [h3684, h3687, h3689, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p3818_1]
                                      · have p3818_0 := h3818c.1
                                        have p3818_1 := h3818c.2.1
                                        have p3818_2 := h3818c.2.2.1
                                        have p3818_3 := h3818c.2.2.2
                                        linarith only [hlam, p3818_0]
                            · linarith only [h1967, h3731, hlam]
                        · have p3697_0 := h3697c.1
                          have p3697_1 := h3697c.2.1
                          have p3697_2 := h3697c.2.2.1
                          have p3697_3 := h3697c.2.2.2
                          linarith only [h1969, hc01, hc35, hlam, hphi, ht12, ht23, p3697_1]
                        · have p3697_0 := h3697c.1
                          have p3697_1 := h3697c.2.1
                          have p3697_2 := h3697c.2.2.1
                          have p3697_3 := h3697c.2.2.2
                          linarith only [h1965, hlam, p3697_1]
                        · have p3697_0 := h3697c.1
                          have p3697_1 := h3697c.2.1
                          have p3697_2 := h3697c.2.2.1
                          have p3697_3 := h3697c.2.2.2
                          linarith only [hlam, p3697_0]
                        · have p3697_0 := h3697c.1
                          have p3697_1 := h3697c.2.1
                          have p3697_2 := h3697c.2.2.1
                          have p3697_3 := h3697c.2.2.2
                          linarith only [h1966, h1969, hc35, hlam, hphi, ht23, p3697_1, u2ehi3]
                        · have p3697_0 := h3697c.1
                          have p3697_1 := h3697c.2.1
                          have p3697_2 := h3697c.2.2.1
                          have p3697_3 := h3697c.2.2.2
                          linarith only [h1969, hlam, p3697_1]
                        · have p3697_0 := h3697c.1
                          have p3697_1 := h3697c.2.1
                          have p3697_2 := h3697c.2.2.1
                          have p3697_3 := h3697c.2.2.2
                          linarith only [h1968, h1969, h3684, h3687, h3689, h3695, hc01, hc12, hlam, hphi, p3697_1]
                        · have p3697_0 := h3697c.1
                          have p3697_1 := h3697c.2.1
                          have p3697_2 := h3697c.2.2.1
                          have p3697_3 := h3697c.2.2.2
                          linarith only [h1966, hlam, p3697_0]
                        · have p3697_0 := h3697c.1
                          have p3697_1 := h3697c.2.1
                          have p3697_2 := h3697c.2.2.1
                          have p3697_3 := h3697c.2.2.2
                          linarith only [h1968, hlam, p3697_0]
                        · have p3697_0 := h3697c.1
                          have p3697_1 := h3697c.2.1
                          have p3697_2 := h3697c.2.2.1
                          have p3697_3 := h3697c.2.2.2
                          linarith only [hlam, p3697_0]
                        · have p3697_0 := h3697c.1
                          have p3697_1 := h3697c.2.1
                          have p3697_2 := h3697c.2.2.1
                          have p3697_3 := h3697c.2.2.2
                          linarith only [h3682, hlam, p3697_0]
                        · have p3697_0 := h3697c.1
                          have p3697_1 := h3697c.2.1
                          have p3697_2 := h3697c.2.2.1
                          have p3697_3 := h3697c.2.2.2
                          linarith only [h1969, h3684, h3687, h3689, h3695, hc01, hc12, hlam, hphi, p3697_1]
                        · have p3697_0 := h3697c.1
                          have p3697_1 := h3697c.2.1
                          have p3697_2 := h3697c.2.2.1
                          have p3697_3 := h3697c.2.2.2
                          linarith only [h1967, hlam, p3697_1]
                        · have p3697_0 := h3697c.1
                          have p3697_1 := h3697c.2.1
                          have p3697_2 := h3697c.2.2.1
                          have p3697_3 := h3697c.2.2.2
                          linarith only [h1965, h1969, h3684, h3687, h3689, h3690, h3695, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3697_1, u2ehi3]
                        · have p3697_0 := h3697c.1
                          have p3697_1 := h3697c.2.1
                          have p3697_2 := h3697c.2.2.1
                          have p3697_3 := h3697c.2.2.2
                          linarith only [h1966, h1969, h3684, h3687, h3689, h3695, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3697_1, u2ehi3]
                        · have p3697_0 := h3697c.1
                          have p3697_1 := h3697c.2.1
                          have p3697_2 := h3697c.2.2.1
                          have p3697_3 := h3697c.2.2.2
                          linarith only [hlam, p3697_0]
                · linarith only [h1968, h1969, h3690, hc23, hc35, hlam, hphi]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3861 | h3861
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3862 | h3862
                  · linarith only [h0, h1414, h1965, h1969, h3862, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3864 | h3864
                    · linarith only [h1728, h1966, h1968, h1969, h3689, h3864, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3866 | h3866
                      · linarith only [h1966, h1968, h1969, h3688, h3689, h3866, hc34, hlam, hphi, ht23, u2ehi3]
                      · rcases h0bigk with h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c | h3868c
                        · have p3868_0 := h3868c.1
                          have p3868_1 := h3868c.2.1
                          have p3868_2 := h3868c.2.2.1
                          have p3868_3 := h3868c.2.2.2
                          linarith only [hlam, p3868_0]
                        · have p3868_0 := h3868c.1
                          have p3868_1 := h3868c.2.1
                          have p3868_2 := h3868c.2.2.1
                          have p3868_3 := h3868c.2.2.2
                          linarith only [h0, hlam, p3868_1]
                        · have p3868_0 := h3868c.1
                          have p3868_1 := h3868c.2.1
                          have p3868_2 := h3868c.2.2.1
                          have p3868_3 := h3868c.2.2.2
                          linarith only [h1414, hlam, p3868_0]
                        · have p3868_0 := h3868c.1
                          have p3868_1 := h3868c.2.1
                          have p3868_2 := h3868c.2.2.1
                          have p3868_3 := h3868c.2.2.2
                          linarith only [h0, h1966, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3868_1, u2ehi3]
                        · have p3868_0 := h3868c.1
                          have p3868_1 := h3868c.2.1
                          have p3868_2 := h3868c.2.2.1
                          have p3868_3 := h3868c.2.2.2
                          linarith only [h1728, hlam, p3868_1]
                        · have p3868_0 := h3868c.1
                          have p3868_1 := h3868c.2.1
                          have p3868_2 := h3868c.2.2.1
                          have p3868_3 := h3868c.2.2.2
                          rcases p3868_3 (m.d 0 1) (by simp) with h3874 | h3874
                          · linarith only [h0, h3874, hlam]
                          · rcases p3868_3 (m.d 0 2) (by simp) with h3876 | h3876
                            · rcases p3868_3 (m.d 0 3) (by simp) with h3877 | h3877
                              · linarith only [h1965, h3877, hlam]
                              · linarith only [h1414, h3877, hlam]
                            · linarith only [h0, h3876, hlam]
                        · have p3868_0 := h3868c.1
                          have p3868_1 := h3868c.2.1
                          have p3868_2 := h3868c.2.2.1
                          have p3868_3 := h3868c.2.2.2
                          linarith only [hlam, p3868_0]
                        · have p3868_0 := h3868c.1
                          have p3868_1 := h3868c.2.1
                          have p3868_2 := h3868c.2.2.1
                          have p3868_3 := h3868c.2.2.2
                          rcases p3868_3 (m.d 0 1) (by simp) with h3882 | h3882
                          · linarith only [h0, h3882, hlam]
                          · rcases p3868_3 (m.d 0 2) (by simp) with h3884 | h3884
                            · rcases p3868_3 (m.d 0 3) (by simp) with h3885 | h3885
                              · linarith only [h1965, h3885, hlam]
                              · rcases p3868_3 (m.d 0 4) (by simp) with h3887 | h3887
                                · linarith only [h1966, h3887, hlam]
                                · rcases p3868_3 (m.d 0 5) (by simp) with h3889 | h3889
                                  · linarith only [h1967, h3889, hlam]
                                  · linarith only [h1969, h3889, hlam]
                            · linarith only [h1965, h3884, hlam]
                        · have p3868_0 := h3868c.1
                          have p3868_1 := h3868c.2.1
                          have p3868_2 := h3868c.2.2.1
                          have p3868_3 := h3868c.2.2.2
                          rcases p3868_3 (m.d 0 1) (by simp) with h3893 | h3893
                          · linarith only [h0, h3893, hlam]
                          · rcases p3868_3 (m.d 0 2) (by simp) with h3895 | h3895
                            · rcases p3868_3 (m.d 0 3) (by simp) with h3896 | h3896
                              · linarith only [h1965, h3896, hlam]
                              · linarith only [h1968, h3896, hlam]
                            · linarith only [h1966, h3895, hlam]
                        · have p3868_0 := h3868c.1
                          have p3868_1 := h3868c.2.1
                          have p3868_2 := h3868c.2.2.1
                          have p3868_3 := h3868c.2.2.2
                          rcases p3868_3 (m.d 0 1) (by simp) with h3900 | h3900
                          · linarith only [h0, h3900, hlam]
                          · rcases p3868_3 (m.d 0 2) (by simp) with h3902 | h3902
                            · rcases p3868_3 (m.d 0 3) (by simp) with h3903 | h3903
                              · linarith only [h1965, h3903, hlam]
                              · rcases p3868_3 (m.d 0 4) (by simp) with h3905 | h3905
                                · linarith only [h1966, h3905, hlam]
                                · rcases p3868_3 (m.d 0 5) (by simp) with h3907 | h3907
                                  · linarith only [h1967, h3907, hlam]
                                  · rcases h0emax with h3909 | h3909 | h3909 | h3909 | h3909
                                    · rcases h5bigk with h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c | h3910c
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [hlam, p3910_0]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h1728, hlam, p3910_1]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h3861, h3862, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3910_1, u2ehi3]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h1969, hlam, p3910_1]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h3682, hlam, p3910_1]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h1728, h3689, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3910_1]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [hlam, p3910_0]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h3689, h3861, h3862, hc45, hlam, hphi, ht23, ht34, p3910_1, u2ehi3]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h1966, h1968, h1969, h3689, hc45, hlam, hphi, ht23, ht34, p3910_1, u2ehi3]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h3689, hlam, p3910_1]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h1967, hlam, p3910_1]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h3686, hlam, p3910_1]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [hlam, p3910_0]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h3862, hlam, p3910_1]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h3864, hlam, p3910_1]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h1967, h3688, h3861, h3862, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3910_1, u2ehi3]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h3688, hlam, p3910_0]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h3684, h3688, h3861, h3862, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3910_1, u2ehi3]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [hlam, p3910_0]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h3866, hlam, p3910_1]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h1967, h3861, h3862, hc45, hlam, hphi, ht23, ht34, p3910_1, u2ehi3]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h1728, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3910_1]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h3861, h3862, hc45, hlam, hphi, ht23, ht34, p3910_1, u2ehi3]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [h1966, h1968, h1969, hc45, hlam, hphi, ht23, ht34, p3910_1, u2ehi3]
                                      · have p3910_0 := h3910c.1
                                        have p3910_1 := h3910c.2.1
                                        have p3910_2 := h3910c.2.2.1
                                        have p3910_3 := h3910c.2.2.2
                                        linarith only [hlam, p3910_0]
                                    · linarith only [h1967, h3861, h3862, h3909, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3868_1, u2ehi3]
                                    · rcases h5bigk with h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c | h3937c
                                      · have p3937_0 := h3937c.1
                                        have p3937_1 := h3937c.2.1
                                        have p3937_2 := h3937c.2.2.1
                                        have p3937_3 := h3937c.2.2.2
                                        linarith only [hlam, p3937_0]
                                      · have p3937_0 := h3937c.1
                                        have p3937_1 := h3937c.2.1
                                        have p3937_2 := h3937c.2.2.1
                                        have p3937_3 := h3937c.2.2.2
                                        linarith only [h1728, hlam, p3937_1]
                                      · have p3937_0 := h3937c.1
                                        have p3937_1 := h3937c.2.1
                                        have p3937_2 := h3937c.2.2.1
                                        have p3937_3 := h3937c.2.2.2
                                        linarith only [h0, h3861, h3862, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3868_1, p3937_1, u2ehi3]
                                      · have p3937_0 := h3937c.1
                                        have p3937_1 := h3937c.2.1
                                        have p3937_2 := h3937c.2.2.1
                                        have p3937_3 := h3937c.2.2.2
                                        linarith only [h1969, hlam, p3937_1]
                                      · have p3937_0 := h3937c.1
                                        have p3937_1 := h3937c.2.1
                                        have p3937_2 := h3937c.2.2.1
                                        have p3937_3 := h3937c.2.2.2
                                        linarith only [h3682, hlam, p3937_1]
                                      · have p3937_0 := h3937c.1
                                        have p3937_1 := h3937c.2.1
                                        have p3937_2 := h3937c.2.2.1
                                        have p3937_3 := h3937c.2.2.2
                                        linarith only [h1728, hc01, hc15, hlam, hphi, p3937_1]
                                      · have p3937_0 := h3937c.1
                                        have p3937_1 := h3937c.2.1
                                        have p3937_2 := h3937c.2.2.1
                                        have p3937_3 := h3937c.2.2.2
                                        linarith only [hlam, p3937_0]
                                      · have p3937_0 := h3937c.1
                                        have p3937_1 := h3937c.2.1
                                        have p3937_2 := h3937c.2.2.1
                                        have p3937_3 := h3937c.2.2.2
                                        linarith only [h3686, h3861, h3862, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3937_1, u2ehi3]
                                      · have p3937_0 := h3937c.1
                                        have p3937_1 := h3937c.2.1
                                        have p3937_2 := h3937c.2.2.1
                                        have p3937_3 := h3937c.2.2.2
                                        linarith only [h1966, h1968, h1969, h3684, h3688, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3937_1, u2ehi3]
                                      · have p3937_0 := h3937c.1
                                        have p3937_1 := h3937c.2.1
                                        have p3937_2 := h3937c.2.2.1
                                        have p3937_3 := h3937c.2.2.2
                                        linarith only [h3689, hlam, p3937_1]
                                      · have p3937_0 := h3937c.1
                                        have p3937_1 := h3937c.2.1
                                        have p3937_2 := h3937c.2.2.1
                                        have p3937_3 := h3937c.2.2.2
                                        linarith only [h1967, hlam, p3937_1]
                                      · have p3937_0 := h3937c.1
                                        have p3937_1 := h3937c.2.1
                                        have p3937_2 := h3937c.2.2.1
                                        have p3937_3 := h3937c.2.2.2
                                        linarith only [h3686, hlam, p3937_1]
                                      · have p3937_0 := h3937c.1
                                        have p3937_1 := h3937c.2.1
                                        have p3937_2 := h3937c.2.2.1
                                        have p3937_3 := h3937c.2.2.2
                                        linarith only [hlam, p3937_0]
                                      · have p3937_0 := h3937c.1
                                        have p3937_1 := h3937c.2.1
                                        have p3937_2 := h3937c.2.2.1
                                        have p3937_3 := h3937c.2.2.2
                                        linarith only [h3862, hlam, p3937_1]
                                      · have p3937_0 := h3937c.1
                                        have p3937_1 := h3937c.2.1
                                        have p3937_2 := h3937c.2.2.1
                                        have p3937_3 := h3937c.2.2.2
                                        linarith only [h3864, hlam, p3937_1]
                                      · have p3937_0 := h3937c.1
                                        have p3937_1 := h3937c.2.1
                                        have p3937_2 := h3937c.2.2.1
                                        have p3937_3 := h3937c.2.2.2
                                        linarith only [h1967, h3861, h3862, hc35, hlam, hphi, ht23, p3937_1, u2ehi3]
                                      · have p3937_0 := h3937c.1
                                        have p3937_1 := h3937c.2.1
                                        have p3937_2 := h3937c.2.2.1
                                        have p3937_3 := h3937c.2.2.2
                                        linarith only [h3688, hlam, p3937_0]
                                      · have p3937_0 := h3937c.1
                                        have p3937_1 := h3937c.2.1
                                        have p3937_2 := h3937c.2.2.1
                                        have p3937_3 := h3937c.2.2.2
                                        linarith only [h3684, h3688, h3861, h3862, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3937_1, u2ehi3]
                                      · have p3937_0 := h3937c.1
                                        have p3937_1 := h3937c.2.1
                                        have p3937_2 := h3937c.2.2.1
                                        have p3937_3 := h3937c.2.2.2
                                        linarith only [hlam, p3937_0]
                                      · have p3937_0 := h3937c.1
                                        have p3937_1 := h3937c.2.1
                                        have p3937_2 := h3937c.2.2.1
                                        have p3937_3 := h3937c.2.2.2
                                        linarith only [h3866, hlam, p3937_1]
                                      · have p3937_0 := h3937c.1
                                        have p3937_1 := h3937c.2.1
                                        have p3937_2 := h3937c.2.2.1
                                        have p3937_3 := h3937c.2.2.2
                                        linarith only [h1967, h3861, h3862, hc45, hlam, hphi, ht23, ht34, p3937_1, u2ehi3]
                                      · have p3937_0 := h3937c.1
                                        have p3937_1 := h3937c.2.1
                                        have p3937_2 := h3937c.2.2.1
                                        have p3937_3 := h3937c.2.2.2
                                        linarith only [h1728, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3937_1]
                                      · have p3937_0 := h3937c.1
                                        have p3937_1 := h3937c.2.1
                                        have p3937_2 := h3937c.2.2.1
                                        have p3937_3 := h3937c.2.2.2
                                        linarith only [h3861, h3862, hc45, hlam, hphi, ht23, ht34, p3937_1, u2ehi3]
                                      · have p3937_0 := h3937c.1
                                        have p3937_1 := h3937c.2.1
                                        have p3937_2 := h3937c.2.2.1
                                        have p3937_3 := h3937c.2.2.2
                                        linarith only [h1966, h1968, h1969, hc45, hlam, hphi, ht23, ht34, p3937_1, u2ehi3]
                                      · have p3937_0 := h3937c.1
                                        have p3937_1 := h3937c.2.1
                                        have p3937_2 := h3937c.2.2.1
                                        have p3937_3 := h3937c.2.2.2
                                        linarith only [hlam, p3937_0]
                                    · rcases h5bigk with h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c
                                      · have p3963_0 := h3963c.1
                                        have p3963_1 := h3963c.2.1
                                        have p3963_2 := h3963c.2.2.1
                                        have p3963_3 := h3963c.2.2.2
                                        linarith only [hlam, p3963_0]
                                      · have p3963_0 := h3963c.1
                                        have p3963_1 := h3963c.2.1
                                        have p3963_2 := h3963c.2.2.1
                                        have p3963_3 := h3963c.2.2.2
                                        linarith only [h1728, hlam, p3963_1]
                                      · have p3963_0 := h3963c.1
                                        have p3963_1 := h3963c.2.1
                                        have p3963_2 := h3963c.2.2.1
                                        have p3963_3 := h3963c.2.2.2
                                        linarith only [h0, h3861, h3862, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3868_1, p3963_1, u2ehi3]
                                      · have p3963_0 := h3963c.1
                                        have p3963_1 := h3963c.2.1
                                        have p3963_2 := h3963c.2.2.1
                                        have p3963_3 := h3963c.2.2.2
                                        linarith only [h1969, hlam, p3963_1]
                                      · have p3963_0 := h3963c.1
                                        have p3963_1 := h3963c.2.1
                                        have p3963_2 := h3963c.2.2.1
                                        have p3963_3 := h3963c.2.2.2
                                        linarith only [h3682, hlam, p3963_1]
                                      · have p3963_0 := h3963c.1
                                        have p3963_1 := h3963c.2.1
                                        have p3963_2 := h3963c.2.2.1
                                        have p3963_3 := h3963c.2.2.2
                                        linarith only [h1728, hc01, hc15, hlam, hphi, p3963_1]
                                      · have p3963_0 := h3963c.1
                                        have p3963_1 := h3963c.2.1
                                        have p3963_2 := h3963c.2.2.1
                                        have p3963_3 := h3963c.2.2.2
                                        linarith only [hlam, p3963_0]
                                      · have p3963_0 := h3963c.1
                                        have p3963_1 := h3963c.2.1
                                        have p3963_2 := h3963c.2.2.1
                                        have p3963_3 := h3963c.2.2.2
                                        linarith only [h3686, h3861, h3862, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3963_1, u2ehi3]
                                      · have p3963_0 := h3963c.1
                                        have p3963_1 := h3963c.2.1
                                        have p3963_2 := h3963c.2.2.1
                                        have p3963_3 := h3963c.2.2.2
                                        linarith only [h1966, h1968, h1969, h3684, h3688, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3963_1, u2ehi3]
                                      · have p3963_0 := h3963c.1
                                        have p3963_1 := h3963c.2.1
                                        have p3963_2 := h3963c.2.2.1
                                        have p3963_3 := h3963c.2.2.2
                                        linarith only [h3689, hlam, p3963_1]
                                      · have p3963_0 := h3963c.1
                                        have p3963_1 := h3963c.2.1
                                        have p3963_2 := h3963c.2.2.1
                                        have p3963_3 := h3963c.2.2.2
                                        linarith only [h1967, hlam, p3963_1]
                                      · have p3963_0 := h3963c.1
                                        have p3963_1 := h3963c.2.1
                                        have p3963_2 := h3963c.2.2.1
                                        have p3963_3 := h3963c.2.2.2
                                        linarith only [h3686, hlam, p3963_1]
                                      · have p3963_0 := h3963c.1
                                        have p3963_1 := h3963c.2.1
                                        have p3963_2 := h3963c.2.2.1
                                        have p3963_3 := h3963c.2.2.2
                                        linarith only [hlam, p3963_0]
                                      · have p3963_0 := h3963c.1
                                        have p3963_1 := h3963c.2.1
                                        have p3963_2 := h3963c.2.2.1
                                        have p3963_3 := h3963c.2.2.2
                                        linarith only [h3862, hlam, p3963_1]
                                      · have p3963_0 := h3963c.1
                                        have p3963_1 := h3963c.2.1
                                        have p3963_2 := h3963c.2.2.1
                                        have p3963_3 := h3963c.2.2.2
                                        linarith only [h3864, hlam, p3963_1]
                                      · have p3963_0 := h3963c.1
                                        have p3963_1 := h3963c.2.1
                                        have p3963_2 := h3963c.2.2.1
                                        have p3963_3 := h3963c.2.2.2
                                        linarith only [h1967, h3861, h3862, hc35, hlam, hphi, ht23, p3963_1, u2ehi3]
                                      · have p3963_0 := h3963c.1
                                        have p3963_1 := h3963c.2.1
                                        have p3963_2 := h3963c.2.2.1
                                        have p3963_3 := h3963c.2.2.2
                                        linarith only [h3688, hlam, p3963_0]
                                      · have p3963_0 := h3963c.1
                                        have p3963_1 := h3963c.2.1
                                        have p3963_2 := h3963c.2.2.1
                                        have p3963_3 := h3963c.2.2.2
                                        linarith only [h3684, h3688, h3861, h3862, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3963_1, u2ehi3]
                                      · have p3963_0 := h3963c.1
                                        have p3963_1 := h3963c.2.1
                                        have p3963_2 := h3963c.2.2.1
                                        have p3963_3 := h3963c.2.2.2
                                        linarith only [hlam, p3963_0]
                                      · have p3963_0 := h3963c.1
                                        have p3963_1 := h3963c.2.1
                                        have p3963_2 := h3963c.2.2.1
                                        have p3963_3 := h3963c.2.2.2
                                        linarith only [h3866, hlam, p3963_1]
                                      · have p3963_0 := h3963c.1
                                        have p3963_1 := h3963c.2.1
                                        have p3963_2 := h3963c.2.2.1
                                        have p3963_3 := h3963c.2.2.2
                                        linarith only [h1967, h3861, h3862, hc45, hlam, hphi, ht23, ht34, p3963_1, u2ehi3]
                                      · have p3963_0 := h3963c.1
                                        have p3963_1 := h3963c.2.1
                                        have p3963_2 := h3963c.2.2.1
                                        have p3963_3 := h3963c.2.2.2
                                        linarith only [h1728, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3963_1]
                                      · have p3963_0 := h3963c.1
                                        have p3963_1 := h3963c.2.1
                                        have p3963_2 := h3963c.2.2.1
                                        have p3963_3 := h3963c.2.2.2
                                        linarith only [h3861, h3862, hc45, hlam, hphi, ht23, ht34, p3963_1, u2ehi3]
                                      · have p3963_0 := h3963c.1
                                        have p3963_1 := h3963c.2.1
                                        have p3963_2 := h3963c.2.2.1
                                        have p3963_3 := h3963c.2.2.2
                                        linarith only [h1966, h1968, h1969, hc45, hlam, hphi, ht23, ht34, p3963_1, u2ehi3]
                                      · have p3963_0 := h3963c.1
                                        have p3963_1 := h3963c.2.1
                                        have p3963_2 := h3963c.2.2.1
                                        have p3963_3 := h3963c.2.2.2
                                        linarith only [hlam, p3963_0]
                                    · rcases h5bigk with h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c
                                      · have p3989_0 := h3989c.1
                                        have p3989_1 := h3989c.2.1
                                        have p3989_2 := h3989c.2.2.1
                                        have p3989_3 := h3989c.2.2.2
                                        linarith only [hlam, p3989_0]
                                      · have p3989_0 := h3989c.1
                                        have p3989_1 := h3989c.2.1
                                        have p3989_2 := h3989c.2.2.1
                                        have p3989_3 := h3989c.2.2.2
                                        linarith only [h1728, hlam, p3989_1]
                                      · have p3989_0 := h3989c.1
                                        have p3989_1 := h3989c.2.1
                                        have p3989_2 := h3989c.2.2.1
                                        have p3989_3 := h3989c.2.2.2
                                        linarith only [h0, h3861, h3862, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3868_1, p3989_1, u2ehi3]
                                      · have p3989_0 := h3989c.1
                                        have p3989_1 := h3989c.2.1
                                        have p3989_2 := h3989c.2.2.1
                                        have p3989_3 := h3989c.2.2.2
                                        linarith only [h1969, hlam, p3989_1]
                                      · have p3989_0 := h3989c.1
                                        have p3989_1 := h3989c.2.1
                                        have p3989_2 := h3989c.2.2.1
                                        have p3989_3 := h3989c.2.2.2
                                        linarith only [h3682, hlam, p3989_1]
                                      · have p3989_0 := h3989c.1
                                        have p3989_1 := h3989c.2.1
                                        have p3989_2 := h3989c.2.2.1
                                        have p3989_3 := h3989c.2.2.2
                                        linarith only [h1728, hc01, hc15, hlam, hphi, p3989_1]
                                      · have p3989_0 := h3989c.1
                                        have p3989_1 := h3989c.2.1
                                        have p3989_2 := h3989c.2.2.1
                                        have p3989_3 := h3989c.2.2.2
                                        linarith only [hlam, p3989_0]
                                      · have p3989_0 := h3989c.1
                                        have p3989_1 := h3989c.2.1
                                        have p3989_2 := h3989c.2.2.1
                                        have p3989_3 := h3989c.2.2.2
                                        linarith only [h3686, h3861, h3862, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3989_1, u2ehi3]
                                      · have p3989_0 := h3989c.1
                                        have p3989_1 := h3989c.2.1
                                        have p3989_2 := h3989c.2.2.1
                                        have p3989_3 := h3989c.2.2.2
                                        linarith only [h1966, h1968, h1969, h3684, h3688, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3989_1, u2ehi3]
                                      · have p3989_0 := h3989c.1
                                        have p3989_1 := h3989c.2.1
                                        have p3989_2 := h3989c.2.2.1
                                        have p3989_3 := h3989c.2.2.2
                                        linarith only [h3689, hlam, p3989_1]
                                      · have p3989_0 := h3989c.1
                                        have p3989_1 := h3989c.2.1
                                        have p3989_2 := h3989c.2.2.1
                                        have p3989_3 := h3989c.2.2.2
                                        linarith only [h1967, hlam, p3989_1]
                                      · have p3989_0 := h3989c.1
                                        have p3989_1 := h3989c.2.1
                                        have p3989_2 := h3989c.2.2.1
                                        have p3989_3 := h3989c.2.2.2
                                        linarith only [h3686, hlam, p3989_1]
                                      · have p3989_0 := h3989c.1
                                        have p3989_1 := h3989c.2.1
                                        have p3989_2 := h3989c.2.2.1
                                        have p3989_3 := h3989c.2.2.2
                                        linarith only [hlam, p3989_0]
                                      · have p3989_0 := h3989c.1
                                        have p3989_1 := h3989c.2.1
                                        have p3989_2 := h3989c.2.2.1
                                        have p3989_3 := h3989c.2.2.2
                                        linarith only [h3862, hlam, p3989_1]
                                      · have p3989_0 := h3989c.1
                                        have p3989_1 := h3989c.2.1
                                        have p3989_2 := h3989c.2.2.1
                                        have p3989_3 := h3989c.2.2.2
                                        linarith only [h3864, hlam, p3989_1]
                                      · have p3989_0 := h3989c.1
                                        have p3989_1 := h3989c.2.1
                                        have p3989_2 := h3989c.2.2.1
                                        have p3989_3 := h3989c.2.2.2
                                        linarith only [h1967, h3861, h3862, hc35, hlam, hphi, ht23, p3989_1, u2ehi3]
                                      · have p3989_0 := h3989c.1
                                        have p3989_1 := h3989c.2.1
                                        have p3989_2 := h3989c.2.2.1
                                        have p3989_3 := h3989c.2.2.2
                                        linarith only [h3688, hlam, p3989_0]
                                      · have p3989_0 := h3989c.1
                                        have p3989_1 := h3989c.2.1
                                        have p3989_2 := h3989c.2.2.1
                                        have p3989_3 := h3989c.2.2.2
                                        linarith only [h3684, h3688, h3861, h3862, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3989_1, u2ehi3]
                                      · have p3989_0 := h3989c.1
                                        have p3989_1 := h3989c.2.1
                                        have p3989_2 := h3989c.2.2.1
                                        have p3989_3 := h3989c.2.2.2
                                        linarith only [hlam, p3989_0]
                                      · have p3989_0 := h3989c.1
                                        have p3989_1 := h3989c.2.1
                                        have p3989_2 := h3989c.2.2.1
                                        have p3989_3 := h3989c.2.2.2
                                        linarith only [h3866, hlam, p3989_1]
                                      · have p3989_0 := h3989c.1
                                        have p3989_1 := h3989c.2.1
                                        have p3989_2 := h3989c.2.2.1
                                        have p3989_3 := h3989c.2.2.2
                                        linarith only [h1967, h3861, h3862, hc45, hlam, hphi, ht23, ht34, p3989_1, u2ehi3]
                                      · have p3989_0 := h3989c.1
                                        have p3989_1 := h3989c.2.1
                                        have p3989_2 := h3989c.2.2.1
                                        have p3989_3 := h3989c.2.2.2
                                        linarith only [h1728, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3989_1]
                                      · have p3989_0 := h3989c.1
                                        have p3989_1 := h3989c.2.1
                                        have p3989_2 := h3989c.2.2.1
                                        have p3989_3 := h3989c.2.2.2
                                        linarith only [h3861, h3862, hc45, hlam, hphi, ht23, ht34, p3989_1, u2ehi3]
                                      · have p3989_0 := h3989c.1
                                        have p3989_1 := h3989c.2.1
                                        have p3989_2 := h3989c.2.2.1
                                        have p3989_3 := h3989c.2.2.2
                                        linarith only [h1966, h1968, h1969, hc45, hlam, hphi, ht23, ht34, p3989_1, u2ehi3]
                                      · have p3989_0 := h3989c.1
                                        have p3989_1 := h3989c.2.1
                                        have p3989_2 := h3989c.2.2.1
                                        have p3989_3 := h3989c.2.2.2
                                        linarith only [hlam, p3989_0]
                            · linarith only [h1967, h3902, hlam]
                        · have p3868_0 := h3868c.1
                          have p3868_1 := h3868c.2.1
                          have p3868_2 := h3868c.2.2.1
                          have p3868_3 := h3868c.2.2.2
                          linarith only [h1969, h3688, hc01, hc15, hlam, hphi, p3868_1]
                        · have p3868_0 := h3868c.1
                          have p3868_1 := h3868c.2.1
                          have p3868_2 := h3868c.2.2.1
                          have p3868_3 := h3868c.2.2.2
                          linarith only [h1965, hlam, p3868_1]
                        · have p3868_0 := h3868c.1
                          have p3868_1 := h3868c.2.1
                          have p3868_2 := h3868c.2.2.1
                          have p3868_3 := h3868c.2.2.2
                          linarith only [hlam, p3868_0]
                        · have p3868_0 := h3868c.1
                          have p3868_1 := h3868c.2.1
                          have p3868_2 := h3868c.2.2.1
                          have p3868_3 := h3868c.2.2.2
                          linarith only [h1966, h1969, hc35, hlam, hphi, ht23, p3868_1, u2ehi3]
                        · have p3868_0 := h3868c.1
                          have p3868_1 := h3868c.2.1
                          have p3868_2 := h3868c.2.2.1
                          have p3868_3 := h3868c.2.2.2
                          linarith only [h1969, hlam, p3868_1]
                        · have p3868_0 := h3868c.1
                          have p3868_1 := h3868c.2.1
                          have p3868_2 := h3868c.2.2.1
                          have p3868_3 := h3868c.2.2.2
                          linarith only [h1968, h1969, h3684, h3688, hc01, hc12, hlam, hphi, p3868_1]
                        · have p3868_0 := h3868c.1
                          have p3868_1 := h3868c.2.1
                          have p3868_2 := h3868c.2.2.1
                          have p3868_3 := h3868c.2.2.2
                          linarith only [h1966, hlam, p3868_0]
                        · have p3868_0 := h3868c.1
                          have p3868_1 := h3868c.2.1
                          have p3868_2 := h3868c.2.2.1
                          have p3868_3 := h3868c.2.2.2
                          linarith only [h1968, hlam, p3868_0]
                        · have p3868_0 := h3868c.1
                          have p3868_1 := h3868c.2.1
                          have p3868_2 := h3868c.2.2.1
                          have p3868_3 := h3868c.2.2.2
                          linarith only [hlam, p3868_0]
                        · have p3868_0 := h3868c.1
                          have p3868_1 := h3868c.2.1
                          have p3868_2 := h3868c.2.2.1
                          have p3868_3 := h3868c.2.2.2
                          linarith only [h3682, hlam, p3868_0]
                        · have p3868_0 := h3868c.1
                          have p3868_1 := h3868c.2.1
                          have p3868_2 := h3868c.2.2.1
                          have p3868_3 := h3868c.2.2.2
                          linarith only [h1969, h3684, h3688, hc01, hc12, hlam, hphi, p3868_1]
                        · have p3868_0 := h3868c.1
                          have p3868_1 := h3868c.2.1
                          have p3868_2 := h3868c.2.2.1
                          have p3868_3 := h3868c.2.2.2
                          linarith only [h1967, hlam, p3868_1]
                        · have p3868_0 := h3868c.1
                          have p3868_1 := h3868c.2.1
                          have p3868_2 := h3868c.2.2.1
                          have p3868_3 := h3868c.2.2.2
                          linarith only [h1965, h1969, h3684, h3688, h3861, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3868_1, u2ehi3]
                        · have p3868_0 := h3868c.1
                          have p3868_1 := h3868c.2.1
                          have p3868_2 := h3868c.2.2.1
                          have p3868_3 := h3868c.2.2.2
                          linarith only [h1966, h1969, h3684, h3688, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3868_1, u2ehi3]
                        · have p3868_0 := h3868c.1
                          have p3868_1 := h3868c.2.1
                          have p3868_2 := h3868c.2.2.1
                          have p3868_3 := h3868c.2.2.2
                          linarith only [hlam, p3868_0]
                · linarith only [h1968, h1969, h3684, h3688, h3861, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4032 | h4032
              · linarith only [h1967, h3682, h3687, h3688, h4032, hc35, hlam, hphi, ht23, u2ehi4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4034 | h4034
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4035 | h4035
                  · linarith only [h1414, h3688, h4035, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4037 | h4037
                    · linarith only [h1728, h1966, h1968, h1969, h4032, h4037, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4039 | h4039
                      · linarith only [h1966, h3682, h4039, hc34, hlam, hphi, ht23, u2ehi3]
                      · rcases h0bigk with h4041c | h4041c | h4041c | h4041c | h4041c | h4041c | h4041c | h4041c | h4041c | h4041c | h4041c | h4041c | h4041c | h4041c | h4041c | h4041c | h4041c | h4041c | h4041c | h4041c | h4041c | h4041c | h4041c | h4041c | h4041c
                        · have p4041_0 := h4041c.1
                          have p4041_1 := h4041c.2.1
                          have p4041_2 := h4041c.2.2.1
                          have p4041_3 := h4041c.2.2.2
                          linarith only [hlam, p4041_0]
                        · have p4041_0 := h4041c.1
                          have p4041_1 := h4041c.2.1
                          have p4041_2 := h4041c.2.2.1
                          have p4041_3 := h4041c.2.2.2
                          linarith only [h0, hlam, p4041_1]
                        · have p4041_0 := h4041c.1
                          have p4041_1 := h4041c.2.1
                          have p4041_2 := h4041c.2.2.1
                          have p4041_3 := h4041c.2.2.2
                          linarith only [h1414, hlam, p4041_0]
                        · have p4041_0 := h4041c.1
                          have p4041_1 := h4041c.2.1
                          have p4041_2 := h4041c.2.2.1
                          have p4041_3 := h4041c.2.2.2
                          linarith only [h0, h1966, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4041_1, u2ehi3]
                        · have p4041_0 := h4041c.1
                          have p4041_1 := h4041c.2.1
                          have p4041_2 := h4041c.2.2.1
                          have p4041_3 := h4041c.2.2.2
                          linarith only [h1728, hlam, p4041_1]
                        · have p4041_0 := h4041c.1
                          have p4041_1 := h4041c.2.1
                          have p4041_2 := h4041c.2.2.1
                          have p4041_3 := h4041c.2.2.2
                          rcases p4041_3 (m.d 0 1) (by simp) with h4047 | h4047
                          · linarith only [h0, h4047, hlam]
                          · rcases p4041_3 (m.d 0 2) (by simp) with h4049 | h4049
                            · rcases p4041_3 (m.d 0 3) (by simp) with h4050 | h4050
                              · linarith only [h1965, h4050, hlam]
                              · linarith only [h1414, h4050, hlam]
                            · linarith only [h0, h4049, hlam]
                        · have p4041_0 := h4041c.1
                          have p4041_1 := h4041c.2.1
                          have p4041_2 := h4041c.2.2.1
                          have p4041_3 := h4041c.2.2.2
                          linarith only [hlam, p4041_0]
                        · have p4041_0 := h4041c.1
                          have p4041_1 := h4041c.2.1
                          have p4041_2 := h4041c.2.2.1
                          have p4041_3 := h4041c.2.2.2
                          rcases p4041_3 (m.d 0 1) (by simp) with h4055 | h4055
                          · linarith only [h0, h4055, hlam]
                          · rcases p4041_3 (m.d 0 2) (by simp) with h4057 | h4057
                            · rcases p4041_3 (m.d 0 3) (by simp) with h4058 | h4058
                              · linarith only [h1965, h4058, hlam]
                              · rcases p4041_3 (m.d 0 4) (by simp) with h4060 | h4060
                                · linarith only [h1966, h4060, hlam]
                                · rcases p4041_3 (m.d 0 5) (by simp) with h4062 | h4062
                                  · linarith only [h1967, h4062, hlam]
                                  · linarith only [h1969, h4062, hlam]
                            · linarith only [h1965, h4057, hlam]
                        · have p4041_0 := h4041c.1
                          have p4041_1 := h4041c.2.1
                          have p4041_2 := h4041c.2.2.1
                          have p4041_3 := h4041c.2.2.2
                          rcases p4041_3 (m.d 0 1) (by simp) with h4066 | h4066
                          · linarith only [h0, h4066, hlam]
                          · rcases p4041_3 (m.d 0 2) (by simp) with h4068 | h4068
                            · rcases p4041_3 (m.d 0 3) (by simp) with h4069 | h4069
                              · linarith only [h1965, h4069, hlam]
                              · linarith only [h1968, h4069, hlam]
                            · linarith only [h1966, h4068, hlam]
                        · have p4041_0 := h4041c.1
                          have p4041_1 := h4041c.2.1
                          have p4041_2 := h4041c.2.2.1
                          have p4041_3 := h4041c.2.2.2
                          rcases p4041_3 (m.d 0 1) (by simp) with h4073 | h4073
                          · linarith only [h0, h4073, hlam]
                          · rcases p4041_3 (m.d 0 2) (by simp) with h4075 | h4075
                            · rcases p4041_3 (m.d 0 3) (by simp) with h4076 | h4076
                              · linarith only [h1965, h4076, hlam]
                              · rcases p4041_3 (m.d 0 4) (by simp) with h4078 | h4078
                                · linarith only [h1966, h4078, hlam]
                                · rcases p4041_3 (m.d 0 5) (by simp) with h4080 | h4080
                                  · linarith only [h1967, h4080, hlam]
                                  · rcases h0emax with h4082 | h4082 | h4082 | h4082 | h4082
                                    · rcases h5bigk with h4083c | h4083c | h4083c | h4083c | h4083c | h4083c | h4083c | h4083c | h4083c | h4083c | h4083c | h4083c | h4083c | h4083c | h4083c | h4083c | h4083c | h4083c | h4083c | h4083c | h4083c | h4083c | h4083c | h4083c | h4083c
                                      · have p4083_0 := h4083c.1
                                        have p4083_1 := h4083c.2.1
                                        have p4083_2 := h4083c.2.2.1
                                        have p4083_3 := h4083c.2.2.2
                                        linarith only [hlam, p4083_0]
                                      · have p4083_0 := h4083c.1
                                        have p4083_1 := h4083c.2.1
                                        have p4083_2 := h4083c.2.2.1
                                        have p4083_3 := h4083c.2.2.2
                                        linarith only [h1728, hlam, p4083_1]
                                      · have p4083_0 := h4083c.1
                                        have p4083_1 := h4083c.2.1
                                        have p4083_2 := h4083c.2.2.1
                                        have p4083_3 := h4083c.2.2.2
                                        linarith only [h0, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p4041_1, p4083_1]
                                      · have p4083_0 := h4083c.1
                                        have p4083_1 := h4083c.2.1
                                        have p4083_2 := h4083c.2.2.1
                                        have p4083_3 := h4083c.2.2.2
                                        linarith only [h1969, hlam, p4083_1]
                                      · have p4083_0 := h4083c.1
                                        have p4083_1 := h4083c.2.1
                                        have p4083_2 := h4083c.2.2.1
                                        have p4083_3 := h4083c.2.2.2
                                        linarith only [h3682, hlam, p4083_1]
                                      · have p4083_0 := h4083c.1
                                        have p4083_1 := h4083c.2.1
                                        have p4083_2 := h4083c.2.2.1
                                        have p4083_3 := h4083c.2.2.2
                                        linarith only [h1965, h1969, h4034, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4083_1]
                                      · have p4083_0 := h4083c.1
                                        have p4083_1 := h4083c.2.1
                                        have p4083_2 := h4083c.2.2.1
                                        have p4083_3 := h4083c.2.2.2
                                        linarith only [hlam, p4083_0]
                                      · have p4083_0 := h4083c.1
                                        have p4083_1 := h4083c.2.1
                                        have p4083_2 := h4083c.2.2.1
                                        have p4083_3 := h4083c.2.2.2
                                        linarith only [h3686, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4083_1, u2ehi4]
                                      · have p4083_0 := h4083c.1
                                        have p4083_1 := h4083c.2.1
                                        have p4083_2 := h4083c.2.2.1
                                        have p4083_3 := h4083c.2.2.2
                                        linarith only [h3688, hlam, p4083_1]
                                      · have p4083_0 := h4083c.1
                                        have p4083_1 := h4083c.2.1
                                        have p4083_2 := h4083c.2.2.1
                                        have p4083_3 := h4083c.2.2.2
                                        linarith only [h4032, hlam, p4083_1]
                                      · have p4083_0 := h4083c.1
                                        have p4083_1 := h4083c.2.1
                                        have p4083_2 := h4083c.2.2.1
                                        have p4083_3 := h4083c.2.2.2
                                        linarith only [h1967, hlam, p4083_1]
                                      · have p4083_0 := h4083c.1
                                        have p4083_1 := h4083c.2.1
                                        have p4083_2 := h4083c.2.2.1
                                        have p4083_3 := h4083c.2.2.2
                                        linarith only [h3686, hlam, p4083_1]
                                      · have p4083_0 := h4083c.1
                                        have p4083_1 := h4083c.2.1
                                        have p4083_2 := h4083c.2.2.1
                                        have p4083_3 := h4083c.2.2.2
                                        linarith only [hlam, p4083_0]
                                      · have p4083_0 := h4083c.1
                                        have p4083_1 := h4083c.2.1
                                        have p4083_2 := h4083c.2.2.1
                                        have p4083_3 := h4083c.2.2.2
                                        linarith only [h4035, hlam, p4083_1]
                                      · have p4083_0 := h4083c.1
                                        have p4083_1 := h4083c.2.1
                                        have p4083_2 := h4083c.2.2.1
                                        have p4083_3 := h4083c.2.2.2
                                        linarith only [h4037, hlam, p4083_1]
                                      · have p4083_0 := h4083c.1
                                        have p4083_1 := h4083c.2.1
                                        have p4083_2 := h4083c.2.2.1
                                        have p4083_3 := h4083c.2.2.2
                                        linarith only [h1966, h1968, h1969, hc35, hlam, hphi, ht23, p4083_1, u2ehi3]
                                      · have p4083_0 := h4083c.1
                                        have p4083_1 := h4083c.2.1
                                        have p4083_2 := h4083c.2.2.1
                                        have p4083_3 := h4083c.2.2.2
                                        linarith only [h1728, h4039, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4083_1]
                                      · have p4083_0 := h4083c.1
                                        have p4083_1 := h4083c.2.1
                                        have p4083_2 := h4083c.2.2.1
                                        have p4083_3 := h4083c.2.2.2
                                        linarith only [h4039, hc45, hlam, hphi, ht23, ht34, p4083_1, u2ehi4]
                                      · have p4083_0 := h4083c.1
                                        have p4083_1 := h4083c.2.1
                                        have p4083_2 := h4083c.2.2.1
                                        have p4083_3 := h4083c.2.2.2
                                        linarith only [hlam, p4083_0]
                                      · have p4083_0 := h4083c.1
                                        have p4083_1 := h4083c.2.1
                                        have p4083_2 := h4083c.2.2.1
                                        have p4083_3 := h4083c.2.2.2
                                        linarith only [h4039, hlam, p4083_1]
                                      · have p4083_0 := h4083c.1
                                        have p4083_1 := h4083c.2.1
                                        have p4083_2 := h4083c.2.2.1
                                        have p4083_3 := h4083c.2.2.2
                                        linarith only [h1966, h1968, h1969, hc45, hlam, hphi, ht23, ht34, p4083_1, u2ehi3]
                                      · have p4083_0 := h4083c.1
                                        have p4083_1 := h4083c.2.1
                                        have p4083_2 := h4083c.2.2.1
                                        have p4083_3 := h4083c.2.2.2
                                        linarith only [h0, h1414, h1966, h1968, h1969, h3688, hc01, hc12, hc45, hlam, hphi, ht23, ht34, p4041_1, p4083_1, u2ehi3]
                                      · have p4083_0 := h4083c.1
                                        have p4083_1 := h4083c.2.1
                                        have p4083_2 := h4083c.2.2.1
                                        have p4083_3 := h4083c.2.2.2
                                        linarith only [h4034, h4035, hc45, hlam, hphi, ht23, ht34, p4083_1, u2ehi3]
                                      · have p4083_0 := h4083c.1
                                        have p4083_1 := h4083c.2.1
                                        have p4083_2 := h4083c.2.2.1
                                        have p4083_3 := h4083c.2.2.2
                                        linarith only [h1966, h1968, h1969, hc45, hlam, hphi, ht23, ht34, p4083_1, u2ehi3]
                                      · have p4083_0 := h4083c.1
                                        have p4083_1 := h4083c.2.1
                                        have p4083_2 := h4083c.2.2.1
                                        have p4083_3 := h4083c.2.2.2
                                        linarith only [hlam, p4083_0]
                                    · linarith only [h1966, h1968, h1969, h4082, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4041_1, u2ehi3]
                                    · rcases h5bigk with h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c | h4110c
                                      · have p4110_0 := h4110c.1
                                        have p4110_1 := h4110c.2.1
                                        have p4110_2 := h4110c.2.2.1
                                        have p4110_3 := h4110c.2.2.2
                                        linarith only [hlam, p4110_0]
                                      · have p4110_0 := h4110c.1
                                        have p4110_1 := h4110c.2.1
                                        have p4110_2 := h4110c.2.2.1
                                        have p4110_3 := h4110c.2.2.2
                                        linarith only [h1728, hlam, p4110_1]
                                      · have p4110_0 := h4110c.1
                                        have p4110_1 := h4110c.2.1
                                        have p4110_2 := h4110c.2.2.1
                                        have p4110_3 := h4110c.2.2.2
                                        linarith only [h0, h4034, h4035, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4041_1, p4110_1, u2ehi3]
                                      · have p4110_0 := h4110c.1
                                        have p4110_1 := h4110c.2.1
                                        have p4110_2 := h4110c.2.2.1
                                        have p4110_3 := h4110c.2.2.2
                                        linarith only [h1969, hlam, p4110_1]
                                      · have p4110_0 := h4110c.1
                                        have p4110_1 := h4110c.2.1
                                        have p4110_2 := h4110c.2.2.1
                                        have p4110_3 := h4110c.2.2.2
                                        linarith only [h3682, hlam, p4110_1]
                                      · have p4110_0 := h4110c.1
                                        have p4110_1 := h4110c.2.1
                                        have p4110_2 := h4110c.2.2.1
                                        have p4110_3 := h4110c.2.2.2
                                        linarith only [h1728, hc01, hc15, hlam, hphi, p4110_1]
                                      · have p4110_0 := h4110c.1
                                        have p4110_1 := h4110c.2.1
                                        have p4110_2 := h4110c.2.2.1
                                        have p4110_3 := h4110c.2.2.2
                                        linarith only [hlam, p4110_0]
                                      · have p4110_0 := h4110c.1
                                        have p4110_1 := h4110c.2.1
                                        have p4110_2 := h4110c.2.2.1
                                        have p4110_3 := h4110c.2.2.2
                                        linarith only [h3686, h4034, h4035, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4110_1, u2ehi3]
                                      · have p4110_0 := h4110c.1
                                        have p4110_1 := h4110c.2.1
                                        have p4110_2 := h4110c.2.2.1
                                        have p4110_3 := h4110c.2.2.2
                                        linarith only [h3688, hlam, p4110_1]
                                      · have p4110_0 := h4110c.1
                                        have p4110_1 := h4110c.2.1
                                        have p4110_2 := h4110c.2.2.1
                                        have p4110_3 := h4110c.2.2.2
                                        linarith only [h4032, hlam, p4110_1]
                                      · have p4110_0 := h4110c.1
                                        have p4110_1 := h4110c.2.1
                                        have p4110_2 := h4110c.2.2.1
                                        have p4110_3 := h4110c.2.2.2
                                        linarith only [h1967, hlam, p4110_1]
                                      · have p4110_0 := h4110c.1
                                        have p4110_1 := h4110c.2.1
                                        have p4110_2 := h4110c.2.2.1
                                        have p4110_3 := h4110c.2.2.2
                                        linarith only [h3686, hlam, p4110_1]
                                      · have p4110_0 := h4110c.1
                                        have p4110_1 := h4110c.2.1
                                        have p4110_2 := h4110c.2.2.1
                                        have p4110_3 := h4110c.2.2.2
                                        linarith only [hlam, p4110_0]
                                      · have p4110_0 := h4110c.1
                                        have p4110_1 := h4110c.2.1
                                        have p4110_2 := h4110c.2.2.1
                                        have p4110_3 := h4110c.2.2.2
                                        linarith only [h4035, hlam, p4110_1]
                                      · have p4110_0 := h4110c.1
                                        have p4110_1 := h4110c.2.1
                                        have p4110_2 := h4110c.2.2.1
                                        have p4110_3 := h4110c.2.2.2
                                        linarith only [h4037, hlam, p4110_1]
                                      · have p4110_0 := h4110c.1
                                        have p4110_1 := h4110c.2.1
                                        have p4110_2 := h4110c.2.2.1
                                        have p4110_3 := h4110c.2.2.2
                                        linarith only [h1967, h4034, h4035, hc35, hlam, hphi, ht23, p4110_1, u2ehi3]
                                      · have p4110_0 := h4110c.1
                                        have p4110_1 := h4110c.2.1
                                        have p4110_2 := h4110c.2.2.1
                                        have p4110_3 := h4110c.2.2.2
                                        linarith only [h1728, hc01, hc35, hlam, hphi, ht12, ht23, p4110_1]
                                      · have p4110_0 := h4110c.1
                                        have p4110_1 := h4110c.2.1
                                        have p4110_2 := h4110c.2.2.1
                                        have p4110_3 := h4110c.2.2.2
                                        linarith only [h4034, h4035, hc35, hlam, hphi, ht23, p4110_1, u2ehi3]
                                      · have p4110_0 := h4110c.1
                                        have p4110_1 := h4110c.2.1
                                        have p4110_2 := h4110c.2.2.1
                                        have p4110_3 := h4110c.2.2.2
                                        linarith only [hlam, p4110_0]
                                      · have p4110_0 := h4110c.1
                                        have p4110_1 := h4110c.2.1
                                        have p4110_2 := h4110c.2.2.1
                                        have p4110_3 := h4110c.2.2.2
                                        linarith only [h4039, hlam, p4110_1]
                                      · have p4110_0 := h4110c.1
                                        have p4110_1 := h4110c.2.1
                                        have p4110_2 := h4110c.2.2.1
                                        have p4110_3 := h4110c.2.2.2
                                        linarith only [h1967, h4034, h4035, hc45, hlam, hphi, ht23, ht34, p4110_1, u2ehi3]
                                      · have p4110_0 := h4110c.1
                                        have p4110_1 := h4110c.2.1
                                        have p4110_2 := h4110c.2.2.1
                                        have p4110_3 := h4110c.2.2.2
                                        linarith only [h0, h1414, h1967, h3688, h4034, h4035, hc01, hc12, hc45, hlam, hphi, ht23, ht34, p4041_1, p4110_1, u2ehi3]
                                      · have p4110_0 := h4110c.1
                                        have p4110_1 := h4110c.2.1
                                        have p4110_2 := h4110c.2.2.1
                                        have p4110_3 := h4110c.2.2.2
                                        linarith only [h4034, h4035, hc45, hlam, hphi, ht23, ht34, p4110_1, u2ehi3]
                                      · have p4110_0 := h4110c.1
                                        have p4110_1 := h4110c.2.1
                                        have p4110_2 := h4110c.2.2.1
                                        have p4110_3 := h4110c.2.2.2
                                        linarith only [h1966, h1968, h1969, hc45, hlam, hphi, ht23, ht34, p4110_1, u2ehi3]
                                      · have p4110_0 := h4110c.1
                                        have p4110_1 := h4110c.2.1
                                        have p4110_2 := h4110c.2.2.1
                                        have p4110_3 := h4110c.2.2.2
                                        linarith only [hlam, p4110_0]
                                    · rcases h5bigk with h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c | h4136c
                                      · have p4136_0 := h4136c.1
                                        have p4136_1 := h4136c.2.1
                                        have p4136_2 := h4136c.2.2.1
                                        have p4136_3 := h4136c.2.2.2
                                        linarith only [hlam, p4136_0]
                                      · have p4136_0 := h4136c.1
                                        have p4136_1 := h4136c.2.1
                                        have p4136_2 := h4136c.2.2.1
                                        have p4136_3 := h4136c.2.2.2
                                        linarith only [h1728, hlam, p4136_1]
                                      · have p4136_0 := h4136c.1
                                        have p4136_1 := h4136c.2.1
                                        have p4136_2 := h4136c.2.2.1
                                        have p4136_3 := h4136c.2.2.2
                                        linarith only [h0, h4034, h4035, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4041_1, p4136_1, u2ehi3]
                                      · have p4136_0 := h4136c.1
                                        have p4136_1 := h4136c.2.1
                                        have p4136_2 := h4136c.2.2.1
                                        have p4136_3 := h4136c.2.2.2
                                        linarith only [h1969, hlam, p4136_1]
                                      · have p4136_0 := h4136c.1
                                        have p4136_1 := h4136c.2.1
                                        have p4136_2 := h4136c.2.2.1
                                        have p4136_3 := h4136c.2.2.2
                                        linarith only [h3682, hlam, p4136_1]
                                      · have p4136_0 := h4136c.1
                                        have p4136_1 := h4136c.2.1
                                        have p4136_2 := h4136c.2.2.1
                                        have p4136_3 := h4136c.2.2.2
                                        linarith only [h1728, hc01, hc15, hlam, hphi, p4136_1]
                                      · have p4136_0 := h4136c.1
                                        have p4136_1 := h4136c.2.1
                                        have p4136_2 := h4136c.2.2.1
                                        have p4136_3 := h4136c.2.2.2
                                        linarith only [hlam, p4136_0]
                                      · have p4136_0 := h4136c.1
                                        have p4136_1 := h4136c.2.1
                                        have p4136_2 := h4136c.2.2.1
                                        have p4136_3 := h4136c.2.2.2
                                        linarith only [h3686, h4034, h4035, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4136_1, u2ehi3]
                                      · have p4136_0 := h4136c.1
                                        have p4136_1 := h4136c.2.1
                                        have p4136_2 := h4136c.2.2.1
                                        have p4136_3 := h4136c.2.2.2
                                        linarith only [h3688, hlam, p4136_1]
                                      · have p4136_0 := h4136c.1
                                        have p4136_1 := h4136c.2.1
                                        have p4136_2 := h4136c.2.2.1
                                        have p4136_3 := h4136c.2.2.2
                                        linarith only [h4032, hlam, p4136_1]
                                      · have p4136_0 := h4136c.1
                                        have p4136_1 := h4136c.2.1
                                        have p4136_2 := h4136c.2.2.1
                                        have p4136_3 := h4136c.2.2.2
                                        linarith only [h1967, hlam, p4136_1]
                                      · have p4136_0 := h4136c.1
                                        have p4136_1 := h4136c.2.1
                                        have p4136_2 := h4136c.2.2.1
                                        have p4136_3 := h4136c.2.2.2
                                        linarith only [h3686, hlam, p4136_1]
                                      · have p4136_0 := h4136c.1
                                        have p4136_1 := h4136c.2.1
                                        have p4136_2 := h4136c.2.2.1
                                        have p4136_3 := h4136c.2.2.2
                                        linarith only [hlam, p4136_0]
                                      · have p4136_0 := h4136c.1
                                        have p4136_1 := h4136c.2.1
                                        have p4136_2 := h4136c.2.2.1
                                        have p4136_3 := h4136c.2.2.2
                                        linarith only [h4035, hlam, p4136_1]
                                      · have p4136_0 := h4136c.1
                                        have p4136_1 := h4136c.2.1
                                        have p4136_2 := h4136c.2.2.1
                                        have p4136_3 := h4136c.2.2.2
                                        linarith only [h4037, hlam, p4136_1]
                                      · have p4136_0 := h4136c.1
                                        have p4136_1 := h4136c.2.1
                                        have p4136_2 := h4136c.2.2.1
                                        have p4136_3 := h4136c.2.2.2
                                        linarith only [h1967, h4034, h4035, hc35, hlam, hphi, ht23, p4136_1, u2ehi3]
                                      · have p4136_0 := h4136c.1
                                        have p4136_1 := h4136c.2.1
                                        have p4136_2 := h4136c.2.2.1
                                        have p4136_3 := h4136c.2.2.2
                                        linarith only [h1728, hc01, hc35, hlam, hphi, ht12, ht23, p4136_1]
                                      · have p4136_0 := h4136c.1
                                        have p4136_1 := h4136c.2.1
                                        have p4136_2 := h4136c.2.2.1
                                        have p4136_3 := h4136c.2.2.2
                                        linarith only [h4034, h4035, hc35, hlam, hphi, ht23, p4136_1, u2ehi3]
                                      · have p4136_0 := h4136c.1
                                        have p4136_1 := h4136c.2.1
                                        have p4136_2 := h4136c.2.2.1
                                        have p4136_3 := h4136c.2.2.2
                                        linarith only [hlam, p4136_0]
                                      · have p4136_0 := h4136c.1
                                        have p4136_1 := h4136c.2.1
                                        have p4136_2 := h4136c.2.2.1
                                        have p4136_3 := h4136c.2.2.2
                                        linarith only [h4039, hlam, p4136_1]
                                      · have p4136_0 := h4136c.1
                                        have p4136_1 := h4136c.2.1
                                        have p4136_2 := h4136c.2.2.1
                                        have p4136_3 := h4136c.2.2.2
                                        linarith only [h1967, h4034, h4035, hc45, hlam, hphi, ht23, ht34, p4136_1, u2ehi3]
                                      · have p4136_0 := h4136c.1
                                        have p4136_1 := h4136c.2.1
                                        have p4136_2 := h4136c.2.2.1
                                        have p4136_3 := h4136c.2.2.2
                                        linarith only [h0, h1414, h1967, h3688, h4034, h4035, hc01, hc12, hc45, hlam, hphi, ht23, ht34, p4041_1, p4136_1, u2ehi3]
                                      · have p4136_0 := h4136c.1
                                        have p4136_1 := h4136c.2.1
                                        have p4136_2 := h4136c.2.2.1
                                        have p4136_3 := h4136c.2.2.2
                                        linarith only [h4034, h4035, hc45, hlam, hphi, ht23, ht34, p4136_1, u2ehi3]
                                      · have p4136_0 := h4136c.1
                                        have p4136_1 := h4136c.2.1
                                        have p4136_2 := h4136c.2.2.1
                                        have p4136_3 := h4136c.2.2.2
                                        linarith only [h1966, h1968, h1969, hc45, hlam, hphi, ht23, ht34, p4136_1, u2ehi3]
                                      · have p4136_0 := h4136c.1
                                        have p4136_1 := h4136c.2.1
                                        have p4136_2 := h4136c.2.2.1
                                        have p4136_3 := h4136c.2.2.2
                                        linarith only [hlam, p4136_0]
                                    · rcases h5bigk with h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c | h4162c
                                      · have p4162_0 := h4162c.1
                                        have p4162_1 := h4162c.2.1
                                        have p4162_2 := h4162c.2.2.1
                                        have p4162_3 := h4162c.2.2.2
                                        linarith only [hlam, p4162_0]
                                      · have p4162_0 := h4162c.1
                                        have p4162_1 := h4162c.2.1
                                        have p4162_2 := h4162c.2.2.1
                                        have p4162_3 := h4162c.2.2.2
                                        linarith only [h1728, hlam, p4162_1]
                                      · have p4162_0 := h4162c.1
                                        have p4162_1 := h4162c.2.1
                                        have p4162_2 := h4162c.2.2.1
                                        have p4162_3 := h4162c.2.2.2
                                        linarith only [h0, h4034, h4035, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4041_1, p4162_1, u2ehi3]
                                      · have p4162_0 := h4162c.1
                                        have p4162_1 := h4162c.2.1
                                        have p4162_2 := h4162c.2.2.1
                                        have p4162_3 := h4162c.2.2.2
                                        linarith only [h1969, hlam, p4162_1]
                                      · have p4162_0 := h4162c.1
                                        have p4162_1 := h4162c.2.1
                                        have p4162_2 := h4162c.2.2.1
                                        have p4162_3 := h4162c.2.2.2
                                        linarith only [h3682, hlam, p4162_1]
                                      · have p4162_0 := h4162c.1
                                        have p4162_1 := h4162c.2.1
                                        have p4162_2 := h4162c.2.2.1
                                        have p4162_3 := h4162c.2.2.2
                                        linarith only [h1728, hc01, hc15, hlam, hphi, p4162_1]
                                      · have p4162_0 := h4162c.1
                                        have p4162_1 := h4162c.2.1
                                        have p4162_2 := h4162c.2.2.1
                                        have p4162_3 := h4162c.2.2.2
                                        linarith only [hlam, p4162_0]
                                      · have p4162_0 := h4162c.1
                                        have p4162_1 := h4162c.2.1
                                        have p4162_2 := h4162c.2.2.1
                                        have p4162_3 := h4162c.2.2.2
                                        linarith only [h3686, h4034, h4035, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4162_1, u2ehi3]
                                      · have p4162_0 := h4162c.1
                                        have p4162_1 := h4162c.2.1
                                        have p4162_2 := h4162c.2.2.1
                                        have p4162_3 := h4162c.2.2.2
                                        linarith only [h3688, hlam, p4162_1]
                                      · have p4162_0 := h4162c.1
                                        have p4162_1 := h4162c.2.1
                                        have p4162_2 := h4162c.2.2.1
                                        have p4162_3 := h4162c.2.2.2
                                        linarith only [h4032, hlam, p4162_1]
                                      · have p4162_0 := h4162c.1
                                        have p4162_1 := h4162c.2.1
                                        have p4162_2 := h4162c.2.2.1
                                        have p4162_3 := h4162c.2.2.2
                                        linarith only [h1967, hlam, p4162_1]
                                      · have p4162_0 := h4162c.1
                                        have p4162_1 := h4162c.2.1
                                        have p4162_2 := h4162c.2.2.1
                                        have p4162_3 := h4162c.2.2.2
                                        linarith only [h3686, hlam, p4162_1]
                                      · have p4162_0 := h4162c.1
                                        have p4162_1 := h4162c.2.1
                                        have p4162_2 := h4162c.2.2.1
                                        have p4162_3 := h4162c.2.2.2
                                        linarith only [hlam, p4162_0]
                                      · have p4162_0 := h4162c.1
                                        have p4162_1 := h4162c.2.1
                                        have p4162_2 := h4162c.2.2.1
                                        have p4162_3 := h4162c.2.2.2
                                        linarith only [h4035, hlam, p4162_1]
                                      · have p4162_0 := h4162c.1
                                        have p4162_1 := h4162c.2.1
                                        have p4162_2 := h4162c.2.2.1
                                        have p4162_3 := h4162c.2.2.2
                                        linarith only [h4037, hlam, p4162_1]
                                      · have p4162_0 := h4162c.1
                                        have p4162_1 := h4162c.2.1
                                        have p4162_2 := h4162c.2.2.1
                                        have p4162_3 := h4162c.2.2.2
                                        linarith only [h1967, h4034, h4035, hc35, hlam, hphi, ht23, p4162_1, u2ehi3]
                                      · have p4162_0 := h4162c.1
                                        have p4162_1 := h4162c.2.1
                                        have p4162_2 := h4162c.2.2.1
                                        have p4162_3 := h4162c.2.2.2
                                        linarith only [h1728, hc01, hc35, hlam, hphi, ht12, ht23, p4162_1]
                                      · have p4162_0 := h4162c.1
                                        have p4162_1 := h4162c.2.1
                                        have p4162_2 := h4162c.2.2.1
                                        have p4162_3 := h4162c.2.2.2
                                        linarith only [h4034, h4035, hc35, hlam, hphi, ht23, p4162_1, u2ehi3]
                                      · have p4162_0 := h4162c.1
                                        have p4162_1 := h4162c.2.1
                                        have p4162_2 := h4162c.2.2.1
                                        have p4162_3 := h4162c.2.2.2
                                        linarith only [hlam, p4162_0]
                                      · have p4162_0 := h4162c.1
                                        have p4162_1 := h4162c.2.1
                                        have p4162_2 := h4162c.2.2.1
                                        have p4162_3 := h4162c.2.2.2
                                        linarith only [h4039, hlam, p4162_1]
                                      · have p4162_0 := h4162c.1
                                        have p4162_1 := h4162c.2.1
                                        have p4162_2 := h4162c.2.2.1
                                        have p4162_3 := h4162c.2.2.2
                                        linarith only [h1967, h4034, h4035, hc45, hlam, hphi, ht23, ht34, p4162_1, u2ehi3]
                                      · have p4162_0 := h4162c.1
                                        have p4162_1 := h4162c.2.1
                                        have p4162_2 := h4162c.2.2.1
                                        have p4162_3 := h4162c.2.2.2
                                        linarith only [h0, h1414, h1967, h3688, h4034, h4035, hc01, hc12, hc45, hlam, hphi, ht23, ht34, p4041_1, p4162_1, u2ehi3]
                                      · have p4162_0 := h4162c.1
                                        have p4162_1 := h4162c.2.1
                                        have p4162_2 := h4162c.2.2.1
                                        have p4162_3 := h4162c.2.2.2
                                        linarith only [h4034, h4035, hc45, hlam, hphi, ht23, ht34, p4162_1, u2ehi3]
                                      · have p4162_0 := h4162c.1
                                        have p4162_1 := h4162c.2.1
                                        have p4162_2 := h4162c.2.2.1
                                        have p4162_3 := h4162c.2.2.2
                                        linarith only [h1966, h1968, h1969, hc45, hlam, hphi, ht23, ht34, p4162_1, u2ehi3]
                                      · have p4162_0 := h4162c.1
                                        have p4162_1 := h4162c.2.1
                                        have p4162_2 := h4162c.2.2.1
                                        have p4162_3 := h4162c.2.2.2
                                        linarith only [hlam, p4162_0]
                            · linarith only [h1967, h4075, hlam]
                        · have p4041_0 := h4041c.1
                          have p4041_1 := h4041c.2.1
                          have p4041_2 := h4041c.2.2.1
                          have p4041_3 := h4041c.2.2.2
                          linarith only [h1969, hc01, hc35, hlam, hphi, ht12, ht23, p4041_1]
                        · have p4041_0 := h4041c.1
                          have p4041_1 := h4041c.2.1
                          have p4041_2 := h4041c.2.2.1
                          have p4041_3 := h4041c.2.2.2
                          linarith only [h1965, hlam, p4041_1]
                        · have p4041_0 := h4041c.1
                          have p4041_1 := h4041c.2.1
                          have p4041_2 := h4041c.2.2.1
                          have p4041_3 := h4041c.2.2.2
                          linarith only [hlam, p4041_0]
                        · have p4041_0 := h4041c.1
                          have p4041_1 := h4041c.2.1
                          have p4041_2 := h4041c.2.2.1
                          have p4041_3 := h4041c.2.2.2
                          linarith only [h1966, h1969, hc35, hlam, hphi, ht23, p4041_1, u2ehi3]
                        · have p4041_0 := h4041c.1
                          have p4041_1 := h4041c.2.1
                          have p4041_2 := h4041c.2.2.1
                          have p4041_3 := h4041c.2.2.2
                          linarith only [h1969, hlam, p4041_1]
                        · have p4041_0 := h4041c.1
                          have p4041_1 := h4041c.2.1
                          have p4041_2 := h4041c.2.2.1
                          have p4041_3 := h4041c.2.2.2
                          linarith only [h1414, h1968, h3688, h4039, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4041_1]
                        · have p4041_0 := h4041c.1
                          have p4041_1 := h4041c.2.1
                          have p4041_2 := h4041c.2.2.1
                          have p4041_3 := h4041c.2.2.2
                          linarith only [h1966, hlam, p4041_0]
                        · have p4041_0 := h4041c.1
                          have p4041_1 := h4041c.2.1
                          have p4041_2 := h4041c.2.2.1
                          have p4041_3 := h4041c.2.2.2
                          linarith only [h1968, hlam, p4041_0]
                        · have p4041_0 := h4041c.1
                          have p4041_1 := h4041c.2.1
                          have p4041_2 := h4041c.2.2.1
                          have p4041_3 := h4041c.2.2.2
                          linarith only [hlam, p4041_0]
                        · have p4041_0 := h4041c.1
                          have p4041_1 := h4041c.2.1
                          have p4041_2 := h4041c.2.2.1
                          have p4041_3 := h4041c.2.2.2
                          linarith only [h3682, hlam, p4041_0]
                        · have p4041_0 := h4041c.1
                          have p4041_1 := h4041c.2.1
                          have p4041_2 := h4041c.2.2.1
                          have p4041_3 := h4041c.2.2.2
                          rcases p4041_3 (m.d 0 1) (by simp) with h4199 | h4199
                          · linarith only [h1728, h4199, hlam]
                          · rcases p4041_3 (m.d 0 2) (by simp) with h4201 | h4201
                            · rcases p4041_3 (m.d 0 3) (by simp) with h4202 | h4202
                              · linarith only [h1969, h4202, hlam]
                              · linarith only [h1414, h4202, hlam]
                            · linarith only [h0, h4201, hlam]
                        · have p4041_0 := h4041c.1
                          have p4041_1 := h4041c.2.1
                          have p4041_2 := h4041c.2.2.1
                          have p4041_3 := h4041c.2.2.2
                          linarith only [h1967, hlam, p4041_1]
                        · have p4041_0 := h4041c.1
                          have p4041_1 := h4041c.2.1
                          have p4041_2 := h4041c.2.2.1
                          have p4041_3 := h4041c.2.2.2
                          linarith only [h1965, h1969, h4034, h4039, hc45, hlam, hphi, ht23, ht34, p4041_1, u2ehi3]
                        · have p4041_0 := h4041c.1
                          have p4041_1 := h4041c.2.1
                          have p4041_2 := h4041c.2.2.1
                          have p4041_3 := h4041c.2.2.2
                          linarith only [h1966, h1969, h4039, hc45, hlam, hphi, ht23, ht34, p4041_1, u2ehi3]
                        · have p4041_0 := h4041c.1
                          have p4041_1 := h4041c.2.1
                          have p4041_2 := h4041c.2.2.1
                          have p4041_3 := h4041c.2.2.2
                          linarith only [hlam, p4041_0]
                · linarith only [h1414, h1968, h3688, h4034, hc35, hlam, hphi, ht23, u2ehi2]
          · linarith only [h1414, h1968, h3687, hlam]
        · linarith only [h0, h1965, h3686, hc25, hlam, hphi, u2ehi2]
      · linarith only [h0, h1965, h3685, hc24, hlam, hphi, u2ehi2]
    · linarith only [h0, h1965, h3684, hlam]

set_option maxHeartbeats 6104000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_s5_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1414 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1728 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg1965 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg1966 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg1967 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1968 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h1414 := hg1414
  have h1728 := hg1728
  have h1965 := hg1965
  have h1966 := hg1966
  have h1967 := hg1967
  rcases m.htr 0 3 5 (by decide) (by decide) with h1969 | h1969
  · exact r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x0 m hb0 hb2 hb5 hg0 hg1414 hg1728 hg1965 hg1966 hg1967 h1968 h1969
  · exact r1l7_10_12_25_L_I_L_R_H_I_s5_x0_x1 m hb0 hb2 hb5 hg0 hg1414 hg1728 hg1965 hg1966 hg1967 h1968 h1969

end R2N4
