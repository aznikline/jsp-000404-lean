import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_10S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8068000 in
set_option maxHeartbeats 8068000 in
theorem r1l7_12_24_L_I_H_I_s4_x1_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h2892 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 1 2 3 (by decide) (by decide) with h3691 | h3691
  · rcases m.htr 1 2 4 (by decide) (by decide) with h3692 | h3692
    · rcases m.htr 1 2 5 (by decide) (by decide) with h3693 | h3693
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3694 | h3694
        · linarith only [h1, h3694, h5, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3696 | h3696
          · linarith only [h1, h2892, h3696, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3698 | h3698
            · linarith only [h2, h3698, h5, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3700 | h3700
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3701 | h3701
                · linarith only [h0, h1, h2892, h3, h3691, h3694, h3700, h3701, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · linarith only [h3698, h3700, h3701, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3704 | h3704
                · linarith only [h2892, h3, h3704, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3706 | h3706
                  · rcases h2bigk with h3707c | h3707c | h3707c | h3707c | h3707c | h3707c | h3707c | h3707c | h3707c | h3707c | h3707c | h3707c | h3707c | h3707c | h3707c | h3707c | h3707c | h3707c | h3707c | h3707c | h3707c | h3707c | h3707c | h3707c | h3707c
                    · have p3707_0 := h3707c.1
                      have p3707_1 := h3707c.2.1
                      have p3707_2 := h3707c.2.2.1
                      have p3707_3 := h3707c.2.2.2
                      linarith only [hlam, p3707_0]
                    · have p3707_0 := h3707c.1
                      have p3707_1 := h3707c.2.1
                      have p3707_2 := h3707c.2.2.1
                      have p3707_3 := h3707c.2.2.2
                      rcases p3707_3 (m.d 0 2) (by simp) with h3709 | h3709
                      · rcases p3707_3 (m.d 1 2) (by simp) with h3710 | h3710
                        · linarith only [h0, h3710, hlam]
                        · rcases p3707_3 (m.d 2 3) (by simp) with h3712 | h3712
                          · linarith only [h2, h3712, hlam]
                          · rcases p3707_3 (m.d 2 4) (by simp) with h3714 | h3714
                            · linarith only [h3, h3714, hlam]
                            · rcases p3707_3 (m.d 2 5) (by simp) with h3716 | h3716
                              · linarith only [h3716, h4, hlam]
                              · rcases h4bigk with h3718c | h3718c | h3718c | h3718c | h3718c | h3718c | h3718c | h3718c | h3718c | h3718c | h3718c | h3718c | h3718c | h3718c | h3718c | h3718c | h3718c | h3718c | h3718c | h3718c | h3718c | h3718c | h3718c | h3718c | h3718c
                                · have p3718_0 := h3718c.1
                                  have p3718_1 := h3718c.2.1
                                  have p3718_2 := h3718c.2.2.1
                                  have p3718_3 := h3718c.2.2.2
                                  linarith only [hlam, p3718_0]
                                · have p3718_0 := h3718c.1
                                  have p3718_1 := h3718c.2.1
                                  have p3718_2 := h3718c.2.2.1
                                  have p3718_3 := h3718c.2.2.2
                                  linarith only [h2892, h3694, h3706, hc13, hc34, hlam, hphi, p3718_1]
                                · have p3718_0 := h3718c.1
                                  have p3718_1 := h3718c.2.1
                                  have p3718_2 := h3718c.2.2.1
                                  have p3718_3 := h3718c.2.2.2
                                  linarith only [h2892, h3698, h3706, hc23, hc34, hlam, hphi, p3718_1]
                                · have p3718_0 := h3718c.1
                                  have p3718_1 := h3718c.2.1
                                  have p3718_2 := h3718c.2.2.1
                                  have p3718_3 := h3718c.2.2.2
                                  linarith only [h5, hlam, p3718_1]
                                · have p3718_0 := h3718c.1
                                  have p3718_1 := h3718c.2.1
                                  have p3718_2 := h3718c.2.2.1
                                  have p3718_3 := h3718c.2.2.2
                                  linarith only [h2892, hlam, p3718_0]
                                · have p3718_0 := h3718c.1
                                  have p3718_1 := h3718c.2.1
                                  have p3718_2 := h3718c.2.2.1
                                  have p3718_3 := h3718c.2.2.2
                                  linarith only [h1, hlam, p3718_0]
                                · have p3718_0 := h3718c.1
                                  have p3718_1 := h3718c.2.1
                                  have p3718_2 := h3718c.2.2.1
                                  have p3718_3 := h3718c.2.2.2
                                  linarith only [hlam, p3718_0]
                                · have p3718_0 := h3718c.1
                                  have p3718_1 := h3718c.2.1
                                  have p3718_2 := h3718c.2.2.1
                                  have p3718_3 := h3718c.2.2.2
                                  linarith only [h1, h3698, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3718_1]
                                · have p3718_0 := h3718c.1
                                  have p3718_1 := h3718c.2.1
                                  have p3718_2 := h3718c.2.2.1
                                  have p3718_3 := h3718c.2.2.2
                                  linarith only [h3694, hlam, p3718_1]
                                · have p3718_0 := h3718c.1
                                  have p3718_1 := h3718c.2.1
                                  have p3718_2 := h3718c.2.2.1
                                  have p3718_3 := h3718c.2.2.2
                                  linarith only [h3696, hlam, p3718_0]
                                · have p3718_0 := h3718c.1
                                  have p3718_1 := h3718c.2.1
                                  have p3718_2 := h3718c.2.2.1
                                  have p3718_3 := h3718c.2.2.2
                                  linarith only [h3, hlam, p3718_0]
                                · have p3718_0 := h3718c.1
                                  have p3718_1 := h3718c.2.1
                                  have p3718_2 := h3718c.2.2.1
                                  have p3718_3 := h3718c.2.2.2
                                  linarith only [h3692, hlam, p3718_0]
                                · have p3718_0 := h3718c.1
                                  have p3718_1 := h3718c.2.1
                                  have p3718_2 := h3718c.2.2.1
                                  have p3718_3 := h3718c.2.2.2
                                  linarith only [hlam, p3718_0]
                                · have p3718_0 := h3718c.1
                                  have p3718_1 := h3718c.2.1
                                  have p3718_2 := h3718c.2.2.1
                                  have p3718_3 := h3718c.2.2.2
                                  linarith only [h3698, hlam, p3718_1]
                                · have p3718_0 := h3718c.1
                                  have p3718_1 := h3718c.2.1
                                  have p3718_2 := h3718c.2.2.1
                                  have p3718_3 := h3718c.2.2.2
                                  linarith only [h3704, hlam, p3718_0]
                                · have p3718_0 := h3718c.1
                                  have p3718_1 := h3718c.2.1
                                  have p3718_2 := h3718c.2.2.1
                                  have p3718_3 := h3718c.2.2.2
                                  linarith only [h5, hc03, hc34, hlam, hphi, p3718_1]
                                · have p3718_0 := h3718c.1
                                  have p3718_1 := h3718c.2.1
                                  have p3718_2 := h3718c.2.2.1
                                  have p3718_3 := h3718c.2.2.2
                                  linarith only [h3692, h3698, hc23, hc34, hlam, hphi, p3718_1]
                                · have p3718_0 := h3718c.1
                                  have p3718_1 := h3718c.2.1
                                  have p3718_2 := h3718c.2.2.1
                                  have p3718_3 := h3718c.2.2.2
                                  linarith only [h3698, hc23, hc34, hlam, hphi, p3718_1]
                                · have p3718_0 := h3718c.1
                                  have p3718_1 := h3718c.2.1
                                  have p3718_2 := h3718c.2.2.1
                                  have p3718_3 := h3718c.2.2.2
                                  linarith only [hlam, p3718_0]
                                · have p3718_0 := h3718c.1
                                  have p3718_1 := h3718c.2.1
                                  have p3718_2 := h3718c.2.2.1
                                  have p3718_3 := h3718c.2.2.2
                                  linarith only [h1, h2892, h3692, h3698, hc23, hc34, hlam, hphi, p3718_1]
                                · have p3718_0 := h3718c.1
                                  have p3718_1 := h3718c.2.1
                                  have p3718_2 := h3718c.2.2.1
                                  have p3718_3 := h3718c.2.2.2
                                  linarith only [h1, h3692, h3698, h3706, hc23, hc35, hlam, hphi, p3718_1]
                                · have p3718_0 := h3718c.1
                                  have p3718_1 := h3718c.2.1
                                  have p3718_2 := h3718c.2.2.1
                                  have p3718_3 := h3718c.2.2.2
                                  linarith only [h3692, h3698, h3706, hc23, hc35, hlam, hphi, p3718_1]
                                · have p3718_0 := h3718c.1
                                  have p3718_1 := h3718c.2.1
                                  have p3718_2 := h3718c.2.2.1
                                  have p3718_3 := h3718c.2.2.2
                                  linarith only [h3698, h3706, hc23, hc35, hlam, hphi, p3718_1]
                                · have p3718_0 := h3718c.1
                                  have p3718_1 := h3718c.2.1
                                  have p3718_2 := h3718c.2.2.1
                                  have p3718_3 := h3718c.2.2.2
                                  linarith only [h3706, hlam, p3718_0]
                                · have p3718_0 := h3718c.1
                                  have p3718_1 := h3718c.2.1
                                  have p3718_2 := h3718c.2.2.1
                                  have p3718_3 := h3718c.2.2.2
                                  linarith only [hlam, p3718_0]
                      · linarith only [h0, h3709, hlam]
                    · have p3707_0 := h3707c.1
                      have p3707_1 := h3707c.2.1
                      have p3707_2 := h3707c.2.2.1
                      have p3707_3 := h3707c.2.2.2
                      rcases p3707_3 (m.d 0 2) (by simp) with h3745 | h3745
                      · rcases p3707_3 (m.d 1 2) (by simp) with h3746 | h3746
                        · linarith only [h0, h3746, hlam]
                        · linarith only [h3691, h3746, hlam]
                      · linarith only [h3745, hlam, p3707_0]
                    · have p3707_0 := h3707c.1
                      have p3707_1 := h3707c.2.1
                      have p3707_2 := h3707c.2.2.1
                      have p3707_3 := h3707c.2.2.2
                      rcases p3707_3 (m.d 0 2) (by simp) with h3750 | h3750
                      · rcases p3707_3 (m.d 1 2) (by simp) with h3751 | h3751
                        · linarith only [h0, h3751, hlam]
                        · linarith only [h3692, h3751, hlam]
                      · linarith only [h3750, hlam, p3707_0]
                    · have p3707_0 := h3707c.1
                      have p3707_1 := h3707c.2.1
                      have p3707_2 := h3707c.2.2.1
                      have p3707_3 := h3707c.2.2.2
                      rcases p3707_3 (m.d 0 2) (by simp) with h3755 | h3755
                      · rcases p3707_3 (m.d 1 2) (by simp) with h3756 | h3756
                        · linarith only [h0, h3756, hlam]
                        · linarith only [h3693, h3756, hlam]
                      · linarith only [h3755, hlam, p3707_0]
                    · have p3707_0 := h3707c.1
                      have p3707_1 := h3707c.2.1
                      have p3707_2 := h3707c.2.2.1
                      have p3707_3 := h3707c.2.2.2
                      linarith only [h0, hlam, p3707_1]
                    · have p3707_0 := h3707c.1
                      have p3707_1 := h3707c.2.1
                      have p3707_2 := h3707c.2.2.1
                      have p3707_3 := h3707c.2.2.2
                      linarith only [hlam, p3707_0]
                    · have p3707_0 := h3707c.1
                      have p3707_1 := h3707c.2.1
                      have p3707_2 := h3707c.2.2.1
                      have p3707_3 := h3707c.2.2.2
                      rcases p3707_3 (m.d 0 2) (by simp) with h3762 | h3762
                      · rcases p3707_3 (m.d 1 2) (by simp) with h3763 | h3763
                        · rcases p3707_3 (m.d 2 3) (by simp) with h3764 | h3764
                          · linarith only [h3764, hlam, p3707_0]
                          · rcases p3707_3 (m.d 2 4) (by simp) with h3766 | h3766
                            · linarith only [h3692, h3766, hlam]
                            · linarith only [h3698, h3766, hlam]
                        · linarith only [h3763, hlam, p3707_0]
                      · linarith only [h2, h3762, hlam]
                    · have p3707_0 := h3707c.1
                      have p3707_1 := h3707c.2.1
                      have p3707_2 := h3707c.2.2.1
                      have p3707_3 := h3707c.2.2.2
                      rcases p3707_3 (m.d 0 2) (by simp) with h3771 | h3771
                      · rcases p3707_3 (m.d 1 2) (by simp) with h3772 | h3772
                        · rcases p3707_3 (m.d 2 3) (by simp) with h3773 | h3773
                          · linarith only [h3691, h3773, hlam]
                          · rcases p3707_3 (m.d 2 4) (by simp) with h3775 | h3775
                            · linarith only [h3775, hlam, p3707_0]
                            · rcases p3707_3 (m.d 2 5) (by simp) with h3777 | h3777
                              · linarith only [h3693, h3777, hlam]
                              · linarith only [h3704, h3777, hlam]
                        · linarith only [h3772, hlam, p3707_0]
                      · linarith only [h3, h3771, hlam]
                    · have p3707_0 := h3707c.1
                      have p3707_1 := h3707c.2.1
                      have p3707_2 := h3707c.2.2.1
                      have p3707_3 := h3707c.2.2.2
                      rcases p3707_3 (m.d 0 2) (by simp) with h3782 | h3782
                      · rcases p3707_3 (m.d 1 2) (by simp) with h3783 | h3783
                        · rcases p3707_3 (m.d 2 3) (by simp) with h3784 | h3784
                          · linarith only [h3691, h3784, hlam]
                          · rcases p3707_3 (m.d 2 4) (by simp) with h3786 | h3786
                            · linarith only [h3692, h3786, hlam]
                            · rcases p3707_3 (m.d 2 5) (by simp) with h3788 | h3788
                              · linarith only [h3788, hlam, p3707_0]
                              · rcases h4bigk with h3790c | h3790c | h3790c | h3790c | h3790c | h3790c | h3790c | h3790c | h3790c | h3790c | h3790c | h3790c | h3790c | h3790c | h3790c | h3790c | h3790c | h3790c | h3790c | h3790c | h3790c | h3790c | h3790c | h3790c | h3790c
                                · have p3790_0 := h3790c.1
                                  have p3790_1 := h3790c.2.1
                                  have p3790_2 := h3790c.2.2.1
                                  have p3790_3 := h3790c.2.2.2
                                  linarith only [hlam, p3790_0]
                                · have p3790_0 := h3790c.1
                                  have p3790_1 := h3790c.2.1
                                  have p3790_2 := h3790c.2.2.1
                                  have p3790_3 := h3790c.2.2.2
                                  linarith only [h3692, h3698, h5, hc23, hc34, hlam, hphi, p3790_1]
                                · have p3790_0 := h3790c.1
                                  have p3790_1 := h3790c.2.1
                                  have p3790_2 := h3790c.2.2.1
                                  have p3790_3 := h3790c.2.2.2
                                  linarith only [h3698, h5, hc23, hc34, hlam, hphi, p3790_1]
                                · have p3790_0 := h3790c.1
                                  have p3790_1 := h3790c.2.1
                                  have p3790_2 := h3790c.2.2.1
                                  have p3790_3 := h3790c.2.2.2
                                  linarith only [h5, hlam, p3790_1]
                                · have p3790_0 := h3790c.1
                                  have p3790_1 := h3790c.2.1
                                  have p3790_2 := h3790c.2.2.1
                                  have p3790_3 := h3790c.2.2.2
                                  linarith only [h2892, hlam, p3790_0]
                                · have p3790_0 := h3790c.1
                                  have p3790_1 := h3790c.2.1
                                  have p3790_2 := h3790c.2.2.1
                                  have p3790_3 := h3790c.2.2.2
                                  linarith only [h1, hlam, p3790_0]
                                · have p3790_0 := h3790c.1
                                  have p3790_1 := h3790c.2.1
                                  have p3790_2 := h3790c.2.2.1
                                  have p3790_3 := h3790c.2.2.2
                                  linarith only [hlam, p3790_0]
                                · have p3790_0 := h3790c.1
                                  have p3790_1 := h3790c.2.1
                                  have p3790_2 := h3790c.2.2.1
                                  have p3790_3 := h3790c.2.2.2
                                  linarith only [h1, h3698, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3790_1]
                                · have p3790_0 := h3790c.1
                                  have p3790_1 := h3790c.2.1
                                  have p3790_2 := h3790c.2.2.1
                                  have p3790_3 := h3790c.2.2.2
                                  linarith only [h3694, hlam, p3790_1]
                                · have p3790_0 := h3790c.1
                                  have p3790_1 := h3790c.2.1
                                  have p3790_2 := h3790c.2.2.1
                                  have p3790_3 := h3790c.2.2.2
                                  linarith only [h3696, hlam, p3790_0]
                                · have p3790_0 := h3790c.1
                                  have p3790_1 := h3790c.2.1
                                  have p3790_2 := h3790c.2.2.1
                                  have p3790_3 := h3790c.2.2.2
                                  linarith only [h3, hlam, p3790_0]
                                · have p3790_0 := h3790c.1
                                  have p3790_1 := h3790c.2.1
                                  have p3790_2 := h3790c.2.2.1
                                  have p3790_3 := h3790c.2.2.2
                                  linarith only [h3692, hlam, p3790_0]
                                · have p3790_0 := h3790c.1
                                  have p3790_1 := h3790c.2.1
                                  have p3790_2 := h3790c.2.2.1
                                  have p3790_3 := h3790c.2.2.2
                                  linarith only [hlam, p3790_0]
                                · have p3790_0 := h3790c.1
                                  have p3790_1 := h3790c.2.1
                                  have p3790_2 := h3790c.2.2.1
                                  have p3790_3 := h3790c.2.2.2
                                  linarith only [h3698, hlam, p3790_1]
                                · have p3790_0 := h3790c.1
                                  have p3790_1 := h3790c.2.1
                                  have p3790_2 := h3790c.2.2.1
                                  have p3790_3 := h3790c.2.2.2
                                  linarith only [h3704, hlam, p3790_0]
                                · have p3790_0 := h3790c.1
                                  have p3790_1 := h3790c.2.1
                                  have p3790_2 := h3790c.2.2.1
                                  have p3790_3 := h3790c.2.2.2
                                  linarith only [h3, h3698, hc23, hc34, hlam, hphi, p3790_1]
                                · have p3790_0 := h3790c.1
                                  have p3790_1 := h3790c.2.1
                                  have p3790_2 := h3790c.2.2.1
                                  have p3790_3 := h3790c.2.2.2
                                  linarith only [h3692, h3698, hc23, hc34, hlam, hphi, p3790_1]
                                · have p3790_0 := h3790c.1
                                  have p3790_1 := h3790c.2.1
                                  have p3790_2 := h3790c.2.2.1
                                  have p3790_3 := h3790c.2.2.2
                                  linarith only [h3698, hc23, hc34, hlam, hphi, p3790_1]
                                · have p3790_0 := h3790c.1
                                  have p3790_1 := h3790c.2.1
                                  have p3790_2 := h3790c.2.2.1
                                  have p3790_3 := h3790c.2.2.2
                                  linarith only [hlam, p3790_0]
                                · have p3790_0 := h3790c.1
                                  have p3790_1 := h3790c.2.1
                                  have p3790_2 := h3790c.2.2.1
                                  have p3790_3 := h3790c.2.2.2
                                  linarith only [h1, h2892, h3692, h3698, hc23, hc34, hlam, hphi, p3790_1]
                                · have p3790_0 := h3790c.1
                                  have p3790_1 := h3790c.2.1
                                  have p3790_2 := h3790c.2.2.1
                                  have p3790_3 := h3790c.2.2.2
                                  linarith only [h1, h3692, h3698, hc23, hc45, hlam, hphi, ht34, p3790_1]
                                · have p3790_0 := h3790c.1
                                  have p3790_1 := h3790c.2.1
                                  have p3790_2 := h3790c.2.2.1
                                  have p3790_3 := h3790c.2.2.2
                                  linarith only [h3692, h3698, hc23, hc45, hlam, hphi, ht34, p3790_1]
                                · have p3790_0 := h3790c.1
                                  have p3790_1 := h3790c.2.1
                                  have p3790_2 := h3790c.2.2.1
                                  have p3790_3 := h3790c.2.2.2
                                  linarith only [h3698, hc23, hc45, hlam, hphi, ht34, p3790_1]
                                · have p3790_0 := h3790c.1
                                  have p3790_1 := h3790c.2.1
                                  have p3790_2 := h3790c.2.2.1
                                  have p3790_3 := h3790c.2.2.2
                                  linarith only [h3706, hlam, p3790_0]
                                · have p3790_0 := h3790c.1
                                  have p3790_1 := h3790c.2.1
                                  have p3790_2 := h3790c.2.2.1
                                  have p3790_3 := h3790c.2.2.2
                                  linarith only [hlam, p3790_0]
                        · linarith only [h3783, hlam, p3707_0]
                      · linarith only [h3782, h4, hlam]
                    · have p3707_0 := h3707c.1
                      have p3707_1 := h3707c.2.1
                      have p3707_2 := h3707c.2.2.1
                      have p3707_3 := h3707c.2.2.2
                      linarith only [h2, hlam, p3707_0]
                    · have p3707_0 := h3707c.1
                      have p3707_1 := h3707c.2.1
                      have p3707_2 := h3707c.2.2.1
                      have p3707_3 := h3707c.2.2.2
                      linarith only [h3691, hlam, p3707_0]
                    · have p3707_0 := h3707c.1
                      have p3707_1 := h3707c.2.1
                      have p3707_2 := h3707c.2.2.1
                      have p3707_3 := h3707c.2.2.2
                      linarith only [hlam, p3707_0]
                    · have p3707_0 := h3707c.1
                      have p3707_1 := h3707c.2.1
                      have p3707_2 := h3707c.2.2.1
                      have p3707_3 := h3707c.2.2.2
                      linarith only [h3698, hlam, p3707_1]
                    · have p3707_0 := h3707c.1
                      have p3707_1 := h3707c.2.1
                      have p3707_2 := h3707c.2.2.1
                      have p3707_3 := h3707c.2.2.2
                      linarith only [h3700, hlam, p3707_1]
                    · have p3707_0 := h3707c.1
                      have p3707_1 := h3707c.2.1
                      have p3707_2 := h3707c.2.2.1
                      have p3707_3 := h3707c.2.2.2
                      linarith only [h3, hlam, p3707_0]
                    · have p3707_0 := h3707c.1
                      have p3707_1 := h3707c.2.1
                      have p3707_2 := h3707c.2.2.1
                      have p3707_3 := h3707c.2.2.2
                      linarith only [h3692, hlam, p3707_0]
                    · have p3707_0 := h3707c.1
                      have p3707_1 := h3707c.2.1
                      have p3707_2 := h3707c.2.2.1
                      have p3707_3 := h3707c.2.2.2
                      linarith only [h1, h2892, h3692, hc23, hc45, hlam, hphi, ht34, p3707_1]
                    · have p3707_0 := h3707c.1
                      have p3707_1 := h3707c.2.1
                      have p3707_2 := h3707c.2.2.1
                      have p3707_3 := h3707c.2.2.2
                      linarith only [hlam, p3707_0]
                    · have p3707_0 := h3707c.1
                      have p3707_1 := h3707c.2.1
                      have p3707_2 := h3707c.2.2.1
                      have p3707_3 := h3707c.2.2.2
                      linarith only [h3704, hlam, p3707_0]
                    · have p3707_0 := h3707c.1
                      have p3707_1 := h3707c.2.1
                      have p3707_2 := h3707c.2.2.1
                      have p3707_3 := h3707c.2.2.2
                      linarith only [h4, hlam, p3707_0]
                    · have p3707_0 := h3707c.1
                      have p3707_1 := h3707c.2.1
                      have p3707_2 := h3707c.2.2.1
                      have p3707_3 := h3707c.2.2.2
                      linarith only [h3693, hlam, p3707_0]
                    · have p3707_0 := h3707c.1
                      have p3707_1 := h3707c.2.1
                      have p3707_2 := h3707c.2.2.1
                      have p3707_3 := h3707c.2.2.2
                      linarith only [h0, h3693, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3707_1]
                    · have p3707_0 := h3707c.1
                      have p3707_1 := h3707c.2.1
                      have p3707_2 := h3707c.2.2.1
                      have p3707_3 := h3707c.2.2.2
                      linarith only [h0, h3693, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3707_1]
                    · have p3707_0 := h3707c.1
                      have p3707_1 := h3707c.2.1
                      have p3707_2 := h3707c.2.2.1
                      have p3707_3 := h3707c.2.2.2
                      linarith only [hlam, p3707_0]
                  · rcases h2bigk with h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c | h3833c
                    · have p3833_0 := h3833c.1
                      have p3833_1 := h3833c.2.1
                      have p3833_2 := h3833c.2.2.1
                      have p3833_3 := h3833c.2.2.2
                      linarith only [hlam, p3833_0]
                    · have p3833_0 := h3833c.1
                      have p3833_1 := h3833c.2.1
                      have p3833_2 := h3833c.2.2.1
                      have p3833_3 := h3833c.2.2.2
                      rcases p3833_3 (m.d 0 2) (by simp) with h3835 | h3835
                      · rcases p3833_3 (m.d 1 2) (by simp) with h3836 | h3836
                        · linarith only [h0, h3836, hlam]
                        · rcases p3833_3 (m.d 2 3) (by simp) with h3838 | h3838
                          · linarith only [h2, h3838, hlam]
                          · rcases p3833_3 (m.d 2 4) (by simp) with h3840 | h3840
                            · linarith only [h3, h3840, hlam]
                            · rcases p3833_3 (m.d 2 5) (by simp) with h3842 | h3842
                              · linarith only [h3842, h4, hlam]
                              · rcases h4bigk with h3844c | h3844c | h3844c | h3844c | h3844c | h3844c | h3844c | h3844c | h3844c | h3844c | h3844c | h3844c | h3844c | h3844c | h3844c | h3844c | h3844c | h3844c | h3844c | h3844c | h3844c | h3844c | h3844c | h3844c | h3844c
                                · have p3844_0 := h3844c.1
                                  have p3844_1 := h3844c.2.1
                                  have p3844_2 := h3844c.2.2.1
                                  have p3844_3 := h3844c.2.2.2
                                  linarith only [hlam, p3844_0]
                                · have p3844_0 := h3844c.1
                                  have p3844_1 := h3844c.2.1
                                  have p3844_2 := h3844c.2.2.1
                                  have p3844_3 := h3844c.2.2.2
                                  linarith only [h3706, h5, hc14, hc45, hlam, hphi, p3844_1]
                                · have p3844_0 := h3844c.1
                                  have p3844_1 := h3844c.2.1
                                  have p3844_2 := h3844c.2.2.1
                                  have p3844_3 := h3844c.2.2.2
                                  linarith only [h3698, h3706, h5, hc23, hc45, hlam, hphi, ht34, p3844_1]
                                · have p3844_0 := h3844c.1
                                  have p3844_1 := h3844c.2.1
                                  have p3844_2 := h3844c.2.2.1
                                  have p3844_3 := h3844c.2.2.2
                                  linarith only [h5, hlam, p3844_1]
                                · have p3844_0 := h3844c.1
                                  have p3844_1 := h3844c.2.1
                                  have p3844_2 := h3844c.2.2.1
                                  have p3844_3 := h3844c.2.2.2
                                  linarith only [h2892, hlam, p3844_0]
                                · have p3844_0 := h3844c.1
                                  have p3844_1 := h3844c.2.1
                                  have p3844_2 := h3844c.2.2.1
                                  have p3844_3 := h3844c.2.2.2
                                  linarith only [h1, hlam, p3844_0]
                                · have p3844_0 := h3844c.1
                                  have p3844_1 := h3844c.2.1
                                  have p3844_2 := h3844c.2.2.1
                                  have p3844_3 := h3844c.2.2.2
                                  linarith only [hlam, p3844_0]
                                · have p3844_0 := h3844c.1
                                  have p3844_1 := h3844c.2.1
                                  have p3844_2 := h3844c.2.2.1
                                  have p3844_3 := h3844c.2.2.2
                                  linarith only [h1, h3698, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3844_1]
                                · have p3844_0 := h3844c.1
                                  have p3844_1 := h3844c.2.1
                                  have p3844_2 := h3844c.2.2.1
                                  have p3844_3 := h3844c.2.2.2
                                  linarith only [h3694, hlam, p3844_1]
                                · have p3844_0 := h3844c.1
                                  have p3844_1 := h3844c.2.1
                                  have p3844_2 := h3844c.2.2.1
                                  have p3844_3 := h3844c.2.2.2
                                  linarith only [h3696, hlam, p3844_0]
                                · have p3844_0 := h3844c.1
                                  have p3844_1 := h3844c.2.1
                                  have p3844_2 := h3844c.2.2.1
                                  have p3844_3 := h3844c.2.2.2
                                  linarith only [h3, hlam, p3844_0]
                                · have p3844_0 := h3844c.1
                                  have p3844_1 := h3844c.2.1
                                  have p3844_2 := h3844c.2.2.1
                                  have p3844_3 := h3844c.2.2.2
                                  linarith only [h3692, hlam, p3844_0]
                                · have p3844_0 := h3844c.1
                                  have p3844_1 := h3844c.2.1
                                  have p3844_2 := h3844c.2.2.1
                                  have p3844_3 := h3844c.2.2.2
                                  linarith only [hlam, p3844_0]
                                · have p3844_0 := h3844c.1
                                  have p3844_1 := h3844c.2.1
                                  have p3844_2 := h3844c.2.2.1
                                  have p3844_3 := h3844c.2.2.2
                                  linarith only [h3698, hlam, p3844_1]
                                · have p3844_0 := h3844c.1
                                  have p3844_1 := h3844c.2.1
                                  have p3844_2 := h3844c.2.2.1
                                  have p3844_3 := h3844c.2.2.2
                                  linarith only [h3704, hlam, p3844_0]
                                · have p3844_0 := h3844c.1
                                  have p3844_1 := h3844c.2.1
                                  have p3844_2 := h3844c.2.2.1
                                  have p3844_3 := h3844c.2.2.2
                                  linarith only [h3706, hc04, hc45, hlam, hphi, p3844_1]
                                · have p3844_0 := h3844c.1
                                  have p3844_1 := h3844c.2.1
                                  have p3844_2 := h3844c.2.2.1
                                  have p3844_3 := h3844c.2.2.2
                                  linarith only [h3692, h3698, h3706, hc23, hc45, hlam, hphi, ht34, p3844_1]
                                · have p3844_0 := h3844c.1
                                  have p3844_1 := h3844c.2.1
                                  have p3844_2 := h3844c.2.2.1
                                  have p3844_3 := h3844c.2.2.2
                                  linarith only [h3698, h3706, hc23, hc45, hlam, hphi, ht34, p3844_1]
                                · have p3844_0 := h3844c.1
                                  have p3844_1 := h3844c.2.1
                                  have p3844_2 := h3844c.2.2.1
                                  have p3844_3 := h3844c.2.2.2
                                  linarith only [hlam, p3844_0]
                                · have p3844_0 := h3844c.1
                                  have p3844_1 := h3844c.2.1
                                  have p3844_2 := h3844c.2.2.1
                                  have p3844_3 := h3844c.2.2.2
                                  linarith only [h3706, hlam, p3844_0]
                                · have p3844_0 := h3844c.1
                                  have p3844_1 := h3844c.2.1
                                  have p3844_2 := h3844c.2.2.1
                                  have p3844_3 := h3844c.2.2.2
                                  linarith only [h1, h3692, h3698, hc23, hc45, hlam, hphi, ht34, p3844_1]
                                · have p3844_0 := h3844c.1
                                  have p3844_1 := h3844c.2.1
                                  have p3844_2 := h3844c.2.2.1
                                  have p3844_3 := h3844c.2.2.2
                                  linarith only [h3692, h3698, hc23, hc45, hlam, hphi, ht34, p3844_1]
                                · have p3844_0 := h3844c.1
                                  have p3844_1 := h3844c.2.1
                                  have p3844_2 := h3844c.2.2.1
                                  have p3844_3 := h3844c.2.2.2
                                  linarith only [h3698, hc23, hc45, hlam, hphi, ht34, p3844_1]
                                · have p3844_0 := h3844c.1
                                  have p3844_1 := h3844c.2.1
                                  have p3844_2 := h3844c.2.2.1
                                  have p3844_3 := h3844c.2.2.2
                                  linarith only [hc34, hc45, hlam, hphi, p3844_1]
                                · have p3844_0 := h3844c.1
                                  have p3844_1 := h3844c.2.1
                                  have p3844_2 := h3844c.2.2.1
                                  have p3844_3 := h3844c.2.2.2
                                  linarith only [hlam, p3844_0]
                      · linarith only [h0, h3835, hlam]
                    · have p3833_0 := h3833c.1
                      have p3833_1 := h3833c.2.1
                      have p3833_2 := h3833c.2.2.1
                      have p3833_3 := h3833c.2.2.2
                      rcases p3833_3 (m.d 0 2) (by simp) with h3871 | h3871
                      · rcases p3833_3 (m.d 1 2) (by simp) with h3872 | h3872
                        · linarith only [h0, h3872, hlam]
                        · linarith only [h3691, h3872, hlam]
                      · linarith only [h3871, hlam, p3833_0]
                    · have p3833_0 := h3833c.1
                      have p3833_1 := h3833c.2.1
                      have p3833_2 := h3833c.2.2.1
                      have p3833_3 := h3833c.2.2.2
                      rcases p3833_3 (m.d 0 2) (by simp) with h3876 | h3876
                      · rcases p3833_3 (m.d 1 2) (by simp) with h3877 | h3877
                        · linarith only [h0, h3877, hlam]
                        · linarith only [h3692, h3877, hlam]
                      · linarith only [h3876, hlam, p3833_0]
                    · have p3833_0 := h3833c.1
                      have p3833_1 := h3833c.2.1
                      have p3833_2 := h3833c.2.2.1
                      have p3833_3 := h3833c.2.2.2
                      rcases p3833_3 (m.d 0 2) (by simp) with h3881 | h3881
                      · rcases p3833_3 (m.d 1 2) (by simp) with h3882 | h3882
                        · linarith only [h0, h3882, hlam]
                        · linarith only [h3693, h3882, hlam]
                      · linarith only [h3881, hlam, p3833_0]
                    · have p3833_0 := h3833c.1
                      have p3833_1 := h3833c.2.1
                      have p3833_2 := h3833c.2.2.1
                      have p3833_3 := h3833c.2.2.2
                      linarith only [h0, hlam, p3833_1]
                    · have p3833_0 := h3833c.1
                      have p3833_1 := h3833c.2.1
                      have p3833_2 := h3833c.2.2.1
                      have p3833_3 := h3833c.2.2.2
                      linarith only [hlam, p3833_0]
                    · have p3833_0 := h3833c.1
                      have p3833_1 := h3833c.2.1
                      have p3833_2 := h3833c.2.2.1
                      have p3833_3 := h3833c.2.2.2
                      rcases p3833_3 (m.d 0 2) (by simp) with h3888 | h3888
                      · rcases p3833_3 (m.d 1 2) (by simp) with h3889 | h3889
                        · rcases p3833_3 (m.d 2 3) (by simp) with h3890 | h3890
                          · linarith only [h3890, hlam, p3833_0]
                          · rcases p3833_3 (m.d 2 4) (by simp) with h3892 | h3892
                            · linarith only [h3692, h3892, hlam]
                            · linarith only [h3698, h3892, hlam]
                        · linarith only [h3889, hlam, p3833_0]
                      · linarith only [h2, h3888, hlam]
                    · have p3833_0 := h3833c.1
                      have p3833_1 := h3833c.2.1
                      have p3833_2 := h3833c.2.2.1
                      have p3833_3 := h3833c.2.2.2
                      rcases p3833_3 (m.d 0 2) (by simp) with h3897 | h3897
                      · rcases p3833_3 (m.d 1 2) (by simp) with h3898 | h3898
                        · rcases p3833_3 (m.d 2 3) (by simp) with h3899 | h3899
                          · linarith only [h3691, h3899, hlam]
                          · rcases p3833_3 (m.d 2 4) (by simp) with h3901 | h3901
                            · linarith only [h3901, hlam, p3833_0]
                            · rcases p3833_3 (m.d 2 5) (by simp) with h3903 | h3903
                              · linarith only [h3693, h3903, hlam]
                              · linarith only [h3704, h3903, hlam]
                        · linarith only [h3898, hlam, p3833_0]
                      · linarith only [h3, h3897, hlam]
                    · have p3833_0 := h3833c.1
                      have p3833_1 := h3833c.2.1
                      have p3833_2 := h3833c.2.2.1
                      have p3833_3 := h3833c.2.2.2
                      rcases p3833_3 (m.d 0 2) (by simp) with h3908 | h3908
                      · rcases p3833_3 (m.d 1 2) (by simp) with h3909 | h3909
                        · rcases p3833_3 (m.d 2 3) (by simp) with h3910 | h3910
                          · linarith only [h3691, h3910, hlam]
                          · rcases p3833_3 (m.d 2 4) (by simp) with h3912 | h3912
                            · linarith only [h3692, h3912, hlam]
                            · rcases p3833_3 (m.d 2 5) (by simp) with h3914 | h3914
                              · linarith only [h3914, hlam, p3833_0]
                              · rcases h4bigk with h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c | h3916c
                                · have p3916_0 := h3916c.1
                                  have p3916_1 := h3916c.2.1
                                  have p3916_2 := h3916c.2.2.1
                                  have p3916_3 := h3916c.2.2.2
                                  linarith only [hlam, p3916_0]
                                · have p3916_0 := h3916c.1
                                  have p3916_1 := h3916c.2.1
                                  have p3916_2 := h3916c.2.2.1
                                  have p3916_3 := h3916c.2.2.2
                                  linarith only [h3692, h3698, h5, hc23, hc34, hlam, hphi, p3916_1]
                                · have p3916_0 := h3916c.1
                                  have p3916_1 := h3916c.2.1
                                  have p3916_2 := h3916c.2.2.1
                                  have p3916_3 := h3916c.2.2.2
                                  linarith only [h3698, h5, hc23, hc34, hlam, hphi, p3916_1]
                                · have p3916_0 := h3916c.1
                                  have p3916_1 := h3916c.2.1
                                  have p3916_2 := h3916c.2.2.1
                                  have p3916_3 := h3916c.2.2.2
                                  linarith only [h5, hlam, p3916_1]
                                · have p3916_0 := h3916c.1
                                  have p3916_1 := h3916c.2.1
                                  have p3916_2 := h3916c.2.2.1
                                  have p3916_3 := h3916c.2.2.2
                                  linarith only [h2892, hlam, p3916_0]
                                · have p3916_0 := h3916c.1
                                  have p3916_1 := h3916c.2.1
                                  have p3916_2 := h3916c.2.2.1
                                  have p3916_3 := h3916c.2.2.2
                                  linarith only [h1, hlam, p3916_0]
                                · have p3916_0 := h3916c.1
                                  have p3916_1 := h3916c.2.1
                                  have p3916_2 := h3916c.2.2.1
                                  have p3916_3 := h3916c.2.2.2
                                  linarith only [hlam, p3916_0]
                                · have p3916_0 := h3916c.1
                                  have p3916_1 := h3916c.2.1
                                  have p3916_2 := h3916c.2.2.1
                                  have p3916_3 := h3916c.2.2.2
                                  linarith only [h1, h3698, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3916_1]
                                · have p3916_0 := h3916c.1
                                  have p3916_1 := h3916c.2.1
                                  have p3916_2 := h3916c.2.2.1
                                  have p3916_3 := h3916c.2.2.2
                                  linarith only [h3694, hlam, p3916_1]
                                · have p3916_0 := h3916c.1
                                  have p3916_1 := h3916c.2.1
                                  have p3916_2 := h3916c.2.2.1
                                  have p3916_3 := h3916c.2.2.2
                                  linarith only [h3696, hlam, p3916_0]
                                · have p3916_0 := h3916c.1
                                  have p3916_1 := h3916c.2.1
                                  have p3916_2 := h3916c.2.2.1
                                  have p3916_3 := h3916c.2.2.2
                                  linarith only [h3, hlam, p3916_0]
                                · have p3916_0 := h3916c.1
                                  have p3916_1 := h3916c.2.1
                                  have p3916_2 := h3916c.2.2.1
                                  have p3916_3 := h3916c.2.2.2
                                  linarith only [h3692, hlam, p3916_0]
                                · have p3916_0 := h3916c.1
                                  have p3916_1 := h3916c.2.1
                                  have p3916_2 := h3916c.2.2.1
                                  have p3916_3 := h3916c.2.2.2
                                  linarith only [hlam, p3916_0]
                                · have p3916_0 := h3916c.1
                                  have p3916_1 := h3916c.2.1
                                  have p3916_2 := h3916c.2.2.1
                                  have p3916_3 := h3916c.2.2.2
                                  linarith only [h3698, hlam, p3916_1]
                                · have p3916_0 := h3916c.1
                                  have p3916_1 := h3916c.2.1
                                  have p3916_2 := h3916c.2.2.1
                                  have p3916_3 := h3916c.2.2.2
                                  linarith only [h3704, hlam, p3916_0]
                                · have p3916_0 := h3916c.1
                                  have p3916_1 := h3916c.2.1
                                  have p3916_2 := h3916c.2.2.1
                                  have p3916_3 := h3916c.2.2.2
                                  linarith only [h3, h3698, hc23, hc34, hlam, hphi, p3916_1]
                                · have p3916_0 := h3916c.1
                                  have p3916_1 := h3916c.2.1
                                  have p3916_2 := h3916c.2.2.1
                                  have p3916_3 := h3916c.2.2.2
                                  linarith only [h3692, h3698, hc23, hc34, hlam, hphi, p3916_1]
                                · have p3916_0 := h3916c.1
                                  have p3916_1 := h3916c.2.1
                                  have p3916_2 := h3916c.2.2.1
                                  have p3916_3 := h3916c.2.2.2
                                  linarith only [h3698, hc23, hc34, hlam, hphi, p3916_1]
                                · have p3916_0 := h3916c.1
                                  have p3916_1 := h3916c.2.1
                                  have p3916_2 := h3916c.2.2.1
                                  have p3916_3 := h3916c.2.2.2
                                  linarith only [hlam, p3916_0]
                                · have p3916_0 := h3916c.1
                                  have p3916_1 := h3916c.2.1
                                  have p3916_2 := h3916c.2.2.1
                                  have p3916_3 := h3916c.2.2.2
                                  linarith only [h3706, hlam, p3916_0]
                                · have p3916_0 := h3916c.1
                                  have p3916_1 := h3916c.2.1
                                  have p3916_2 := h3916c.2.2.1
                                  have p3916_3 := h3916c.2.2.2
                                  linarith only [h1, h3692, h3698, hc23, hc45, hlam, hphi, ht34, p3916_1]
                                · have p3916_0 := h3916c.1
                                  have p3916_1 := h3916c.2.1
                                  have p3916_2 := h3916c.2.2.1
                                  have p3916_3 := h3916c.2.2.2
                                  linarith only [h3692, h3698, hc23, hc45, hlam, hphi, ht34, p3916_1]
                                · have p3916_0 := h3916c.1
                                  have p3916_1 := h3916c.2.1
                                  have p3916_2 := h3916c.2.2.1
                                  have p3916_3 := h3916c.2.2.2
                                  linarith only [h3698, hc23, hc45, hlam, hphi, ht34, p3916_1]
                                · have p3916_0 := h3916c.1
                                  have p3916_1 := h3916c.2.1
                                  have p3916_2 := h3916c.2.2.1
                                  have p3916_3 := h3916c.2.2.2
                                  linarith only [hc34, hc45, hlam, hphi, p3916_1]
                                · have p3916_0 := h3916c.1
                                  have p3916_1 := h3916c.2.1
                                  have p3916_2 := h3916c.2.2.1
                                  have p3916_3 := h3916c.2.2.2
                                  linarith only [hlam, p3916_0]
                        · linarith only [h3909, hlam, p3833_0]
                      · linarith only [h3908, h4, hlam]
                    · have p3833_0 := h3833c.1
                      have p3833_1 := h3833c.2.1
                      have p3833_2 := h3833c.2.2.1
                      have p3833_3 := h3833c.2.2.2
                      linarith only [h2, hlam, p3833_0]
                    · have p3833_0 := h3833c.1
                      have p3833_1 := h3833c.2.1
                      have p3833_2 := h3833c.2.2.1
                      have p3833_3 := h3833c.2.2.2
                      linarith only [h3691, hlam, p3833_0]
                    · have p3833_0 := h3833c.1
                      have p3833_1 := h3833c.2.1
                      have p3833_2 := h3833c.2.2.1
                      have p3833_3 := h3833c.2.2.2
                      linarith only [hlam, p3833_0]
                    · have p3833_0 := h3833c.1
                      have p3833_1 := h3833c.2.1
                      have p3833_2 := h3833c.2.2.1
                      have p3833_3 := h3833c.2.2.2
                      linarith only [h3698, hlam, p3833_1]
                    · have p3833_0 := h3833c.1
                      have p3833_1 := h3833c.2.1
                      have p3833_2 := h3833c.2.2.1
                      have p3833_3 := h3833c.2.2.2
                      linarith only [h3700, hlam, p3833_1]
                    · have p3833_0 := h3833c.1
                      have p3833_1 := h3833c.2.1
                      have p3833_2 := h3833c.2.2.1
                      have p3833_3 := h3833c.2.2.2
                      linarith only [h3, hlam, p3833_0]
                    · have p3833_0 := h3833c.1
                      have p3833_1 := h3833c.2.1
                      have p3833_2 := h3833c.2.2.1
                      have p3833_3 := h3833c.2.2.2
                      linarith only [h3692, hlam, p3833_0]
                    · have p3833_0 := h3833c.1
                      have p3833_1 := h3833c.2.1
                      have p3833_2 := h3833c.2.2.1
                      have p3833_3 := h3833c.2.2.2
                      linarith only [h1, h2892, h3692, hc23, hc45, hlam, hphi, ht34, p3833_1]
                    · have p3833_0 := h3833c.1
                      have p3833_1 := h3833c.2.1
                      have p3833_2 := h3833c.2.2.1
                      have p3833_3 := h3833c.2.2.2
                      linarith only [hlam, p3833_0]
                    · have p3833_0 := h3833c.1
                      have p3833_1 := h3833c.2.1
                      have p3833_2 := h3833c.2.2.1
                      have p3833_3 := h3833c.2.2.2
                      linarith only [h3704, hlam, p3833_0]
                    · have p3833_0 := h3833c.1
                      have p3833_1 := h3833c.2.1
                      have p3833_2 := h3833c.2.2.1
                      have p3833_3 := h3833c.2.2.2
                      linarith only [h4, hlam, p3833_0]
                    · have p3833_0 := h3833c.1
                      have p3833_1 := h3833c.2.1
                      have p3833_2 := h3833c.2.2.1
                      have p3833_3 := h3833c.2.2.2
                      linarith only [h3693, hlam, p3833_0]
                    · have p3833_0 := h3833c.1
                      have p3833_1 := h3833c.2.1
                      have p3833_2 := h3833c.2.2.1
                      have p3833_3 := h3833c.2.2.2
                      linarith only [h0, h3693, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3833_1]
                    · have p3833_0 := h3833c.1
                      have p3833_1 := h3833c.2.1
                      have p3833_2 := h3833c.2.2.1
                      have p3833_3 := h3833c.2.2.2
                      linarith only [h0, h3693, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3833_1]
                    · have p3833_0 := h3833c.1
                      have p3833_1 := h3833c.2.1
                      have p3833_2 := h3833c.2.2.1
                      have p3833_3 := h3833c.2.2.2
                      linarith only [hlam, p3833_0]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3959 | h3959
        · linarith only [h0, h2, h3691, h3693, h3959, h4, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3961 | h3961
          · linarith only [h1, h2892, h3961, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3963 | h3963
            · linarith only [h2, h3963, h5, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3965 | h3965
              · linarith only [h0, h3691, h3693, h3965, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3967 | h3967
                · linarith only [h2892, h3692, h3693, h3967, h4, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3969 | h3969
                  · linarith only [h2892, h3692, h3693, h3963, h3969, h4, hc23, hc34, hlam, hphi]
                  · rcases h2bigk with h3971c | h3971c | h3971c | h3971c | h3971c | h3971c | h3971c | h3971c | h3971c | h3971c | h3971c | h3971c | h3971c | h3971c | h3971c | h3971c | h3971c | h3971c | h3971c | h3971c | h3971c | h3971c | h3971c | h3971c | h3971c
                    · have p3971_0 := h3971c.1
                      have p3971_1 := h3971c.2.1
                      have p3971_2 := h3971c.2.2.1
                      have p3971_3 := h3971c.2.2.2
                      linarith only [hlam, p3971_0]
                    · have p3971_0 := h3971c.1
                      have p3971_1 := h3971c.2.1
                      have p3971_2 := h3971c.2.2.1
                      have p3971_3 := h3971c.2.2.2
                      rcases p3971_3 (m.d 0 2) (by simp) with h3973 | h3973
                      · rcases p3971_3 (m.d 1 2) (by simp) with h3974 | h3974
                        · linarith only [h0, h3974, hlam]
                        · rcases p3971_3 (m.d 2 3) (by simp) with h3976 | h3976
                          · linarith only [h2, h3976, hlam]
                          · rcases p3971_3 (m.d 2 4) (by simp) with h3978 | h3978
                            · linarith only [h3, h3978, hlam]
                            · rcases p3971_3 (m.d 2 5) (by simp) with h3980 | h3980
                              · linarith only [h3980, h4, hlam]
                              · linarith only [h3693, h3980, hlam]
                      · linarith only [h0, h3973, hlam]
                    · have p3971_0 := h3971c.1
                      have p3971_1 := h3971c.2.1
                      have p3971_2 := h3971c.2.2.1
                      have p3971_3 := h3971c.2.2.2
                      linarith only [h3692, h3693, h3963, h4, hlam, p3971_2]
                    · have p3971_0 := h3971c.1
                      have p3971_1 := h3971c.2.1
                      have p3971_2 := h3971c.2.2.1
                      have p3971_3 := h3971c.2.2.2
                      linarith only [h3692, h3693, h4, hlam, p3971_2]
                    · have p3971_0 := h3971c.1
                      have p3971_1 := h3971c.2.1
                      have p3971_2 := h3971c.2.2.1
                      have p3971_3 := h3971c.2.2.2
                      linarith only [h3692, h3693, h3963, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3971_1]
                    · have p3971_0 := h3971c.1
                      have p3971_1 := h3971c.2.1
                      have p3971_2 := h3971c.2.2.1
                      have p3971_3 := h3971c.2.2.2
                      linarith only [h0, hlam, p3971_1]
                    · have p3971_0 := h3971c.1
                      have p3971_1 := h3971c.2.1
                      have p3971_2 := h3971c.2.2.1
                      have p3971_3 := h3971c.2.2.2
                      linarith only [hlam, p3971_0]
                    · have p3971_0 := h3971c.1
                      have p3971_1 := h3971c.2.1
                      have p3971_2 := h3971c.2.2.1
                      have p3971_3 := h3971c.2.2.2
                      linarith only [h3693, h3965, hc23, hc35, hlam, hphi, p3971_1]
                    · have p3971_0 := h3971c.1
                      have p3971_1 := h3971c.2.1
                      have p3971_2 := h3971c.2.2.1
                      have p3971_3 := h3971c.2.2.2
                      linarith only [h0, h3693, h3963, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3971_1]
                    · have p3971_0 := h3971c.1
                      have p3971_1 := h3971c.2.1
                      have p3971_2 := h3971c.2.2.1
                      have p3971_3 := h3971c.2.2.2
                      linarith only [h3693, hlam, p3971_0]
                    · have p3971_0 := h3971c.1
                      have p3971_1 := h3971c.2.1
                      have p3971_2 := h3971c.2.2.1
                      have p3971_3 := h3971c.2.2.2
                      linarith only [h2, hlam, p3971_0]
                    · have p3971_0 := h3971c.1
                      have p3971_1 := h3971c.2.1
                      have p3971_2 := h3971c.2.2.1
                      have p3971_3 := h3971c.2.2.2
                      linarith only [h3691, hlam, p3971_0]
                    · have p3971_0 := h3971c.1
                      have p3971_1 := h3971c.2.1
                      have p3971_2 := h3971c.2.2.1
                      have p3971_3 := h3971c.2.2.2
                      linarith only [hlam, p3971_0]
                    · have p3971_0 := h3971c.1
                      have p3971_1 := h3971c.2.1
                      have p3971_2 := h3971c.2.2.1
                      have p3971_3 := h3971c.2.2.2
                      linarith only [h3963, hlam, p3971_1]
                    · have p3971_0 := h3971c.1
                      have p3971_1 := h3971c.2.1
                      have p3971_2 := h3971c.2.2.1
                      have p3971_3 := h3971c.2.2.2
                      linarith only [h3965, hlam, p3971_1]
                    · have p3971_0 := h3971c.1
                      have p3971_1 := h3971c.2.1
                      have p3971_2 := h3971c.2.2.1
                      have p3971_3 := h3971c.2.2.2
                      linarith only [h3, hlam, p3971_0]
                    · have p3971_0 := h3971c.1
                      have p3971_1 := h3971c.2.1
                      have p3971_2 := h3971c.2.2.1
                      have p3971_3 := h3971c.2.2.2
                      linarith only [h3692, hlam, p3971_0]
                    · have p3971_0 := h3971c.1
                      have p3971_1 := h3971c.2.1
                      have p3971_2 := h3971c.2.2.1
                      have p3971_3 := h3971c.2.2.2
                      linarith only [h3, h3969, h5, hc23, hc45, hlam, hphi, ht34, p3971_1]
                    · have p3971_0 := h3971c.1
                      have p3971_1 := h3971c.2.1
                      have p3971_2 := h3971c.2.2.1
                      have p3971_3 := h3971c.2.2.2
                      linarith only [hlam, p3971_0]
                    · have p3971_0 := h3971c.1
                      have p3971_1 := h3971c.2.1
                      have p3971_2 := h3971c.2.2.1
                      have p3971_3 := h3971c.2.2.2
                      linarith only [h3967, hlam, p3971_0]
                    · have p3971_0 := h3971c.1
                      have p3971_1 := h3971c.2.1
                      have p3971_2 := h3971c.2.2.1
                      have p3971_3 := h3971c.2.2.2
                      linarith only [h4, hlam, p3971_0]
                    · have p3971_0 := h3971c.1
                      have p3971_1 := h3971c.2.1
                      have p3971_2 := h3971c.2.2.1
                      have p3971_3 := h3971c.2.2.2
                      linarith only [h0, h3691, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3971_1]
                    · have p3971_0 := h3971c.1
                      have p3971_1 := h3971c.2.1
                      have p3971_2 := h3971c.2.2.1
                      have p3971_3 := h3971c.2.2.2
                      rcases p3971_3 (m.d 0 2) (by simp) with h4004 | h4004
                      · rcases p3971_3 (m.d 1 2) (by simp) with h4005 | h4005
                        · linarith only [h3693, h4005, hlam]
                        · linarith only [h3691, h4005, hlam]
                      · linarith only [h2, h4004, hlam]
                    · have p3971_0 := h3971c.1
                      have p3971_1 := h3971c.2.1
                      have p3971_2 := h3971c.2.2.1
                      have p3971_3 := h3971c.2.2.2
                      rcases p3971_3 (m.d 0 2) (by simp) with h4009 | h4009
                      · rcases p3971_3 (m.d 1 2) (by simp) with h4010 | h4010
                        · linarith only [h3693, h4010, hlam]
                        · linarith only [h3692, h4010, hlam]
                      · linarith only [h3, h4009, hlam]
                    · have p3971_0 := h3971c.1
                      have p3971_1 := h3971c.2.1
                      have p3971_2 := h3971c.2.2.1
                      have p3971_3 := h3971c.2.2.2
                      linarith only [hlam, p3971_0]
    · linarith only [h2892, h3, h3691, h3692, hc23, hc45, hlam, hphi, ht34]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h4016 | h4016
    · linarith only [h2, h2892, h3691, h4016, h5, hc24, hc45, hlam, hphi]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h4018 | h4018
      · rcases m.htr 1 3 4 (by decide) (by decide) with h4019 | h4019
        · linarith only [h2, h3691, h4018, h4019, h5, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4021 | h4021
          · linarith only [h2, h2892, h3691, h4018, h4021, h5, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
          · linarith only [h4016, h4018, h4021, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h4024 | h4024
        · linarith only [h2, h3691, h4024, h5, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4026 | h4026
          · linarith only [h1, h2892, h4026, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4028 | h4028
            · linarith only [h2, h4028, h5, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h4030 | h4030
              · rcases m.htr 2 4 5 (by decide) (by decide) with h4031 | h4031
                · linarith only [h2, h2892, h4018, h4030, h4031, h5, hc12, hc24, hlam, hphi]
                · linarith only [h4028, h4030, h4031, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h4034 | h4034
                · linarith only [h2892, h3, h4034, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h4036 | h4036
                  · linarith only [h2, h2892, h3691, h4036, h5, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h2, h3691, h4036, h5, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 8068000 in
set_option maxHeartbeats 8068000 in
theorem r1l7_12_24_L_I_H_I_s4_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 4 5 (by decide) (by decide) with h2892 | h2892
  · exact r1l7_12_24_L_I_H_I_s4_x1_x0 m hb2 hb4 hg0 hg1 hg2 hg3 hg4 h5 h2892
  · exact r1l7_12_24_L_I_H_I_s4_x1_x1 m hb2 hb4 hg0 hg1 hg2 hg3 hg4 h5 h2892

set_option maxHeartbeats 8068000 in
set_option maxHeartbeats 8068000 in
theorem r1l7_12_24_L_I_H_I_s4 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_12_24_L_I_H_I_s4_x0 m hb2 hb4 hg0 hg1 hg2 hg3 hg4 h5
  · exact r1l7_12_24_L_I_H_I_s4_x1 m hb2 hb4 hg0 hg1 hg2 hg3 hg4 h5

set_option maxHeartbeats 8226000 in
set_option maxHeartbeats 8226000 in
theorem r1l7_12_24_L_I_H_I_s3 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
  · exact r1l7_12_24_L_I_H_I_s4 m hb2 hb4 h0 h1 h2 h3 h4
  · rcases m.htr 0 3 4 (by decide) (by decide) with h4039 | h4039
    · rcases m.htr 0 4 5 (by decide) (by decide) with h4040 | h4040
      · linarith only [h2, h4, h4039, h4040, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4042 | h4042
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4043 | h4043
          · rcases m.htr 1 2 5 (by decide) (by decide) with h4044 | h4044
            · linarith only [h0, h4, h4044, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h4046 | h4046
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4047 | h4047
                · linarith only [h1, h4040, h4047, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4049 | h4049
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4050 | h4050
                    · linarith only [h0, h4, h4042, h4050, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4052 | h4052
                      · linarith only [h0, h4, h4040, h4042, h4049, h4050, h4052, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h4, h4042, h4049, h4052, hc34, hc45, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4055 | h4055
                    · linarith only [h0, h4, h4042, h4046, h4049, h4055, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h0, h4, h4042, h4046, h4049, h4055, hc23, hc35, hlam, hphi]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4058 | h4058
                · linarith only [h1, h4040, h4058, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4060 | h4060
                  · linarith only [h4042, h4046, h4060, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4062 | h4062
                    · linarith only [h2, h4, h4039, h4042, h4046, h4062, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h2, h4, h4039, h4042, h4046, h4062, hc23, hc35, hlam, hphi]
          · linarith only [h3, h4, h4043, hc12, hc25, hlam, hphi]
        · linarith only [h2, h4, h4042, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h4067 | h4067
      · linarith only [h3, h4, h4067, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4069 | h4069
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4070 | h4070
          · rcases m.htr 1 2 5 (by decide) (by decide) with h4071 | h4071
            · linarith only [h0, h4, h4071, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h4073 | h4073
              · linarith only [h1, h4039, h4073, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4075 | h4075
                · linarith only [h1, h4067, h4075, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4077 | h4077
                  · linarith only [h2, h4039, h4077, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4079 | h4079
                    · linarith only [h0, h4, h4070, h4077, h4079, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4081 | h4081
                      · linarith only [h0, h4, h4067, h4070, h4079, h4081, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4083 | h4083
                        · linarith only [h0, h4, h4070, h4077, h4081, h4083, hc23, hc34, hlam, hphi]
                        · rcases h2bigk with h4085c | h4085c | h4085c | h4085c | h4085c | h4085c | h4085c | h4085c | h4085c | h4085c | h4085c | h4085c | h4085c | h4085c | h4085c | h4085c | h4085c | h4085c | h4085c | h4085c | h4085c | h4085c | h4085c | h4085c | h4085c
                          · have p4085_0 := h4085c.1
                            have p4085_1 := h4085c.2.1
                            have p4085_2 := h4085c.2.2.1
                            have p4085_3 := h4085c.2.2.2
                            linarith only [hlam, p4085_0]
                          · have p4085_0 := h4085c.1
                            have p4085_1 := h4085c.2.1
                            have p4085_2 := h4085c.2.2.1
                            have p4085_3 := h4085c.2.2.2
                            linarith only [h4, h4070, h4077, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4085_1]
                          · have p4085_0 := h4085c.1
                            have p4085_1 := h4085c.2.1
                            have p4085_2 := h4085c.2.2.1
                            have p4085_3 := h4085c.2.2.2
                            linarith only [h4, h4079, h4083, hc23, hc45, hlam, hphi, ht34, p4085_1]
                          · have p4085_0 := h4085c.1
                            have p4085_1 := h4085c.2.1
                            have p4085_2 := h4085c.2.2.1
                            have p4085_3 := h4085c.2.2.2
                            linarith only [h4, h4077, h4079, h4083, hc23, hc45, hlam, hphi, ht34, p4085_1]
                          · have p4085_0 := h4085c.1
                            have p4085_1 := h4085c.2.1
                            have p4085_2 := h4085c.2.2.1
                            have p4085_3 := h4085c.2.2.2
                            linarith only [h4, hlam, p4085_0]
                          · have p4085_0 := h4085c.1
                            have p4085_1 := h4085c.2.1
                            have p4085_2 := h4085c.2.2.1
                            have p4085_3 := h4085c.2.2.2
                            linarith only [h0, hlam, p4085_1]
                          · have p4085_0 := h4085c.1
                            have p4085_1 := h4085c.2.1
                            have p4085_2 := h4085c.2.2.1
                            have p4085_3 := h4085c.2.2.2
                            linarith only [hlam, p4085_0]
                          · have p4085_0 := h4085c.1
                            have p4085_1 := h4085c.2.1
                            have p4085_2 := h4085c.2.2.1
                            have p4085_3 := h4085c.2.2.2
                            linarith only [h0, h4, h4079, h4083, hc23, hc45, hlam, hphi, ht34, p4085_1]
                          · have p4085_0 := h4085c.1
                            have p4085_1 := h4085c.2.1
                            have p4085_2 := h4085c.2.2.1
                            have p4085_3 := h4085c.2.2.2
                            linarith only [h0, h4, h4077, h4079, h4083, hc23, hc45, hlam, hphi, ht34, p4085_1]
                          · have p4085_0 := h4085c.1
                            have p4085_1 := h4085c.2.1
                            have p4085_2 := h4085c.2.2.1
                            have p4085_3 := h4085c.2.2.2
                            linarith only [h4071, hlam, p4085_0]
                          · have p4085_0 := h4085c.1
                            have p4085_1 := h4085c.2.1
                            have p4085_2 := h4085c.2.2.1
                            have p4085_3 := h4085c.2.2.2
                            linarith only [h2, hlam, p4085_0]
                          · have p4085_0 := h4085c.1
                            have p4085_1 := h4085c.2.1
                            have p4085_2 := h4085c.2.2.1
                            have p4085_3 := h4085c.2.2.2
                            linarith only [h4069, hlam, p4085_0]
                          · have p4085_0 := h4085c.1
                            have p4085_1 := h4085c.2.1
                            have p4085_2 := h4085c.2.2.1
                            have p4085_3 := h4085c.2.2.2
                            linarith only [hlam, p4085_0]
                          · have p4085_0 := h4085c.1
                            have p4085_1 := h4085c.2.1
                            have p4085_2 := h4085c.2.2.1
                            have p4085_3 := h4085c.2.2.2
                            linarith only [h4077, hlam, p4085_1]
                          · have p4085_0 := h4085c.1
                            have p4085_1 := h4085c.2.1
                            have p4085_2 := h4085c.2.2.1
                            have p4085_3 := h4085c.2.2.2
                            linarith only [h4079, hlam, p4085_1]
                          · have p4085_0 := h4085c.1
                            have p4085_1 := h4085c.2.1
                            have p4085_2 := h4085c.2.2.1
                            have p4085_3 := h4085c.2.2.2
                            linarith only [h3, hlam, p4085_0]
                          · have p4085_0 := h4085c.1
                            have p4085_1 := h4085c.2.1
                            have p4085_2 := h4085c.2.2.1
                            have p4085_3 := h4085c.2.2.2
                            linarith only [h4070, hlam, p4085_0]
                          · have p4085_0 := h4085c.1
                            have p4085_1 := h4085c.2.1
                            have p4085_2 := h4085c.2.2.1
                            have p4085_3 := h4085c.2.2.2
                            linarith only [h3, h4, h4079, h4083, hc23, hc45, hlam, hphi, ht34, p4085_1]
                          · have p4085_0 := h4085c.1
                            have p4085_1 := h4085c.2.1
                            have p4085_2 := h4085c.2.2.1
                            have p4085_3 := h4085c.2.2.2
                            linarith only [hlam, p4085_0]
                          · have p4085_0 := h4085c.1
                            have p4085_1 := h4085c.2.1
                            have p4085_2 := h4085c.2.2.1
                            have p4085_3 := h4085c.2.2.2
                            linarith only [h4081, hlam, p4085_0]
                          · have p4085_0 := h4085c.1
                            have p4085_1 := h4085c.2.1
                            have p4085_2 := h4085c.2.2.1
                            have p4085_3 := h4085c.2.2.2
                            linarith only [h2, h4079, h4083, hc23, hc45, hlam, hphi, ht34, p4085_1]
                          · have p4085_0 := h4085c.1
                            have p4085_1 := h4085c.2.1
                            have p4085_2 := h4085c.2.2.1
                            have p4085_3 := h4085c.2.2.2
                            linarith only [h4070, h4079, h4083, hc24, hc45, hlam, hphi, p4085_1]
                          · have p4085_0 := h4085c.1
                            have p4085_1 := h4085c.2.1
                            have p4085_2 := h4085c.2.2.1
                            have p4085_3 := h4085c.2.2.2
                            rcases p4085_3 (m.d 0 2) (by simp) with h4108 | h4108
                            · linarith only [h4, h4108, hlam]
                            · linarith only [h2, h4108, hlam]
                          · have p4085_0 := h4085c.1
                            have p4085_1 := h4085c.2.1
                            have p4085_2 := h4085c.2.2.1
                            have p4085_3 := h4085c.2.2.2
                            rcases p4085_3 (m.d 0 2) (by simp) with h4111 | h4111
                            · linarith only [h4, h4111, hlam]
                            · linarith only [h3, h4111, hlam]
                          · have p4085_0 := h4085c.1
                            have p4085_1 := h4085c.2.1
                            have p4085_2 := h4085c.2.2.1
                            have p4085_3 := h4085c.2.2.2
                            linarith only [hlam, p4085_0]
          · linarith only [h3, h4, h4070, hc12, hc25, hlam, hphi]
        · linarith only [h2, h4, h4069, hc12, hc25, hlam, hphi]

set_option maxHeartbeats 8556000 in
set_option maxHeartbeats 8556000 in
theorem r1l7_12_24_L_I_H_I_s2 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
  · exact r1l7_12_24_L_I_H_I_s3 m hb2 hb4 h0 h1 h2 h3
  · rcases m.htr 0 2 5 (by decide) (by decide) with h4117 | h4117
    · rcases m.htr 0 3 4 (by decide) (by decide) with h4118 | h4118
      · linarith only [h2, h3, h4118, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4120 | h4120
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4121 | h4121
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4122 | h4122
            · linarith only [h0, h3, h4117, h4122, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4124 | h4124
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4125 | h4125
                · linarith only [h0, h3, h4118, h4121, h4125, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h4127 | h4127
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4128 | h4128
                    · linarith only [h2, h3, h4125, h4128, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h4130 | h4130
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4131 | h4131
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4132 | h4132
                          · rcases h2bigk with h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c
                            · have p4133_0 := h4133c.1
                              have p4133_1 := h4133c.2.1
                              have p4133_2 := h4133c.2.2.1
                              have p4133_3 := h4133c.2.2.2
                              linarith only [hlam, p4133_0]
                            · have p4133_0 := h4133c.1
                              have p4133_1 := h4133c.2.1
                              have p4133_2 := h4133c.2.2.1
                              have p4133_3 := h4133c.2.2.2
                              linarith only [h3, h4121, h4128, h4130, h4132, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4133_1]
                            · have p4133_0 := h4133c.1
                              have p4133_1 := h4133c.2.1
                              have p4133_2 := h4133c.2.2.1
                              have p4133_3 := h4133c.2.2.2
                              linarith only [h3, h4128, h4130, h4132, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4133_1]
                            · have p4133_0 := h4133c.1
                              have p4133_1 := h4133c.2.1
                              have p4133_2 := h4133c.2.2.1
                              have p4133_3 := h4133c.2.2.2
                              linarith only [h3, hlam, p4133_0]
                            · have p4133_0 := h4133c.1
                              have p4133_1 := h4133c.2.1
                              have p4133_2 := h4133c.2.2.1
                              have p4133_3 := h4133c.2.2.2
                              rcases p4133_3 (m.d 0 2) (by simp) with h4138 | h4138
                              · rcases p4133_3 (m.d 1 2) (by simp) with h4139 | h4139
                                · linarith only [h0, h4139, hlam]
                                · linarith only [h4124, h4139, hlam]
                              · linarith only [h4138, hlam, p4133_0]
                            · have p4133_0 := h4133c.1
                              have p4133_1 := h4133c.2.1
                              have p4133_2 := h4133c.2.2.1
                              have p4133_3 := h4133c.2.2.2
                              linarith only [h0, hlam, p4133_1]
                            · have p4133_0 := h4133c.1
                              have p4133_1 := h4133c.2.1
                              have p4133_2 := h4133c.2.2.1
                              have p4133_3 := h4133c.2.2.2
                              linarith only [hlam, p4133_0]
                            · have p4133_0 := h4133c.1
                              have p4133_1 := h4133c.2.1
                              have p4133_2 := h4133c.2.2.1
                              have p4133_3 := h4133c.2.2.2
                              linarith only [h0, h4130, h4132, hc01, hc45, hlam, hphi, ht0b, ht5b, p4133_1]
                            · have p4133_0 := h4133c.1
                              have p4133_1 := h4133c.2.1
                              have p4133_2 := h4133c.2.2.1
                              have p4133_3 := h4133c.2.2.2
                              linarith only [h4122, hlam, p4133_0]
                            · have p4133_0 := h4133c.1
                              have p4133_1 := h4133c.2.1
                              have p4133_2 := h4133c.2.2.1
                              have p4133_3 := h4133c.2.2.2
                              rcases p4133_3 (m.d 0 2) (by simp) with h4147 | h4147
                              · rcases p4133_3 (m.d 1 2) (by simp) with h4148 | h4148
                                · rcases p4133_3 (m.d 2 3) (by simp) with h4149 | h4149
                                  · linarith only [h4121, h4149, hlam]
                                  · linarith only [h4130, h4149, hlam]
                                · linarith only [h4148, hlam, p4133_0]
                              · linarith only [h4117, h4147, hlam]
                            · have p4133_0 := h4133c.1
                              have p4133_1 := h4133c.2.1
                              have p4133_2 := h4133c.2.2.1
                              have p4133_3 := h4133c.2.2.2
                              linarith only [h2, hlam, p4133_0]
                            · have p4133_0 := h4133c.1
                              have p4133_1 := h4133c.2.1
                              have p4133_2 := h4133c.2.2.1
                              have p4133_3 := h4133c.2.2.2
                              linarith only [h4121, hlam, p4133_0]
                            · have p4133_0 := h4133c.1
                              have p4133_1 := h4133c.2.1
                              have p4133_2 := h4133c.2.2.1
                              have p4133_3 := h4133c.2.2.2
                              linarith only [hlam, p4133_0]
                            · have p4133_0 := h4133c.1
                              have p4133_1 := h4133c.2.1
                              have p4133_2 := h4133c.2.2.1
                              have p4133_3 := h4133c.2.2.2
                              linarith only [h4128, hlam, p4133_1]
                            · have p4133_0 := h4133c.1
                              have p4133_1 := h4133c.2.1
                              have p4133_2 := h4133c.2.2.1
                              have p4133_3 := h4133c.2.2.2
                              linarith only [h2, h3, h4128, h4130, h4132, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4133_1]
                            · have p4133_0 := h4133c.1
                              have p4133_1 := h4133c.2.1
                              have p4133_2 := h4133c.2.2.1
                              have p4133_3 := h4133c.2.2.2
                              linarith only [h2, h4128, hc23, hc34, hlam, hphi, p4133_1]
                            · have p4133_0 := h4133c.1
                              have p4133_1 := h4133c.2.1
                              have p4133_2 := h4133c.2.2.1
                              have p4133_3 := h4133c.2.2.2
                              linarith only [h4121, h4128, hc23, hc34, hlam, hphi, p4133_1]
                            · have p4133_0 := h4133c.1
                              have p4133_1 := h4133c.2.1
                              have p4133_2 := h4133c.2.2.1
                              have p4133_3 := h4133c.2.2.2
                              rcases p4133_3 (m.d 0 2) (by simp) with h4161 | h4161
                              · linarith only [h3, h4161, hlam]
                              · linarith only [h2, h4161, hlam]
                            · have p4133_0 := h4133c.1
                              have p4133_1 := h4133c.2.1
                              have p4133_2 := h4133c.2.2.1
                              have p4133_3 := h4133c.2.2.2
                              linarith only [hlam, p4133_0]
                            · have p4133_0 := h4133c.1
                              have p4133_1 := h4133c.2.1
                              have p4133_2 := h4133c.2.2.1
                              have p4133_3 := h4133c.2.2.2
                              rcases p4133_3 (m.d 0 2) (by simp) with h4165 | h4165
                              · linarith only [h3, h4165, hlam]
                              · linarith only [h4117, h4165, hlam]
                            · have p4133_0 := h4133c.1
                              have p4133_1 := h4133c.2.1
                              have p4133_2 := h4133c.2.2.1
                              have p4133_3 := h4133c.2.2.2
                              linarith only [h4117, hlam, p4133_0]
                            · have p4133_0 := h4133c.1
                              have p4133_1 := h4133c.2.1
                              have p4133_2 := h4133c.2.2.1
                              have p4133_3 := h4133c.2.2.2
                              linarith only [h4124, hlam, p4133_0]
                            · have p4133_0 := h4133c.1
                              have p4133_1 := h4133c.2.1
                              have p4133_2 := h4133c.2.2.1
                              have p4133_3 := h4133c.2.2.2
                              linarith only [h4130, hlam, p4133_0]
                            · have p4133_0 := h4133c.1
                              have p4133_1 := h4133c.2.1
                              have p4133_2 := h4133c.2.2.1
                              have p4133_3 := h4133c.2.2.2
                              linarith only [h4131, hlam, p4133_1]
                            · have p4133_0 := h4133c.1
                              have p4133_1 := h4133c.2.1
                              have p4133_2 := h4133c.2.2.1
                              have p4133_3 := h4133c.2.2.2
                              linarith only [hlam, p4133_0]
                          · linarith only [h4118, h4120, h4132, hlam]
                        · linarith only [h0, h1, h3, h4121, h4127, h4130, h4131, hc01, hc35, hlam, hphi, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4175 | h4175
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4176 | h4176
                          · rcases h2bigk with h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c
                            · have p4177_0 := h4177c.1
                              have p4177_1 := h4177c.2.1
                              have p4177_2 := h4177c.2.2.1
                              have p4177_3 := h4177c.2.2.2
                              linarith only [hlam, p4177_0]
                            · have p4177_0 := h4177c.1
                              have p4177_1 := h4177c.2.1
                              have p4177_2 := h4177c.2.2.1
                              have p4177_3 := h4177c.2.2.2
                              linarith only [h3, hc12, hc24, hlam, hphi, p4177_1]
                            · have p4177_0 := h4177c.1
                              have p4177_1 := h4177c.2.1
                              have p4177_2 := h4177c.2.2.1
                              have p4177_3 := h4177c.2.2.2
                              linarith only [h3, h4128, hc23, hc34, hlam, hphi, p4177_1]
                            · have p4177_0 := h4177c.1
                              have p4177_1 := h4177c.2.1
                              have p4177_2 := h4177c.2.2.1
                              have p4177_3 := h4177c.2.2.2
                              linarith only [h3, hlam, p4177_0]
                            · have p4177_0 := h4177c.1
                              have p4177_1 := h4177c.2.1
                              have p4177_2 := h4177c.2.2.1
                              have p4177_3 := h4177c.2.2.2
                              linarith only [h3, h4128, h4130, hc23, hc34, hlam, hphi, p4177_1]
                            · have p4177_0 := h4177c.1
                              have p4177_1 := h4177c.2.1
                              have p4177_2 := h4177c.2.2.1
                              have p4177_3 := h4177c.2.2.2
                              linarith only [h0, hlam, p4177_1]
                            · have p4177_0 := h4177c.1
                              have p4177_1 := h4177c.2.1
                              have p4177_2 := h4177c.2.2.1
                              have p4177_3 := h4177c.2.2.2
                              linarith only [hlam, p4177_0]
                            · have p4177_0 := h4177c.1
                              have p4177_1 := h4177c.2.1
                              have p4177_2 := h4177c.2.2.1
                              have p4177_3 := h4177c.2.2.2
                              linarith only [h0, h3, h4128, hc23, hc34, hlam, hphi, p4177_1]
                            · have p4177_0 := h4177c.1
                              have p4177_1 := h4177c.2.1
                              have p4177_2 := h4177c.2.2.1
                              have p4177_3 := h4177c.2.2.2
                              linarith only [h4122, hlam, p4177_0]
                            · have p4177_0 := h4177c.1
                              have p4177_1 := h4177c.2.1
                              have p4177_2 := h4177c.2.2.1
                              have p4177_3 := h4177c.2.2.2
                              linarith only [h0, h3, h4128, h4130, hc23, hc34, hlam, hphi, p4177_1]
                            · have p4177_0 := h4177c.1
                              have p4177_1 := h4177c.2.1
                              have p4177_2 := h4177c.2.2.1
                              have p4177_3 := h4177c.2.2.2
                              linarith only [h2, hlam, p4177_0]
                            · have p4177_0 := h4177c.1
                              have p4177_1 := h4177c.2.1
                              have p4177_2 := h4177c.2.2.1
                              have p4177_3 := h4177c.2.2.2
                              linarith only [h4121, hlam, p4177_0]
                            · have p4177_0 := h4177c.1
                              have p4177_1 := h4177c.2.1
                              have p4177_2 := h4177c.2.2.1
                              have p4177_3 := h4177c.2.2.2
                              linarith only [hlam, p4177_0]
                            · have p4177_0 := h4177c.1
                              have p4177_1 := h4177c.2.1
                              have p4177_2 := h4177c.2.2.1
                              have p4177_3 := h4177c.2.2.2
                              linarith only [h4128, hlam, p4177_1]
                            · have p4177_0 := h4177c.1
                              have p4177_1 := h4177c.2.1
                              have p4177_2 := h4177c.2.2.1
                              have p4177_3 := h4177c.2.2.2
                              linarith only [h4130, hlam, p4177_1]
                            · have p4177_0 := h4177c.1
                              have p4177_1 := h4177c.2.1
                              have p4177_2 := h4177c.2.2.1
                              have p4177_3 := h4177c.2.2.2
                              linarith only [h2, h4128, hc23, hc34, hlam, hphi, p4177_1]
                            · have p4177_0 := h4177c.1
                              have p4177_1 := h4177c.2.1
                              have p4177_2 := h4177c.2.2.1
                              have p4177_3 := h4177c.2.2.2
                              linarith only [h4121, h4128, hc23, hc34, hlam, hphi, p4177_1]
                            · have p4177_0 := h4177c.1
                              have p4177_1 := h4177c.2.1
                              have p4177_2 := h4177c.2.2.1
                              have p4177_3 := h4177c.2.2.2
                              rcases p4177_3 (m.d 0 2) (by simp) with h4195 | h4195
                              · linarith only [h3, h4195, hlam]
                              · linarith only [h2, h4195, hlam]
                            · have p4177_0 := h4177c.1
                              have p4177_1 := h4177c.2.1
                              have p4177_2 := h4177c.2.2.1
                              have p4177_3 := h4177c.2.2.2
                              linarith only [hlam, p4177_0]
                            · have p4177_0 := h4177c.1
                              have p4177_1 := h4177c.2.1
                              have p4177_2 := h4177c.2.2.1
                              have p4177_3 := h4177c.2.2.2
                              rcases p4177_3 (m.d 0 2) (by simp) with h4199 | h4199
                              · linarith only [h3, h4199, hlam]
                              · linarith only [h4117, h4199, hlam]
                            · have p4177_0 := h4177c.1
                              have p4177_1 := h4177c.2.1
                              have p4177_2 := h4177c.2.2.1
                              have p4177_3 := h4177c.2.2.2
                              linarith only [h4117, hlam, p4177_0]
                            · have p4177_0 := h4177c.1
                              have p4177_1 := h4177c.2.1
                              have p4177_2 := h4177c.2.2.1
                              have p4177_3 := h4177c.2.2.2
                              linarith only [h4124, hlam, p4177_0]
                            · have p4177_0 := h4177c.1
                              have p4177_1 := h4177c.2.1
                              have p4177_2 := h4177c.2.2.1
                              have p4177_3 := h4177c.2.2.2
                              linarith only [h0, h4124, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4177_1]
                            · have p4177_0 := h4177c.1
                              have p4177_1 := h4177c.2.1
                              have p4177_2 := h4177c.2.2.1
                              have p4177_3 := h4177c.2.2.2
                              linarith only [h4175, hlam, p4177_1]
                            · have p4177_0 := h4177c.1
                              have p4177_1 := h4177c.2.1
                              have p4177_2 := h4177c.2.2.1
                              have p4177_3 := h4177c.2.2.2
                              linarith only [hlam, p4177_0]
                          · linarith only [h0, h3, h4124, h4128, h4175, h4176, hlam]
                        · linarith only [h2, h3, h4175, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h4118, h4120, h4121, h4122, h4127, hc23, hc34, hlam, hphi]
              · linarith only [h3, h4117, h4121, h4124, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · linarith only [h2, h3, h4121, hc12, hc24, hlam, hphi]
        · linarith only [h3, h4117, h4120, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h4213 | h4213
      · linarith only [h2, h3, h4213, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4215 | h4215
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4216 | h4216
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4217 | h4217
            · linarith only [h0, h3, h4217, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4219 | h4219
              · linarith only [h0, h4117, h4219, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4221 | h4221
                · linarith only [h0, h4117, h4213, h4215, h4216, h4221, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h4223 | h4223
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4224 | h4224
                    · linarith only [h2, h3, h4221, h4224, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h4226 | h4226
                      · linarith only [h0, h4117, h4216, h4226, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4228 | h4228
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4229 | h4229
                          · rcases h2bigk with h4230c | h4230c | h4230c | h4230c | h4230c | h4230c | h4230c | h4230c | h4230c | h4230c | h4230c | h4230c | h4230c | h4230c | h4230c | h4230c | h4230c | h4230c | h4230c | h4230c | h4230c | h4230c | h4230c | h4230c | h4230c
                            · have p4230_0 := h4230c.1
                              have p4230_1 := h4230c.2.1
                              have p4230_2 := h4230c.2.2.1
                              have p4230_3 := h4230c.2.2.2
                              linarith only [hlam, p4230_0]
                            · have p4230_0 := h4230c.1
                              have p4230_1 := h4230c.2.1
                              have p4230_2 := h4230c.2.2.1
                              have p4230_3 := h4230c.2.2.2
                              linarith only [h4117, h4224, h4228, hc12, hc34, hlam, hphi, ht23, p4230_1]
                            · have p4230_0 := h4230c.1
                              have p4230_1 := h4230c.2.1
                              have p4230_2 := h4230c.2.2.1
                              have p4230_3 := h4230c.2.2.2
                              linarith only [h4117, h4224, h4228, hc23, hc34, hlam, hphi, p4230_1]
                            · have p4230_0 := h4230c.1
                              have p4230_1 := h4230c.2.1
                              have p4230_2 := h4230c.2.2.1
                              have p4230_3 := h4230c.2.2.2
                              linarith only [h3, hlam, p4230_0]
                            · have p4230_0 := h4230c.1
                              have p4230_1 := h4230c.2.1
                              have p4230_2 := h4230c.2.2.1
                              have p4230_3 := h4230c.2.2.2
                              linarith only [h4117, hlam, p4230_0]
                            · have p4230_0 := h4230c.1
                              have p4230_1 := h4230c.2.1
                              have p4230_2 := h4230c.2.2.1
                              have p4230_3 := h4230c.2.2.2
                              linarith only [h0, hlam, p4230_1]
                            · have p4230_0 := h4230c.1
                              have p4230_1 := h4230c.2.1
                              have p4230_2 := h4230c.2.2.1
                              have p4230_3 := h4230c.2.2.2
                              linarith only [hlam, p4230_0]
                            · have p4230_0 := h4230c.1
                              have p4230_1 := h4230c.2.1
                              have p4230_2 := h4230c.2.2.1
                              have p4230_3 := h4230c.2.2.2
                              linarith only [h0, h4117, h4224, h4228, hc23, hc34, hlam, hphi, p4230_1]
                            · have p4230_0 := h4230c.1
                              have p4230_1 := h4230c.2.1
                              have p4230_2 := h4230c.2.2.1
                              have p4230_3 := h4230c.2.2.2
                              linarith only [h4217, hlam, p4230_0]
                            · have p4230_0 := h4230c.1
                              have p4230_1 := h4230c.2.1
                              have p4230_2 := h4230c.2.2.1
                              have p4230_3 := h4230c.2.2.2
                              linarith only [h4219, hlam, p4230_0]
                            · have p4230_0 := h4230c.1
                              have p4230_1 := h4230c.2.1
                              have p4230_2 := h4230c.2.2.1
                              have p4230_3 := h4230c.2.2.2
                              linarith only [h2, hlam, p4230_0]
                            · have p4230_0 := h4230c.1
                              have p4230_1 := h4230c.2.1
                              have p4230_2 := h4230c.2.2.1
                              have p4230_3 := h4230c.2.2.2
                              linarith only [h4216, hlam, p4230_0]
                            · have p4230_0 := h4230c.1
                              have p4230_1 := h4230c.2.1
                              have p4230_2 := h4230c.2.2.1
                              have p4230_3 := h4230c.2.2.2
                              linarith only [hlam, p4230_0]
                            · have p4230_0 := h4230c.1
                              have p4230_1 := h4230c.2.1
                              have p4230_2 := h4230c.2.2.1
                              have p4230_3 := h4230c.2.2.2
                              linarith only [h4224, hlam, p4230_1]
                            · have p4230_0 := h4230c.1
                              have p4230_1 := h4230c.2.1
                              have p4230_2 := h4230c.2.2.1
                              have p4230_3 := h4230c.2.2.2
                              linarith only [h4226, hlam, p4230_1]
                            · have p4230_0 := h4230c.1
                              have p4230_1 := h4230c.2.1
                              have p4230_2 := h4230c.2.2.1
                              have p4230_3 := h4230c.2.2.2
                              linarith only [h2, h4224, hc23, hc34, hlam, hphi, p4230_1]
                            · have p4230_0 := h4230c.1
                              have p4230_1 := h4230c.2.1
                              have p4230_2 := h4230c.2.2.1
                              have p4230_3 := h4230c.2.2.2
                              linarith only [h4216, h4224, hc23, hc34, hlam, hphi, p4230_1]
                            · have p4230_0 := h4230c.1
                              have p4230_1 := h4230c.2.1
                              have p4230_2 := h4230c.2.2.1
                              have p4230_3 := h4230c.2.2.2
                              rcases p4230_3 (m.d 0 2) (by simp) with h4248 | h4248
                              · linarith only [h3, h4248, hlam]
                              · linarith only [h2, h4248, hlam]
                            · have p4230_0 := h4230c.1
                              have p4230_1 := h4230c.2.1
                              have p4230_2 := h4230c.2.2.1
                              have p4230_3 := h4230c.2.2.2
                              linarith only [hlam, p4230_0]
                            · have p4230_0 := h4230c.1
                              have p4230_1 := h4230c.2.1
                              have p4230_2 := h4230c.2.2.1
                              have p4230_3 := h4230c.2.2.2
                              linarith only [h0, h4117, h4216, h4224, hc23, hc34, hlam, hphi, p4230_1]
                            · have p4230_0 := h4230c.1
                              have p4230_1 := h4230c.2.1
                              have p4230_2 := h4230c.2.2.1
                              have p4230_3 := h4230c.2.2.2
                              linarith only [h0, h4216, h4226, hc23, hc35, hlam, hphi, p4230_1]
                            · have p4230_0 := h4230c.1
                              have p4230_1 := h4230c.2.1
                              have p4230_2 := h4230c.2.2.1
                              have p4230_3 := h4230c.2.2.2
                              linarith only [h4216, h4226, hc23, hc35, hlam, hphi, p4230_1]
                            · have p4230_0 := h4230c.1
                              have p4230_1 := h4230c.2.1
                              have p4230_2 := h4230c.2.2.1
                              have p4230_3 := h4230c.2.2.2
                              rcases p4230_3 (m.d 0 2) (by simp) with h4255 | h4255
                              · linarith only [h4117, h4255, hlam]
                              · linarith only [h2, h4255, hlam]
                            · have p4230_0 := h4230c.1
                              have p4230_1 := h4230c.2.1
                              have p4230_2 := h4230c.2.2.1
                              have p4230_3 := h4230c.2.2.2
                              linarith only [h4228, hlam, p4230_1]
                            · have p4230_0 := h4230c.1
                              have p4230_1 := h4230c.2.1
                              have p4230_2 := h4230c.2.2.1
                              have p4230_3 := h4230c.2.2.2
                              linarith only [hlam, p4230_0]
                          · linarith only [h0, h3, h4216, h4224, h4229, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h0, h3, h4216, h4223, h4228, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h4213, h4215, h4216, h4217, h4223, hc23, hc34, hlam, hphi]
          · linarith only [h2, h3, h4216, hc12, hc24, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4264 | h4264
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4265 | h4265
            · linarith only [h0, h3, h4265, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4267 | h4267
              · linarith only [h0, h4117, h4267, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4269 | h4269
                · linarith only [h0, h3, h4213, h4264, h4269, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h4271 | h4271
                  · linarith only [h1, h4215, h4271, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4273 | h4273
                    · linarith only [h0, h3, h4213, h4264, h4273, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h4275 | h4275
                      · linarith only [h0, h4117, h4264, h4275, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4277 | h4277
                        · linarith only [h0, h3, h4215, h4264, h4273, h4277, hc23, hc34, hlam, hphi]
                        · linarith only [h0, h3, h4264, h4277, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h2, h3, h4264, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 12300000 in
set_option maxHeartbeats 12300000 in
theorem r1l7_12_24_L_I_H_I_s1_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  exact r1l7_12_24_L_I_H_I_s2 m hb2 hb4 h0 h1 h2

end R2N4
