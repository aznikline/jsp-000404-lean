import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5526000 in
set_option maxHeartbeats 5526000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s5_x1_x1_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3977 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4846 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h5465 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h5778 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5779 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5780 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h5bigk := hb5.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
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
  rcases m.htr 0 3 4 (by decide) (by decide) with h5781 | h5781
  · rcases m.htr 0 3 5 (by decide) (by decide) with h5782 | h5782
    · rcases m.htr 0 4 5 (by decide) (by decide) with h5783 | h5783
      · rcases m.htr 1 2 3 (by decide) (by decide) with h5784 | h5784
        · rcases m.htr 1 2 4 (by decide) (by decide) with h5785 | h5785
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5786 | h5786
            · rcases m.htr 1 3 4 (by decide) (by decide) with h5787 | h5787
              · rcases m.htr 1 3 5 (by decide) (by decide) with h5788 | h5788
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5789 | h5789
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5790 | h5790
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5791 | h5791
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5792 | h5792
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5793 | h5793
                          · linarith only [h5778, h5790, h5793, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · rcases h2bigk with h5795c | h5795c | h5795c | h5795c | h5795c | h5795c | h5795c | h5795c | h5795c | h5795c | h5795c | h5795c | h5795c | h5795c | h5795c | h5795c | h5795c | h5795c | h5795c | h5795c | h5795c | h5795c | h5795c | h5795c | h5795c
                            · have p5795_0 := h5795c.1
                              have p5795_1 := h5795c.2.1
                              have p5795_2 := h5795c.2.2.1
                              have p5795_3 := h5795c.2.2.2
                              linarith only [hlam, p5795_0]
                            · have p5795_0 := h5795c.1
                              have p5795_1 := h5795c.2.1
                              have p5795_2 := h5795c.2.2.1
                              have p5795_3 := h5795c.2.2.2
                              linarith only [h0, hlam, p5795_1]
                            · have p5795_0 := h5795c.1
                              have p5795_1 := h5795c.2.1
                              have p5795_2 := h5795c.2.2.1
                              have p5795_3 := h5795c.2.2.2
                              linarith only [h0, h5790, h5792, h5793, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5795_1]
                            · have p5795_0 := h5795c.1
                              have p5795_1 := h5795c.2.1
                              have p5795_2 := h5795c.2.2.1
                              have p5795_3 := h5795c.2.2.2
                              linarith only [h0, h5792, h5793, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5795_1]
                            · have p5795_0 := h5795c.1
                              have p5795_1 := h5795c.2.1
                              have p5795_2 := h5795c.2.2.1
                              have p5795_3 := h5795c.2.2.2
                              rcases p5795_3 (m.d 0 2) (by simp) with h5800 | h5800
                              · rcases p5795_3 (m.d 1 2) (by simp) with h5801 | h5801
                                · rcases p5795_3 (m.d 2 3) (by simp) with h5802 | h5802
                                  · linarith only [h5778, h5802, hlam]
                                  · linarith only [h5791, h5802, hlam]
                                · linarith only [h5786, h5801, hlam]
                              · linarith only [h5800, hlam, p5795_0]
                            · have p5795_0 := h5795c.1
                              have p5795_1 := h5795c.2.1
                              have p5795_2 := h5795c.2.2.1
                              have p5795_3 := h5795c.2.2.2
                              linarith only [hc12, hlam, hphi, ht01, p5795_1, u0ehi1]
                            · have p5795_0 := h5795c.1
                              have p5795_1 := h5795c.2.1
                              have p5795_2 := h5795c.2.2.1
                              have p5795_3 := h5795c.2.2.2
                              linarith only [hlam, p5795_0]
                            · have p5795_0 := h5795c.1
                              have p5795_1 := h5795c.2.1
                              have p5795_2 := h5795c.2.2.1
                              have p5795_3 := h5795c.2.2.2
                              linarith only [h5790, h5792, h5793, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5795_1]
                            · have p5795_0 := h5795c.1
                              have p5795_1 := h5795c.2.1
                              have p5795_2 := h5795c.2.2.1
                              have p5795_3 := h5795c.2.2.2
                              linarith only [h5792, h5793, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5795_1]
                            · have p5795_0 := h5795c.1
                              have p5795_1 := h5795c.2.1
                              have p5795_2 := h5795c.2.2.1
                              have p5795_3 := h5795c.2.2.2
                              rcases p5795_3 (m.d 0 2) (by simp) with h5811 | h5811
                              · linarith only [h0, h5811, hlam]
                              · linarith only [h5780, h5811, hlam]
                            · have p5795_0 := h5795c.1
                              have p5795_1 := h5795c.2.1
                              have p5795_2 := h5795c.2.2.1
                              have p5795_3 := h5795c.2.2.2
                              linarith only [h5778, hlam, p5795_0]
                            · have p5795_0 := h5795c.1
                              have p5795_1 := h5795c.2.1
                              have p5795_2 := h5795c.2.2.1
                              have p5795_3 := h5795c.2.2.2
                              linarith only [h5784, hlam, p5795_0]
                            · have p5795_0 := h5795c.1
                              have p5795_1 := h5795c.2.1
                              have p5795_2 := h5795c.2.2.1
                              have p5795_3 := h5795c.2.2.2
                              linarith only [hlam, p5795_0]
                            · have p5795_0 := h5795c.1
                              have p5795_1 := h5795c.2.1
                              have p5795_2 := h5795c.2.2.1
                              have p5795_3 := h5795c.2.2.2
                              linarith only [h5778, h5792, h5793, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p5795_1]
                            · have p5795_0 := h5795c.1
                              have p5795_1 := h5795c.2.1
                              have p5795_2 := h5795c.2.2.1
                              have p5795_3 := h5795c.2.2.2
                              linarith only [h0, h5778, h5792, h5793, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5795_1]
                            · have p5795_0 := h5795c.1
                              have p5795_1 := h5795c.2.1
                              have p5795_2 := h5795c.2.2.1
                              have p5795_3 := h5795c.2.2.2
                              linarith only [h5779, hlam, p5795_0]
                            · have p5795_0 := h5795c.1
                              have p5795_1 := h5795c.2.1
                              have p5795_2 := h5795c.2.2.1
                              have p5795_3 := h5795c.2.2.2
                              linarith only [h5785, hlam, p5795_0]
                            · have p5795_0 := h5795c.1
                              have p5795_1 := h5795c.2.1
                              have p5795_2 := h5795c.2.2.1
                              have p5795_3 := h5795c.2.2.2
                              linarith only [h5790, hlam, p5795_1]
                            · have p5795_0 := h5795c.1
                              have p5795_1 := h5795c.2.1
                              have p5795_2 := h5795c.2.2.1
                              have p5795_3 := h5795c.2.2.2
                              linarith only [hlam, p5795_0]
                            · have p5795_0 := h5795c.1
                              have p5795_1 := h5795c.2.1
                              have p5795_2 := h5795c.2.2.1
                              have p5795_3 := h5795c.2.2.2
                              linarith only [h0, h5779, h5792, h5793, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5795_1]
                            · have p5795_0 := h5795c.1
                              have p5795_1 := h5795c.2.1
                              have p5795_2 := h5795c.2.2.1
                              have p5795_3 := h5795c.2.2.2
                              linarith only [h5780, hlam, p5795_0]
                            · have p5795_0 := h5795c.1
                              have p5795_1 := h5795c.2.1
                              have p5795_2 := h5795c.2.2.1
                              have p5795_3 := h5795c.2.2.2
                              linarith only [h5786, hlam, p5795_0]
                            · have p5795_0 := h5795c.1
                              have p5795_1 := h5795c.2.1
                              have p5795_2 := h5795c.2.2.1
                              have p5795_3 := h5795c.2.2.2
                              linarith only [h5791, hlam, p5795_1]
                            · have p5795_0 := h5795c.1
                              have p5795_1 := h5795c.2.1
                              have p5795_2 := h5795c.2.2.1
                              have p5795_3 := h5795c.2.2.2
                              linarith only [h5792, hlam, p5795_0]
                            · have p5795_0 := h5795c.1
                              have p5795_1 := h5795c.2.1
                              have p5795_2 := h5795c.2.2.1
                              have p5795_3 := h5795c.2.2.2
                              linarith only [hlam, p5795_0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5829 | h5829
                          · linarith only [h0, h5778, h5790, h5792, h5829, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases h2bigk with h5831c | h5831c | h5831c | h5831c | h5831c | h5831c | h5831c | h5831c | h5831c | h5831c | h5831c | h5831c | h5831c | h5831c | h5831c | h5831c | h5831c | h5831c | h5831c | h5831c | h5831c | h5831c | h5831c | h5831c | h5831c
                            · have p5831_0 := h5831c.1
                              have p5831_1 := h5831c.2.1
                              have p5831_2 := h5831c.2.2.1
                              have p5831_3 := h5831c.2.2.2
                              linarith only [hlam, p5831_0]
                            · have p5831_0 := h5831c.1
                              have p5831_1 := h5831c.2.1
                              have p5831_2 := h5831c.2.2.1
                              have p5831_3 := h5831c.2.2.2
                              linarith only [h0, hlam, p5831_1]
                            · have p5831_0 := h5831c.1
                              have p5831_1 := h5831c.2.1
                              have p5831_2 := h5831c.2.2.1
                              have p5831_3 := h5831c.2.2.2
                              linarith only [h0, h5791, hc12, hlam, hphi, ht01, ht0b, ht5b, p5831_1, u5ehi3]
                            · have p5831_0 := h5831c.1
                              have p5831_1 := h5831c.2.1
                              have p5831_2 := h5831c.2.2.1
                              have p5831_3 := h5831c.2.2.2
                              rcases p5831_3 (m.d 0 2) (by simp) with h5835 | h5835
                              · rcases p5831_3 (m.d 1 2) (by simp) with h5836 | h5836
                                · rcases p5831_3 (m.d 2 3) (by simp) with h5837 | h5837
                                  · linarith only [h5778, h5837, hlam]
                                  · linarith only [h5790, h5837, hlam]
                                · linarith only [h5785, h5836, hlam]
                              · linarith only [h5835, hlam, p5831_0]
                            · have p5831_0 := h5831c.1
                              have p5831_1 := h5831c.2.1
                              have p5831_2 := h5831c.2.2.1
                              have p5831_3 := h5831c.2.2.2
                              rcases p5831_3 (m.d 0 2) (by simp) with h5842 | h5842
                              · rcases p5831_3 (m.d 1 2) (by simp) with h5843 | h5843
                                · rcases p5831_3 (m.d 2 3) (by simp) with h5844 | h5844
                                  · linarith only [h5778, h5844, hlam]
                                  · linarith only [h5791, h5844, hlam]
                                · linarith only [h5786, h5843, hlam]
                              · linarith only [h5842, hlam, p5831_0]
                            · have p5831_0 := h5831c.1
                              have p5831_1 := h5831c.2.1
                              have p5831_2 := h5831c.2.2.1
                              have p5831_3 := h5831c.2.2.2
                              linarith only [hc12, hlam, hphi, ht01, p5831_1, u0ehi1]
                            · have p5831_0 := h5831c.1
                              have p5831_1 := h5831c.2.1
                              have p5831_2 := h5831c.2.2.1
                              have p5831_3 := h5831c.2.2.2
                              linarith only [hlam, p5831_0]
                            · have p5831_0 := h5831c.1
                              have p5831_1 := h5831c.2.1
                              have p5831_2 := h5831c.2.2.1
                              have p5831_3 := h5831c.2.2.2
                              linarith only [h5791, hc12, hlam, hphi, ht01, ht0b, ht5b, p5831_1, u5ehi3]
                            · have p5831_0 := h5831c.1
                              have p5831_1 := h5831c.2.1
                              have p5831_2 := h5831c.2.2.1
                              have p5831_3 := h5831c.2.2.2
                              rcases p5831_3 (m.d 0 2) (by simp) with h5852 | h5852
                              · linarith only [h0, h5852, hlam]
                              · linarith only [h5779, h5852, hlam]
                            · have p5831_0 := h5831c.1
                              have p5831_1 := h5831c.2.1
                              have p5831_2 := h5831c.2.2.1
                              have p5831_3 := h5831c.2.2.2
                              rcases p5831_3 (m.d 0 2) (by simp) with h5855 | h5855
                              · linarith only [h0, h5855, hlam]
                              · linarith only [h5780, h5855, hlam]
                            · have p5831_0 := h5831c.1
                              have p5831_1 := h5831c.2.1
                              have p5831_2 := h5831c.2.2.1
                              have p5831_3 := h5831c.2.2.2
                              linarith only [h5778, hlam, p5831_0]
                            · have p5831_0 := h5831c.1
                              have p5831_1 := h5831c.2.1
                              have p5831_2 := h5831c.2.2.1
                              have p5831_3 := h5831c.2.2.2
                              linarith only [h5784, hlam, p5831_0]
                            · have p5831_0 := h5831c.1
                              have p5831_1 := h5831c.2.1
                              have p5831_2 := h5831c.2.2.1
                              have p5831_3 := h5831c.2.2.2
                              linarith only [hlam, p5831_0]
                            · have p5831_0 := h5831c.1
                              have p5831_1 := h5831c.2.1
                              have p5831_2 := h5831c.2.2.1
                              have p5831_3 := h5831c.2.2.2
                              rcases p5831_3 (m.d 0 2) (by simp) with h5861 | h5861
                              · rcases p5831_3 (m.d 1 2) (by simp) with h5862 | h5862
                                · rcases p5831_3 (m.d 2 3) (by simp) with h5863 | h5863
                                  · rcases p5831_3 (m.d 2 4) (by simp) with h5864 | h5864
                                    · linarith only [h5790, h5864, hlam]
                                    · rcases p5831_3 (m.d 2 5) (by simp) with h5866 | h5866
                                      · linarith only [h5791, h5866, hlam]
                                      · linarith only [h5792, h5866, hlam]
                                  · linarith only [h5790, h5863, hlam]
                                · linarith only [h5785, h5862, hlam]
                              · linarith only [h5779, h5861, hlam]
                            · have p5831_0 := h5831c.1
                              have p5831_1 := h5831c.2.1
                              have p5831_2 := h5831c.2.2.1
                              have p5831_3 := h5831c.2.2.2
                              linarith only [h5778, h5791, hc02, hlam, hphi, ht0b, ht5b, p5831_1, u5ehi3]
                            · have p5831_0 := h5831c.1
                              have p5831_1 := h5831c.2.1
                              have p5831_2 := h5831c.2.2.1
                              have p5831_3 := h5831c.2.2.2
                              linarith only [h5779, hlam, p5831_0]
                            · have p5831_0 := h5831c.1
                              have p5831_1 := h5831c.2.1
                              have p5831_2 := h5831c.2.2.1
                              have p5831_3 := h5831c.2.2.2
                              linarith only [h5785, hlam, p5831_0]
                            · have p5831_0 := h5831c.1
                              have p5831_1 := h5831c.2.1
                              have p5831_2 := h5831c.2.2.1
                              have p5831_3 := h5831c.2.2.2
                              linarith only [h5790, hlam, p5831_1]
                            · have p5831_0 := h5831c.1
                              have p5831_1 := h5831c.2.1
                              have p5831_2 := h5831c.2.2.1
                              have p5831_3 := h5831c.2.2.2
                              linarith only [hlam, p5831_0]
                            · have p5831_0 := h5831c.1
                              have p5831_1 := h5831c.2.1
                              have p5831_2 := h5831c.2.2.1
                              have p5831_3 := h5831c.2.2.2
                              linarith only [h5792, hlam, p5831_1]
                            · have p5831_0 := h5831c.1
                              have p5831_1 := h5831c.2.1
                              have p5831_2 := h5831c.2.2.1
                              have p5831_3 := h5831c.2.2.2
                              linarith only [h5780, hlam, p5831_0]
                            · have p5831_0 := h5831c.1
                              have p5831_1 := h5831c.2.1
                              have p5831_2 := h5831c.2.2.1
                              have p5831_3 := h5831c.2.2.2
                              linarith only [h5786, hlam, p5831_0]
                            · have p5831_0 := h5831c.1
                              have p5831_1 := h5831c.2.1
                              have p5831_2 := h5831c.2.2.1
                              have p5831_3 := h5831c.2.2.2
                              linarith only [h5791, hlam, p5831_1]
                            · have p5831_0 := h5831c.1
                              have p5831_1 := h5831c.2.1
                              have p5831_2 := h5831c.2.2.1
                              have p5831_3 := h5831c.2.2.2
                              rcases p5831_3 (m.d 0 2) (by simp) with h5881 | h5881
                              · rcases p5831_3 (m.d 1 2) (by simp) with h5882 | h5882
                                · rcases p5831_3 (m.d 2 3) (by simp) with h5883 | h5883
                                  · rcases p5831_3 (m.d 2 4) (by simp) with h5884 | h5884
                                    · linarith only [h5792, h5884, hlam]
                                    · rcases p5831_3 (m.d 2 5) (by simp) with h5886 | h5886
                                      · rcases h3bigk with h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c | h5887c
                                        · have p5887_0 := h5887c.1
                                          have p5887_1 := h5887c.2.1
                                          have p5887_2 := h5887c.2.2.1
                                          have p5887_3 := h5887c.2.2.2
                                          linarith only [hlam, p5887_0]
                                        · have p5887_0 := h5887c.1
                                          have p5887_1 := h5887c.2.1
                                          have p5887_2 := h5887c.2.2.1
                                          have p5887_3 := h5887c.2.2.2
                                          linarith only [h3977, hlam, p5887_1]
                                        · have p5887_0 := h5887c.1
                                          have p5887_1 := h5887c.2.1
                                          have p5887_2 := h5887c.2.2.1
                                          have p5887_3 := h5887c.2.2.2
                                          linarith only [h0, h5778, h5791, hc12, hlam, hphi, ht01, ht0b, ht5b, p5887_1, u5ehi3]
                                        · have p5887_0 := h5887c.1
                                          have p5887_1 := h5887c.2.1
                                          have p5887_2 := h5887c.2.2.1
                                          have p5887_3 := h5887c.2.2.2
                                          linarith only [h5781, h5783, h5790, h5792, hlam, p5831_1, p5887_2]
                                        · have p5887_0 := h5887c.1
                                          have p5887_1 := h5887c.2.1
                                          have p5887_2 := h5887c.2.2.1
                                          have p5887_3 := h5887c.2.2.2
                                          rcases p5887_3 (m.d 0 3) (by simp) with h5892 | h5892
                                          · rcases p5887_3 (m.d 1 3) (by simp) with h5893 | h5893
                                            · rcases p5887_3 (m.d 2 3) (by simp) with h5894 | h5894
                                              · linarith only [h5778, h5894, hlam]
                                              · linarith only [h5791, h5894, hlam]
                                            · linarith only [h5788, h5893, hlam]
                                          · linarith only [h5892, hlam, p5887_0]
                                        · have p5887_0 := h5887c.1
                                          have p5887_1 := h5887c.2.1
                                          have p5887_2 := h5887c.2.2.1
                                          have p5887_3 := h5887c.2.2.2
                                          linarith only [h5781, h5783, h5784, h5790, h5792, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5831_1, p5887_1]
                                        · have p5887_0 := h5887c.1
                                          have p5887_1 := h5887c.2.1
                                          have p5887_2 := h5887c.2.2.1
                                          have p5887_3 := h5887c.2.2.2
                                          linarith only [hlam, p5887_0]
                                        · have p5887_0 := h5887c.1
                                          have p5887_1 := h5887c.2.1
                                          have p5887_2 := h5887c.2.2.1
                                          have p5887_3 := h5887c.2.2.2
                                          linarith only [h5784, h5790, h5791, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5831_1, p5887_1]
                                        · have p5887_0 := h5887c.1
                                          have p5887_1 := h5887c.2.1
                                          have p5887_2 := h5887c.2.2.1
                                          have p5887_3 := h5887c.2.2.2
                                          linarith only [h3977, h5781, h5783, h5790, h5792, hlam, p5831_1, p5887_2]
                                        · have p5887_0 := h5887c.1
                                          have p5887_1 := h5887c.2.1
                                          have p5887_2 := h5887c.2.2.1
                                          have p5887_3 := h5887c.2.2.2
                                          rcases p5887_3 (m.d 0 3) (by simp) with h5903 | h5903
                                          · linarith only [h3977, h5903, hlam]
                                          · linarith only [h5782, h5903, hlam]
                                        · have p5887_0 := h5887c.1
                                          have p5887_1 := h5887c.2.1
                                          have p5887_2 := h5887c.2.2.1
                                          have p5887_3 := h5887c.2.2.2
                                          linarith only [h5778, hlam, p5887_0]
                                        · have p5887_0 := h5887c.1
                                          have p5887_1 := h5887c.2.1
                                          have p5887_2 := h5887c.2.2.1
                                          have p5887_3 := h5887c.2.2.2
                                          linarith only [h5784, hlam, p5887_0]
                                        · have p5887_0 := h5887c.1
                                          have p5887_1 := h5887c.2.1
                                          have p5887_2 := h5887c.2.2.1
                                          have p5887_3 := h5887c.2.2.2
                                          linarith only [hlam, p5887_0]
                                        · have p5887_0 := h5887c.1
                                          have p5887_1 := h5887c.2.1
                                          have p5887_2 := h5887c.2.2.1
                                          have p5887_3 := h5887c.2.2.2
                                          rcases p5887_3 (m.d 0 3) (by simp) with h5909 | h5909
                                          · rcases p5887_3 (m.d 1 3) (by simp) with h5910 | h5910
                                            · rcases p5887_3 (m.d 2 3) (by simp) with h5911 | h5911
                                              · rcases p5887_3 (m.d 3 4) (by simp) with h5912 | h5912
                                                · linarith only [h5912, hlam, p5887_0]
                                                · rcases p5887_3 (m.d 3 5) (by simp) with h5914 | h5914
                                                  · linarith only [h5791, h5914, hlam]
                                                  · linarith only [h5829, h5914, hlam]
                                              · linarith only [h5911, hlam, p5887_0]
                                            · linarith only [h5787, h5910, hlam]
                                          · linarith only [h5781, h5909, hlam]
                                        · have p5887_0 := h5887c.1
                                          have p5887_1 := h5887c.2.1
                                          have p5887_2 := h5887c.2.2.1
                                          have p5887_3 := h5887c.2.2.2
                                          linarith only [h0, h5778, hc12, hlam, hphi, ht01, ht0b, ht5b, p5887_1, u5ehi3]
                                        · have p5887_0 := h5887c.1
                                          have p5887_1 := h5887c.2.1
                                          have p5887_2 := h5887c.2.2.1
                                          have p5887_3 := h5887c.2.2.2
                                          linarith only [h5781, hlam, p5887_0]
                                        · have p5887_0 := h5887c.1
                                          have p5887_1 := h5887c.2.1
                                          have p5887_2 := h5887c.2.2.1
                                          have p5887_3 := h5887c.2.2.2
                                          linarith only [h5787, hlam, p5887_0]
                                        · have p5887_0 := h5887c.1
                                          have p5887_1 := h5887c.2.1
                                          have p5887_2 := h5887c.2.2.1
                                          have p5887_3 := h5887c.2.2.2
                                          linarith only [h5790, hlam, p5887_0]
                                        · have p5887_0 := h5887c.1
                                          have p5887_1 := h5887c.2.1
                                          have p5887_2 := h5887c.2.2.1
                                          have p5887_3 := h5887c.2.2.2
                                          linarith only [hlam, p5887_0]
                                        · have p5887_0 := h5887c.1
                                          have p5887_1 := h5887c.2.1
                                          have p5887_2 := h5887c.2.2.1
                                          have p5887_3 := h5887c.2.2.2
                                          linarith only [h5829, hlam, p5887_1]
                                        · have p5887_0 := h5887c.1
                                          have p5887_1 := h5887c.2.1
                                          have p5887_2 := h5887c.2.2.1
                                          have p5887_3 := h5887c.2.2.2
                                          linarith only [h5782, hlam, p5887_0]
                                        · have p5887_0 := h5887c.1
                                          have p5887_1 := h5887c.2.1
                                          have p5887_2 := h5887c.2.2.1
                                          have p5887_3 := h5887c.2.2.2
                                          linarith only [h5788, hlam, p5887_0]
                                        · have p5887_0 := h5887c.1
                                          have p5887_1 := h5887c.2.1
                                          have p5887_2 := h5887c.2.2.1
                                          have p5887_3 := h5887c.2.2.2
                                          linarith only [h5791, hlam, p5887_0]
                                        · have p5887_0 := h5887c.1
                                          have p5887_1 := h5887c.2.1
                                          have p5887_2 := h5887c.2.2.1
                                          have p5887_3 := h5887c.2.2.2
                                          linarith only [h0, h5778, h5791, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5887_1]
                                        · have p5887_0 := h5887c.1
                                          have p5887_1 := h5887c.2.1
                                          have p5887_2 := h5887c.2.2.1
                                          have p5887_3 := h5887c.2.2.2
                                          linarith only [hlam, p5887_0]
                                      · linarith only [h5792, h5886, hlam]
                                  · linarith only [h5790, h5883, hlam]
                                · linarith only [h5785, h5882, hlam]
                              · linarith only [h5779, h5881, hlam]
                            · have p5831_0 := h5831c.1
                              have p5831_1 := h5831c.2.1
                              have p5831_2 := h5831c.2.2.1
                              have p5831_3 := h5831c.2.2.2
                              linarith only [hlam, p5831_0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5936 | h5936
                        · linarith only [h0, h5778, h5782, h5790, h5791, h5936, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5938 | h5938
                          · linarith only [h0, h5778, h5782, h5790, h5791, h5936, h5938, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases h2bigk with h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c | h5940c
                            · have p5940_0 := h5940c.1
                              have p5940_1 := h5940c.2.1
                              have p5940_2 := h5940c.2.2.1
                              have p5940_3 := h5940c.2.2.2
                              linarith only [hlam, p5940_0]
                            · have p5940_0 := h5940c.1
                              have p5940_1 := h5940c.2.1
                              have p5940_2 := h5940c.2.2.1
                              have p5940_3 := h5940c.2.2.2
                              linarith only [h0, hlam, p5940_1]
                            · have p5940_0 := h5940c.1
                              have p5940_1 := h5940c.2.1
                              have p5940_2 := h5940c.2.2.1
                              have p5940_3 := h5940c.2.2.2
                              rcases p5940_3 (m.d 0 2) (by simp) with h5943 | h5943
                              · rcases p5940_3 (m.d 1 2) (by simp) with h5944 | h5944
                                · rcases p5940_3 (m.d 2 3) (by simp) with h5945 | h5945
                                  · linarith only [h5945, hlam, p5940_0]
                                  · rcases p5940_3 (m.d 2 4) (by simp) with h5947 | h5947
                                    · linarith only [h5779, h5947, hlam]
                                    · rcases p5940_3 (m.d 2 5) (by simp) with h5949 | h5949
                                      · linarith only [h5780, h5949, hlam]
                                      · linarith only [h5791, h5949, hlam]
                                · linarith only [h5784, h5944, hlam]
                              · linarith only [h5943, hlam, p5940_0]
                            · have p5940_0 := h5940c.1
                              have p5940_1 := h5940c.2.1
                              have p5940_2 := h5940c.2.2.1
                              have p5940_3 := h5940c.2.2.2
                              rcases p5940_3 (m.d 0 2) (by simp) with h5954 | h5954
                              · rcases p5940_3 (m.d 1 2) (by simp) with h5955 | h5955
                                · rcases p5940_3 (m.d 2 3) (by simp) with h5956 | h5956
                                  · linarith only [h5778, h5956, hlam]
                                  · linarith only [h5790, h5956, hlam]
                                · linarith only [h5785, h5955, hlam]
                              · linarith only [h5954, hlam, p5940_0]
                            · have p5940_0 := h5940c.1
                              have p5940_1 := h5940c.2.1
                              have p5940_2 := h5940c.2.2.1
                              have p5940_3 := h5940c.2.2.2
                              rcases p5940_3 (m.d 0 2) (by simp) with h5961 | h5961
                              · rcases p5940_3 (m.d 1 2) (by simp) with h5962 | h5962
                                · rcases p5940_3 (m.d 2 3) (by simp) with h5963 | h5963
                                  · linarith only [h5778, h5963, hlam]
                                  · rcases p5940_3 (m.d 2 4) (by simp) with h5965 | h5965
                                    · linarith only [h5779, h5965, hlam]
                                    · rcases p5940_3 (m.d 2 5) (by simp) with h5967 | h5967
                                      · linarith only [h5967, hlam, p5940_0]
                                      · rcases h3bigk with h5969c | h5969c | h5969c | h5969c | h5969c | h5969c | h5969c | h5969c | h5969c | h5969c | h5969c | h5969c | h5969c | h5969c | h5969c | h5969c | h5969c | h5969c | h5969c | h5969c | h5969c | h5969c | h5969c | h5969c | h5969c
                                        · have p5969_0 := h5969c.1
                                          have p5969_1 := h5969c.2.1
                                          have p5969_2 := h5969c.2.2.1
                                          have p5969_3 := h5969c.2.2.2
                                          linarith only [hlam, p5969_0]
                                        · have p5969_0 := h5969c.1
                                          have p5969_1 := h5969c.2.1
                                          have p5969_2 := h5969c.2.2.1
                                          have p5969_3 := h5969c.2.2.2
                                          linarith only [h3977, hlam, p5969_1]
                                        · have p5969_0 := h5969c.1
                                          have p5969_1 := h5969c.2.1
                                          have p5969_2 := h5969c.2.2.1
                                          have p5969_3 := h5969c.2.2.2
                                          rcases p5969_3 (m.d 0 3) (by simp) with h5972 | h5972
                                          · rcases p5969_3 (m.d 1 3) (by simp) with h5973 | h5973
                                            · rcases p5969_3 (m.d 2 3) (by simp) with h5974 | h5974
                                              · linarith only [h5778, h5974, hlam]
                                              · rcases p5969_3 (m.d 3 4) (by simp) with h5976 | h5976
                                                · linarith only [h5781, h5976, hlam]
                                                · rcases p5969_3 (m.d 3 5) (by simp) with h5978 | h5978
                                                  · linarith only [h5782, h5978, hlam]
                                                  · linarith only [h5791, h5978, hlam]
                                            · linarith only [h5784, h5973, hlam]
                                          · linarith only [h5778, h5972, hlam]
                                        · have p5969_0 := h5969c.1
                                          have p5969_1 := h5969c.2.1
                                          have p5969_2 := h5969c.2.2.1
                                          have p5969_3 := h5969c.2.2.2
                                          linarith only [h5781, h5783, h5790, h5791, h5938, hlam, p5969_2]
                                        · have p5969_0 := h5969c.1
                                          have p5969_1 := h5969c.2.1
                                          have p5969_2 := h5969c.2.2.1
                                          have p5969_3 := h5969c.2.2.2
                                          linarith only [h0, h5778, h5790, h5791, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5969_1]
                                        · have p5969_0 := h5969c.1
                                          have p5969_1 := h5969c.2.1
                                          have p5969_2 := h5969c.2.2.1
                                          have p5969_3 := h5969c.2.2.2
                                          linarith only [h5781, h5783, h5784, hc12, hlam, hphi, ht01, ht0b, ht5b, p5969_1, u5ehi4]
                                        · have p5969_0 := h5969c.1
                                          have p5969_1 := h5969c.2.1
                                          have p5969_2 := h5969c.2.2.1
                                          have p5969_3 := h5969c.2.2.2
                                          linarith only [hlam, p5969_0]
                                        · have p5969_0 := h5969c.1
                                          have p5969_1 := h5969c.2.1
                                          have p5969_2 := h5969c.2.2.1
                                          have p5969_3 := h5969c.2.2.2
                                          rcases p5969_3 (m.d 0 3) (by simp) with h5987 | h5987
                                          · linarith only [h3977, h5987, hlam]
                                          · linarith only [h5778, h5987, hlam]
                                        · have p5969_0 := h5969c.1
                                          have p5969_1 := h5969c.2.1
                                          have p5969_2 := h5969c.2.2.1
                                          have p5969_3 := h5969c.2.2.2
                                          linarith only [h3977, h5781, h5783, h5790, h5791, h5938, hlam, p5969_2]
                                        · have p5969_0 := h5969c.1
                                          have p5969_1 := h5969c.2.1
                                          have p5969_2 := h5969c.2.2.1
                                          have p5969_3 := h5969c.2.2.2
                                          linarith only [h5790, h5791, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5969_1]
                                        · have p5969_0 := h5969c.1
                                          have p5969_1 := h5969c.2.1
                                          have p5969_2 := h5969c.2.2.1
                                          have p5969_3 := h5969c.2.2.2
                                          linarith only [h5778, hlam, p5969_0]
                                        · have p5969_0 := h5969c.1
                                          have p5969_1 := h5969c.2.1
                                          have p5969_2 := h5969c.2.2.1
                                          have p5969_3 := h5969c.2.2.2
                                          linarith only [h5784, hlam, p5969_0]
                                        · have p5969_0 := h5969c.1
                                          have p5969_1 := h5969c.2.1
                                          have p5969_2 := h5969c.2.2.1
                                          have p5969_3 := h5969c.2.2.2
                                          linarith only [hlam, p5969_0]
                                        · have p5969_0 := h5969c.1
                                          have p5969_1 := h5969c.2.1
                                          have p5969_2 := h5969c.2.2.1
                                          have p5969_3 := h5969c.2.2.2
                                          linarith only [h5781, h5783, h5791, h5938, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p5969_1]
                                        · have p5969_0 := h5969c.1
                                          have p5969_1 := h5969c.2.1
                                          have p5969_2 := h5969c.2.2.1
                                          have p5969_3 := h5969c.2.2.2
                                          linarith only [h5791, hlam, p5969_0]
                                        · have p5969_0 := h5969c.1
                                          have p5969_1 := h5969c.2.1
                                          have p5969_2 := h5969c.2.2.1
                                          have p5969_3 := h5969c.2.2.2
                                          linarith only [h5781, hlam, p5969_0]
                                        · have p5969_0 := h5969c.1
                                          have p5969_1 := h5969c.2.1
                                          have p5969_2 := h5969c.2.2.1
                                          have p5969_3 := h5969c.2.2.2
                                          linarith only [h5787, hlam, p5969_0]
                                        · have p5969_0 := h5969c.1
                                          have p5969_1 := h5969c.2.1
                                          have p5969_2 := h5969c.2.2.1
                                          have p5969_3 := h5969c.2.2.2
                                          linarith only [h5790, hlam, p5969_0]
                                        · have p5969_0 := h5969c.1
                                          have p5969_1 := h5969c.2.1
                                          have p5969_2 := h5969c.2.2.1
                                          have p5969_3 := h5969c.2.2.2
                                          linarith only [hlam, p5969_0]
                                        · have p5969_0 := h5969c.1
                                          have p5969_1 := h5969c.2.1
                                          have p5969_2 := h5969c.2.2.1
                                          have p5969_3 := h5969c.2.2.2
                                          linarith only [h5938, hlam, p5969_1]
                                        · have p5969_0 := h5969c.1
                                          have p5969_1 := h5969c.2.1
                                          have p5969_2 := h5969c.2.2.1
                                          have p5969_3 := h5969c.2.2.2
                                          linarith only [h5782, hlam, p5969_0]
                                        · have p5969_0 := h5969c.1
                                          have p5969_1 := h5969c.2.1
                                          have p5969_2 := h5969c.2.2.1
                                          have p5969_3 := h5969c.2.2.2
                                          linarith only [h5788, hlam, p5969_0]
                                        · have p5969_0 := h5969c.1
                                          have p5969_1 := h5969c.2.1
                                          have p5969_2 := h5969c.2.2.1
                                          have p5969_3 := h5969c.2.2.2
                                          linarith only [h0, h5778, h5781, h5783, h5790, h5938, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5969_1]
                                        · have p5969_0 := h5969c.1
                                          have p5969_1 := h5969c.2.1
                                          have p5969_2 := h5969c.2.2.1
                                          have p5969_3 := h5969c.2.2.2
                                          rcases p5969_3 (m.d 0 3) (by simp) with h6005 | h6005
                                          · rcases p5969_3 (m.d 1 3) (by simp) with h6006 | h6006
                                            · rcases p5969_3 (m.d 2 3) (by simp) with h6007 | h6007
                                              · linarith only [h5791, h6007, hlam]
                                              · linarith only [h5790, h6007, hlam]
                                            · linarith only [h5787, h6006, hlam]
                                          · linarith only [h5781, h6005, hlam]
                                        · have p5969_0 := h5969c.1
                                          have p5969_1 := h5969c.2.1
                                          have p5969_2 := h5969c.2.2.1
                                          have p5969_3 := h5969c.2.2.2
                                          linarith only [hlam, p5969_0]
                                · linarith only [h5786, h5962, hlam]
                              · linarith only [h5961, hlam, p5940_0]
                            · have p5940_0 := h5940c.1
                              have p5940_1 := h5940c.2.1
                              have p5940_2 := h5940c.2.2.1
                              have p5940_3 := h5940c.2.2.2
                              linarith only [h5778, h5781, h5783, h5938, hc12, hlam, hphi, ht01, ht0b, ht5b, p5940_1, u5ehi3]
                            · have p5940_0 := h5940c.1
                              have p5940_1 := h5940c.2.1
                              have p5940_2 := h5940c.2.2.1
                              have p5940_3 := h5940c.2.2.2
                              linarith only [hlam, p5940_0]
                            · have p5940_0 := h5940c.1
                              have p5940_1 := h5940c.2.1
                              have p5940_2 := h5940c.2.2.1
                              have p5940_3 := h5940c.2.2.2
                              rcases p5940_3 (m.d 0 2) (by simp) with h6017 | h6017
                              · linarith only [h0, h6017, hlam]
                              · linarith only [h5778, h6017, hlam]
                            · have p5940_0 := h5940c.1
                              have p5940_1 := h5940c.2.1
                              have p5940_2 := h5940c.2.2.1
                              have p5940_3 := h5940c.2.2.2
                              rcases p5940_3 (m.d 0 2) (by simp) with h6020 | h6020
                              · linarith only [h0, h6020, hlam]
                              · linarith only [h5779, h6020, hlam]
                            · have p5940_0 := h5940c.1
                              have p5940_1 := h5940c.2.1
                              have p5940_2 := h5940c.2.2.1
                              have p5940_3 := h5940c.2.2.2
                              rcases p5940_3 (m.d 0 2) (by simp) with h6023 | h6023
                              · linarith only [h0, h6023, hlam]
                              · linarith only [h5780, h6023, hlam]
                            · have p5940_0 := h5940c.1
                              have p5940_1 := h5940c.2.1
                              have p5940_2 := h5940c.2.2.1
                              have p5940_3 := h5940c.2.2.2
                              linarith only [h5778, hlam, p5940_0]
                            · have p5940_0 := h5940c.1
                              have p5940_1 := h5940c.2.1
                              have p5940_2 := h5940c.2.2.1
                              have p5940_3 := h5940c.2.2.2
                              linarith only [h5784, hlam, p5940_0]
                            · have p5940_0 := h5940c.1
                              have p5940_1 := h5940c.2.1
                              have p5940_2 := h5940c.2.2.1
                              have p5940_3 := h5940c.2.2.2
                              linarith only [hlam, p5940_0]
                            · have p5940_0 := h5940c.1
                              have p5940_1 := h5940c.2.1
                              have p5940_2 := h5940c.2.2.1
                              have p5940_3 := h5940c.2.2.2
                              linarith only [h5778, h5781, h5783, h5791, h5938, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p5940_1]
                            · have p5940_0 := h5940c.1
                              have p5940_1 := h5940c.2.1
                              have p5940_2 := h5940c.2.2.1
                              have p5940_3 := h5940c.2.2.2
                              linarith only [h5791, hlam, p5940_0]
                            · have p5940_0 := h5940c.1
                              have p5940_1 := h5940c.2.1
                              have p5940_2 := h5940c.2.2.1
                              have p5940_3 := h5940c.2.2.2
                              linarith only [h5779, hlam, p5940_0]
                            · have p5940_0 := h5940c.1
                              have p5940_1 := h5940c.2.1
                              have p5940_2 := h5940c.2.2.1
                              have p5940_3 := h5940c.2.2.2
                              linarith only [h5785, hlam, p5940_0]
                            · have p5940_0 := h5940c.1
                              have p5940_1 := h5940c.2.1
                              have p5940_2 := h5940c.2.2.1
                              have p5940_3 := h5940c.2.2.2
                              linarith only [h5790, hlam, p5940_1]
                            · have p5940_0 := h5940c.1
                              have p5940_1 := h5940c.2.1
                              have p5940_2 := h5940c.2.2.1
                              have p5940_3 := h5940c.2.2.2
                              linarith only [hlam, p5940_0]
                            · have p5940_0 := h5940c.1
                              have p5940_1 := h5940c.2.1
                              have p5940_2 := h5940c.2.2.1
                              have p5940_3 := h5940c.2.2.2
                              linarith only [h5936, hlam, p5940_1]
                            · have p5940_0 := h5940c.1
                              have p5940_1 := h5940c.2.1
                              have p5940_2 := h5940c.2.2.1
                              have p5940_3 := h5940c.2.2.2
                              linarith only [h5780, hlam, p5940_0]
                            · have p5940_0 := h5940c.1
                              have p5940_1 := h5940c.2.1
                              have p5940_2 := h5940c.2.2.1
                              have p5940_3 := h5940c.2.2.2
                              linarith only [h5786, hlam, p5940_0]
                            · have p5940_0 := h5940c.1
                              have p5940_1 := h5940c.2.1
                              have p5940_2 := h5940c.2.2.1
                              have p5940_3 := h5940c.2.2.2
                              linarith only [h0, h5780, h5790, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5940_1]
                            · have p5940_0 := h5940c.1
                              have p5940_1 := h5940c.2.1
                              have p5940_2 := h5940c.2.2.1
                              have p5940_3 := h5940c.2.2.2
                              rcases p5940_3 (m.d 0 2) (by simp) with h6039 | h6039
                              · rcases p5940_3 (m.d 1 2) (by simp) with h6040 | h6040
                                · rcases p5940_3 (m.d 2 3) (by simp) with h6041 | h6041
                                  · linarith only [h5791, h6041, hlam]
                                  · linarith only [h5790, h6041, hlam]
                                · linarith only [h5785, h6040, hlam]
                              · linarith only [h5779, h6039, hlam]
                            · have p5940_0 := h5940c.1
                              have p5940_1 := h5940c.2.1
                              have p5940_2 := h5940c.2.2.1
                              have p5940_3 := h5940c.2.2.2
                              linarith only [hlam, p5940_0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h6047 | h6047
                      · linarith only [h0, h5778, h5781, h5790, h6047, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6049 | h6049
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h6050 | h6050
                          · rcases h2bigk with h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c
                            · have p6051_0 := h6051c.1
                              have p6051_1 := h6051c.2.1
                              have p6051_2 := h6051c.2.2.1
                              have p6051_3 := h6051c.2.2.2
                              linarith only [hlam, p6051_0]
                            · have p6051_0 := h6051c.1
                              have p6051_1 := h6051c.2.1
                              have p6051_2 := h6051c.2.2.1
                              have p6051_3 := h6051c.2.2.2
                              linarith only [h0, hlam, p6051_1]
                            · have p6051_0 := h6051c.1
                              have p6051_1 := h6051c.2.1
                              have p6051_2 := h6051c.2.2.1
                              have p6051_3 := h6051c.2.2.2
                              rcases p6051_3 (m.d 0 2) (by simp) with h6054 | h6054
                              · rcases p6051_3 (m.d 1 2) (by simp) with h6055 | h6055
                                · rcases p6051_3 (m.d 2 3) (by simp) with h6056 | h6056
                                  · linarith only [h6056, hlam, p6051_0]
                                  · rcases p6051_3 (m.d 2 4) (by simp) with h6058 | h6058
                                    · linarith only [h5779, h6058, hlam]
                                    · linarith only [h5790, h6058, hlam]
                                · linarith only [h5784, h6055, hlam]
                              · linarith only [h6054, hlam, p6051_0]
                            · have p6051_0 := h6051c.1
                              have p6051_1 := h6051c.2.1
                              have p6051_2 := h6051c.2.2.1
                              have p6051_3 := h6051c.2.2.2
                              linarith only [h0, h6049, hc12, hlam, hphi, ht01, ht0b, ht5b, p6051_1, u5ehi4]
                            · have p6051_0 := h6051c.1
                              have p6051_1 := h6051c.2.1
                              have p6051_2 := h6051c.2.2.1
                              have p6051_3 := h6051c.2.2.2
                              rcases p6051_3 (m.d 0 2) (by simp) with h6064 | h6064
                              · rcases p6051_3 (m.d 1 2) (by simp) with h6065 | h6065
                                · rcases p6051_3 (m.d 2 3) (by simp) with h6066 | h6066
                                  · linarith only [h5778, h6066, hlam]
                                  · rcases p6051_3 (m.d 2 4) (by simp) with h6068 | h6068
                                    · linarith only [h5779, h6068, hlam]
                                    · linarith only [h6049, h6068, hlam]
                                · linarith only [h5786, h6065, hlam]
                              · linarith only [h6064, hlam, p6051_0]
                            · have p6051_0 := h6051c.1
                              have p6051_1 := h6051c.2.1
                              have p6051_2 := h6051c.2.2.1
                              have p6051_3 := h6051c.2.2.2
                              linarith only [h5778, h5781, h6047, h6050, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6051_1]
                            · have p6051_0 := h6051c.1
                              have p6051_1 := h6051c.2.1
                              have p6051_2 := h6051c.2.2.1
                              have p6051_3 := h6051c.2.2.2
                              linarith only [hlam, p6051_0]
                            · have p6051_0 := h6051c.1
                              have p6051_1 := h6051c.2.1
                              have p6051_2 := h6051c.2.2.1
                              have p6051_3 := h6051c.2.2.2
                              rcases p6051_3 (m.d 0 2) (by simp) with h6075 | h6075
                              · linarith only [h0, h6075, hlam]
                              · linarith only [h5778, h6075, hlam]
                            · have p6051_0 := h6051c.1
                              have p6051_1 := h6051c.2.1
                              have p6051_2 := h6051c.2.2.1
                              have p6051_3 := h6051c.2.2.2
                              linarith only [h6049, hc12, hlam, hphi, ht01, ht0b, ht5b, p6051_1, u5ehi4]
                            · have p6051_0 := h6051c.1
                              have p6051_1 := h6051c.2.1
                              have p6051_2 := h6051c.2.2.1
                              have p6051_3 := h6051c.2.2.2
                              rcases p6051_3 (m.d 0 2) (by simp) with h6079 | h6079
                              · linarith only [h0, h6079, hlam]
                              · linarith only [h5780, h6079, hlam]
                            · have p6051_0 := h6051c.1
                              have p6051_1 := h6051c.2.1
                              have p6051_2 := h6051c.2.2.1
                              have p6051_3 := h6051c.2.2.2
                              linarith only [h5778, hlam, p6051_0]
                            · have p6051_0 := h6051c.1
                              have p6051_1 := h6051c.2.1
                              have p6051_2 := h6051c.2.2.1
                              have p6051_3 := h6051c.2.2.2
                              linarith only [h5784, hlam, p6051_0]
                            · have p6051_0 := h6051c.1
                              have p6051_1 := h6051c.2.1
                              have p6051_2 := h6051c.2.2.1
                              have p6051_3 := h6051c.2.2.2
                              linarith only [hlam, p6051_0]
                            · have p6051_0 := h6051c.1
                              have p6051_1 := h6051c.2.1
                              have p6051_2 := h6051c.2.2.1
                              have p6051_3 := h6051c.2.2.2
                              linarith only [h5790, hlam, p6051_0]
                            · have p6051_0 := h6051c.1
                              have p6051_1 := h6051c.2.1
                              have p6051_2 := h6051c.2.2.1
                              have p6051_3 := h6051c.2.2.2
                              linarith only [h6047, hlam, p6051_0]
                            · have p6051_0 := h6051c.1
                              have p6051_1 := h6051c.2.1
                              have p6051_2 := h6051c.2.2.1
                              have p6051_3 := h6051c.2.2.2
                              linarith only [h5779, hlam, p6051_0]
                            · have p6051_0 := h6051c.1
                              have p6051_1 := h6051c.2.1
                              have p6051_2 := h6051c.2.2.1
                              have p6051_3 := h6051c.2.2.2
                              linarith only [h5785, hlam, p6051_0]
                            · have p6051_0 := h6051c.1
                              have p6051_1 := h6051c.2.1
                              have p6051_2 := h6051c.2.2.1
                              have p6051_3 := h6051c.2.2.2
                              rcases p6051_3 (m.d 0 2) (by simp) with h6089 | h6089
                              · rcases p6051_3 (m.d 1 2) (by simp) with h6090 | h6090
                                · rcases p6051_3 (m.d 2 3) (by simp) with h6091 | h6091
                                  · linarith only [h5790, h6091, hlam]
                                  · rcases p6051_3 (m.d 2 4) (by simp) with h6093 | h6093
                                    · rcases p6051_3 (m.d 2 5) (by simp) with h6094 | h6094
                                      · linarith only [h6049, h6094, hlam]
                                      · linarith only [h6047, h6094, hlam]
                                    · linarith only [h5790, h6093, hlam]
                                · linarith only [h5784, h6090, hlam]
                              · linarith only [h5778, h6089, hlam]
                            · have p6051_0 := h6051c.1
                              have p6051_1 := h6051c.2.1
                              have p6051_2 := h6051c.2.2.1
                              have p6051_3 := h6051c.2.2.2
                              linarith only [hlam, p6051_0]
                            · have p6051_0 := h6051c.1
                              have p6051_1 := h6051c.2.1
                              have p6051_2 := h6051c.2.2.1
                              have p6051_3 := h6051c.2.2.2
                              linarith only [h5778, h5781, h5790, hc02, hlam, hphi, ht0b, ht5b, p6051_1, u5ehi2]
                            · have p6051_0 := h6051c.1
                              have p6051_1 := h6051c.2.1
                              have p6051_2 := h6051c.2.2.1
                              have p6051_3 := h6051c.2.2.2
                              linarith only [h5780, hlam, p6051_0]
                            · have p6051_0 := h6051c.1
                              have p6051_1 := h6051c.2.1
                              have p6051_2 := h6051c.2.2.1
                              have p6051_3 := h6051c.2.2.2
                              linarith only [h5786, hlam, p6051_0]
                            · have p6051_0 := h6051c.1
                              have p6051_1 := h6051c.2.1
                              have p6051_2 := h6051c.2.2.1
                              have p6051_3 := h6051c.2.2.2
                              rcases p6051_3 (m.d 0 2) (by simp) with h6104 | h6104
                              · rcases p6051_3 (m.d 1 2) (by simp) with h6105 | h6105
                                · rcases p6051_3 (m.d 2 3) (by simp) with h6106 | h6106
                                  · linarith only [h6047, h6106, hlam]
                                  · rcases p6051_3 (m.d 2 4) (by simp) with h6108 | h6108
                                    · rcases p6051_3 (m.d 2 5) (by simp) with h6109 | h6109
                                      · rcases h3bigk with h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c | h6110c
                                        · have p6110_0 := h6110c.1
                                          have p6110_1 := h6110c.2.1
                                          have p6110_2 := h6110c.2.2.1
                                          have p6110_3 := h6110c.2.2.2
                                          linarith only [hlam, p6110_0]
                                        · have p6110_0 := h6110c.1
                                          have p6110_1 := h6110c.2.1
                                          have p6110_2 := h6110c.2.2.1
                                          have p6110_3 := h6110c.2.2.2
                                          linarith only [h3977, hlam, p6110_1]
                                        · have p6110_0 := h6110c.1
                                          have p6110_1 := h6110c.2.1
                                          have p6110_2 := h6110c.2.2.1
                                          have p6110_3 := h6110c.2.2.2
                                          linarith only [h5781, h5790, h6049, hlam, p6051_1, p6110_2]
                                        · have p6110_0 := h6110c.1
                                          have p6110_1 := h6110c.2.1
                                          have p6110_2 := h6110c.2.2.1
                                          have p6110_3 := h6110c.2.2.2
                                          linarith only [h0, h5778, h5790, h6049, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6051_1, p6110_1]
                                        · have p6110_0 := h6110c.1
                                          have p6110_1 := h6110c.2.1
                                          have p6110_2 := h6110c.2.2.1
                                          have p6110_3 := h6110c.2.2.2
                                          linarith only [h0, h5778, h6047, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6051_1, p6110_1]
                                        · have p6110_0 := h6110c.1
                                          have p6110_1 := h6110c.2.1
                                          have p6110_2 := h6110c.2.2.1
                                          have p6110_3 := h6110c.2.2.2
                                          linarith only [h5784, hc12, hlam, hphi, ht01, p6110_1, u0ehi2]
                                        · have p6110_0 := h6110c.1
                                          have p6110_1 := h6110c.2.1
                                          have p6110_2 := h6110c.2.2.1
                                          have p6110_3 := h6110c.2.2.2
                                          linarith only [hlam, p6110_0]
                                        · have p6110_0 := h6110c.1
                                          have p6110_1 := h6110c.2.1
                                          have p6110_2 := h6110c.2.2.1
                                          have p6110_3 := h6110c.2.2.2
                                          linarith only [h3977, h5781, h5790, h6049, hlam, p6051_1, p6110_2]
                                        · have p6110_0 := h6110c.1
                                          have p6110_1 := h6110c.2.1
                                          have p6110_2 := h6110c.2.2.1
                                          have p6110_3 := h6110c.2.2.2
                                          linarith only [h5784, h5790, h6049, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6051_1, p6110_1]
                                        · have p6110_0 := h6110c.1
                                          have p6110_1 := h6110c.2.1
                                          have p6110_2 := h6110c.2.2.1
                                          have p6110_3 := h6110c.2.2.2
                                          linarith only [h5784, h6047, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6051_1, p6110_1]
                                        · have p6110_0 := h6110c.1
                                          have p6110_1 := h6110c.2.1
                                          have p6110_2 := h6110c.2.2.1
                                          have p6110_3 := h6110c.2.2.2
                                          linarith only [h5778, hlam, p6110_0]
                                        · have p6110_0 := h6110c.1
                                          have p6110_1 := h6110c.2.1
                                          have p6110_2 := h6110c.2.2.1
                                          have p6110_3 := h6110c.2.2.2
                                          linarith only [h5784, hlam, p6110_0]
                                        · have p6110_0 := h6110c.1
                                          have p6110_1 := h6110c.2.1
                                          have p6110_2 := h6110c.2.2.1
                                          have p6110_3 := h6110c.2.2.2
                                          linarith only [hlam, p6110_0]
                                        · have p6110_0 := h6110c.1
                                          have p6110_1 := h6110c.2.1
                                          have p6110_2 := h6110c.2.2.1
                                          have p6110_3 := h6110c.2.2.2
                                          linarith only [h5790, hlam, p6110_0]
                                        · have p6110_0 := h6110c.1
                                          have p6110_1 := h6110c.2.1
                                          have p6110_2 := h6110c.2.2.1
                                          have p6110_3 := h6110c.2.2.2
                                          linarith only [h6047, hlam, p6110_0]
                                        · have p6110_0 := h6110c.1
                                          have p6110_1 := h6110c.2.1
                                          have p6110_2 := h6110c.2.2.1
                                          have p6110_3 := h6110c.2.2.2
                                          linarith only [h5781, hlam, p6110_0]
                                        · have p6110_0 := h6110c.1
                                          have p6110_1 := h6110c.2.1
                                          have p6110_2 := h6110c.2.2.1
                                          have p6110_3 := h6110c.2.2.2
                                          linarith only [h5787, hlam, p6110_0]
                                        · have p6110_0 := h6110c.1
                                          have p6110_1 := h6110c.2.1
                                          have p6110_2 := h6110c.2.2.1
                                          have p6110_3 := h6110c.2.2.2
                                          rcases p6110_3 (m.d 0 3) (by simp) with h6128 | h6128
                                          · rcases p6110_3 (m.d 1 3) (by simp) with h6129 | h6129
                                            · rcases p6110_3 (m.d 2 3) (by simp) with h6130 | h6130
                                              · linarith only [h6130, hlam, p6110_0]
                                              · rcases p6110_3 (m.d 3 4) (by simp) with h6132 | h6132
                                                · rcases p6110_3 (m.d 3 5) (by simp) with h6133 | h6133
                                                  · linarith only [h6050, h6133, hlam]
                                                  · linarith only [h6047, h6133, hlam]
                                                · linarith only [h6132, hlam, p6110_0]
                                            · linarith only [h5784, h6129, hlam]
                                          · linarith only [h5778, h6128, hlam]
                                        · have p6110_0 := h6110c.1
                                          have p6110_1 := h6110c.2.1
                                          have p6110_2 := h6110c.2.2.1
                                          have p6110_3 := h6110c.2.2.2
                                          linarith only [hlam, p6110_0]
                                        · have p6110_0 := h6110c.1
                                          have p6110_1 := h6110c.2.1
                                          have p6110_2 := h6110c.2.2.1
                                          have p6110_3 := h6110c.2.2.2
                                          linarith only [h6047, hc23, hc34, hlam, hphi, p6051_1, p6110_1]
                                        · have p6110_0 := h6110c.1
                                          have p6110_1 := h6110c.2.1
                                          have p6110_2 := h6110c.2.2.1
                                          have p6110_3 := h6110c.2.2.2
                                          linarith only [h5782, hlam, p6110_0]
                                        · have p6110_0 := h6110c.1
                                          have p6110_1 := h6110c.2.1
                                          have p6110_2 := h6110c.2.2.1
                                          have p6110_3 := h6110c.2.2.2
                                          linarith only [h5788, hlam, p6110_0]
                                        · have p6110_0 := h6110c.1
                                          have p6110_1 := h6110c.2.1
                                          have p6110_2 := h6110c.2.2.1
                                          have p6110_3 := h6110c.2.2.2
                                          rcases p6110_3 (m.d 0 3) (by simp) with h6143 | h6143
                                          · rcases p6110_3 (m.d 1 3) (by simp) with h6144 | h6144
                                            · rcases p6110_3 (m.d 2 3) (by simp) with h6145 | h6145
                                              · linarith only [h6145, hlam, p6110_0]
                                              · rcases p6110_3 (m.d 3 4) (by simp) with h6147 | h6147
                                                · rcases p6110_3 (m.d 3 5) (by simp) with h6148 | h6148
                                                  · rcases h5bigk with h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c | h6149c
                                                    · have p6149_0 := h6149c.1
                                                      have p6149_1 := h6149c.2.1
                                                      have p6149_2 := h6149c.2.2.1
                                                      have p6149_3 := h6149c.2.2.2
                                                      linarith only [hlam, p6149_0]
                                                    · have p6149_0 := h6149c.1
                                                      have p6149_1 := h6149c.2.1
                                                      have p6149_2 := h6149c.2.2.1
                                                      have p6149_3 := h6149c.2.2.2
                                                      linarith only [h5465, hlam, p6149_1]
                                                    · have p6149_0 := h6149c.1
                                                      have p6149_1 := h6149c.2.1
                                                      have p6149_2 := h6149c.2.2.1
                                                      have p6149_3 := h6149c.2.2.2
                                                      linarith only [h5783, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6051_1, p6149_1]
                                                    · have p6149_0 := h6149c.1
                                                      have p6149_1 := h6149c.2.1
                                                      have p6149_2 := h6149c.2.2.1
                                                      have p6149_3 := h6149c.2.2.2
                                                      linarith only [h4846, h5783, h5784, h5787, h6047, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6051_1, p6149_1]
                                                    · have p6149_0 := h6149c.1
                                                      have p6149_1 := h6149c.2.1
                                                      have p6149_2 := h6149c.2.2.1
                                                      have p6149_3 := h6149c.2.2.2
                                                      rcases p6149_3 (m.d 0 5) (by simp) with h6154 | h6154
                                                      · rcases p6149_3 (m.d 1 5) (by simp) with h6155 | h6155
                                                        · rcases p6149_3 (m.d 2 5) (by simp) with h6156 | h6156
                                                          · linarith only [h5780, h6156, hlam]
                                                          · linarith only [h6049, h6156, hlam]
                                                        · linarith only [h5789, h6155, hlam]
                                                      · linarith only [h5783, h6154, hlam]
                                                    · have p6149_0 := h6149c.1
                                                      have p6149_1 := h6149c.2.1
                                                      have p6149_2 := h6149c.2.2.1
                                                      have p6149_3 := h6149c.2.2.2
                                                      linarith only [h5784, h5787, h5789, hc12, hlam, hphi, ht01, p6149_1, u0ehi4]
                                                    · have p6149_0 := h6149c.1
                                                      have p6149_1 := h6149c.2.1
                                                      have p6149_2 := h6149c.2.2.1
                                                      have p6149_3 := h6149c.2.2.2
                                                      linarith only [hlam, p6149_0]
                                                    · have p6149_0 := h6149c.1
                                                      have p6149_1 := h6149c.2.1
                                                      have p6149_2 := h6149c.2.2.1
                                                      have p6149_3 := h6149c.2.2.2
                                                      linarith only [h5784, h5787, h5789, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6051_1, p6149_1]
                                                    · have p6149_0 := h6149c.1
                                                      have p6149_1 := h6149c.2.1
                                                      have p6149_2 := h6149c.2.2.1
                                                      have p6149_3 := h6149c.2.2.2
                                                      linarith only [h5784, h5787, h5789, h6047, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6051_1, p6149_1]
                                                    · have p6149_0 := h6149c.1
                                                      have p6149_1 := h6149c.2.1
                                                      have p6149_2 := h6149c.2.2.1
                                                      have p6149_3 := h6149c.2.2.2
                                                      rcases p6149_3 (m.d 0 5) (by simp) with h6165 | h6165
                                                      · linarith only [h5465, h6165, hlam]
                                                      · linarith only [h5783, h6165, hlam]
                                                    · have p6149_0 := h6149c.1
                                                      have p6149_1 := h6149c.2.1
                                                      have p6149_2 := h6149c.2.2.1
                                                      have p6149_3 := h6149c.2.2.2
                                                      linarith only [h5780, hlam, p6149_1]
                                                    · have p6149_0 := h6149c.1
                                                      have p6149_1 := h6149c.2.1
                                                      have p6149_2 := h6149c.2.2.1
                                                      have p6149_3 := h6149c.2.2.2
                                                      linarith only [h5786, hlam, p6149_1]
                                                    · have p6149_0 := h6149c.1
                                                      have p6149_1 := h6149c.2.1
                                                      have p6149_2 := h6149c.2.2.1
                                                      have p6149_3 := h6149c.2.2.2
                                                      linarith only [hlam, p6149_0]
                                                    · have p6149_0 := h6149c.1
                                                      have p6149_1 := h6149c.2.1
                                                      have p6149_2 := h6149c.2.2.1
                                                      have p6149_3 := h6149c.2.2.2
                                                      linarith only [h6047, hlam, p6149_1]
                                                    · have p6149_0 := h6149c.1
                                                      have p6149_1 := h6149c.2.1
                                                      have p6149_2 := h6149c.2.2.1
                                                      have p6149_3 := h6149c.2.2.2
                                                      linarith only [h0, h5779, h6049, hc12, hlam, hphi, ht01, ht0b, ht5b, p6149_1, u5ehi4]
                                                    · have p6149_0 := h6149c.1
                                                      have p6149_1 := h6149c.2.1
                                                      have p6149_2 := h6149c.2.2.1
                                                      have p6149_3 := h6149c.2.2.2
                                                      linarith only [h5782, hlam, p6149_0]
                                                    · have p6149_0 := h6149c.1
                                                      have p6149_1 := h6149c.2.1
                                                      have p6149_2 := h6149c.2.2.1
                                                      have p6149_3 := h6149c.2.2.2
                                                      linarith only [h5788, hlam, p6149_0]
                                                    · have p6149_0 := h6149c.1
                                                      have p6149_1 := h6149c.2.1
                                                      have p6149_2 := h6149c.2.2.1
                                                      have p6149_3 := h6149c.2.2.2
                                                      linarith only [h3977, h5782, h5784, hc12, hlam, hphi, ht01, ht0b, ht5b, p6149_1, u5ehi2]
                                                    · have p6149_0 := h6149c.1
                                                      have p6149_1 := h6149c.2.1
                                                      have p6149_2 := h6149c.2.2.1
                                                      have p6149_3 := h6149c.2.2.2
                                                      linarith only [hlam, p6149_0]
                                                    · have p6149_0 := h6149c.1
                                                      have p6149_1 := h6149c.2.1
                                                      have p6149_2 := h6149c.2.2.1
                                                      have p6149_3 := h6149c.2.2.2
                                                      linarith only [h3977, h5781, h5784, h6050, hc12, hlam, hphi, ht01, ht0b, ht5b, p6149_1, u5ehi4]
                                                    · have p6149_0 := h6149c.1
                                                      have p6149_1 := h6149c.2.1
                                                      have p6149_2 := h6149c.2.2.1
                                                      have p6149_3 := h6149c.2.2.2
                                                      linarith only [h5783, hlam, p6149_0]
                                                    · have p6149_0 := h6149c.1
                                                      have p6149_1 := h6149c.2.1
                                                      have p6149_2 := h6149c.2.2.1
                                                      have p6149_3 := h6149c.2.2.2
                                                      linarith only [h5789, hlam, p6149_0]
                                                    · have p6149_0 := h6149c.1
                                                      have p6149_1 := h6149c.2.1
                                                      have p6149_2 := h6149c.2.2.1
                                                      have p6149_3 := h6149c.2.2.2
                                                      linarith only [h6049, hlam, p6149_0]
                                                    · have p6149_0 := h6149c.1
                                                      have p6149_1 := h6149c.2.1
                                                      have p6149_2 := h6149c.2.2.1
                                                      have p6149_3 := h6149c.2.2.2
                                                      linarith only [h6050, hlam, p6149_0]
                                                    · have p6149_0 := h6149c.1
                                                      have p6149_1 := h6149c.2.1
                                                      have p6149_2 := h6149c.2.2.1
                                                      have p6149_3 := h6149c.2.2.2
                                                      linarith only [hlam, p6149_0]
                                                  · linarith only [h6148, hlam, p6110_0]
                                                · linarith only [h5790, h6147, hlam]
                                            · linarith only [h5784, h6144, hlam]
                                          · linarith only [h5778, h6143, hlam]
                                        · have p6110_0 := h6110c.1
                                          have p6110_1 := h6110c.2.1
                                          have p6110_2 := h6110c.2.2.1
                                          have p6110_3 := h6110c.2.2.2
                                          linarith only [h6050, hlam, p6110_0]
                                        · have p6110_0 := h6110c.1
                                          have p6110_1 := h6110c.2.1
                                          have p6110_2 := h6110c.2.2.1
                                          have p6110_3 := h6110c.2.2.2
                                          linarith only [hlam, p6110_0]
                                      · linarith only [h6047, h6109, hlam]
                                    · linarith only [h5790, h6108, hlam]
                                · linarith only [h5784, h6105, hlam]
                              · linarith only [h5778, h6104, hlam]
                            · have p6051_0 := h6051c.1
                              have p6051_1 := h6051c.2.1
                              have p6051_2 := h6051c.2.2.1
                              have p6051_3 := h6051c.2.2.2
                              linarith only [h6049, hlam, p6051_0]
                            · have p6051_0 := h6051c.1
                              have p6051_1 := h6051c.2.1
                              have p6051_2 := h6051c.2.2.1
                              have p6051_3 := h6051c.2.2.2
                              linarith only [hlam, p6051_0]
                          · linarith only [h5790, h6049, h6050, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h6196 | h6196
                          · rcases h2bigk with h6197c | h6197c | h6197c | h6197c | h6197c | h6197c | h6197c | h6197c | h6197c | h6197c | h6197c | h6197c | h6197c | h6197c | h6197c | h6197c | h6197c | h6197c | h6197c | h6197c | h6197c | h6197c | h6197c | h6197c | h6197c
                            · have p6197_0 := h6197c.1
                              have p6197_1 := h6197c.2.1
                              have p6197_2 := h6197c.2.2.1
                              have p6197_3 := h6197c.2.2.2
                              linarith only [hlam, p6197_0]
                            · have p6197_0 := h6197c.1
                              have p6197_1 := h6197c.2.1
                              have p6197_2 := h6197c.2.2.1
                              have p6197_3 := h6197c.2.2.2
                              linarith only [h0, hlam, p6197_1]
                            · have p6197_0 := h6197c.1
                              have p6197_1 := h6197c.2.1
                              have p6197_2 := h6197c.2.2.1
                              have p6197_3 := h6197c.2.2.2
                              linarith only [h5778, h5781, h5790, h6049, h6196, hlam, p6197_2]
                            · have p6197_0 := h6197c.1
                              have p6197_1 := h6197c.2.1
                              have p6197_2 := h6197c.2.2.1
                              have p6197_3 := h6197c.2.2.2
                              linarith only [h5778, h5781, h6049, h6196, hlam, p6197_2]
                            · have p6197_0 := h6197c.1
                              have p6197_1 := h6197c.2.1
                              have p6197_2 := h6197c.2.2.1
                              have p6197_3 := h6197c.2.2.2
                              rcases p6197_3 (m.d 0 2) (by simp) with h6202 | h6202
                              · rcases p6197_3 (m.d 1 2) (by simp) with h6203 | h6203
                                · rcases p6197_3 (m.d 2 3) (by simp) with h6204 | h6204
                                  · linarith only [h5778, h6204, hlam]
                                  · rcases p6197_3 (m.d 2 4) (by simp) with h6206 | h6206
                                    · linarith only [h5779, h6206, hlam]
                                    · rcases p6197_3 (m.d 2 5) (by simp) with h6208 | h6208
                                      · linarith only [h6208, hlam, p6197_0]
                                      · rcases h3bigk with h6210c | h6210c | h6210c | h6210c | h6210c | h6210c | h6210c | h6210c | h6210c | h6210c | h6210c | h6210c | h6210c | h6210c | h6210c | h6210c | h6210c | h6210c | h6210c | h6210c | h6210c | h6210c | h6210c | h6210c | h6210c
                                        · have p6210_0 := h6210c.1
                                          have p6210_1 := h6210c.2.1
                                          have p6210_2 := h6210c.2.2.1
                                          have p6210_3 := h6210c.2.2.2
                                          linarith only [hlam, p6210_0]
                                        · have p6210_0 := h6210c.1
                                          have p6210_1 := h6210c.2.1
                                          have p6210_2 := h6210c.2.2.1
                                          have p6210_3 := h6210c.2.2.2
                                          linarith only [h3977, hlam, p6210_1]
                                        · have p6210_0 := h6210c.1
                                          have p6210_1 := h6210c.2.1
                                          have p6210_2 := h6210c.2.2.1
                                          have p6210_3 := h6210c.2.2.2
                                          linarith only [h5781, h5790, h6049, h6196, hlam, p6210_2]
                                        · have p6210_0 := h6210c.1
                                          have p6210_1 := h6210c.2.1
                                          have p6210_2 := h6210c.2.2.1
                                          have p6210_3 := h6210c.2.2.2
                                          linarith only [h3977, h5784, h5790, h6049, h6196, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6210_1]
                                        · have p6210_0 := h6210c.1
                                          have p6210_1 := h6210c.2.1
                                          have p6210_2 := h6210c.2.2.1
                                          have p6210_3 := h6210c.2.2.2
                                          rcases p6210_3 (m.d 0 3) (by simp) with h6215 | h6215
                                          · rcases p6210_3 (m.d 1 3) (by simp) with h6216 | h6216
                                            · rcases p6210_3 (m.d 2 3) (by simp) with h6217 | h6217
                                              · linarith only [h5778, h6217, hlam]
                                              · rcases p6210_3 (m.d 3 4) (by simp) with h6219 | h6219
                                                · linarith only [h5781, h6219, hlam]
                                                · linarith only [h6196, h6219, hlam]
                                            · linarith only [h5788, h6216, hlam]
                                          · linarith only [h6215, hlam, p6210_0]
                                        · have p6210_0 := h6210c.1
                                          have p6210_1 := h6210c.2.1
                                          have p6210_2 := h6210c.2.2.1
                                          have p6210_3 := h6210c.2.2.2
                                          linarith only [h5784, hc12, hlam, hphi, ht01, p6210_1, u0ehi2]
                                        · have p6210_0 := h6210c.1
                                          have p6210_1 := h6210c.2.1
                                          have p6210_2 := h6210c.2.2.1
                                          have p6210_3 := h6210c.2.2.2
                                          linarith only [hlam, p6210_0]
                                        · have p6210_0 := h6210c.1
                                          have p6210_1 := h6210c.2.1
                                          have p6210_2 := h6210c.2.2.1
                                          have p6210_3 := h6210c.2.2.2
                                          linarith only [h3977, h5781, h5790, h6049, h6196, hlam, p6210_2]
                                        · have p6210_0 := h6210c.1
                                          have p6210_1 := h6210c.2.1
                                          have p6210_2 := h6210c.2.2.1
                                          have p6210_3 := h6210c.2.2.2
                                          linarith only [h5790, h6049, h6196, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6210_1]
                                        · have p6210_0 := h6210c.1
                                          have p6210_1 := h6210c.2.1
                                          have p6210_2 := h6210c.2.2.1
                                          have p6210_3 := h6210c.2.2.2
                                          rcases p6210_3 (m.d 0 3) (by simp) with h6228 | h6228
                                          · linarith only [h3977, h6228, hlam]
                                          · linarith only [h5782, h6228, hlam]
                                        · have p6210_0 := h6210c.1
                                          have p6210_1 := h6210c.2.1
                                          have p6210_2 := h6210c.2.2.1
                                          have p6210_3 := h6210c.2.2.2
                                          linarith only [h5778, hlam, p6210_0]
                                        · have p6210_0 := h6210c.1
                                          have p6210_1 := h6210c.2.1
                                          have p6210_2 := h6210c.2.2.1
                                          have p6210_3 := h6210c.2.2.2
                                          linarith only [h5784, hlam, p6210_0]
                                        · have p6210_0 := h6210c.1
                                          have p6210_1 := h6210c.2.1
                                          have p6210_2 := h6210c.2.2.1
                                          have p6210_3 := h6210c.2.2.2
                                          linarith only [hlam, p6210_0]
                                        · have p6210_0 := h6210c.1
                                          have p6210_1 := h6210c.2.1
                                          have p6210_2 := h6210c.2.2.1
                                          have p6210_3 := h6210c.2.2.2
                                          linarith only [h5790, hlam, p6210_0]
                                        · have p6210_0 := h6210c.1
                                          have p6210_1 := h6210c.2.1
                                          have p6210_2 := h6210c.2.2.1
                                          have p6210_3 := h6210c.2.2.2
                                          linarith only [h6047, hlam, p6210_0]
                                        · have p6210_0 := h6210c.1
                                          have p6210_1 := h6210c.2.1
                                          have p6210_2 := h6210c.2.2.1
                                          have p6210_3 := h6210c.2.2.2
                                          linarith only [h5781, hlam, p6210_0]
                                        · have p6210_0 := h6210c.1
                                          have p6210_1 := h6210c.2.1
                                          have p6210_2 := h6210c.2.2.1
                                          have p6210_3 := h6210c.2.2.2
                                          linarith only [h5787, hlam, p6210_0]
                                        · have p6210_0 := h6210c.1
                                          have p6210_1 := h6210c.2.1
                                          have p6210_2 := h6210c.2.2.1
                                          have p6210_3 := h6210c.2.2.2
                                          rcases p6210_3 (m.d 0 3) (by simp) with h6238 | h6238
                                          · rcases p6210_3 (m.d 1 3) (by simp) with h6239 | h6239
                                            · rcases p6210_3 (m.d 2 3) (by simp) with h6240 | h6240
                                              · linarith only [h6240, hlam, p6210_0]
                                              · rcases p6210_3 (m.d 3 4) (by simp) with h6242 | h6242
                                                · rcases p6210_3 (m.d 3 5) (by simp) with h6243 | h6243
                                                  · linarith only [h6196, h6243, hlam]
                                                  · linarith only [h6047, h6243, hlam]
                                                · linarith only [h6242, hlam, p6210_0]
                                            · linarith only [h5784, h6239, hlam]
                                          · linarith only [h5778, h6238, hlam]
                                        · have p6210_0 := h6210c.1
                                          have p6210_1 := h6210c.2.1
                                          have p6210_2 := h6210c.2.2.1
                                          have p6210_3 := h6210c.2.2.2
                                          linarith only [hlam, p6210_0]
                                        · have p6210_0 := h6210c.1
                                          have p6210_1 := h6210c.2.1
                                          have p6210_2 := h6210c.2.2.1
                                          have p6210_3 := h6210c.2.2.2
                                          linarith only [h5778, h5781, h5790, h6049, h6196, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6210_1]
                                        · have p6210_0 := h6210c.1
                                          have p6210_1 := h6210c.2.1
                                          have p6210_2 := h6210c.2.2.1
                                          have p6210_3 := h6210c.2.2.2
                                          linarith only [h5782, hlam, p6210_0]
                                        · have p6210_0 := h6210c.1
                                          have p6210_1 := h6210c.2.1
                                          have p6210_2 := h6210c.2.2.1
                                          have p6210_3 := h6210c.2.2.2
                                          linarith only [h5788, hlam, p6210_0]
                                        · have p6210_0 := h6210c.1
                                          have p6210_1 := h6210c.2.1
                                          have p6210_2 := h6210c.2.2.1
                                          have p6210_3 := h6210c.2.2.2
                                          rcases p6210_3 (m.d 0 3) (by simp) with h6253 | h6253
                                          · rcases p6210_3 (m.d 1 3) (by simp) with h6254 | h6254
                                            · rcases p6210_3 (m.d 2 3) (by simp) with h6255 | h6255
                                              · linarith only [h6255, hlam, p6210_0]
                                              · rcases p6210_3 (m.d 3 4) (by simp) with h6257 | h6257
                                                · rcases p6210_3 (m.d 3 5) (by simp) with h6258 | h6258
                                                  · rcases h5bigk with h6259c | h6259c | h6259c | h6259c | h6259c | h6259c | h6259c | h6259c | h6259c | h6259c | h6259c | h6259c | h6259c | h6259c | h6259c | h6259c | h6259c | h6259c | h6259c | h6259c | h6259c | h6259c | h6259c | h6259c | h6259c
                                                    · have p6259_0 := h6259c.1
                                                      have p6259_1 := h6259c.2.1
                                                      have p6259_2 := h6259c.2.2.1
                                                      have p6259_3 := h6259c.2.2.2
                                                      linarith only [hlam, p6259_0]
                                                    · have p6259_0 := h6259c.1
                                                      have p6259_1 := h6259c.2.1
                                                      have p6259_2 := h6259c.2.2.1
                                                      have p6259_3 := h6259c.2.2.2
                                                      linarith only [h5465, hlam, p6259_1]
                                                    · have p6259_0 := h6259c.1
                                                      have p6259_1 := h6259c.2.1
                                                      have p6259_2 := h6259c.2.2.1
                                                      have p6259_3 := h6259c.2.2.2
                                                      rcases p6259_3 (m.d 0 5) (by simp) with h6262 | h6262
                                                      · rcases p6259_3 (m.d 1 5) (by simp) with h6263 | h6263
                                                        · rcases p6259_3 (m.d 2 5) (by simp) with h6264 | h6264
                                                          · linarith only [h5780, h6264, hlam]
                                                          · rcases p6259_3 (m.d 3 5) (by simp) with h6266 | h6266
                                                            · linarith only [h5782, h6266, hlam]
                                                            · linarith only [h6047, h6266, hlam]
                                                        · linarith only [h5786, h6263, hlam]
                                                      · linarith only [h5780, h6262, hlam]
                                                    · have p6259_0 := h6259c.1
                                                      have p6259_1 := h6259c.2.1
                                                      have p6259_2 := h6259c.2.2.1
                                                      have p6259_3 := h6259c.2.2.2
                                                      linarith only [h0, h5778, h5781, h5783, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6210_1, p6259_1]
                                                    · have p6259_0 := h6259c.1
                                                      have p6259_1 := h6259c.2.1
                                                      have p6259_2 := h6259c.2.2.1
                                                      have p6259_3 := h6259c.2.2.2
                                                      rcases p6259_3 (m.d 0 5) (by simp) with h6272 | h6272
                                                      · rcases p6259_3 (m.d 1 5) (by simp) with h6273 | h6273
                                                        · rcases p6259_3 (m.d 2 5) (by simp) with h6274 | h6274
                                                          · linarith only [h5780, h6274, hlam]
                                                          · rcases p6259_3 (m.d 3 5) (by simp) with h6276 | h6276
                                                            · linarith only [h5782, h6276, hlam]
                                                            · linarith only [h6196, h6276, hlam]
                                                        · linarith only [h5789, h6273, hlam]
                                                      · linarith only [h5783, h6272, hlam]
                                                    · have p6259_0 := h6259c.1
                                                      have p6259_1 := h6259c.2.1
                                                      have p6259_2 := h6259c.2.2.1
                                                      have p6259_3 := h6259c.2.2.2
                                                      linarith only [h5784, h5787, h5789, hc12, hlam, hphi, ht01, p6259_1, u0ehi4]
                                                    · have p6259_0 := h6259c.1
                                                      have p6259_1 := h6259c.2.1
                                                      have p6259_2 := h6259c.2.2.1
                                                      have p6259_3 := h6259c.2.2.2
                                                      linarith only [hlam, p6259_0]
                                                    · have p6259_0 := h6259c.1
                                                      have p6259_1 := h6259c.2.1
                                                      have p6259_2 := h6259c.2.2.1
                                                      have p6259_3 := h6259c.2.2.2
                                                      rcases p6259_3 (m.d 0 5) (by simp) with h6283 | h6283
                                                      · linarith only [h5465, h6283, hlam]
                                                      · linarith only [h5780, h6283, hlam]
                                                    · have p6259_0 := h6259c.1
                                                      have p6259_1 := h6259c.2.1
                                                      have p6259_2 := h6259c.2.2.1
                                                      have p6259_3 := h6259c.2.2.2
                                                      linarith only [h5784, h5787, h5789, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6210_1, p6259_1]
                                                    · have p6259_0 := h6259c.1
                                                      have p6259_1 := h6259c.2.1
                                                      have p6259_2 := h6259c.2.2.1
                                                      have p6259_3 := h6259c.2.2.2
                                                      rcases p6259_3 (m.d 0 5) (by simp) with h6287 | h6287
                                                      · linarith only [h5465, h6287, hlam]
                                                      · linarith only [h5783, h6287, hlam]
                                                    · have p6259_0 := h6259c.1
                                                      have p6259_1 := h6259c.2.1
                                                      have p6259_2 := h6259c.2.2.1
                                                      have p6259_3 := h6259c.2.2.2
                                                      linarith only [h5780, hlam, p6259_1]
                                                    · have p6259_0 := h6259c.1
                                                      have p6259_1 := h6259c.2.1
                                                      have p6259_2 := h6259c.2.2.1
                                                      have p6259_3 := h6259c.2.2.2
                                                      linarith only [h5786, hlam, p6259_1]
                                                    · have p6259_0 := h6259c.1
                                                      have p6259_1 := h6259c.2.1
                                                      have p6259_2 := h6259c.2.2.1
                                                      have p6259_3 := h6259c.2.2.2
                                                      linarith only [hlam, p6259_0]
                                                    · have p6259_0 := h6259c.1
                                                      have p6259_1 := h6259c.2.1
                                                      have p6259_2 := h6259c.2.2.1
                                                      have p6259_3 := h6259c.2.2.2
                                                      linarith only [h6047, hlam, p6259_1]
                                                    · have p6259_0 := h6259c.1
                                                      have p6259_1 := h6259c.2.1
                                                      have p6259_2 := h6259c.2.2.1
                                                      have p6259_3 := h6259c.2.2.2
                                                      linarith only [h6049, hlam, p6259_1]
                                                    · have p6259_0 := h6259c.1
                                                      have p6259_1 := h6259c.2.1
                                                      have p6259_2 := h6259c.2.2.1
                                                      have p6259_3 := h6259c.2.2.2
                                                      linarith only [h5782, hlam, p6259_0]
                                                    · have p6259_0 := h6259c.1
                                                      have p6259_1 := h6259c.2.1
                                                      have p6259_2 := h6259c.2.2.1
                                                      have p6259_3 := h6259c.2.2.2
                                                      linarith only [h5788, hlam, p6259_0]
                                                    · have p6259_0 := h6259c.1
                                                      have p6259_1 := h6259c.2.1
                                                      have p6259_2 := h6259c.2.2.1
                                                      have p6259_3 := h6259c.2.2.2
                                                      linarith only [h0, h5778, h5782, hc12, hlam, hphi, ht01, ht0b, ht5b, p6259_1, u5ehi2]
                                                    · have p6259_0 := h6259c.1
                                                      have p6259_1 := h6259c.2.1
                                                      have p6259_2 := h6259c.2.2.1
                                                      have p6259_3 := h6259c.2.2.2
                                                      linarith only [hlam, p6259_0]
                                                    · have p6259_0 := h6259c.1
                                                      have p6259_1 := h6259c.2.1
                                                      have p6259_2 := h6259c.2.2.1
                                                      have p6259_3 := h6259c.2.2.2
                                                      linarith only [h0, h5778, h5781, h5790, h6049, h6196, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6259_1]
                                                    · have p6259_0 := h6259c.1
                                                      have p6259_1 := h6259c.2.1
                                                      have p6259_2 := h6259c.2.2.1
                                                      have p6259_3 := h6259c.2.2.2
                                                      linarith only [h5783, hlam, p6259_0]
                                                    · have p6259_0 := h6259c.1
                                                      have p6259_1 := h6259c.2.1
                                                      have p6259_2 := h6259c.2.2.1
                                                      have p6259_3 := h6259c.2.2.2
                                                      linarith only [h5789, hlam, p6259_0]
                                                    · have p6259_0 := h6259c.1
                                                      have p6259_1 := h6259c.2.1
                                                      have p6259_2 := h6259c.2.2.1
                                                      have p6259_3 := h6259c.2.2.2
                                                      linarith only [h0, h5778, h5781, h5783, hc12, hlam, hphi, ht01, ht0b, ht5b, p6259_1, u5ehi2]
                                                    · have p6259_0 := h6259c.1
                                                      have p6259_1 := h6259c.2.1
                                                      have p6259_2 := h6259c.2.2.1
                                                      have p6259_3 := h6259c.2.2.2
                                                      linarith only [h6196, hlam, p6259_0]
                                                    · have p6259_0 := h6259c.1
                                                      have p6259_1 := h6259c.2.1
                                                      have p6259_2 := h6259c.2.2.1
                                                      have p6259_3 := h6259c.2.2.2
                                                      linarith only [hlam, p6259_0]
                                                  · linarith only [h6258, hlam, p6210_0]
                                                · linarith only [h5790, h6257, hlam]
                                            · linarith only [h5784, h6254, hlam]
                                          · linarith only [h5778, h6253, hlam]
                                        · have p6210_0 := h6210c.1
                                          have p6210_1 := h6210c.2.1
                                          have p6210_2 := h6210c.2.2.1
                                          have p6210_3 := h6210c.2.2.2
                                          linarith only [h6196, hlam, p6210_0]
                                        · have p6210_0 := h6210c.1
                                          have p6210_1 := h6210c.2.1
                                          have p6210_2 := h6210c.2.2.1
                                          have p6210_3 := h6210c.2.2.2
                                          linarith only [hlam, p6210_0]
                                · linarith only [h5786, h6203, hlam]
                              · linarith only [h6202, hlam, p6197_0]
                            · have p6197_0 := h6197c.1
                              have p6197_1 := h6197c.2.1
                              have p6197_2 := h6197c.2.2.1
                              have p6197_3 := h6197c.2.2.2
                              linarith only [h5778, h5781, h6196, hc12, hlam, hphi, ht01, ht0b, ht5b, p6197_1, u5ehi3]
                            · have p6197_0 := h6197c.1
                              have p6197_1 := h6197c.2.1
                              have p6197_2 := h6197c.2.2.1
                              have p6197_3 := h6197c.2.2.2
                              linarith only [hlam, p6197_0]
                            · have p6197_0 := h6197c.1
                              have p6197_1 := h6197c.2.1
                              have p6197_2 := h6197c.2.2.1
                              have p6197_3 := h6197c.2.2.2
                              linarith only [h0, h5778, h5781, h5790, h6049, h6196, hlam, p6197_2]
                            · have p6197_0 := h6197c.1
                              have p6197_1 := h6197c.2.1
                              have p6197_2 := h6197c.2.2.1
                              have p6197_3 := h6197c.2.2.2
                              linarith only [h0, h5778, h5781, h6049, h6196, hlam, p6197_2]
                            · have p6197_0 := h6197c.1
                              have p6197_1 := h6197c.2.1
                              have p6197_2 := h6197c.2.2.1
                              have p6197_3 := h6197c.2.2.2
                              rcases p6197_3 (m.d 0 2) (by simp) with h6317 | h6317
                              · linarith only [h0, h6317, hlam]
                              · linarith only [h5780, h6317, hlam]
                            · have p6197_0 := h6197c.1
                              have p6197_1 := h6197c.2.1
                              have p6197_2 := h6197c.2.2.1
                              have p6197_3 := h6197c.2.2.2
                              linarith only [h5778, hlam, p6197_0]
                            · have p6197_0 := h6197c.1
                              have p6197_1 := h6197c.2.1
                              have p6197_2 := h6197c.2.2.1
                              have p6197_3 := h6197c.2.2.2
                              linarith only [h5784, hlam, p6197_0]
                            · have p6197_0 := h6197c.1
                              have p6197_1 := h6197c.2.1
                              have p6197_2 := h6197c.2.2.1
                              have p6197_3 := h6197c.2.2.2
                              linarith only [hlam, p6197_0]
                            · have p6197_0 := h6197c.1
                              have p6197_1 := h6197c.2.1
                              have p6197_2 := h6197c.2.2.1
                              have p6197_3 := h6197c.2.2.2
                              linarith only [h5790, hlam, p6197_0]
                            · have p6197_0 := h6197c.1
                              have p6197_1 := h6197c.2.1
                              have p6197_2 := h6197c.2.2.1
                              have p6197_3 := h6197c.2.2.2
                              linarith only [h6047, hlam, p6197_0]
                            · have p6197_0 := h6197c.1
                              have p6197_1 := h6197c.2.1
                              have p6197_2 := h6197c.2.2.1
                              have p6197_3 := h6197c.2.2.2
                              linarith only [h5779, hlam, p6197_0]
                            · have p6197_0 := h6197c.1
                              have p6197_1 := h6197c.2.1
                              have p6197_2 := h6197c.2.2.1
                              have p6197_3 := h6197c.2.2.2
                              linarith only [h5785, hlam, p6197_0]
                            · have p6197_0 := h6197c.1
                              have p6197_1 := h6197c.2.1
                              have p6197_2 := h6197c.2.2.1
                              have p6197_3 := h6197c.2.2.2
                              linarith only [h0, h5778, h5781, h6049, h6196, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6197_1]
                            · have p6197_0 := h6197c.1
                              have p6197_1 := h6197c.2.1
                              have p6197_2 := h6197c.2.2.1
                              have p6197_3 := h6197c.2.2.2
                              linarith only [hlam, p6197_0]
                            · have p6197_0 := h6197c.1
                              have p6197_1 := h6197c.2.1
                              have p6197_2 := h6197c.2.2.1
                              have p6197_3 := h6197c.2.2.2
                              linarith only [h6049, hlam, p6197_1]
                            · have p6197_0 := h6197c.1
                              have p6197_1 := h6197c.2.1
                              have p6197_2 := h6197c.2.2.1
                              have p6197_3 := h6197c.2.2.2
                              linarith only [h5780, hlam, p6197_0]
                            · have p6197_0 := h6197c.1
                              have p6197_1 := h6197c.2.1
                              have p6197_2 := h6197c.2.2.1
                              have p6197_3 := h6197c.2.2.2
                              linarith only [h5786, hlam, p6197_0]
                            · have p6197_0 := h6197c.1
                              have p6197_1 := h6197c.2.1
                              have p6197_2 := h6197c.2.2.1
                              have p6197_3 := h6197c.2.2.2
                              linarith only [h0, h5778, h5781, h6049, h6196, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6197_1]
                            · have p6197_0 := h6197c.1
                              have p6197_1 := h6197c.2.1
                              have p6197_2 := h6197c.2.2.1
                              have p6197_3 := h6197c.2.2.2
                              linarith only [h0, h5778, h5781, h6049, h6196, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p6197_1]
                            · have p6197_0 := h6197c.1
                              have p6197_1 := h6197c.2.1
                              have p6197_2 := h6197c.2.2.1
                              have p6197_3 := h6197c.2.2.2
                              linarith only [hlam, p6197_0]
                          · rcases h2bigk with h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c | h6335c
                            · have p6335_0 := h6335c.1
                              have p6335_1 := h6335c.2.1
                              have p6335_2 := h6335c.2.2.1
                              have p6335_3 := h6335c.2.2.2
                              linarith only [hlam, p6335_0]
                            · have p6335_0 := h6335c.1
                              have p6335_1 := h6335c.2.1
                              have p6335_2 := h6335c.2.2.1
                              have p6335_3 := h6335c.2.2.2
                              linarith only [h0, hlam, p6335_1]
                            · have p6335_0 := h6335c.1
                              have p6335_1 := h6335c.2.1
                              have p6335_2 := h6335c.2.2.1
                              have p6335_3 := h6335c.2.2.2
                              linarith only [h5778, h5781, h5783, h5790, h6196, hlam, p6335_2]
                            · have p6335_0 := h6335c.1
                              have p6335_1 := h6335c.2.1
                              have p6335_2 := h6335c.2.2.1
                              have p6335_3 := h6335c.2.2.2
                              rcases p6335_3 (m.d 0 2) (by simp) with h6339 | h6339
                              · rcases p6335_3 (m.d 1 2) (by simp) with h6340 | h6340
                                · rcases p6335_3 (m.d 2 3) (by simp) with h6341 | h6341
                                  · linarith only [h5778, h6341, hlam]
                                  · rcases p6335_3 (m.d 2 4) (by simp) with h6343 | h6343
                                    · linarith only [h6343, hlam, p6335_0]
                                    · rcases p6335_3 (m.d 2 5) (by simp) with h6345 | h6345
                                      · linarith only [h5780, h6345, hlam]
                                      · linarith only [h6049, h6345, hlam]
                                · linarith only [h5785, h6340, hlam]
                              · linarith only [h6339, hlam, p6335_0]
                            · have p6335_0 := h6335c.1
                              have p6335_1 := h6335c.2.1
                              have p6335_2 := h6335c.2.2.1
                              have p6335_3 := h6335c.2.2.2
                              rcases p6335_3 (m.d 0 2) (by simp) with h6350 | h6350
                              · rcases p6335_3 (m.d 1 2) (by simp) with h6351 | h6351
                                · rcases p6335_3 (m.d 2 3) (by simp) with h6352 | h6352
                                  · linarith only [h5778, h6352, hlam]
                                  · rcases p6335_3 (m.d 2 4) (by simp) with h6354 | h6354
                                    · linarith only [h5779, h6354, hlam]
                                    · rcases p6335_3 (m.d 2 5) (by simp) with h6356 | h6356
                                      · linarith only [h6356, hlam, p6335_0]
                                      · rcases h3bigk with h6358c | h6358c | h6358c | h6358c | h6358c | h6358c | h6358c | h6358c | h6358c | h6358c | h6358c | h6358c | h6358c | h6358c | h6358c | h6358c | h6358c | h6358c | h6358c | h6358c | h6358c | h6358c | h6358c | h6358c | h6358c
                                        · have p6358_0 := h6358c.1
                                          have p6358_1 := h6358c.2.1
                                          have p6358_2 := h6358c.2.2.1
                                          have p6358_3 := h6358c.2.2.2
                                          linarith only [hlam, p6358_0]
                                        · have p6358_0 := h6358c.1
                                          have p6358_1 := h6358c.2.1
                                          have p6358_2 := h6358c.2.2.1
                                          have p6358_3 := h6358c.2.2.2
                                          linarith only [h3977, hlam, p6358_1]
                                        · have p6358_0 := h6358c.1
                                          have p6358_1 := h6358c.2.1
                                          have p6358_2 := h6358c.2.2.1
                                          have p6358_3 := h6358c.2.2.2
                                          linarith only [h5781, h5783, h5790, h6196, hlam, p6358_2]
                                        · have p6358_0 := h6358c.1
                                          have p6358_1 := h6358c.2.1
                                          have p6358_2 := h6358c.2.2.1
                                          have p6358_3 := h6358c.2.2.2
                                          rcases p6358_3 (m.d 0 3) (by simp) with h6362 | h6362
                                          · rcases p6358_3 (m.d 1 3) (by simp) with h6363 | h6363
                                            · rcases p6358_3 (m.d 2 3) (by simp) with h6364 | h6364
                                              · linarith only [h5778, h6364, hlam]
                                              · rcases p6358_3 (m.d 3 4) (by simp) with h6366 | h6366
                                                · linarith only [h6366, hlam, p6358_0]
                                                · rcases p6358_3 (m.d 3 5) (by simp) with h6368 | h6368
                                                  · linarith only [h5782, h6368, hlam]
                                                  · linarith only [h6196, h6368, hlam]
                                            · linarith only [h5787, h6363, hlam]
                                          · linarith only [h6362, hlam, p6358_0]
                                        · have p6358_0 := h6358c.1
                                          have p6358_1 := h6358c.2.1
                                          have p6358_2 := h6358c.2.2.1
                                          have p6358_3 := h6358c.2.2.2
                                          rcases p6358_3 (m.d 0 3) (by simp) with h6373 | h6373
                                          · rcases p6358_3 (m.d 1 3) (by simp) with h6374 | h6374
                                            · rcases p6358_3 (m.d 2 3) (by simp) with h6375 | h6375
                                              · linarith only [h5778, h6375, hlam]
                                              · rcases p6358_3 (m.d 3 4) (by simp) with h6377 | h6377
                                                · linarith only [h5781, h6377, hlam]
                                                · rcases p6358_3 (m.d 3 5) (by simp) with h6379 | h6379
                                                  · linarith only [h6379, hlam, p6358_0]
                                                  · rcases h5bigk with h6381c | h6381c | h6381c | h6381c | h6381c | h6381c | h6381c | h6381c | h6381c | h6381c | h6381c | h6381c | h6381c | h6381c | h6381c | h6381c | h6381c | h6381c | h6381c | h6381c | h6381c | h6381c | h6381c | h6381c | h6381c
                                                    · have p6381_0 := h6381c.1
                                                      have p6381_1 := h6381c.2.1
                                                      have p6381_2 := h6381c.2.2.1
                                                      have p6381_3 := h6381c.2.2.2
                                                      linarith only [hlam, p6381_0]
                                                    · have p6381_0 := h6381c.1
                                                      have p6381_1 := h6381c.2.1
                                                      have p6381_2 := h6381c.2.2.1
                                                      have p6381_3 := h6381c.2.2.2
                                                      linarith only [h5465, hlam, p6381_1]
                                                    · have p6381_0 := h6381c.1
                                                      have p6381_1 := h6381c.2.1
                                                      have p6381_2 := h6381c.2.2.1
                                                      have p6381_3 := h6381c.2.2.2
                                                      rcases p6381_3 (m.d 0 5) (by simp) with h6384 | h6384
                                                      · rcases p6381_3 (m.d 1 5) (by simp) with h6385 | h6385
                                                        · rcases p6381_3 (m.d 2 5) (by simp) with h6386 | h6386
                                                          · linarith only [h5780, h6386, hlam]
                                                          · rcases p6381_3 (m.d 3 5) (by simp) with h6388 | h6388
                                                            · linarith only [h5782, h6388, hlam]
                                                            · linarith only [h6047, h6388, hlam]
                                                        · linarith only [h5786, h6385, hlam]
                                                      · linarith only [h5780, h6384, hlam]
                                                    · have p6381_0 := h6381c.1
                                                      have p6381_1 := h6381c.2.1
                                                      have p6381_2 := h6381c.2.2.1
                                                      have p6381_3 := h6381c.2.2.2
                                                      rcases p6381_3 (m.d 0 5) (by simp) with h6393 | h6393
                                                      · rcases p6381_3 (m.d 1 5) (by simp) with h6394 | h6394
                                                        · rcases p6381_3 (m.d 2 5) (by simp) with h6395 | h6395
                                                          · linarith only [h5780, h6395, hlam]
                                                          · rcases p6381_3 (m.d 3 5) (by simp) with h6397 | h6397
                                                            · linarith only [h5782, h6397, hlam]
                                                            · rcases p6381_3 (m.d 4 5) (by simp) with h6399 | h6399
                                                              · linarith only [h5783, h6399, hlam]
                                                              · linarith only [h6196, h6399, hlam]
                                                        · linarith only [h5788, h6394, hlam]
                                                      · linarith only [h5782, h6393, hlam]
                                                    · have p6381_0 := h6381c.1
                                                      have p6381_1 := h6381c.2.1
                                                      have p6381_2 := h6381c.2.2.1
                                                      have p6381_3 := h6381c.2.2.2
                                                      linarith only [h5778, h5781, h5783, h5790, h6196, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6381_1]
                                                    · have p6381_0 := h6381c.1
                                                      have p6381_1 := h6381c.2.1
                                                      have p6381_2 := h6381c.2.2.1
                                                      have p6381_3 := h6381c.2.2.2
                                                      linarith only [h5784, h5787, h5789, hc12, hlam, hphi, ht01, p6381_1, u0ehi4]
                                                    · have p6381_0 := h6381c.1
                                                      have p6381_1 := h6381c.2.1
                                                      have p6381_2 := h6381c.2.2.1
                                                      have p6381_3 := h6381c.2.2.2
                                                      linarith only [hlam, p6381_0]
                                                    · have p6381_0 := h6381c.1
                                                      have p6381_1 := h6381c.2.1
                                                      have p6381_2 := h6381c.2.2.1
                                                      have p6381_3 := h6381c.2.2.2
                                                      rcases p6381_3 (m.d 0 5) (by simp) with h6407 | h6407
                                                      · linarith only [h5465, h6407, hlam]
                                                      · linarith only [h5780, h6407, hlam]
                                                    · have p6381_0 := h6381c.1
                                                      have p6381_1 := h6381c.2.1
                                                      have p6381_2 := h6381c.2.2.1
                                                      have p6381_3 := h6381c.2.2.2
                                                      rcases p6381_3 (m.d 0 5) (by simp) with h6410 | h6410
                                                      · linarith only [h5465, h6410, hlam]
                                                      · linarith only [h5782, h6410, hlam]
                                                    · have p6381_0 := h6381c.1
                                                      have p6381_1 := h6381c.2.1
                                                      have p6381_2 := h6381c.2.2.1
                                                      have p6381_3 := h6381c.2.2.2
                                                      linarith only [h5784, h5787, h5789, h5790, h6196, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6381_1]
                                                    · have p6381_0 := h6381c.1
                                                      have p6381_1 := h6381c.2.1
                                                      have p6381_2 := h6381c.2.2.1
                                                      have p6381_3 := h6381c.2.2.2
                                                      linarith only [h5780, hlam, p6381_1]
                                                    · have p6381_0 := h6381c.1
                                                      have p6381_1 := h6381c.2.1
                                                      have p6381_2 := h6381c.2.2.1
                                                      have p6381_3 := h6381c.2.2.2
                                                      linarith only [h5786, hlam, p6381_1]
                                                    · have p6381_0 := h6381c.1
                                                      have p6381_1 := h6381c.2.1
                                                      have p6381_2 := h6381c.2.2.1
                                                      have p6381_3 := h6381c.2.2.2
                                                      linarith only [hlam, p6381_0]
                                                    · have p6381_0 := h6381c.1
                                                      have p6381_1 := h6381c.2.1
                                                      have p6381_2 := h6381c.2.2.1
                                                      have p6381_3 := h6381c.2.2.2
                                                      linarith only [h6047, hlam, p6381_1]
                                                    · have p6381_0 := h6381c.1
                                                      have p6381_1 := h6381c.2.1
                                                      have p6381_2 := h6381c.2.2.1
                                                      have p6381_3 := h6381c.2.2.2
                                                      linarith only [h6049, hlam, p6381_1]
                                                    · have p6381_0 := h6381c.1
                                                      have p6381_1 := h6381c.2.1
                                                      have p6381_2 := h6381c.2.2.1
                                                      have p6381_3 := h6381c.2.2.2
                                                      linarith only [h5782, hlam, p6381_0]
                                                    · have p6381_0 := h6381c.1
                                                      have p6381_1 := h6381c.2.1
                                                      have p6381_2 := h6381c.2.2.1
                                                      have p6381_3 := h6381c.2.2.2
                                                      linarith only [h5788, hlam, p6381_0]
                                                    · have p6381_0 := h6381c.1
                                                      have p6381_1 := h6381c.2.1
                                                      have p6381_2 := h6381c.2.2.1
                                                      have p6381_3 := h6381c.2.2.2
                                                      linarith only [h0, h5778, hc12, hlam, hphi, ht01, ht0b, ht5b, p6358_1, p6381_1, u5ehi2]
                                                    · have p6381_0 := h6381c.1
                                                      have p6381_1 := h6381c.2.1
                                                      have p6381_2 := h6381c.2.2.1
                                                      have p6381_3 := h6381c.2.2.2
                                                      linarith only [hlam, p6381_0]
                                                    · have p6381_0 := h6381c.1
                                                      have p6381_1 := h6381c.2.1
                                                      have p6381_2 := h6381c.2.2.1
                                                      have p6381_3 := h6381c.2.2.2
                                                      linarith only [h6196, hlam, p6381_1]
                                                    · have p6381_0 := h6381c.1
                                                      have p6381_1 := h6381c.2.1
                                                      have p6381_2 := h6381c.2.2.1
                                                      have p6381_3 := h6381c.2.2.2
                                                      linarith only [h5783, hlam, p6381_0]
                                                    · have p6381_0 := h6381c.1
                                                      have p6381_1 := h6381c.2.1
                                                      have p6381_2 := h6381c.2.2.1
                                                      have p6381_3 := h6381c.2.2.2
                                                      linarith only [h5789, hlam, p6381_0]
                                                    · have p6381_0 := h6381c.1
                                                      have p6381_1 := h6381c.2.1
                                                      have p6381_2 := h6381c.2.2.1
                                                      have p6381_3 := h6381c.2.2.2
                                                      linarith only [h0, h5778, h5781, h5783, hc12, hlam, hphi, ht01, ht0b, ht5b, p6381_1, u5ehi2]
                                                    · have p6381_0 := h6381c.1
                                                      have p6381_1 := h6381c.2.1
                                                      have p6381_2 := h6381c.2.2.1
                                                      have p6381_3 := h6381c.2.2.2
                                                      linarith only [h0, h5778, h5781, h5783, hc12, hlam, hphi, ht01, ht0b, ht5b, p6381_1, u5ehi3]
                                                    · have p6381_0 := h6381c.1
                                                      have p6381_1 := h6381c.2.1
                                                      have p6381_2 := h6381c.2.2.1
                                                      have p6381_3 := h6381c.2.2.2
                                                      linarith only [hlam, p6381_0]
                                            · linarith only [h5788, h6374, hlam]
                                          · linarith only [h6373, hlam, p6358_0]
                                        · have p6358_0 := h6358c.1
                                          have p6358_1 := h6358c.2.1
                                          have p6358_2 := h6358c.2.2.1
                                          have p6358_3 := h6358c.2.2.2
                                          linarith only [h5781, h5783, h5784, hc12, hlam, hphi, ht01, ht0b, ht5b, p6358_1, u5ehi4]
                                        · have p6358_0 := h6358c.1
                                          have p6358_1 := h6358c.2.1
                                          have p6358_2 := h6358c.2.2.1
                                          have p6358_3 := h6358c.2.2.2
                                          linarith only [hlam, p6358_0]
                                        · have p6358_0 := h6358c.1
                                          have p6358_1 := h6358c.2.1
                                          have p6358_2 := h6358c.2.2.1
                                          have p6358_3 := h6358c.2.2.2
                                          linarith only [h3977, h5781, h5783, h5790, h6196, hlam, p6358_2]
                                        · have p6358_0 := h6358c.1
                                          have p6358_1 := h6358c.2.1
                                          have p6358_2 := h6358c.2.2.1
                                          have p6358_3 := h6358c.2.2.2
                                          rcases p6358_3 (m.d 0 3) (by simp) with h6434 | h6434
                                          · linarith only [h3977, h6434, hlam]
                                          · linarith only [h5781, h6434, hlam]
                                        · have p6358_0 := h6358c.1
                                          have p6358_1 := h6358c.2.1
                                          have p6358_2 := h6358c.2.2.1
                                          have p6358_3 := h6358c.2.2.2
                                          rcases p6358_3 (m.d 0 3) (by simp) with h6437 | h6437
                                          · linarith only [h3977, h6437, hlam]
                                          · linarith only [h5782, h6437, hlam]
                                        · have p6358_0 := h6358c.1
                                          have p6358_1 := h6358c.2.1
                                          have p6358_2 := h6358c.2.2.1
                                          have p6358_3 := h6358c.2.2.2
                                          linarith only [h5778, hlam, p6358_0]
                                        · have p6358_0 := h6358c.1
                                          have p6358_1 := h6358c.2.1
                                          have p6358_2 := h6358c.2.2.1
                                          have p6358_3 := h6358c.2.2.2
                                          linarith only [h5784, hlam, p6358_0]
                                        · have p6358_0 := h6358c.1
                                          have p6358_1 := h6358c.2.1
                                          have p6358_2 := h6358c.2.2.1
                                          have p6358_3 := h6358c.2.2.2
                                          linarith only [hlam, p6358_0]
                                        · have p6358_0 := h6358c.1
                                          have p6358_1 := h6358c.2.1
                                          have p6358_2 := h6358c.2.2.1
                                          have p6358_3 := h6358c.2.2.2
                                          linarith only [h5790, hlam, p6358_0]
                                        · have p6358_0 := h6358c.1
                                          have p6358_1 := h6358c.2.1
                                          have p6358_2 := h6358c.2.2.1
                                          have p6358_3 := h6358c.2.2.2
                                          linarith only [h6047, hlam, p6358_0]
                                        · have p6358_0 := h6358c.1
                                          have p6358_1 := h6358c.2.1
                                          have p6358_2 := h6358c.2.2.1
                                          have p6358_3 := h6358c.2.2.2
                                          linarith only [h5781, hlam, p6358_0]
                                        · have p6358_0 := h6358c.1
                                          have p6358_1 := h6358c.2.1
                                          have p6358_2 := h6358c.2.2.1
                                          have p6358_3 := h6358c.2.2.2
                                          linarith only [h5787, hlam, p6358_0]
                                        · have p6358_0 := h6358c.1
                                          have p6358_1 := h6358c.2.1
                                          have p6358_2 := h6358c.2.2.1
                                          have p6358_3 := h6358c.2.2.2
                                          linarith only [h5781, h5783, h6196, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6358_1]
                                        · have p6358_0 := h6358c.1
                                          have p6358_1 := h6358c.2.1
                                          have p6358_2 := h6358c.2.2.1
                                          have p6358_3 := h6358c.2.2.2
                                          linarith only [hlam, p6358_0]
                                        · have p6358_0 := h6358c.1
                                          have p6358_1 := h6358c.2.1
                                          have p6358_2 := h6358c.2.2.1
                                          have p6358_3 := h6358c.2.2.2
                                          linarith only [h6196, hlam, p6358_1]
                                        · have p6358_0 := h6358c.1
                                          have p6358_1 := h6358c.2.1
                                          have p6358_2 := h6358c.2.2.1
                                          have p6358_3 := h6358c.2.2.2
                                          linarith only [h5782, hlam, p6358_0]
                                        · have p6358_0 := h6358c.1
                                          have p6358_1 := h6358c.2.1
                                          have p6358_2 := h6358c.2.2.1
                                          have p6358_3 := h6358c.2.2.2
                                          linarith only [h5788, hlam, p6358_0]
                                        · have p6358_0 := h6358c.1
                                          have p6358_1 := h6358c.2.1
                                          have p6358_2 := h6358c.2.2.1
                                          have p6358_3 := h6358c.2.2.2
                                          rcases p6358_3 (m.d 0 3) (by simp) with h6452 | h6452
                                          · rcases p6358_3 (m.d 1 3) (by simp) with h6453 | h6453
                                            · rcases p6358_3 (m.d 2 3) (by simp) with h6454 | h6454
                                              · linarith only [h6454, hlam, p6358_0]
                                              · rcases p6358_3 (m.d 3 4) (by simp) with h6456 | h6456
                                                · linarith only [h6196, h6456, hlam]
                                                · linarith only [h5790, h6456, hlam]
                                            · linarith only [h5784, h6453, hlam]
                                          · linarith only [h5778, h6452, hlam]
                                        · have p6358_0 := h6358c.1
                                          have p6358_1 := h6358c.2.1
                                          have p6358_2 := h6358c.2.2.1
                                          have p6358_3 := h6358c.2.2.2
                                          linarith only [h5790, hc23, hc35, hlam, hphi, p6358_1]
                                        · have p6358_0 := h6358c.1
                                          have p6358_1 := h6358c.2.1
                                          have p6358_2 := h6358c.2.2.1
                                          have p6358_3 := h6358c.2.2.2
                                          linarith only [hlam, p6358_0]
                                · linarith only [h5786, h6351, hlam]
                              · linarith only [h6350, hlam, p6335_0]
                            · have p6335_0 := h6335c.1
                              have p6335_1 := h6335c.2.1
                              have p6335_2 := h6335c.2.2.1
                              have p6335_3 := h6335c.2.2.2
                              linarith only [h5778, h5781, h5783, hc12, hlam, hphi, ht01, ht0b, ht5b, p6335_1, u5ehi4]
                            · have p6335_0 := h6335c.1
                              have p6335_1 := h6335c.2.1
                              have p6335_2 := h6335c.2.2.1
                              have p6335_3 := h6335c.2.2.2
                              linarith only [hlam, p6335_0]
                            · have p6335_0 := h6335c.1
                              have p6335_1 := h6335c.2.1
                              have p6335_2 := h6335c.2.2.1
                              have p6335_3 := h6335c.2.2.2
                              linarith only [h0, h5778, h5781, h5783, h5790, h6196, hlam, p6335_2]
                            · have p6335_0 := h6335c.1
                              have p6335_1 := h6335c.2.1
                              have p6335_2 := h6335c.2.2.1
                              have p6335_3 := h6335c.2.2.2
                              rcases p6335_3 (m.d 0 2) (by simp) with h6468 | h6468
                              · linarith only [h0, h6468, hlam]
                              · linarith only [h5779, h6468, hlam]
                            · have p6335_0 := h6335c.1
                              have p6335_1 := h6335c.2.1
                              have p6335_2 := h6335c.2.2.1
                              have p6335_3 := h6335c.2.2.2
                              rcases p6335_3 (m.d 0 2) (by simp) with h6471 | h6471
                              · linarith only [h0, h6471, hlam]
                              · linarith only [h5780, h6471, hlam]
                            · have p6335_0 := h6335c.1
                              have p6335_1 := h6335c.2.1
                              have p6335_2 := h6335c.2.2.1
                              have p6335_3 := h6335c.2.2.2
                              linarith only [h5778, hlam, p6335_0]
                            · have p6335_0 := h6335c.1
                              have p6335_1 := h6335c.2.1
                              have p6335_2 := h6335c.2.2.1
                              have p6335_3 := h6335c.2.2.2
                              linarith only [h5784, hlam, p6335_0]
                            · have p6335_0 := h6335c.1
                              have p6335_1 := h6335c.2.1
                              have p6335_2 := h6335c.2.2.1
                              have p6335_3 := h6335c.2.2.2
                              linarith only [hlam, p6335_0]
                            · have p6335_0 := h6335c.1
                              have p6335_1 := h6335c.2.1
                              have p6335_2 := h6335c.2.2.1
                              have p6335_3 := h6335c.2.2.2
                              linarith only [h5790, hlam, p6335_0]
                            · have p6335_0 := h6335c.1
                              have p6335_1 := h6335c.2.1
                              have p6335_2 := h6335c.2.2.1
                              have p6335_3 := h6335c.2.2.2
                              linarith only [h6047, hlam, p6335_0]
                            · have p6335_0 := h6335c.1
                              have p6335_1 := h6335c.2.1
                              have p6335_2 := h6335c.2.2.1
                              have p6335_3 := h6335c.2.2.2
                              linarith only [h5779, hlam, p6335_0]
                            · have p6335_0 := h6335c.1
                              have p6335_1 := h6335c.2.1
                              have p6335_2 := h6335c.2.2.1
                              have p6335_3 := h6335c.2.2.2
                              linarith only [h5785, hlam, p6335_0]
                            · have p6335_0 := h6335c.1
                              have p6335_1 := h6335c.2.1
                              have p6335_2 := h6335c.2.2.1
                              have p6335_3 := h6335c.2.2.2
                              linarith only [h5778, h5781, h5783, h5790, h6196, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6335_1]
                            · have p6335_0 := h6335c.1
                              have p6335_1 := h6335c.2.1
                              have p6335_2 := h6335c.2.2.1
                              have p6335_3 := h6335c.2.2.2
                              linarith only [hlam, p6335_0]
                            · have p6335_0 := h6335c.1
                              have p6335_1 := h6335c.2.1
                              have p6335_2 := h6335c.2.2.1
                              have p6335_3 := h6335c.2.2.2
                              linarith only [h6049, hlam, p6335_1]
                            · have p6335_0 := h6335c.1
                              have p6335_1 := h6335c.2.1
                              have p6335_2 := h6335c.2.2.1
                              have p6335_3 := h6335c.2.2.2
                              linarith only [h5780, hlam, p6335_0]
                            · have p6335_0 := h6335c.1
                              have p6335_1 := h6335c.2.1
                              have p6335_2 := h6335c.2.2.1
                              have p6335_3 := h6335c.2.2.2
                              linarith only [h5786, hlam, p6335_0]
                            · have p6335_0 := h6335c.1
                              have p6335_1 := h6335c.2.1
                              have p6335_2 := h6335c.2.2.1
                              have p6335_3 := h6335c.2.2.2
                              rcases p6335_3 (m.d 0 2) (by simp) with h6486 | h6486
                              · rcases p6335_3 (m.d 1 2) (by simp) with h6487 | h6487
                                · rcases p6335_3 (m.d 2 3) (by simp) with h6488 | h6488
                                  · linarith only [h6047, h6488, hlam]
                                  · rcases p6335_3 (m.d 2 4) (by simp) with h6490 | h6490
                                    · linarith only [h6049, h6490, hlam]
                                    · linarith only [h5790, h6490, hlam]
                                · linarith only [h5784, h6487, hlam]
                              · linarith only [h5778, h6486, hlam]
                            · have p6335_0 := h6335c.1
                              have p6335_1 := h6335c.2.1
                              have p6335_2 := h6335c.2.2.1
                              have p6335_3 := h6335c.2.2.2
                              rcases p6335_3 (m.d 0 2) (by simp) with h6495 | h6495
                              · rcases p6335_3 (m.d 1 2) (by simp) with h6496 | h6496
                                · rcases p6335_3 (m.d 2 3) (by simp) with h6497 | h6497
                                  · linarith only [h6047, h6497, hlam]
                                  · rcases p6335_3 (m.d 2 4) (by simp) with h6499 | h6499
                                    · linarith only [h6049, h6499, hlam]
                                    · rcases p6335_3 (m.d 2 5) (by simp) with h6501 | h6501
                                      · rcases h3bigk with h6502c | h6502c | h6502c | h6502c | h6502c | h6502c | h6502c | h6502c | h6502c | h6502c | h6502c | h6502c | h6502c | h6502c | h6502c | h6502c | h6502c | h6502c | h6502c | h6502c | h6502c | h6502c | h6502c | h6502c | h6502c
                                        · have p6502_0 := h6502c.1
                                          have p6502_1 := h6502c.2.1
                                          have p6502_2 := h6502c.2.2.1
                                          have p6502_3 := h6502c.2.2.2
                                          linarith only [hlam, p6502_0]
                                        · have p6502_0 := h6502c.1
                                          have p6502_1 := h6502c.2.1
                                          have p6502_2 := h6502c.2.2.1
                                          have p6502_3 := h6502c.2.2.2
                                          linarith only [h3977, hlam, p6502_1]
                                        · have p6502_0 := h6502c.1
                                          have p6502_1 := h6502c.2.1
                                          have p6502_2 := h6502c.2.2.1
                                          have p6502_3 := h6502c.2.2.2
                                          linarith only [h5781, h5783, h5790, h6196, hlam, p6502_2]
                                        · have p6502_0 := h6502c.1
                                          have p6502_1 := h6502c.2.1
                                          have p6502_2 := h6502c.2.2.1
                                          have p6502_3 := h6502c.2.2.2
                                          rcases p6502_3 (m.d 0 3) (by simp) with h6506 | h6506
                                          · rcases p6502_3 (m.d 1 3) (by simp) with h6507 | h6507
                                            · rcases p6502_3 (m.d 2 3) (by simp) with h6508 | h6508
                                              · linarith only [h5778, h6508, hlam]
                                              · rcases p6502_3 (m.d 3 4) (by simp) with h6510 | h6510
                                                · linarith only [h6510, hlam, p6502_0]
                                                · rcases p6502_3 (m.d 3 5) (by simp) with h6512 | h6512
                                                  · linarith only [h5782, h6512, hlam]
                                                  · linarith only [h6196, h6512, hlam]
                                            · linarith only [h5787, h6507, hlam]
                                          · linarith only [h6506, hlam, p6502_0]
                                        · have p6502_0 := h6502c.1
                                          have p6502_1 := h6502c.2.1
                                          have p6502_2 := h6502c.2.2.1
                                          have p6502_3 := h6502c.2.2.2
                                          linarith only [h0, h5778, h5790, h6047, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6335_1, p6502_1]
                                        · have p6502_0 := h6502c.1
                                          have p6502_1 := h6502c.2.1
                                          have p6502_2 := h6502c.2.2.1
                                          have p6502_3 := h6502c.2.2.2
                                          linarith only [h5781, h5783, h5784, h6196, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6502_1]
                                        · have p6502_0 := h6502c.1
                                          have p6502_1 := h6502c.2.1
                                          have p6502_2 := h6502c.2.2.1
                                          have p6502_3 := h6502c.2.2.2
                                          linarith only [hlam, p6502_0]
                                        · have p6502_0 := h6502c.1
                                          have p6502_1 := h6502c.2.1
                                          have p6502_2 := h6502c.2.2.1
                                          have p6502_3 := h6502c.2.2.2
                                          linarith only [h3977, h5782, h5790, h6047, hlam, p6335_1, p6502_2]
                                        · have p6502_0 := h6502c.1
                                          have p6502_1 := h6502c.2.1
                                          have p6502_2 := h6502c.2.2.1
                                          have p6502_3 := h6502c.2.2.2
                                          rcases p6502_3 (m.d 0 3) (by simp) with h6521 | h6521
                                          · linarith only [h3977, h6521, hlam]
                                          · linarith only [h5781, h6521, hlam]
                                        · have p6502_0 := h6502c.1
                                          have p6502_1 := h6502c.2.1
                                          have p6502_2 := h6502c.2.2.1
                                          have p6502_3 := h6502c.2.2.2
                                          linarith only [h5790, h6047, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6335_1, p6502_1]
                                        · have p6502_0 := h6502c.1
                                          have p6502_1 := h6502c.2.1
                                          have p6502_2 := h6502c.2.2.1
                                          have p6502_3 := h6502c.2.2.2
                                          linarith only [h5778, hlam, p6502_0]
                                        · have p6502_0 := h6502c.1
                                          have p6502_1 := h6502c.2.1
                                          have p6502_2 := h6502c.2.2.1
                                          have p6502_3 := h6502c.2.2.2
                                          linarith only [h5784, hlam, p6502_0]
                                        · have p6502_0 := h6502c.1
                                          have p6502_1 := h6502c.2.1
                                          have p6502_2 := h6502c.2.2.1
                                          have p6502_3 := h6502c.2.2.2
                                          linarith only [hlam, p6502_0]
                                        · have p6502_0 := h6502c.1
                                          have p6502_1 := h6502c.2.1
                                          have p6502_2 := h6502c.2.2.1
                                          have p6502_3 := h6502c.2.2.2
                                          linarith only [h5790, hlam, p6502_0]
                                        · have p6502_0 := h6502c.1
                                          have p6502_1 := h6502c.2.1
                                          have p6502_2 := h6502c.2.2.1
                                          have p6502_3 := h6502c.2.2.2
                                          linarith only [h6047, hlam, p6502_0]
                                        · have p6502_0 := h6502c.1
                                          have p6502_1 := h6502c.2.1
                                          have p6502_2 := h6502c.2.2.1
                                          have p6502_3 := h6502c.2.2.2
                                          linarith only [h5781, hlam, p6502_0]
                                        · have p6502_0 := h6502c.1
                                          have p6502_1 := h6502c.2.1
                                          have p6502_2 := h6502c.2.2.1
                                          have p6502_3 := h6502c.2.2.2
                                          linarith only [h5787, hlam, p6502_0]
                                        · have p6502_0 := h6502c.1
                                          have p6502_1 := h6502c.2.1
                                          have p6502_2 := h6502c.2.2.1
                                          have p6502_3 := h6502c.2.2.2
                                          linarith only [h5781, h5783, h6196, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6502_1]
                                        · have p6502_0 := h6502c.1
                                          have p6502_1 := h6502c.2.1
                                          have p6502_2 := h6502c.2.2.1
                                          have p6502_3 := h6502c.2.2.2
                                          linarith only [hlam, p6502_0]
                                        · have p6502_0 := h6502c.1
                                          have p6502_1 := h6502c.2.1
                                          have p6502_2 := h6502c.2.2.1
                                          have p6502_3 := h6502c.2.2.2
                                          linarith only [h6196, hlam, p6502_1]
                                        · have p6502_0 := h6502c.1
                                          have p6502_1 := h6502c.2.1
                                          have p6502_2 := h6502c.2.2.1
                                          have p6502_3 := h6502c.2.2.2
                                          linarith only [h5782, hlam, p6502_0]
                                        · have p6502_0 := h6502c.1
                                          have p6502_1 := h6502c.2.1
                                          have p6502_2 := h6502c.2.2.1
                                          have p6502_3 := h6502c.2.2.2
                                          linarith only [h5788, hlam, p6502_0]
                                        · have p6502_0 := h6502c.1
                                          have p6502_1 := h6502c.2.1
                                          have p6502_2 := h6502c.2.2.1
                                          have p6502_3 := h6502c.2.2.2
                                          rcases p6502_3 (m.d 0 3) (by simp) with h6537 | h6537
                                          · rcases p6502_3 (m.d 1 3) (by simp) with h6538 | h6538
                                            · rcases p6502_3 (m.d 2 3) (by simp) with h6539 | h6539
                                              · linarith only [h6539, hlam, p6502_0]
                                              · rcases p6502_3 (m.d 3 4) (by simp) with h6541 | h6541
                                                · linarith only [h6196, h6541, hlam]
                                                · linarith only [h5790, h6541, hlam]
                                            · linarith only [h5784, h6538, hlam]
                                          · linarith only [h5778, h6537, hlam]
                                        · have p6502_0 := h6502c.1
                                          have p6502_1 := h6502c.2.1
                                          have p6502_2 := h6502c.2.2.1
                                          have p6502_3 := h6502c.2.2.2
                                          linarith only [h3977, h5782, h5784, h5790, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6502_1]
                                        · have p6502_0 := h6502c.1
                                          have p6502_1 := h6502c.2.1
                                          have p6502_2 := h6502c.2.2.1
                                          have p6502_3 := h6502c.2.2.2
                                          linarith only [hlam, p6502_0]
                                      · linarith only [h6049, h6501, hlam]
                                · linarith only [h5785, h6496, hlam]
                              · linarith only [h5779, h6495, hlam]
                            · have p6335_0 := h6335c.1
                              have p6335_1 := h6335c.2.1
                              have p6335_2 := h6335c.2.2.1
                              have p6335_3 := h6335c.2.2.2
                              linarith only [hlam, p6335_0]
                  · linarith only [h3977, h4846, h5781, h5783, h5784, h5789, hc12, hlam, hphi, ht01, u0ehi0]
                · linarith only [h3977, h5782, h5788, hlam]
              · linarith only [h3977, h5787, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
            · linarith only [h0, h5786, hc25, hlam, hphi, ht01, ht12, u0ehi0]
          · linarith only [h3977, h5784, h5785, hc24, hlam, hphi, ht01, ht12, u0ehi0]
        · linarith only [h0, h5784, hc23, hlam, hphi, ht01, ht12, u0ehi0]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h6558 | h6558
        · rcases m.htr 1 2 4 (by decide) (by decide) with h6559 | h6559
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6560 | h6560
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6561 | h6561
              · rcases m.htr 1 3 5 (by decide) (by decide) with h6562 | h6562
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6563 | h6563
                  · linarith only [h5783, h6558, h6561, h6563, hc12, hlam, hphi, ht01, u0ehi3]
                  · linarith only [h4846, h6563, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi0]
                · linarith only [h3977, h5778, h5782, h6562, hc02, hlam, hphi, u0ehi0]
              · linarith only [h3977, h6561, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
            · linarith only [h0, h5780, h6560, hlam]
          · linarith only [h0, h5779, h6559, hlam]
        · linarith only [h0, h5778, h6558, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h6571 | h6571
      · linarith only [h5781, h5782, h6571, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h6573 | h6573
        · rcases m.htr 1 2 4 (by decide) (by decide) with h6574 | h6574
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6575 | h6575
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6576 | h6576
              · rcases m.htr 1 3 5 (by decide) (by decide) with h6577 | h6577
                · linarith only [h5782, h6573, h6577, hc12, hlam, hphi, ht01, u0ehi2]
                · linarith only [h3977, h6577, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
              · linarith only [h3977, h5780, h5781, h5782, h6576, hc02, hlam, hphi, u0ehi0]
            · linarith only [h0, h6575, hc25, hlam, hphi, ht01, ht12, u0ehi0]
          · linarith only [h3977, h5779, h6573, h6574, hc02, hlam, hphi, u0ehi0]
        · linarith only [h0, h5778, h5780, h5782, h6573, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h6584 | h6584
    · rcases m.htr 0 4 5 (by decide) (by decide) with h6585 | h6585
      · rcases m.htr 1 2 3 (by decide) (by decide) with h6586 | h6586
        · rcases m.htr 1 2 4 (by decide) (by decide) with h6587 | h6587
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6588 | h6588
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6589 | h6589
              · linarith only [h5465, h5781, h6584, h6586, h6589, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h3977, h6589, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
            · linarith only [h0, h6588, hc25, hlam, hphi, ht01, ht12, u0ehi0]
          · linarith only [h3977, h5779, h6586, h6587, hc02, hlam, hphi, u0ehi0]
        · linarith only [h0, h5778, h6586, hc03, hlam, hphi, u0ehi0]
      · linarith only [h5781, h6584, h6585, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h6596 | h6596
      · rcases m.htr 1 2 3 (by decide) (by decide) with h6597 | h6597
        · rcases m.htr 1 2 4 (by decide) (by decide) with h6598 | h6598
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6599 | h6599
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6600 | h6600
              · linarith only [h3977, h5781, h6597, h6600, hc12, hlam, hphi, ht01, u0ehi0]
              · linarith only [h3977, h6600, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
            · linarith only [h0, h5780, h6599, hc02, hlam, hphi, u0ehi0]
          · linarith only [h0, h5779, h6598, hlam]
        · linarith only [h0, h5778, h6584, h6597, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h6606 | h6606
        · rcases m.htr 1 2 4 (by decide) (by decide) with h6607 | h6607
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6608 | h6608
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6609 | h6609
              · linarith only [h5781, h6606, h6609, hc12, hlam, hphi, ht01, u0ehi2]
              · linarith only [h3977, h6609, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
            · linarith only [h0, h5780, h6608, hc02, hlam, hphi, u0ehi0]
          · linarith only [h0, h6607, hc24, hlam, hphi, ht01, ht12, u0ehi0]
        · linarith only [h0, h5778, h6606, hlam]

end R2N4
