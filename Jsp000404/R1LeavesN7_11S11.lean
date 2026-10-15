import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_11S9
import Jsp000404.R1LeavesN7_11S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 12210000 in
set_option maxHeartbeats 12210000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s5_x1_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h5004 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h5238 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h5239 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h5bigk := hb5.1
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 1 2 5 (by decide) (by decide) with h5878 | h5878
  · rcases m.htr 1 3 4 (by decide) (by decide) with h5879 | h5879
    · linarith only [h3, h5004, h5239, h5879, h6, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h5881 | h5881
      · linarith only [h3, h5004, h5239, h5881, hlam]
      · linarith only [h5239, h5878, h5881, hlam]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h5884 | h5884
    · linarith only [h5884, h6, hc13, hlam, hphi, ht01, u0ehi2]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h5886 | h5886
      · linarith only [h3, h5004, h5239, h5886, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h5888 | h5888
        · rcases m.htr 2 3 4 (by decide) (by decide) with h5889 | h5889
          · linarith only [h3, h5889, h6, hlam]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5891 | h5891
            · linarith only [h3, h5004, h5891, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h5893 | h5893
              · rcases m.htr 3 4 5 (by decide) (by decide) with h5894 | h5894
                · rcases h2bigk with h5895c | h5895c | h5895c | h5895c | h5895c | h5895c | h5895c | h5895c | h5895c | h5895c | h5895c | h5895c | h5895c | h5895c | h5895c | h5895c | h5895c | h5895c | h5895c | h5895c | h5895c | h5895c | h5895c | h5895c | h5895c
                  · have p5895_0 := h5895c.1
                    have p5895_1 := h5895c.2.1
                    have p5895_2 := h5895c.2.2.1
                    have p5895_3 := h5895c.2.2.2
                    linarith only [hlam, p5895_0]
                  · have p5895_0 := h5895c.1
                    have p5895_1 := h5895c.2.1
                    have p5895_2 := h5895c.2.2.1
                    have p5895_3 := h5895c.2.2.2
                    rcases p5895_3 (m.d 0 2) (by simp) with h5897 | h5897
                    · rcases p5895_3 (m.d 1 2) (by simp) with h5898 | h5898
                      · linarith only [h0, h5898, hlam]
                      · rcases p5895_3 (m.d 2 3) (by simp) with h5900 | h5900
                        · linarith only [h3, h5900, hlam]
                        · linarith only [h5239, h5900, hlam]
                    · linarith only [h0, h5897, hlam]
                  · have p5895_0 := h5895c.1
                    have p5895_1 := h5895c.2.1
                    have p5895_2 := h5895c.2.2.1
                    have p5895_3 := h5895c.2.2.2
                    rcases p5895_3 (m.d 0 2) (by simp) with h5904 | h5904
                    · rcases p5895_3 (m.d 1 2) (by simp) with h5905 | h5905
                      · linarith only [h0, h5905, hlam]
                      · rcases p5895_3 (m.d 2 3) (by simp) with h5907 | h5907
                        · linarith only [h5907, hlam, p5895_0]
                        · rcases p5895_3 (m.d 2 4) (by simp) with h5909 | h5909
                          · linarith only [h4, h5909, hlam]
                          · linarith only [h5889, h5909, hlam]
                    · linarith only [h5904, hlam, p5895_0]
                  · have p5895_0 := h5895c.1
                    have p5895_1 := h5895c.2.1
                    have p5895_2 := h5895c.2.2.1
                    have p5895_3 := h5895c.2.2.2
                    rcases p5895_3 (m.d 0 2) (by simp) with h5913 | h5913
                    · rcases p5895_3 (m.d 1 2) (by simp) with h5914 | h5914
                      · linarith only [h0, h5914, hlam]
                      · rcases p5895_3 (m.d 2 3) (by simp) with h5916 | h5916
                        · linarith only [h3, h5916, hlam]
                        · rcases p5895_3 (m.d 2 4) (by simp) with h5918 | h5918
                          · linarith only [h5918, hlam, p5895_0]
                          · rcases p5895_3 (m.d 2 5) (by simp) with h5920 | h5920
                            · linarith only [h5, h5920, hlam]
                            · rcases h3bigk with h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c | h5922c
                              · have p5922_0 := h5922c.1
                                have p5922_1 := h5922c.2.1
                                have p5922_2 := h5922c.2.2.1
                                have p5922_3 := h5922c.2.2.2
                                linarith only [hlam, p5922_0]
                              · have p5922_0 := h5922c.1
                                have p5922_1 := h5922c.2.1
                                have p5922_2 := h5922c.2.2.1
                                have p5922_3 := h5922c.2.2.2
                                linarith only [h5004, h5894, hc13, hc34, hlam, hphi, p5922_1]
                              · have p5922_0 := h5922c.1
                                have p5922_1 := h5922c.2.1
                                have p5922_2 := h5922c.2.2.1
                                have p5922_3 := h5922c.2.2.2
                                linarith only [h5004, h5239, h5894, hc12, hc34, hlam, hphi, ht23, p5922_1]
                              · have p5922_0 := h5922c.1
                                have p5922_1 := h5922c.2.1
                                have p5922_2 := h5922c.2.2.1
                                have p5922_3 := h5922c.2.2.2
                                linarith only [h6, hlam, p5922_0]
                              · have p5922_0 := h5922c.1
                                have p5922_1 := h5922c.2.1
                                have p5922_2 := h5922c.2.2.1
                                have p5922_3 := h5922c.2.2.2
                                linarith only [h5004, hlam, p5922_0]
                              · have p5922_0 := h5922c.1
                                have p5922_1 := h5922c.2.1
                                have p5922_2 := h5922c.2.2.1
                                have p5922_3 := h5922c.2.2.2
                                linarith only [h1, hlam, p5922_0]
                              · have p5922_0 := h5922c.1
                                have p5922_1 := h5922c.2.1
                                have p5922_2 := h5922c.2.2.1
                                have p5922_3 := h5922c.2.2.2
                                linarith only [hlam, p5922_0]
                              · have p5922_0 := h5922c.1
                                have p5922_1 := h5922c.2.1
                                have p5922_2 := h5922c.2.2.1
                                have p5922_3 := h5922c.2.2.2
                                linarith only [h5239, hlam, p5922_1]
                              · have p5922_0 := h5922c.1
                                have p5922_1 := h5922c.2.1
                                have p5922_2 := h5922c.2.2.1
                                have p5922_3 := h5922c.2.2.2
                                linarith only [h5884, hlam, p5922_0]
                              · have p5922_0 := h5922c.1
                                have p5922_1 := h5922c.2.1
                                have p5922_2 := h5922c.2.2.1
                                have p5922_3 := h5922c.2.2.2
                                linarith only [h5886, hlam, p5922_0]
                              · have p5922_0 := h5922c.1
                                have p5922_1 := h5922c.2.1
                                have p5922_2 := h5922c.2.2.1
                                have p5922_3 := h5922c.2.2.2
                                linarith only [h3, hlam, p5922_0]
                              · have p5922_0 := h5922c.1
                                have p5922_1 := h5922c.2.1
                                have p5922_2 := h5922c.2.2.1
                                have p5922_3 := h5922c.2.2.2
                                linarith only [h3, h5004, h5894, hc13, hc34, hlam, hphi, p5922_1]
                              · have p5922_0 := h5922c.1
                                have p5922_1 := h5922c.2.1
                                have p5922_2 := h5922c.2.2.1
                                have p5922_3 := h5922c.2.2.2
                                linarith only [hlam, p5922_0]
                              · have p5922_0 := h5922c.1
                                have p5922_1 := h5922c.2.1
                                have p5922_2 := h5922c.2.2.1
                                have p5922_3 := h5922c.2.2.2
                                linarith only [h5889, hlam, p5922_0]
                              · have p5922_0 := h5922c.1
                                have p5922_1 := h5922c.2.1
                                have p5922_2 := h5922c.2.2.1
                                have p5922_3 := h5922c.2.2.2
                                linarith only [h5891, hlam, p5922_0]
                              · have p5922_0 := h5922c.1
                                have p5922_1 := h5922c.2.1
                                have p5922_2 := h5922c.2.2.1
                                have p5922_3 := h5922c.2.2.2
                                linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p5922_1, u0ehi2]
                              · have p5922_0 := h5922c.1
                                have p5922_1 := h5922c.2.1
                                have p5922_2 := h5922c.2.2.1
                                have p5922_3 := h5922c.2.2.2
                                rcases p5922_3 (m.d 0 3) (by simp) with h5939 | h5939
                                · linarith only [h5939, h6, hlam]
                                · linarith only [h1, h5939, hlam]
                              · have p5922_0 := h5922c.1
                                have p5922_1 := h5922c.2.1
                                have p5922_2 := h5922c.2.2.1
                                have p5922_3 := h5922c.2.2.2
                                linarith only [h5239, hc12, hc34, hlam, hphi, ht23, p5922_1]
                              · have p5922_0 := h5922c.1
                                have p5922_1 := h5922c.2.1
                                have p5922_2 := h5922c.2.2.1
                                have p5922_3 := h5922c.2.2.2
                                linarith only [hlam, p5922_0]
                              · have p5922_0 := h5922c.1
                                have p5922_1 := h5922c.2.1
                                have p5922_2 := h5922c.2.2.1
                                have p5922_3 := h5922c.2.2.2
                                linarith only [h0, h5004, h5239, h5891, h5893, hc01, hc12, hc34, hlam, hphi, ht23, p5895_1, p5922_1, u0ehi2]
                              · have p5922_0 := h5922c.1
                                have p5922_1 := h5922c.2.1
                                have p5922_2 := h5922c.2.2.1
                                have p5922_3 := h5922c.2.2.2
                                linarith only [h0, h5239, h5891, h5893, hc01, hc12, hc35, hlam, hphi, ht23, p5895_1, p5922_1, u0ehi2]
                              · have p5922_0 := h5922c.1
                                have p5922_1 := h5922c.2.1
                                have p5922_2 := h5922c.2.2.1
                                have p5922_3 := h5922c.2.2.2
                                rcases p5922_3 (m.d 0 3) (by simp) with h5946 | h5946
                                · linarith only [h5004, h5946, hlam]
                                · linarith only [h1, h5946, hlam]
                              · have p5922_0 := h5922c.1
                                have p5922_1 := h5922c.2.1
                                have p5922_2 := h5922c.2.2.1
                                have p5922_3 := h5922c.2.2.2
                                linarith only [h5239, h5894, hc12, hc34, hlam, hphi, ht23, p5922_1]
                              · have p5922_0 := h5922c.1
                                have p5922_1 := h5922c.2.1
                                have p5922_2 := h5922c.2.2.1
                                have p5922_3 := h5922c.2.2.2
                                linarith only [h5894, hlam, p5922_0]
                              · have p5922_0 := h5922c.1
                                have p5922_1 := h5922c.2.1
                                have p5922_2 := h5922c.2.2.1
                                have p5922_3 := h5922c.2.2.2
                                linarith only [hlam, p5922_0]
                    · linarith only [h5913, hlam, p5895_0]
                  · have p5895_0 := h5895c.1
                    have p5895_1 := h5895c.2.1
                    have p5895_2 := h5895c.2.2.1
                    have p5895_3 := h5895c.2.2.2
                    rcases p5895_3 (m.d 0 2) (by simp) with h5953 | h5953
                    · rcases p5895_3 (m.d 1 2) (by simp) with h5954 | h5954
                      · linarith only [h0, h5954, hlam]
                      · rcases p5895_3 (m.d 2 3) (by simp) with h5956 | h5956
                        · linarith only [h3, h5956, hlam]
                        · rcases p5895_3 (m.d 2 4) (by simp) with h5958 | h5958
                          · linarith only [h4, h5958, hlam]
                          · linarith only [h5893, h5958, hlam]
                    · linarith only [h5953, hlam, p5895_0]
                  · have p5895_0 := h5895c.1
                    have p5895_1 := h5895c.2.1
                    have p5895_2 := h5895c.2.2.1
                    have p5895_3 := h5895c.2.2.2
                    linarith only [h0, hlam, p5895_0]
                  · have p5895_0 := h5895c.1
                    have p5895_1 := h5895c.2.1
                    have p5895_2 := h5895c.2.2.1
                    have p5895_3 := h5895c.2.2.2
                    linarith only [hlam, p5895_0]
                  · have p5895_0 := h5895c.1
                    have p5895_1 := h5895c.2.1
                    have p5895_2 := h5895c.2.2.1
                    have p5895_3 := h5895c.2.2.2
                    linarith only [h5239, hlam, p5895_0]
                  · have p5895_0 := h5895c.1
                    have p5895_1 := h5895c.2.1
                    have p5895_2 := h5895c.2.2.1
                    have p5895_3 := h5895c.2.2.2
                    linarith only [h5239, h5891, h5893, hlam, p5895_1]
                  · have p5895_0 := h5895c.1
                    have p5895_1 := h5895c.2.1
                    have p5895_2 := h5895c.2.2.1
                    have p5895_3 := h5895c.2.2.2
                    linarith only [h5878, hlam, p5895_0]
                  · have p5895_0 := h5895c.1
                    have p5895_1 := h5895c.2.1
                    have p5895_2 := h5895c.2.2.1
                    have p5895_3 := h5895c.2.2.2
                    linarith only [h3, hlam, p5895_0]
                  · have p5895_0 := h5895c.1
                    have p5895_1 := h5895c.2.1
                    have p5895_2 := h5895c.2.2.1
                    have p5895_3 := h5895c.2.2.2
                    linarith only [h3, h6, hc12, hc34, hlam, hphi, ht23, p5895_1]
                  · have p5895_0 := h5895c.1
                    have p5895_1 := h5895c.2.1
                    have p5895_2 := h5895c.2.2.1
                    have p5895_3 := h5895c.2.2.2
                    linarith only [hlam, p5895_0]
                  · have p5895_0 := h5895c.1
                    have p5895_1 := h5895c.2.1
                    have p5895_2 := h5895c.2.2.1
                    have p5895_3 := h5895c.2.2.2
                    linarith only [h5889, hlam, p5895_0]
                  · have p5895_0 := h5895c.1
                    have p5895_1 := h5895c.2.1
                    have p5895_2 := h5895c.2.2.1
                    have p5895_3 := h5895c.2.2.2
                    linarith only [h5891, hlam, p5895_0]
                  · have p5895_0 := h5895c.1
                    have p5895_1 := h5895c.2.1
                    have p5895_2 := h5895c.2.2.1
                    have p5895_3 := h5895c.2.2.2
                    linarith only [h4, hlam, p5895_0]
                  · have p5895_0 := h5895c.1
                    have p5895_1 := h5895c.2.1
                    have p5895_2 := h5895c.2.2.1
                    have p5895_3 := h5895c.2.2.2
                    rcases p5895_3 (m.d 0 2) (by simp) with h5973 | h5973
                    · rcases p5895_3 (m.d 1 2) (by simp) with h5974 | h5974
                      · linarith only [h5974, hlam, p5895_0]
                      · rcases p5895_3 (m.d 2 3) (by simp) with h5976 | h5976
                        · linarith only [h5889, h5976, hlam]
                        · linarith only [h5239, h5976, hlam]
                    · linarith only [h0, h5973, hlam]
                  · have p5895_0 := h5895c.1
                    have p5895_1 := h5895c.2.1
                    have p5895_2 := h5895c.2.2.1
                    have p5895_3 := h5895c.2.2.2
                    linarith only [h0, h4, h5239, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5895_1]
                  · have p5895_0 := h5895c.1
                    have p5895_1 := h5895c.2.1
                    have p5895_2 := h5895c.2.2.1
                    have p5895_3 := h5895c.2.2.2
                    linarith only [hlam, p5895_0]
                  · have p5895_0 := h5895c.1
                    have p5895_1 := h5895c.2.1
                    have p5895_2 := h5895c.2.2.1
                    have p5895_3 := h5895c.2.2.2
                    linarith only [h0, h4, h5239, h5891, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5895_1]
                  · have p5895_0 := h5895c.1
                    have p5895_1 := h5895c.2.1
                    have p5895_2 := h5895c.2.2.1
                    have p5895_3 := h5895c.2.2.2
                    linarith only [h5, hlam, p5895_0]
                  · have p5895_0 := h5895c.1
                    have p5895_1 := h5895c.2.1
                    have p5895_2 := h5895c.2.2.1
                    have p5895_3 := h5895c.2.2.2
                    rcases p5895_3 (m.d 0 2) (by simp) with h5984 | h5984
                    · rcases p5895_3 (m.d 1 2) (by simp) with h5985 | h5985
                      · linarith only [h5985, hlam, p5895_0]
                      · rcases p5895_3 (m.d 2 3) (by simp) with h5987 | h5987
                        · linarith only [h5891, h5987, hlam]
                        · linarith only [h5239, h5987, hlam]
                    · linarith only [h0, h5984, hlam]
                  · have p5895_0 := h5895c.1
                    have p5895_1 := h5895c.2.1
                    have p5895_2 := h5895c.2.2.1
                    have p5895_3 := h5895c.2.2.2
                    linarith only [h5239, hc12, hc25, hlam, hphi, p5895_1]
                  · have p5895_0 := h5895c.1
                    have p5895_1 := h5895c.2.1
                    have p5895_2 := h5895c.2.2.1
                    have p5895_3 := h5895c.2.2.2
                    linarith only [h5893, hlam, p5895_0]
                  · have p5895_0 := h5895c.1
                    have p5895_1 := h5895c.2.1
                    have p5895_2 := h5895c.2.2.1
                    have p5895_3 := h5895c.2.2.2
                    linarith only [hlam, p5895_0]
                · linarith only [h0, h4, h5893, h5894, h6, hc01, hlam, hphi, u0ehi3]
              · linarith only [h5238, h5239, h5889, h5893, h6, hc12, hc34, hlam, hphi, ht23]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h5996 | h5996
          · linarith only [h0, h3, h5238, h5888, h5996, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5998 | h5998
            · linarith only [h3, h5004, h5998, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h6000 | h6000
              · rcases m.htr 3 4 5 (by decide) (by decide) with h6001 | h6001
                · rcases h2bigk with h6002c | h6002c | h6002c | h6002c | h6002c | h6002c | h6002c | h6002c | h6002c | h6002c | h6002c | h6002c | h6002c | h6002c | h6002c | h6002c | h6002c | h6002c | h6002c | h6002c | h6002c | h6002c | h6002c | h6002c | h6002c
                  · have p6002_0 := h6002c.1
                    have p6002_1 := h6002c.2.1
                    have p6002_2 := h6002c.2.2.1
                    have p6002_3 := h6002c.2.2.2
                    linarith only [hlam, p6002_0]
                  · have p6002_0 := h6002c.1
                    have p6002_1 := h6002c.2.1
                    have p6002_2 := h6002c.2.2.1
                    have p6002_3 := h6002c.2.2.2
                    linarith only [h4, h5239, h5884, h5888, h6000, hlam, p6002_2]
                  · have p6002_0 := h6002c.1
                    have p6002_1 := h6002c.2.1
                    have p6002_2 := h6002c.2.2.1
                    have p6002_3 := h6002c.2.2.2
                    rcases p6002_3 (m.d 0 2) (by simp) with h6005 | h6005
                    · rcases p6002_3 (m.d 1 2) (by simp) with h6006 | h6006
                      · linarith only [h0, h6006, hlam]
                      · rcases p6002_3 (m.d 2 3) (by simp) with h6008 | h6008
                        · linarith only [h6008, hlam, p6002_0]
                        · rcases p6002_3 (m.d 2 4) (by simp) with h6010 | h6010
                          · linarith only [h4, h6010, hlam]
                          · linarith only [h5996, h6010, hlam]
                    · linarith only [h6005, hlam, p6002_0]
                  · have p6002_0 := h6002c.1
                    have p6002_1 := h6002c.2.1
                    have p6002_2 := h6002c.2.2.1
                    have p6002_3 := h6002c.2.2.2
                    linarith only [h0, h5239, h5884, h5888, h6000, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6002_1]
                  · have p6002_0 := h6002c.1
                    have p6002_1 := h6002c.2.1
                    have p6002_2 := h6002c.2.2.1
                    have p6002_3 := h6002c.2.2.2
                    rcases p6002_3 (m.d 0 2) (by simp) with h6015 | h6015
                    · rcases p6002_3 (m.d 1 2) (by simp) with h6016 | h6016
                      · linarith only [h0, h6016, hlam]
                      · rcases p6002_3 (m.d 2 3) (by simp) with h6018 | h6018
                        · linarith only [h3, h6018, hlam]
                        · rcases p6002_3 (m.d 2 4) (by simp) with h6020 | h6020
                          · linarith only [h4, h6020, hlam]
                          · linarith only [h6000, h6020, hlam]
                    · linarith only [h6015, hlam, p6002_0]
                  · have p6002_0 := h6002c.1
                    have p6002_1 := h6002c.2.1
                    have p6002_2 := h6002c.2.2.1
                    have p6002_3 := h6002c.2.2.2
                    linarith only [h0, hlam, p6002_0]
                  · have p6002_0 := h6002c.1
                    have p6002_1 := h6002c.2.1
                    have p6002_2 := h6002c.2.2.1
                    have p6002_3 := h6002c.2.2.2
                    linarith only [hlam, p6002_0]
                  · have p6002_0 := h6002c.1
                    have p6002_1 := h6002c.2.1
                    have p6002_2 := h6002c.2.2.1
                    have p6002_3 := h6002c.2.2.2
                    linarith only [h5239, hlam, p6002_0]
                  · have p6002_0 := h6002c.1
                    have p6002_1 := h6002c.2.1
                    have p6002_2 := h6002c.2.2.1
                    have p6002_3 := h6002c.2.2.2
                    linarith only [h5239, h5884, h5888, h6000, hlam, p6002_1]
                  · have p6002_0 := h6002c.1
                    have p6002_1 := h6002c.2.1
                    have p6002_2 := h6002c.2.2.1
                    have p6002_3 := h6002c.2.2.2
                    linarith only [h5878, hlam, p6002_0]
                  · have p6002_0 := h6002c.1
                    have p6002_1 := h6002c.2.1
                    have p6002_2 := h6002c.2.2.1
                    have p6002_3 := h6002c.2.2.2
                    linarith only [h3, hlam, p6002_0]
                  · have p6002_0 := h6002c.1
                    have p6002_1 := h6002c.2.1
                    have p6002_2 := h6002c.2.2.1
                    have p6002_3 := h6002c.2.2.2
                    linarith only [h3, h6, hc12, hc34, hlam, hphi, ht23, p6002_1]
                  · have p6002_0 := h6002c.1
                    have p6002_1 := h6002c.2.1
                    have p6002_2 := h6002c.2.2.1
                    have p6002_3 := h6002c.2.2.2
                    linarith only [hlam, p6002_0]
                  · have p6002_0 := h6002c.1
                    have p6002_1 := h6002c.2.1
                    have p6002_2 := h6002c.2.2.1
                    have p6002_3 := h6002c.2.2.2
                    linarith only [h5996, hlam, p6002_0]
                  · have p6002_0 := h6002c.1
                    have p6002_1 := h6002c.2.1
                    have p6002_2 := h6002c.2.2.1
                    have p6002_3 := h6002c.2.2.2
                    linarith only [h5998, hlam, p6002_0]
                  · have p6002_0 := h6002c.1
                    have p6002_1 := h6002c.2.1
                    have p6002_2 := h6002c.2.2.1
                    have p6002_3 := h6002c.2.2.2
                    linarith only [h4, hlam, p6002_0]
                  · have p6002_0 := h6002c.1
                    have p6002_1 := h6002c.2.1
                    have p6002_2 := h6002c.2.2.1
                    have p6002_3 := h6002c.2.2.2
                    rcases p6002_3 (m.d 0 2) (by simp) with h6035 | h6035
                    · rcases p6002_3 (m.d 1 2) (by simp) with h6036 | h6036
                      · linarith only [h6036, hlam, p6002_0]
                      · rcases p6002_3 (m.d 2 3) (by simp) with h6038 | h6038
                        · linarith only [h5996, h6038, hlam]
                        · linarith only [h5239, h6038, hlam]
                    · linarith only [h0, h6035, hlam]
                  · have p6002_0 := h6002c.1
                    have p6002_1 := h6002c.2.1
                    have p6002_2 := h6002c.2.2.1
                    have p6002_3 := h6002c.2.2.2
                    linarith only [h0, h4, h5239, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6002_1]
                  · have p6002_0 := h6002c.1
                    have p6002_1 := h6002c.2.1
                    have p6002_2 := h6002c.2.2.1
                    have p6002_3 := h6002c.2.2.2
                    linarith only [hlam, p6002_0]
                  · have p6002_0 := h6002c.1
                    have p6002_1 := h6002c.2.1
                    have p6002_2 := h6002c.2.2.1
                    have p6002_3 := h6002c.2.2.2
                    linarith only [h0, h4, h5239, h5998, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6002_1]
                  · have p6002_0 := h6002c.1
                    have p6002_1 := h6002c.2.1
                    have p6002_2 := h6002c.2.2.1
                    have p6002_3 := h6002c.2.2.2
                    linarith only [h5, hlam, p6002_0]
                  · have p6002_0 := h6002c.1
                    have p6002_1 := h6002c.2.1
                    have p6002_2 := h6002c.2.2.1
                    have p6002_3 := h6002c.2.2.2
                    rcases p6002_3 (m.d 0 2) (by simp) with h6046 | h6046
                    · rcases p6002_3 (m.d 1 2) (by simp) with h6047 | h6047
                      · linarith only [h6047, hlam, p6002_0]
                      · rcases p6002_3 (m.d 2 3) (by simp) with h6049 | h6049
                        · linarith only [h5998, h6049, hlam]
                        · linarith only [h5239, h6049, hlam]
                    · linarith only [h0, h6046, hlam]
                  · have p6002_0 := h6002c.1
                    have p6002_1 := h6002c.2.1
                    have p6002_2 := h6002c.2.2.1
                    have p6002_3 := h6002c.2.2.2
                    linarith only [h5239, hc12, hc25, hlam, hphi, p6002_1]
                  · have p6002_0 := h6002c.1
                    have p6002_1 := h6002c.2.1
                    have p6002_2 := h6002c.2.2.1
                    have p6002_3 := h6002c.2.2.2
                    linarith only [h6000, hlam, p6002_0]
                  · have p6002_0 := h6002c.1
                    have p6002_1 := h6002c.2.1
                    have p6002_2 := h6002c.2.2.1
                    have p6002_3 := h6002c.2.2.2
                    linarith only [hlam, p6002_0]
                · linarith only [h6, h6001, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
              · linarith only [h5238, h5239, h5996, h6, h6000, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 12210000 in
set_option maxHeartbeats 12210000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s5_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h5004 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h5238 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h5bigk := hb5.1
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 1 2 3 (by decide) (by decide) with h5239 | h5239
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s5_x1_x1_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 h6 h5004 h5238 h5239
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s5_x1_x1_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 h6 h5004 h5238 h5239

set_option maxHeartbeats 12210000 in
set_option maxHeartbeats 12210000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s5_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h5004 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h5238 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h5bigk := hb5.1
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 1 2 3 (by decide) (by decide) with h6058 | h6058
  · rcases m.htr 1 2 5 (by decide) (by decide) with h6059 | h6059
    · rcases m.htr 1 3 4 (by decide) (by decide) with h6060 | h6060
      · linarith only [h6, h6060, hc13, hlam, hphi, ht01, u0ehi2]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h6062 | h6062
        · linarith only [h1, h5004, h6062, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h6064 | h6064
          · linarith only [h5238, h6064, hc14, hlam, hphi, ht01, u0ehi3]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h6066 | h6066
            · linarith only [h6, h6066, hc23, hlam, hphi, ht01, ht12, u0ehi2]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h6068 | h6068
              · linarith only [h5004, h6058, h6068, hc12, hlam, hphi, ht01, u0ehi2]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h6070 | h6070
                · linarith only [h5238, h6, h6070, hc24, hlam, hphi, ht01, ht12, u0ehi2]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h6072 | h6072
                  · linarith only [h5238, h6, h6072, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                  · linarith only [h6, h6072, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h6075 | h6075
      · linarith only [h0, h5, h6, h6058, h6059, h6075, hc01, hlam, hphi, u0ehi2]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h6077 | h6077
        · linarith only [h0, h5, h5004, h6058, h6059, h6077, hc01, hlam, hphi, u0ehi2]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h6079 | h6079
          · linarith only [h5238, h6, h6079, hc14, hlam, hphi, ht01, u0ehi2]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h6081 | h6081
            · linarith only [h0, h5, h6058, h6059, h6081, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h6083 | h6083
              · linarith only [h0, h5, h5004, h6058, h6059, h6083, hc01, hlam, hphi, u0ehi2]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h6085 | h6085
                · linarith only [h5238, h6, h6085, hc24, hlam, hphi, ht01, ht12, u0ehi2]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h6087 | h6087
                  · linarith only [h5238, h6, h6087, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                  · linarith only [h6, h6087, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h6090 | h6090
    · rcases m.htr 1 3 4 (by decide) (by decide) with h6091 | h6091
      · linarith only [h3, h6, h6058, h6090, h6091, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h6093 | h6093
        · linarith only [h3, h5004, h6058, h6093, hlam]
        · linarith only [h6058, h6090, h6093, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h6096 | h6096
      · linarith only [h6, h6096, hc13, hlam, hphi, ht01, u0ehi2]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h6098 | h6098
        · linarith only [h3, h5004, h6058, h6098, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h6100 | h6100
          · linarith only [h5238, h6100, hc14, hlam, hphi, ht01, u0ehi3]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h6102 | h6102
            · linarith only [h3, h6, h6102, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h6104 | h6104
              · linarith only [h3, h5004, h6104, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h6106 | h6106
                · linarith only [h4, h5238, h6106, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h6108 | h6108
                  · linarith only [h5238, h6, h6108, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                  · linarith only [h6, h6108, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]

set_option maxHeartbeats 12210000 in
set_option maxHeartbeats 12210000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s5_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h5004 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h5bigk := hb5.1
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 0 4 5 (by decide) (by decide) with h5238 | h5238
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s5_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 h6 h5004 h5238
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s5_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 h6 h5004 h5238

set_option maxHeartbeats 12210000 in
set_option maxHeartbeats 12210000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s5_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h5bigk := hb5.1
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 0 3 5 (by decide) (by decide) with h5004 | h5004
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s5_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 h6 h5004
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s5_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 h6 h5004

set_option maxHeartbeats 12210000 in
set_option maxHeartbeats 12210000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s5 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h5bigk := hb5.1
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s5_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 h6
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s5_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 h6

set_option maxHeartbeats 12302000 in
set_option maxHeartbeats 12302000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s4 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h5bigk := hb5.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s5 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4 h5
  · rcases m.htr 0 3 4 (by decide) (by decide) with h6111 | h6111
    · rcases m.htr 0 3 5 (by decide) (by decide) with h6112 | h6112
      · linarith only [h3, h5, h6112, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h6114 | h6114
        · linarith only [h4, h5, h6114, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6116 | h6116
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6117 | h6117
            · linarith only [h0, h5, h6117, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6119 | h6119
              · rcases m.htr 1 3 5 (by decide) (by decide) with h6120 | h6120
                · linarith only [h6112, h6120, hc13, hlam, hphi, ht01, u0ehi2]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6122 | h6122
                  · linarith only [h6114, h6122, hc14, hlam, hphi, ht01, u0ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6124 | h6124
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h6125 | h6125
                      · linarith only [h0, h1, h5, h6112, h6116, h6125, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6127 | h6127
                        · linarith only [h0, h5, h6114, h6116, h6124, h6125, h6127, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h0, h5, h6116, h6124, h6127, hc34, hc45, hlam, hphi]
                    · linarith only [h1, h6112, h6119, h6124, hc23, hc35, hlam, hphi]
              · linarith only [h6111, h6112, h6119, hc13, hc35, hlam, hphi]
          · linarith only [h3, h5, h6116, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h6133 | h6133
      · linarith only [h4, h5, h6111, h6133, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h6135 | h6135
        · linarith only [h4, h5, h6135, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6137 | h6137
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6138 | h6138
            · linarith only [h5, h6138, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6140 | h6140
              · linarith only [h6111, h6140, hc13, hlam, hphi, ht01, u0ehi2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h6142 | h6142
                · linarith only [h1, h6133, h6142, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6144 | h6144
                  · linarith only [h6135, h6144, hc14, hlam, hphi, ht01, u0ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6146 | h6146
                    · linarith only [h6111, h6146, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h6148 | h6148
                      · linarith only [h0, h5, h6133, h6137, h6148, hc25, hlam, hphi, ht01, ht12, u0ehi2]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6150 | h6150
                        · linarith only [h6111, h6135, h6150, hc24, hlam, hphi, ht01, ht12, u0ehi2]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h6152 | h6152
                          · linarith only [h0, h5, h6137, h6150, h6152, hc23, hc34, hlam, hphi]
                          · linarith only [h6111, h6152, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
          · linarith only [h3, h5, h6137, hc12, hc25, hlam, hphi]

set_option maxHeartbeats 12758000 in
set_option maxHeartbeats 12758000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s3 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h5bigk := hb5.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s4 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4
  · rcases m.htr 0 2 5 (by decide) (by decide) with h6156 | h6156
    · rcases m.htr 0 3 4 (by decide) (by decide) with h6157 | h6157
      · linarith only [h3, h4, h6157, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h6159 | h6159
        · rcases m.htr 0 4 5 (by decide) (by decide) with h6160 | h6160
          · rcases m.htr 1 2 3 (by decide) (by decide) with h6161 | h6161
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6162 | h6162
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6163 | h6163
                · linarith only [h1, h6157, h6163, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6165 | h6165
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6166 | h6166
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6167 | h6167
                      · linarith only [h0, h4, h6157, h6161, h6167, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6169 | h6169
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h6170 | h6170
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h6171 | h6171
                            · rcases h2bigk with h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c
                              · have p6172_0 := h6172c.1
                                have p6172_1 := h6172c.2.1
                                have p6172_2 := h6172c.2.2.1
                                have p6172_3 := h6172c.2.2.2
                                linarith only [hlam, p6172_0]
                              · have p6172_0 := h6172c.1
                                have p6172_1 := h6172c.2.1
                                have p6172_2 := h6172c.2.2.1
                                have p6172_3 := h6172c.2.2.2
                                linarith only [h4, h6167, hc12, hc34, hlam, hphi, ht23, p6172_1]
                              · have p6172_0 := h6172c.1
                                have p6172_1 := h6172c.2.1
                                have p6172_2 := h6172c.2.2.1
                                have p6172_3 := h6172c.2.2.2
                                linarith only [h4, h6167, h6169, h6171, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p6172_1]
                              · have p6172_0 := h6172c.1
                                have p6172_1 := h6172c.2.1
                                have p6172_2 := h6172c.2.2.1
                                have p6172_3 := h6172c.2.2.2
                                linarith only [h4, hlam, p6172_0]
                              · have p6172_0 := h6172c.1
                                have p6172_1 := h6172c.2.1
                                have p6172_2 := h6172c.2.2.1
                                have p6172_3 := h6172c.2.2.2
                                rcases p6172_3 (m.d 0 2) (by simp) with h6177 | h6177
                                · rcases p6172_3 (m.d 1 2) (by simp) with h6178 | h6178
                                  · linarith only [h0, h6178, hlam]
                                  · linarith only [h6162, h6178, hlam]
                                · linarith only [h6177, hlam, p6172_0]
                              · have p6172_0 := h6172c.1
                                have p6172_1 := h6172c.2.1
                                have p6172_2 := h6172c.2.2.1
                                have p6172_3 := h6172c.2.2.2
                                linarith only [h0, hlam, p6172_0]
                              · have p6172_0 := h6172c.1
                                have p6172_1 := h6172c.2.1
                                have p6172_2 := h6172c.2.2.1
                                have p6172_3 := h6172c.2.2.2
                                linarith only [hlam, p6172_0]
                              · have p6172_0 := h6172c.1
                                have p6172_1 := h6172c.2.1
                                have p6172_2 := h6172c.2.2.1
                                have p6172_3 := h6172c.2.2.2
                                linarith only [h0, h6169, h6171, hc01, hc45, hlam, hphi, ht0b, ht5b, p6172_1]
                              · have p6172_0 := h6172c.1
                                have p6172_1 := h6172c.2.1
                                have p6172_2 := h6172c.2.2.1
                                have p6172_3 := h6172c.2.2.2
                                linarith only [h0, h4, hlam, p6172_1]
                              · have p6172_0 := h6172c.1
                                have p6172_1 := h6172c.2.1
                                have p6172_2 := h6172c.2.2.1
                                have p6172_3 := h6172c.2.2.2
                                rcases p6172_3 (m.d 0 2) (by simp) with h6186 | h6186
                                · rcases p6172_3 (m.d 1 2) (by simp) with h6187 | h6187
                                  · rcases p6172_3 (m.d 2 3) (by simp) with h6188 | h6188
                                    · linarith only [h6161, h6188, hlam]
                                    · linarith only [h6169, h6188, hlam]
                                  · linarith only [h6187, hlam, p6172_0]
                                · linarith only [h6156, h6186, hlam]
                              · have p6172_0 := h6172c.1
                                have p6172_1 := h6172c.2.1
                                have p6172_2 := h6172c.2.2.1
                                have p6172_3 := h6172c.2.2.2
                                linarith only [h3, hlam, p6172_0]
                              · have p6172_0 := h6172c.1
                                have p6172_1 := h6172c.2.1
                                have p6172_2 := h6172c.2.2.1
                                have p6172_3 := h6172c.2.2.2
                                linarith only [h6161, hlam, p6172_0]
                              · have p6172_0 := h6172c.1
                                have p6172_1 := h6172c.2.1
                                have p6172_2 := h6172c.2.2.1
                                have p6172_3 := h6172c.2.2.2
                                linarith only [hlam, p6172_0]
                              · have p6172_0 := h6172c.1
                                have p6172_1 := h6172c.2.1
                                have p6172_2 := h6172c.2.2.1
                                have p6172_3 := h6172c.2.2.2
                                linarith only [h6167, hlam, p6172_0]
                              · have p6172_0 := h6172c.1
                                have p6172_1 := h6172c.2.1
                                have p6172_2 := h6172c.2.2.1
                                have p6172_3 := h6172c.2.2.2
                                linarith only [h3, h4, h6167, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p6172_1]
                              · have p6172_0 := h6172c.1
                                have p6172_1 := h6172c.2.1
                                have p6172_2 := h6172c.2.2.1
                                have p6172_3 := h6172c.2.2.2
                                linarith only [h6167, hc34, hlam, hphi, ht01, ht12, ht23, p6172_1, u0ehi1]
                              · have p6172_0 := h6172c.1
                                have p6172_1 := h6172c.2.1
                                have p6172_2 := h6172c.2.2.1
                                have p6172_3 := h6172c.2.2.2
                                linarith only [h6161, h6167, hc23, hc34, hlam, hphi, p6172_1]
                              · have p6172_0 := h6172c.1
                                have p6172_1 := h6172c.2.1
                                have p6172_2 := h6172c.2.2.1
                                have p6172_3 := h6172c.2.2.2
                                rcases p6172_3 (m.d 0 2) (by simp) with h6200 | h6200
                                · linarith only [h4, h6200, hlam]
                                · linarith only [h3, h6200, hlam]
                              · have p6172_0 := h6172c.1
                                have p6172_1 := h6172c.2.1
                                have p6172_2 := h6172c.2.2.1
                                have p6172_3 := h6172c.2.2.2
                                linarith only [hlam, p6172_0]
                              · have p6172_0 := h6172c.1
                                have p6172_1 := h6172c.2.1
                                have p6172_2 := h6172c.2.2.1
                                have p6172_3 := h6172c.2.2.2
                                rcases p6172_3 (m.d 0 2) (by simp) with h6204 | h6204
                                · linarith only [h4, h6204, hlam]
                                · linarith only [h6156, h6204, hlam]
                              · have p6172_0 := h6172c.1
                                have p6172_1 := h6172c.2.1
                                have p6172_2 := h6172c.2.2.1
                                have p6172_3 := h6172c.2.2.2
                                linarith only [h6156, hlam, p6172_0]
                              · have p6172_0 := h6172c.1
                                have p6172_1 := h6172c.2.1
                                have p6172_2 := h6172c.2.2.1
                                have p6172_3 := h6172c.2.2.2
                                linarith only [h6162, hlam, p6172_0]
                              · have p6172_0 := h6172c.1
                                have p6172_1 := h6172c.2.1
                                have p6172_2 := h6172c.2.2.1
                                have p6172_3 := h6172c.2.2.2
                                linarith only [h6169, hlam, p6172_1]
                              · have p6172_0 := h6172c.1
                                have p6172_1 := h6172c.2.1
                                have p6172_2 := h6172c.2.2.1
                                have p6172_3 := h6172c.2.2.2
                                linarith only [h6170, hlam, p6172_0]
                              · have p6172_0 := h6172c.1
                                have p6172_1 := h6172c.2.1
                                have p6172_2 := h6172c.2.2.1
                                have p6172_3 := h6172c.2.2.2
                                linarith only [hlam, p6172_0]
                            · linarith only [h4, h6167, h6171, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                          · linarith only [h0, h4, h6161, h6166, h6170, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h3, h4, h6159, h6167, h6169, hc23, hc34, hlam, hphi]
                    · linarith only [h6163, h6165, h6166, hlam]
                  · linarith only [h6157, h6159, h6165, hc13, hc34, hlam, hphi]
              · linarith only [h4, h6156, h6161, h6162, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · linarith only [h3, h4, h6161, hc12, hc24, hlam, hphi]
          · linarith only [h3, h4, h6159, h6160, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h6220 | h6220
          · rcases m.htr 1 2 3 (by decide) (by decide) with h6221 | h6221
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6222 | h6222
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6223 | h6223
                · linarith only [h1, h6157, h6223, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6225 | h6225
                  · linarith only [h6159, h6221, h6225, hc12, hlam, hphi, ht01, u0ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6227 | h6227
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6228 | h6228
                      · linarith only [h6157, h6228, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6230 | h6230
                        · linarith only [h6159, h6221, h6230, hc13, hlam, hphi, ht01, u0ehi2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h6232 | h6232
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h6233 | h6233
                            · rcases h2bigk with h6234c | h6234c | h6234c | h6234c | h6234c | h6234c | h6234c | h6234c | h6234c | h6234c | h6234c | h6234c | h6234c | h6234c | h6234c | h6234c | h6234c | h6234c | h6234c | h6234c | h6234c | h6234c | h6234c | h6234c | h6234c
                              · have p6234_0 := h6234c.1
                                have p6234_1 := h6234c.2.1
                                have p6234_2 := h6234c.2.2.1
                                have p6234_3 := h6234c.2.2.2
                                linarith only [hlam, p6234_0]
                              · have p6234_0 := h6234c.1
                                have p6234_1 := h6234c.2.1
                                have p6234_2 := h6234c.2.2.1
                                have p6234_3 := h6234c.2.2.2
                                linarith only [h4, h6228, hc12, hc34, hlam, hphi, ht23, p6234_1]
                              · have p6234_0 := h6234c.1
                                have p6234_1 := h6234c.2.1
                                have p6234_2 := h6234c.2.2.1
                                have p6234_3 := h6234c.2.2.2
                                linarith only [h4, h6228, hc23, hc34, hlam, hphi, p6234_1]
                              · have p6234_0 := h6234c.1
                                have p6234_1 := h6234c.2.1
                                have p6234_2 := h6234c.2.2.1
                                have p6234_3 := h6234c.2.2.2
                                linarith only [h4, hlam, p6234_0]
                              · have p6234_0 := h6234c.1
                                have p6234_1 := h6234c.2.1
                                have p6234_2 := h6234c.2.2.1
                                have p6234_3 := h6234c.2.2.2
                                linarith only [h4, h6228, h6230, hc23, hc34, hlam, hphi, p6234_1]
                              · have p6234_0 := h6234c.1
                                have p6234_1 := h6234c.2.1
                                have p6234_2 := h6234c.2.2.1
                                have p6234_3 := h6234c.2.2.2
                                linarith only [h0, hlam, p6234_0]
                              · have p6234_0 := h6234c.1
                                have p6234_1 := h6234c.2.1
                                have p6234_2 := h6234c.2.2.1
                                have p6234_3 := h6234c.2.2.2
                                linarith only [hlam, p6234_0]
                              · have p6234_0 := h6234c.1
                                have p6234_1 := h6234c.2.1
                                have p6234_2 := h6234c.2.2.1
                                have p6234_3 := h6234c.2.2.2
                                linarith only [h0, h4, h6228, hc23, hc34, hlam, hphi, p6234_1]
                              · have p6234_0 := h6234c.1
                                have p6234_1 := h6234c.2.1
                                have p6234_2 := h6234c.2.2.1
                                have p6234_3 := h6234c.2.2.2
                                linarith only [h0, h4, hlam, p6234_1]
                              · have p6234_0 := h6234c.1
                                have p6234_1 := h6234c.2.1
                                have p6234_2 := h6234c.2.2.1
                                have p6234_3 := h6234c.2.2.2
                                linarith only [h0, h4, h6228, h6230, hc23, hc34, hlam, hphi, p6234_1]
                              · have p6234_0 := h6234c.1
                                have p6234_1 := h6234c.2.1
                                have p6234_2 := h6234c.2.2.1
                                have p6234_3 := h6234c.2.2.2
                                linarith only [h3, hlam, p6234_0]
                              · have p6234_0 := h6234c.1
                                have p6234_1 := h6234c.2.1
                                have p6234_2 := h6234c.2.2.1
                                have p6234_3 := h6234c.2.2.2
                                linarith only [h6221, hlam, p6234_0]
                              · have p6234_0 := h6234c.1
                                have p6234_1 := h6234c.2.1
                                have p6234_2 := h6234c.2.2.1
                                have p6234_3 := h6234c.2.2.2
                                linarith only [hlam, p6234_0]
                              · have p6234_0 := h6234c.1
                                have p6234_1 := h6234c.2.1
                                have p6234_2 := h6234c.2.2.1
                                have p6234_3 := h6234c.2.2.2
                                linarith only [h6228, hlam, p6234_0]
                              · have p6234_0 := h6234c.1
                                have p6234_1 := h6234c.2.1
                                have p6234_2 := h6234c.2.2.1
                                have p6234_3 := h6234c.2.2.2
                                linarith only [h6230, hlam, p6234_0]
                              · have p6234_0 := h6234c.1
                                have p6234_1 := h6234c.2.1
                                have p6234_2 := h6234c.2.2.1
                                have p6234_3 := h6234c.2.2.2
                                linarith only [h6156, h6159, h6228, hc34, hlam, hphi, ht01, ht12, ht23, p6234_1, u0ehi2]
                              · have p6234_0 := h6234c.1
                                have p6234_1 := h6234c.2.1
                                have p6234_2 := h6234c.2.2.1
                                have p6234_3 := h6234c.2.2.2
                                linarith only [h6221, h6228, hc23, hc34, hlam, hphi, p6234_1]
                              · have p6234_0 := h6234c.1
                                have p6234_1 := h6234c.2.1
                                have p6234_2 := h6234c.2.2.1
                                have p6234_3 := h6234c.2.2.2
                                rcases p6234_3 (m.d 0 2) (by simp) with h6252 | h6252
                                · linarith only [h4, h6252, hlam]
                                · linarith only [h3, h6252, hlam]
                              · have p6234_0 := h6234c.1
                                have p6234_1 := h6234c.2.1
                                have p6234_2 := h6234c.2.2.1
                                have p6234_3 := h6234c.2.2.2
                                linarith only [hlam, p6234_0]
                              · have p6234_0 := h6234c.1
                                have p6234_1 := h6234c.2.1
                                have p6234_2 := h6234c.2.2.1
                                have p6234_3 := h6234c.2.2.2
                                rcases p6234_3 (m.d 0 2) (by simp) with h6256 | h6256
                                · linarith only [h4, h6256, hlam]
                                · linarith only [h6156, h6256, hlam]
                              · have p6234_0 := h6234c.1
                                have p6234_1 := h6234c.2.1
                                have p6234_2 := h6234c.2.2.1
                                have p6234_3 := h6234c.2.2.2
                                linarith only [h6156, hlam, p6234_0]
                              · have p6234_0 := h6234c.1
                                have p6234_1 := h6234c.2.1
                                have p6234_2 := h6234c.2.2.1
                                have p6234_3 := h6234c.2.2.2
                                linarith only [h6222, hlam, p6234_0]
                              · have p6234_0 := h6234c.1
                                have p6234_1 := h6234c.2.1
                                have p6234_2 := h6234c.2.2.1
                                have p6234_3 := h6234c.2.2.2
                                linarith only [h4, h6156, h6228, hc23, hc34, hlam, hphi, p6234_1]
                              · have p6234_0 := h6234c.1
                                have p6234_1 := h6234c.2.1
                                have p6234_2 := h6234c.2.2.1
                                have p6234_3 := h6234c.2.2.2
                                linarith only [h6232, hlam, p6234_0]
                              · have p6234_0 := h6234c.1
                                have p6234_1 := h6234c.2.1
                                have p6234_2 := h6234c.2.2.1
                                have p6234_3 := h6234c.2.2.2
                                linarith only [hlam, p6234_0]
                            · linarith only [h4, h6228, h6233, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                          · linarith only [h4, h6156, h6159, h6220, h6232, hc04, hlam, hphi, u0ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6266 | h6266
                      · linarith only [h3, h6157, h6266, hc02, hlam, hphi, u0ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6268 | h6268
                        · linarith only [h4, h6156, h6159, h6220, h6221, h6223, h6227, h6266, h6268, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h6270 | h6270
                          · linarith only [h0, h4, h6222, h6223, h6227, h6266, h6270, hc13, hc34, hlam, hphi]
                          · linarith only [h0, h4, h6220, h6222, h6270, hc04, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h4, h6156, h6222, hc12, hc24, hlam, hphi]
            · linarith only [h3, h4, h6221, hc12, hc24, hlam, hphi]
          · linarith only [h4, h6156, h6220, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h6276 | h6276
      · linarith only [h3, h4, h6276, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h6278 | h6278
        · linarith only [h3, h6156, h6278, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h6280 | h6280
          · rcases m.htr 1 2 3 (by decide) (by decide) with h6281 | h6281
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6282 | h6282
              · linarith only [h6156, h6282, hc12, hlam, hphi, ht01, u0ehi1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6284 | h6284
                · linarith only [h6276, h6284, hc13, hlam, hphi, ht01, u0ehi2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6286 | h6286
                  · linarith only [h1, h6278, h6286, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6288 | h6288
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6289 | h6289
                      · linarith only [h6276, h6289, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6291 | h6291
                        · linarith only [h0, h6278, h6281, h6291, hc02, hlam, hphi, u0ehi2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h6293 | h6293
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h6294 | h6294
                            · rcases h2bigk with h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c
                              · have p6295_0 := h6295c.1
                                have p6295_1 := h6295c.2.1
                                have p6295_2 := h6295c.2.2.1
                                have p6295_3 := h6295c.2.2.2
                                linarith only [hlam, p6295_0]
                              · have p6295_0 := h6295c.1
                                have p6295_1 := h6295c.2.1
                                have p6295_2 := h6295c.2.2.1
                                have p6295_3 := h6295c.2.2.2
                                linarith only [h6156, h6289, h6293, hc12, hc34, hlam, hphi, ht23, p6295_1]
                              · have p6295_0 := h6295c.1
                                have p6295_1 := h6295c.2.1
                                have p6295_2 := h6295c.2.2.1
                                have p6295_3 := h6295c.2.2.2
                                linarith only [h6156, h6289, h6293, hc23, hc34, hlam, hphi, p6295_1]
                              · have p6295_0 := h6295c.1
                                have p6295_1 := h6295c.2.1
                                have p6295_2 := h6295c.2.2.1
                                have p6295_3 := h6295c.2.2.2
                                linarith only [h4, hlam, p6295_0]
                              · have p6295_0 := h6295c.1
                                have p6295_1 := h6295c.2.1
                                have p6295_2 := h6295c.2.2.1
                                have p6295_3 := h6295c.2.2.2
                                linarith only [h6156, hlam, p6295_0]
                              · have p6295_0 := h6295c.1
                                have p6295_1 := h6295c.2.1
                                have p6295_2 := h6295c.2.2.1
                                have p6295_3 := h6295c.2.2.2
                                linarith only [h0, hlam, p6295_0]
                              · have p6295_0 := h6295c.1
                                have p6295_1 := h6295c.2.1
                                have p6295_2 := h6295c.2.2.1
                                have p6295_3 := h6295c.2.2.2
                                linarith only [hlam, p6295_0]
                              · have p6295_0 := h6295c.1
                                have p6295_1 := h6295c.2.1
                                have p6295_2 := h6295c.2.2.1
                                have p6295_3 := h6295c.2.2.2
                                linarith only [h0, h6156, h6289, h6293, hc23, hc34, hlam, hphi, p6295_1]
                              · have p6295_0 := h6295c.1
                                have p6295_1 := h6295c.2.1
                                have p6295_2 := h6295c.2.2.1
                                have p6295_3 := h6295c.2.2.2
                                linarith only [h0, h6156, h6293, hlam, p6295_1]
                              · have p6295_0 := h6295c.1
                                have p6295_1 := h6295c.2.1
                                have p6295_2 := h6295c.2.2.1
                                have p6295_3 := h6295c.2.2.2
                                linarith only [h6282, hlam, p6295_0]
                              · have p6295_0 := h6295c.1
                                have p6295_1 := h6295c.2.1
                                have p6295_2 := h6295c.2.2.1
                                have p6295_3 := h6295c.2.2.2
                                linarith only [h3, hlam, p6295_0]
                              · have p6295_0 := h6295c.1
                                have p6295_1 := h6295c.2.1
                                have p6295_2 := h6295c.2.2.1
                                have p6295_3 := h6295c.2.2.2
                                linarith only [h6281, hlam, p6295_0]
                              · have p6295_0 := h6295c.1
                                have p6295_1 := h6295c.2.1
                                have p6295_2 := h6295c.2.2.1
                                have p6295_3 := h6295c.2.2.2
                                linarith only [hlam, p6295_0]
                              · have p6295_0 := h6295c.1
                                have p6295_1 := h6295c.2.1
                                have p6295_2 := h6295c.2.2.1
                                have p6295_3 := h6295c.2.2.2
                                linarith only [h6289, hlam, p6295_0]
                              · have p6295_0 := h6295c.1
                                have p6295_1 := h6295c.2.1
                                have p6295_2 := h6295c.2.2.1
                                have p6295_3 := h6295c.2.2.2
                                linarith only [h6291, hlam, p6295_0]
                              · have p6295_0 := h6295c.1
                                have p6295_1 := h6295c.2.1
                                have p6295_2 := h6295c.2.2.1
                                have p6295_3 := h6295c.2.2.2
                                linarith only [h6289, hc34, hlam, hphi, ht01, ht12, ht23, p6295_1, u0ehi1]
                              · have p6295_0 := h6295c.1
                                have p6295_1 := h6295c.2.1
                                have p6295_2 := h6295c.2.2.1
                                have p6295_3 := h6295c.2.2.2
                                linarith only [h6281, h6289, hc23, hc34, hlam, hphi, p6295_1]
                              · have p6295_0 := h6295c.1
                                have p6295_1 := h6295c.2.1
                                have p6295_2 := h6295c.2.2.1
                                have p6295_3 := h6295c.2.2.2
                                rcases p6295_3 (m.d 0 2) (by simp) with h6313 | h6313
                                · linarith only [h4, h6313, hlam]
                                · linarith only [h3, h6313, hlam]
                              · have p6295_0 := h6295c.1
                                have p6295_1 := h6295c.2.1
                                have p6295_2 := h6295c.2.2.1
                                have p6295_3 := h6295c.2.2.2
                                linarith only [hlam, p6295_0]
                              · have p6295_0 := h6295c.1
                                have p6295_1 := h6295c.2.1
                                have p6295_2 := h6295c.2.2.1
                                have p6295_3 := h6295c.2.2.2
                                linarith only [h3, h6156, h6289, hc34, hlam, hphi, ht01, ht12, ht23, p6295_1, u0ehi2]
                              · have p6295_0 := h6295c.1
                                have p6295_1 := h6295c.2.1
                                have p6295_2 := h6295c.2.2.1
                                have p6295_3 := h6295c.2.2.2
                                linarith only [h3, hc25, hlam, hphi, ht01, ht12, p6295_1, u0ehi2]
                              · have p6295_0 := h6295c.1
                                have p6295_1 := h6295c.2.1
                                have p6295_2 := h6295c.2.2.1
                                have p6295_3 := h6295c.2.2.2
                                linarith only [h6281, h6291, h6294, hc23, hc34, hlam, hphi, p6295_1]
                              · have p6295_0 := h6295c.1
                                have p6295_1 := h6295c.2.1
                                have p6295_2 := h6295c.2.2.1
                                have p6295_3 := h6295c.2.2.2
                                rcases p6295_3 (m.d 0 2) (by simp) with h6320 | h6320
                                · linarith only [h6156, h6320, hlam]
                                · linarith only [h3, h6320, hlam]
                              · have p6295_0 := h6295c.1
                                have p6295_1 := h6295c.2.1
                                have p6295_2 := h6295c.2.2.1
                                have p6295_3 := h6295c.2.2.2
                                linarith only [h6293, hlam, p6295_0]
                              · have p6295_0 := h6295c.1
                                have p6295_1 := h6295c.2.1
                                have p6295_2 := h6295c.2.2.1
                                have p6295_3 := h6295c.2.2.2
                                linarith only [hlam, p6295_0]
                            · linarith only [h4, h6280, h6289, h6294, hlam]
                          · linarith only [h4, h6280, h6293, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6327 | h6327
                      · linarith only [h0, h6276, h6281, h6327, hc02, hlam, hphi, u0ehi2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6329 | h6329
                        · linarith only [h6278, h6280, h6281, h6284, h6288, h6329, hc04, hlam, hphi, u0ehi2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h6331 | h6331
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h6332 | h6332
                            · rcases h2bigk with h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c
                              · have p6333_0 := h6333c.1
                                have p6333_1 := h6333c.2.1
                                have p6333_2 := h6333c.2.2.1
                                have p6333_3 := h6333c.2.2.2
                                linarith only [hlam, p6333_0]
                              · have p6333_0 := h6333c.1
                                have p6333_1 := h6333c.2.1
                                have p6333_2 := h6333c.2.2.1
                                have p6333_3 := h6333c.2.2.2
                                linarith only [h6156, h6327, h6331, hc12, hc34, hlam, hphi, ht23, p6333_1]
                              · have p6333_0 := h6333c.1
                                have p6333_1 := h6333c.2.1
                                have p6333_2 := h6333c.2.2.1
                                have p6333_3 := h6333c.2.2.2
                                linarith only [h6156, h6327, h6331, hc23, hc34, hlam, hphi, p6333_1]
                              · have p6333_0 := h6333c.1
                                have p6333_1 := h6333c.2.1
                                have p6333_2 := h6333c.2.2.1
                                have p6333_3 := h6333c.2.2.2
                                linarith only [h4, hlam, p6333_0]
                              · have p6333_0 := h6333c.1
                                have p6333_1 := h6333c.2.1
                                have p6333_2 := h6333c.2.2.1
                                have p6333_3 := h6333c.2.2.2
                                linarith only [h6156, hlam, p6333_0]
                              · have p6333_0 := h6333c.1
                                have p6333_1 := h6333c.2.1
                                have p6333_2 := h6333c.2.2.1
                                have p6333_3 := h6333c.2.2.2
                                linarith only [h0, hlam, p6333_0]
                              · have p6333_0 := h6333c.1
                                have p6333_1 := h6333c.2.1
                                have p6333_2 := h6333c.2.2.1
                                have p6333_3 := h6333c.2.2.2
                                linarith only [hlam, p6333_0]
                              · have p6333_0 := h6333c.1
                                have p6333_1 := h6333c.2.1
                                have p6333_2 := h6333c.2.2.1
                                have p6333_3 := h6333c.2.2.2
                                linarith only [h0, h6156, h6327, h6331, hc23, hc34, hlam, hphi, p6333_1]
                              · have p6333_0 := h6333c.1
                                have p6333_1 := h6333c.2.1
                                have p6333_2 := h6333c.2.2.1
                                have p6333_3 := h6333c.2.2.2
                                linarith only [h4, h6280, h6282, h6288, hlam, p6333_1]
                              · have p6333_0 := h6333c.1
                                have p6333_1 := h6333c.2.1
                                have p6333_2 := h6333c.2.2.1
                                have p6333_3 := h6333c.2.2.2
                                linarith only [h6282, hlam, p6333_0]
                              · have p6333_0 := h6333c.1
                                have p6333_1 := h6333c.2.1
                                have p6333_2 := h6333c.2.2.1
                                have p6333_3 := h6333c.2.2.2
                                linarith only [h3, hlam, p6333_0]
                              · have p6333_0 := h6333c.1
                                have p6333_1 := h6333c.2.1
                                have p6333_2 := h6333c.2.2.1
                                have p6333_3 := h6333c.2.2.2
                                linarith only [h6281, hlam, p6333_0]
                              · have p6333_0 := h6333c.1
                                have p6333_1 := h6333c.2.1
                                have p6333_2 := h6333c.2.2.1
                                have p6333_3 := h6333c.2.2.2
                                linarith only [hlam, p6333_0]
                              · have p6333_0 := h6333c.1
                                have p6333_1 := h6333c.2.1
                                have p6333_2 := h6333c.2.2.1
                                have p6333_3 := h6333c.2.2.2
                                linarith only [h6327, hlam, p6333_0]
                              · have p6333_0 := h6333c.1
                                have p6333_1 := h6333c.2.1
                                have p6333_2 := h6333c.2.2.1
                                have p6333_3 := h6333c.2.2.2
                                linarith only [h6329, hlam, p6333_0]
                              · have p6333_0 := h6333c.1
                                have p6333_1 := h6333c.2.1
                                have p6333_2 := h6333c.2.2.1
                                have p6333_3 := h6333c.2.2.2
                                linarith only [h6327, hc34, hlam, hphi, ht01, ht12, ht23, p6333_1, u0ehi1]
                              · have p6333_0 := h6333c.1
                                have p6333_1 := h6333c.2.1
                                have p6333_2 := h6333c.2.2.1
                                have p6333_3 := h6333c.2.2.2
                                linarith only [h6281, h6327, hc23, hc34, hlam, hphi, p6333_1]
                              · have p6333_0 := h6333c.1
                                have p6333_1 := h6333c.2.1
                                have p6333_2 := h6333c.2.2.1
                                have p6333_3 := h6333c.2.2.2
                                rcases p6333_3 (m.d 0 2) (by simp) with h6351 | h6351
                                · linarith only [h4, h6351, hlam]
                                · linarith only [h3, h6351, hlam]
                              · have p6333_0 := h6333c.1
                                have p6333_1 := h6333c.2.1
                                have p6333_2 := h6333c.2.2.1
                                have p6333_3 := h6333c.2.2.2
                                linarith only [hlam, p6333_0]
                              · have p6333_0 := h6333c.1
                                have p6333_1 := h6333c.2.1
                                have p6333_2 := h6333c.2.2.1
                                have p6333_3 := h6333c.2.2.2
                                linarith only [h3, h6156, h6327, hc34, hlam, hphi, ht01, ht12, ht23, p6333_1, u0ehi2]
                              · have p6333_0 := h6333c.1
                                have p6333_1 := h6333c.2.1
                                have p6333_2 := h6333c.2.2.1
                                have p6333_3 := h6333c.2.2.2
                                linarith only [h3, hc25, hlam, hphi, ht01, ht12, p6333_1, u0ehi2]
                              · have p6333_0 := h6333c.1
                                have p6333_1 := h6333c.2.1
                                have p6333_2 := h6333c.2.2.1
                                have p6333_3 := h6333c.2.2.2
                                linarith only [h6281, h6329, h6332, hc23, hc34, hlam, hphi, p6333_1]
                              · have p6333_0 := h6333c.1
                                have p6333_1 := h6333c.2.1
                                have p6333_2 := h6333c.2.2.1
                                have p6333_3 := h6333c.2.2.2
                                rcases p6333_3 (m.d 0 2) (by simp) with h6358 | h6358
                                · linarith only [h6156, h6358, hlam]
                                · linarith only [h3, h6358, hlam]
                              · have p6333_0 := h6333c.1
                                have p6333_1 := h6333c.2.1
                                have p6333_2 := h6333c.2.2.1
                                have p6333_3 := h6333c.2.2.2
                                linarith only [h6331, hlam, p6333_0]
                              · have p6333_0 := h6333c.1
                                have p6333_1 := h6333c.2.1
                                have p6333_2 := h6333c.2.2.1
                                have p6333_3 := h6333c.2.2.2
                                linarith only [hlam, p6333_0]
                            · linarith only [h4, h6280, h6327, h6332, hlam]
                          · linarith only [h4, h6280, h6331, hlam]
            · linarith only [h3, h4, h6281, hc12, hc24, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h6366 | h6366
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6367 | h6367
              · linarith only [h6156, h6367, hc12, hlam, hphi, ht01, u0ehi1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6369 | h6369
                · linarith only [h6276, h6369, hc13, hlam, hphi, ht01, u0ehi2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6371 | h6371
                  · linarith only [h1, h6278, h6371, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6373 | h6373
                    · linarith only [h3, h4, h6280, h6373, hc14, hlam, hphi, ht01, u0ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6375 | h6375
                      · linarith only [h6276, h6375, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6377 | h6377
                        · linarith only [h0, h6278, h6366, h6377, hc02, hlam, hphi, u0ehi2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h6379 | h6379
                          · linarith only [h0, h4, h6280, h6366, h6375, h6379, hc23, hc34, hlam, hphi]
                          · linarith only [h3, h4, h6379, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
            · linarith only [h3, h4, h6366, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 15178000 in
set_option maxHeartbeats 15178000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s2_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h5bigk := hb5.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s3 m hb0 hb2 hb3 hb5 h0 h1 h2 h3

end R2N4
