import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_3S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 16094000 in
set_option maxHeartbeats 16094000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s6_x1_x1_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h5823 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h6193 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h6194 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h6195 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 2 5 (by decide) (by decide) with h6856 | h6856
  · rcases m.htr 1 3 4 (by decide) (by decide) with h6857 | h6857
    · linarith only [h1, h6857, h7, hlam]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h6859 | h6859
      · linarith only [h1, h5823, h6859, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h6861 | h6861
        · rcases m.htr 2 3 4 (by decide) (by decide) with h6862 | h6862
          · linarith only [h5, h6194, h6195, h6862, h7, hlam]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h6864 | h6864
            · linarith only [h5, h5823, h6194, h6195, h6864, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h6866 | h6866
              · rcases m.htr 3 4 5 (by decide) (by decide) with h6867 | h6867
                · rcases h1bigk with h6868c | h6868c | h6868c | h6868c | h6868c | h6868c | h6868c | h6868c | h6868c | h6868c | h6868c | h6868c | h6868c | h6868c | h6868c | h6868c | h6868c | h6868c | h6868c | h6868c | h6868c | h6868c | h6868c | h6868c | h6868c
                  · have p6868_0 := h6868c.1
                    have p6868_1 := h6868c.2.1
                    have p6868_2 := h6868c.2.2.1
                    have p6868_3 := h6868c.2.2.2
                    linarith only [hlam, p6868_0]
                  · have p6868_0 := h6868c.1
                    have p6868_1 := h6868c.2.1
                    have p6868_2 := h6868c.2.2.1
                    have p6868_3 := h6868c.2.2.2
                    rcases p6868_3 (m.d 0 1) (by simp) with h6870 | h6870
                    · rcases p6868_3 (m.d 1 2) (by simp) with h6871 | h6871
                      · linarith only [h6871, hlam, p6868_0]
                      · rcases p6868_3 (m.d 1 3) (by simp) with h6873 | h6873
                        · linarith only [h1, h6873, hlam]
                        · rcases p6868_3 (m.d 1 4) (by simp) with h6875 | h6875
                          · linarith only [h2, h6875, hlam]
                          · linarith only [h6195, h6875, hlam]
                    · linarith only [h6870, hlam, p6868_0]
                  · have p6868_0 := h6868c.1
                    have p6868_1 := h6868c.2.1
                    have p6868_2 := h6868c.2.2.1
                    have p6868_3 := h6868c.2.2.2
                    rcases p6868_3 (m.d 0 1) (by simp) with h6879 | h6879
                    · rcases p6868_3 (m.d 1 2) (by simp) with h6880 | h6880
                      · linarith only [h0, h6880, hlam]
                      · linarith only [h6194, h6880, hlam]
                    · linarith only [h6879, hlam, p6868_0]
                  · have p6868_0 := h6868c.1
                    have p6868_1 := h6868c.2.1
                    have p6868_2 := h6868c.2.2.1
                    have p6868_3 := h6868c.2.2.2
                    rcases p6868_3 (m.d 0 1) (by simp) with h6884 | h6884
                    · rcases p6868_3 (m.d 1 2) (by simp) with h6885 | h6885
                      · linarith only [h0, h6885, hlam]
                      · rcases p6868_3 (m.d 1 3) (by simp) with h6887 | h6887
                        · linarith only [h1, h6887, hlam]
                        · rcases p6868_3 (m.d 1 4) (by simp) with h6889 | h6889
                          · linarith only [h6889, hlam, p6868_0]
                          · rcases p6868_3 (m.d 1 5) (by simp) with h6891 | h6891
                            · linarith only [h3, h6891, hlam]
                            · rcases h3bigk with h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [hlam, p6893_0]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [h5823, hc13, hc35, hlam, hphi, p6893_1]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [h5823, hc23, hc35, hlam, hphi, p6893_1]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [h7, hlam, p6893_0]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [h5823, hlam, p6893_0]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [h1, hlam, p6893_0]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [hlam, p6893_0]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [h1, h5823, hc23, hc35, hlam, hphi, p6893_1]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [h6857, hlam, p6893_0]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [h6859, hlam, p6893_0]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [h4, hlam, p6893_0]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [h6194, hlam, p6893_0]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [hlam, p6893_0]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [h6862, hlam, p6893_0]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [h6864, hlam, p6893_0]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                rcases p6893_3 (m.d 0 3) (by simp) with h6909 | h6909
                                · linarith only [h6909, hlam, p6893_0]
                                · rcases p6893_3 (m.d 1 3) (by simp) with h6911 | h6911
                                  · linarith only [h6857, h6911, hlam]
                                  · rcases p6893_3 (m.d 2 3) (by simp) with h6913 | h6913
                                    · linarith only [h6862, h6913, hlam]
                                    · rcases p6893_3 (m.d 3 4) (by simp) with h6915 | h6915
                                      · rcases p6893_3 (m.d 3 5) (by simp) with h6916 | h6916
                                        · linarith only [h6867, h6916, hlam]
                                        · linarith only [h5823, h6916, hlam]
                                      · linarith only [h6915, hlam, p6893_0]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                rcases p6893_3 (m.d 0 3) (by simp) with h6920 | h6920
                                · linarith only [h6920, h7, hlam]
                                · linarith only [h1, h6920, hlam]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                rcases p6893_3 (m.d 0 3) (by simp) with h6923 | h6923
                                · linarith only [h6923, h7, hlam]
                                · linarith only [h4, h6923, hlam]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [hlam, p6893_0]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [h5823, hc03, hc34, hlam, hphi, p6893_1]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                rcases p6893_3 (m.d 0 3) (by simp) with h6928 | h6928
                                · linarith only [h6928, hlam, p6893_0]
                                · rcases p6893_3 (m.d 1 3) (by simp) with h6930 | h6930
                                  · linarith only [h6859, h6930, hlam]
                                  · rcases p6893_3 (m.d 2 3) (by simp) with h6932 | h6932
                                    · linarith only [h6864, h6932, hlam]
                                    · rcases p6893_3 (m.d 3 4) (by simp) with h6934 | h6934
                                      · rcases p6893_3 (m.d 3 5) (by simp) with h6935 | h6935
                                        · rcases h5bigk with h6936c | h6936c | h6936c | h6936c | h6936c | h6936c | h6936c | h6936c | h6936c | h6936c | h6936c | h6936c | h6936c | h6936c | h6936c | h6936c | h6936c | h6936c | h6936c | h6936c | h6936c | h6936c | h6936c | h6936c | h6936c
                                          · have p6936_0 := h6936c.1
                                            have p6936_1 := h6936c.2.1
                                            have p6936_2 := h6936c.2.2.1
                                            have p6936_3 := h6936c.2.2.2
                                            linarith only [hlam, p6936_0]
                                          · have p6936_0 := h6936c.1
                                            have p6936_1 := h6936c.2.1
                                            have p6936_2 := h6936c.2.2.1
                                            have p6936_3 := h6936c.2.2.2
                                            linarith only [h5823, h6194, h6859, hc23, hc35, hlam, hphi, p6936_1]
                                          · have p6936_0 := h6936c.1
                                            have p6936_1 := h6936c.2.1
                                            have p6936_2 := h6936c.2.2.1
                                            have p6936_3 := h6936c.2.2.2
                                            linarith only [h5823, h6864, hc23, hc35, hlam, hphi, p6936_1]
                                          · have p6936_0 := h6936c.1
                                            have p6936_1 := h6936c.2.1
                                            have p6936_2 := h6936c.2.2.1
                                            have p6936_3 := h6936c.2.2.2
                                            linarith only [h5823, hlam, p6936_1]
                                          · have p6936_0 := h6936c.1
                                            have p6936_1 := h6936c.2.1
                                            have p6936_2 := h6936c.2.2.1
                                            have p6936_3 := h6936c.2.2.2
                                            rcases p6936_3 (m.d 0 5) (by simp) with h6941 | h6941
                                            · rcases p6936_3 (m.d 1 5) (by simp) with h6942 | h6942
                                              · linarith only [h3, h6942, hlam]
                                              · linarith only [h6861, h6942, hlam]
                                            · linarith only [h6193, h6941, hlam]
                                          · have p6936_0 := h6936c.1
                                            have p6936_1 := h6936c.2.1
                                            have p6936_2 := h6936c.2.2.1
                                            have p6936_3 := h6936c.2.2.2
                                            linarith only [h3, hlam, p6936_0]
                                          · have p6936_0 := h6936c.1
                                            have p6936_1 := h6936c.2.1
                                            have p6936_2 := h6936c.2.2.1
                                            have p6936_3 := h6936c.2.2.2
                                            linarith only [hlam, p6936_0]
                                          · have p6936_0 := h6936c.1
                                            have p6936_1 := h6936c.2.1
                                            have p6936_2 := h6936c.2.2.1
                                            have p6936_3 := h6936c.2.2.2
                                            linarith only [h3, h6864, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6936_1]
                                          · have p6936_0 := h6936c.1
                                            have p6936_1 := h6936c.2.1
                                            have p6936_2 := h6936c.2.2.1
                                            have p6936_3 := h6936c.2.2.2
                                            linarith only [h6859, hlam, p6936_1]
                                          · have p6936_0 := h6936c.1
                                            have p6936_1 := h6936c.2.1
                                            have p6936_2 := h6936c.2.2.1
                                            have p6936_3 := h6936c.2.2.2
                                            linarith only [h5, h6195, h6856, hc02, hc45, hlam, hphi, ht0b, ht5b, p6936_1]
                                          · have p6936_0 := h6936c.1
                                            have p6936_1 := h6936c.2.1
                                            have p6936_2 := h6936c.2.2.1
                                            have p6936_3 := h6936c.2.2.2
                                            linarith only [h6, hlam, p6936_1]
                                          · have p6936_0 := h6936c.1
                                            have p6936_1 := h6936c.2.1
                                            have p6936_2 := h6936c.2.2.1
                                            have p6936_3 := h6936c.2.2.2
                                            linarith only [h6856, hlam, p6936_1]
                                          · have p6936_0 := h6936c.1
                                            have p6936_1 := h6936c.2.1
                                            have p6936_2 := h6936c.2.2.1
                                            have p6936_3 := h6936c.2.2.2
                                            linarith only [hlam, p6936_0]
                                          · have p6936_0 := h6936c.1
                                            have p6936_1 := h6936c.2.1
                                            have p6936_2 := h6936c.2.2.1
                                            have p6936_3 := h6936c.2.2.2
                                            linarith only [h6864, hlam, p6936_1]
                                          · have p6936_0 := h6936c.1
                                            have p6936_1 := h6936c.2.1
                                            have p6936_2 := h6936c.2.2.1
                                            have p6936_3 := h6936c.2.2.2
                                            linarith only [h0, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p6936_1]
                                          · have p6936_0 := h6936c.1
                                            have p6936_1 := h6936c.2.1
                                            have p6936_2 := h6936c.2.2.1
                                            have p6936_3 := h6936c.2.2.2
                                            linarith only [h1, h5823, h6194, h6867, hc23, hc34, hlam, hphi, p6936_1]
                                          · have p6936_0 := h6936c.1
                                            have p6936_1 := h6936c.2.1
                                            have p6936_2 := h6936c.2.2.1
                                            have p6936_3 := h6936c.2.2.2
                                            linarith only [h6194, h6859, h6867, hc23, hc34, hlam, hphi, p6936_1]
                                          · have p6936_0 := h6936c.1
                                            have p6936_1 := h6936c.2.1
                                            have p6936_2 := h6936c.2.2.1
                                            have p6936_3 := h6936c.2.2.2
                                            linarith only [h6864, h6867, hc23, hc34, hlam, hphi, p6936_1]
                                          · have p6936_0 := h6936c.1
                                            have p6936_1 := h6936c.2.1
                                            have p6936_2 := h6936c.2.2.1
                                            have p6936_3 := h6936c.2.2.2
                                            linarith only [hlam, p6936_0]
                                          · have p6936_0 := h6936c.1
                                            have p6936_1 := h6936c.2.1
                                            have p6936_2 := h6936c.2.2.1
                                            have p6936_3 := h6936c.2.2.2
                                            rcases p6936_3 (m.d 0 5) (by simp) with h6960 | h6960
                                            · linarith only [h5823, h6960, hlam]
                                            · linarith only [h6193, h6960, hlam]
                                          · have p6936_0 := h6936c.1
                                            have p6936_1 := h6936c.2.1
                                            have p6936_2 := h6936c.2.2.1
                                            have p6936_3 := h6936c.2.2.2
                                            linarith only [h6193, hlam, p6936_0]
                                          · have p6936_0 := h6936c.1
                                            have p6936_1 := h6936c.2.1
                                            have p6936_2 := h6936c.2.2.1
                                            have p6936_3 := h6936c.2.2.2
                                            linarith only [h6861, hlam, p6936_0]
                                          · have p6936_0 := h6936c.1
                                            have p6936_1 := h6936c.2.1
                                            have p6936_2 := h6936c.2.2.1
                                            have p6936_3 := h6936c.2.2.2
                                            linarith only [h6866, hlam, p6936_0]
                                          · have p6936_0 := h6936c.1
                                            have p6936_1 := h6936c.2.1
                                            have p6936_2 := h6936c.2.2.1
                                            have p6936_3 := h6936c.2.2.2
                                            linarith only [h6867, hlam, p6936_0]
                                          · have p6936_0 := h6936c.1
                                            have p6936_1 := h6936c.2.1
                                            have p6936_2 := h6936c.2.2.1
                                            have p6936_3 := h6936c.2.2.2
                                            linarith only [hlam, p6936_0]
                                        · linarith only [h6935, hlam, p6893_0]
                                      · linarith only [h6934, h7, hlam]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                rcases p6893_3 (m.d 0 3) (by simp) with h6970 | h6970
                                · linarith only [h5823, h6970, hlam]
                                · linarith only [h1, h6970, hlam]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                rcases p6893_3 (m.d 0 3) (by simp) with h6973 | h6973
                                · linarith only [h5823, h6973, hlam]
                                · linarith only [h4, h6973, hlam]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [h6867, hlam, p6893_0]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [hlam, p6893_0]
                    · linarith only [h6884, hlam, p6868_0]
                  · have p6868_0 := h6868c.1
                    have p6868_1 := h6868c.2.1
                    have p6868_2 := h6868c.2.2.1
                    have p6868_3 := h6868c.2.2.2
                    rcases p6868_3 (m.d 0 1) (by simp) with h6979 | h6979
                    · rcases p6868_3 (m.d 1 2) (by simp) with h6980 | h6980
                      · linarith only [h0, h6980, hlam]
                      · linarith only [h6856, h6980, hlam]
                    · linarith only [h6979, hlam, p6868_0]
                  · have p6868_0 := h6868c.1
                    have p6868_1 := h6868c.2.1
                    have p6868_2 := h6868c.2.2.1
                    have p6868_3 := h6868c.2.2.2
                    linarith only [h0, hlam, p6868_0]
                  · have p6868_0 := h6868c.1
                    have p6868_1 := h6868c.2.1
                    have p6868_2 := h6868c.2.2.1
                    have p6868_3 := h6868c.2.2.2
                    linarith only [hlam, p6868_0]
                  · have p6868_0 := h6868c.1
                    have p6868_1 := h6868c.2.1
                    have p6868_2 := h6868c.2.2.1
                    have p6868_3 := h6868c.2.2.2
                    linarith only [h0, h5, h6194, h6195, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6868_1]
                  · have p6868_0 := h6868c.1
                    have p6868_1 := h6868c.2.1
                    have p6868_2 := h6868c.2.2.1
                    have p6868_3 := h6868c.2.2.2
                    linarith only [h6195, hlam, p6868_0]
                  · have p6868_0 := h6868c.1
                    have p6868_1 := h6868c.2.1
                    have p6868_2 := h6868c.2.2.1
                    have p6868_3 := h6868c.2.2.2
                    linarith only [h0, h5, h6195, hc01, hc15, hlam, hphi, ht0b, ht5b, p6868_1]
                  · have p6868_0 := h6868c.1
                    have p6868_1 := h6868c.2.1
                    have p6868_2 := h6868c.2.2.1
                    have p6868_3 := h6868c.2.2.2
                    linarith only [h1, hlam, p6868_0]
                  · have p6868_0 := h6868c.1
                    have p6868_1 := h6868c.2.1
                    have p6868_2 := h6868c.2.2.1
                    have p6868_3 := h6868c.2.2.2
                    linarith only [h6194, hlam, p6868_1]
                  · have p6868_0 := h6868c.1
                    have p6868_1 := h6868c.2.1
                    have p6868_2 := h6868c.2.2.1
                    have p6868_3 := h6868c.2.2.2
                    linarith only [hlam, p6868_0]
                  · have p6868_0 := h6868c.1
                    have p6868_1 := h6868c.2.1
                    have p6868_2 := h6868c.2.2.1
                    have p6868_3 := h6868c.2.2.2
                    linarith only [h6857, hlam, p6868_1]
                  · have p6868_0 := h6868c.1
                    have p6868_1 := h6868c.2.1
                    have p6868_2 := h6868c.2.2.1
                    have p6868_3 := h6868c.2.2.2
                    linarith only [h6859, hlam, p6868_1]
                  · have p6868_0 := h6868c.1
                    have p6868_1 := h6868c.2.1
                    have p6868_2 := h6868c.2.2.1
                    have p6868_3 := h6868c.2.2.2
                    linarith only [h2, hlam, p6868_0]
                  · have p6868_0 := h6868c.1
                    have p6868_1 := h6868c.2.1
                    have p6868_2 := h6868c.2.2.1
                    have p6868_3 := h6868c.2.2.2
                    linarith only [h2, h6194, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6868_1]
                  · have p6868_0 := h6868c.1
                    have p6868_1 := h6868c.2.1
                    have p6868_2 := h6868c.2.2.1
                    have p6868_3 := h6868c.2.2.2
                    rcases p6868_3 (m.d 0 1) (by simp) with h6996 | h6996
                    · rcases p6868_3 (m.d 1 2) (by simp) with h6997 | h6997
                      · linarith only [h6195, h6997, hlam]
                      · linarith only [h6194, h6997, hlam]
                    · linarith only [h1, h6996, hlam]
                  · have p6868_0 := h6868c.1
                    have p6868_1 := h6868c.2.1
                    have p6868_2 := h6868c.2.2.1
                    have p6868_3 := h6868c.2.2.2
                    linarith only [hlam, p6868_0]
                  · have p6868_0 := h6868c.1
                    have p6868_1 := h6868c.2.1
                    have p6868_2 := h6868c.2.2.1
                    have p6868_3 := h6868c.2.2.2
                    rcases p6868_3 (m.d 0 1) (by simp) with h7002 | h7002
                    · rcases p6868_3 (m.d 1 2) (by simp) with h7003 | h7003
                      · linarith only [h6195, h7003, hlam]
                      · linarith only [h6856, h7003, hlam]
                    · linarith only [h3, h7002, hlam]
                  · have p6868_0 := h6868c.1
                    have p6868_1 := h6868c.2.1
                    have p6868_2 := h6868c.2.2.1
                    have p6868_3 := h6868c.2.2.2
                    linarith only [h3, hlam, p6868_0]
                  · have p6868_0 := h6868c.1
                    have p6868_1 := h6868c.2.1
                    have p6868_2 := h6868c.2.2.1
                    have p6868_3 := h6868c.2.2.2
                    linarith only [h6856, hlam, p6868_1]
                  · have p6868_0 := h6868c.1
                    have p6868_1 := h6868c.2.1
                    have p6868_2 := h6868c.2.2.1
                    have p6868_3 := h6868c.2.2.2
                    linarith only [h0, h5, h6194, h6195, h6856, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6868_1]
                  · have p6868_0 := h6868c.1
                    have p6868_1 := h6868c.2.1
                    have p6868_2 := h6868c.2.2.1
                    have p6868_3 := h6868c.2.2.2
                    linarith only [h6861, hlam, p6868_0]
                  · have p6868_0 := h6868c.1
                    have p6868_1 := h6868c.2.1
                    have p6868_2 := h6868c.2.2.1
                    have p6868_3 := h6868c.2.2.2
                    linarith only [hlam, p6868_0]
                · linarith only [h6193, h6867, h7, hlam]
              · linarith only [h6195, h6856, h6861, h6866, hlam]
        · linarith only [h6193, h6194, h6195, h6861, h7, hc23, hc34, hlam, hphi]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h7015 | h7015
    · linarith only [h1, h5, h6194, h6195, h7, h7015, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h7017 | h7017
      · linarith only [h1, h5823, h7017, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h7019 | h7019
        · rcases m.htr 2 3 4 (by decide) (by decide) with h7020 | h7020
          · linarith only [h1, h6194, h7, h7020, hlam]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h7022 | h7022
            · linarith only [h5823, h6, h6193, h6194, h6856, h7022, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h7024 | h7024
              · rcases m.htr 3 4 5 (by decide) (by decide) with h7025 | h7025
                · rcases h1bigk with h7026c | h7026c | h7026c | h7026c | h7026c | h7026c | h7026c | h7026c | h7026c | h7026c | h7026c | h7026c | h7026c | h7026c | h7026c | h7026c | h7026c | h7026c | h7026c | h7026c | h7026c | h7026c | h7026c | h7026c | h7026c
                  · have p7026_0 := h7026c.1
                    have p7026_1 := h7026c.2.1
                    have p7026_2 := h7026c.2.2.1
                    have p7026_3 := h7026c.2.2.2
                    linarith only [hlam, p7026_0]
                  · have p7026_0 := h7026c.1
                    have p7026_1 := h7026c.2.1
                    have p7026_2 := h7026c.2.2.1
                    have p7026_3 := h7026c.2.2.2
                    rcases p7026_3 (m.d 0 1) (by simp) with h7028 | h7028
                    · rcases p7026_3 (m.d 1 2) (by simp) with h7029 | h7029
                      · linarith only [h7029, hlam, p7026_0]
                      · rcases p7026_3 (m.d 1 3) (by simp) with h7031 | h7031
                        · linarith only [h1, h7031, hlam]
                        · rcases p7026_3 (m.d 1 4) (by simp) with h7033 | h7033
                          · linarith only [h2, h7033, hlam]
                          · linarith only [h6195, h7033, hlam]
                    · linarith only [h7028, hlam, p7026_0]
                  · have p7026_0 := h7026c.1
                    have p7026_1 := h7026c.2.1
                    have p7026_2 := h7026c.2.2.1
                    have p7026_3 := h7026c.2.2.2
                    rcases p7026_3 (m.d 0 1) (by simp) with h7037 | h7037
                    · rcases p7026_3 (m.d 1 2) (by simp) with h7038 | h7038
                      · linarith only [h0, h7038, hlam]
                      · linarith only [h6194, h7038, hlam]
                    · linarith only [h7037, hlam, p7026_0]
                  · have p7026_0 := h7026c.1
                    have p7026_1 := h7026c.2.1
                    have p7026_2 := h7026c.2.2.1
                    have p7026_3 := h7026c.2.2.2
                    rcases p7026_3 (m.d 0 1) (by simp) with h7042 | h7042
                    · rcases p7026_3 (m.d 1 2) (by simp) with h7043 | h7043
                      · linarith only [h0, h7043, hlam]
                      · rcases p7026_3 (m.d 1 3) (by simp) with h7045 | h7045
                        · linarith only [h1, h7045, hlam]
                        · rcases p7026_3 (m.d 1 4) (by simp) with h7047 | h7047
                          · linarith only [h7047, hlam, p7026_0]
                          · rcases p7026_3 (m.d 1 5) (by simp) with h7049 | h7049
                            · linarith only [h3, h7049, hlam]
                            · rcases h3bigk with h7051c | h7051c | h7051c | h7051c | h7051c | h7051c | h7051c | h7051c | h7051c | h7051c | h7051c | h7051c | h7051c | h7051c | h7051c | h7051c | h7051c | h7051c | h7051c | h7051c | h7051c | h7051c | h7051c | h7051c | h7051c
                              · have p7051_0 := h7051c.1
                                have p7051_1 := h7051c.2.1
                                have p7051_2 := h7051c.2.2.1
                                have p7051_3 := h7051c.2.2.2
                                linarith only [hlam, p7051_0]
                              · have p7051_0 := h7051c.1
                                have p7051_1 := h7051c.2.1
                                have p7051_2 := h7051c.2.2.1
                                have p7051_3 := h7051c.2.2.2
                                linarith only [h7, hc13, hc34, hlam, hphi, p7051_1]
                              · have p7051_0 := h7051c.1
                                have p7051_1 := h7051c.2.1
                                have p7051_2 := h7051c.2.2.1
                                have p7051_3 := h7051c.2.2.2
                                linarith only [h7, hc23, hc34, hlam, hphi, p7051_1]
                              · have p7051_0 := h7051c.1
                                have p7051_1 := h7051c.2.1
                                have p7051_2 := h7051c.2.2.1
                                have p7051_3 := h7051c.2.2.2
                                linarith only [h7, hlam, p7051_0]
                              · have p7051_0 := h7051c.1
                                have p7051_1 := h7051c.2.1
                                have p7051_2 := h7051c.2.2.1
                                have p7051_3 := h7051c.2.2.2
                                linarith only [h5823, hlam, p7051_0]
                              · have p7051_0 := h7051c.1
                                have p7051_1 := h7051c.2.1
                                have p7051_2 := h7051c.2.2.1
                                have p7051_3 := h7051c.2.2.2
                                linarith only [h1, hlam, p7051_0]
                              · have p7051_0 := h7051c.1
                                have p7051_1 := h7051c.2.1
                                have p7051_2 := h7051c.2.2.1
                                have p7051_3 := h7051c.2.2.2
                                linarith only [hlam, p7051_0]
                              · have p7051_0 := h7051c.1
                                have p7051_1 := h7051c.2.1
                                have p7051_2 := h7051c.2.2.1
                                have p7051_3 := h7051c.2.2.2
                                linarith only [h1, h5823, hc23, hc35, hlam, hphi, p7051_1]
                              · have p7051_0 := h7051c.1
                                have p7051_1 := h7051c.2.1
                                have p7051_2 := h7051c.2.2.1
                                have p7051_3 := h7051c.2.2.2
                                linarith only [h7015, hlam, p7051_0]
                              · have p7051_0 := h7051c.1
                                have p7051_1 := h7051c.2.1
                                have p7051_2 := h7051c.2.2.1
                                have p7051_3 := h7051c.2.2.2
                                linarith only [h7017, hlam, p7051_0]
                              · have p7051_0 := h7051c.1
                                have p7051_1 := h7051c.2.1
                                have p7051_2 := h7051c.2.2.1
                                have p7051_3 := h7051c.2.2.2
                                linarith only [h4, hlam, p7051_0]
                              · have p7051_0 := h7051c.1
                                have p7051_1 := h7051c.2.1
                                have p7051_2 := h7051c.2.2.1
                                have p7051_3 := h7051c.2.2.2
                                linarith only [h6194, hlam, p7051_0]
                              · have p7051_0 := h7051c.1
                                have p7051_1 := h7051c.2.1
                                have p7051_2 := h7051c.2.2.1
                                have p7051_3 := h7051c.2.2.2
                                linarith only [hlam, p7051_0]
                              · have p7051_0 := h7051c.1
                                have p7051_1 := h7051c.2.1
                                have p7051_2 := h7051c.2.2.1
                                have p7051_3 := h7051c.2.2.2
                                linarith only [h7020, hlam, p7051_0]
                              · have p7051_0 := h7051c.1
                                have p7051_1 := h7051c.2.1
                                have p7051_2 := h7051c.2.2.1
                                have p7051_3 := h7051c.2.2.2
                                linarith only [h7022, hlam, p7051_0]
                              · have p7051_0 := h7051c.1
                                have p7051_1 := h7051c.2.1
                                have p7051_2 := h7051c.2.2.1
                                have p7051_3 := h7051c.2.2.2
                                rcases p7051_3 (m.d 0 3) (by simp) with h7067 | h7067
                                · linarith only [h7067, hlam, p7051_0]
                                · rcases p7051_3 (m.d 1 3) (by simp) with h7069 | h7069
                                  · linarith only [h7015, h7069, hlam]
                                  · rcases p7051_3 (m.d 2 3) (by simp) with h7071 | h7071
                                    · linarith only [h7020, h7071, hlam]
                                    · rcases p7051_3 (m.d 3 4) (by simp) with h7073 | h7073
                                      · rcases p7051_3 (m.d 3 5) (by simp) with h7074 | h7074
                                        · linarith only [h7025, h7074, hlam]
                                        · linarith only [h5823, h7074, hlam]
                                      · linarith only [h7073, hlam, p7051_0]
                              · have p7051_0 := h7051c.1
                                have p7051_1 := h7051c.2.1
                                have p7051_2 := h7051c.2.2.1
                                have p7051_3 := h7051c.2.2.2
                                rcases p7051_3 (m.d 0 3) (by simp) with h7078 | h7078
                                · linarith only [h7, h7078, hlam]
                                · linarith only [h1, h7078, hlam]
                              · have p7051_0 := h7051c.1
                                have p7051_1 := h7051c.2.1
                                have p7051_2 := h7051c.2.2.1
                                have p7051_3 := h7051c.2.2.2
                                rcases p7051_3 (m.d 0 3) (by simp) with h7081 | h7081
                                · linarith only [h7, h7081, hlam]
                                · linarith only [h4, h7081, hlam]
                              · have p7051_0 := h7051c.1
                                have p7051_1 := h7051c.2.1
                                have p7051_2 := h7051c.2.2.1
                                have p7051_3 := h7051c.2.2.2
                                linarith only [hlam, p7051_0]
                              · have p7051_0 := h7051c.1
                                have p7051_1 := h7051c.2.1
                                have p7051_2 := h7051c.2.2.1
                                have p7051_3 := h7051c.2.2.2
                                linarith only [h5823, hc03, hc34, hlam, hphi, p7051_1]
                              · have p7051_0 := h7051c.1
                                have p7051_1 := h7051c.2.1
                                have p7051_2 := h7051c.2.2.1
                                have p7051_3 := h7051c.2.2.2
                                rcases p7051_3 (m.d 0 3) (by simp) with h7086 | h7086
                                · linarith only [h7086, hlam, p7051_0]
                                · rcases p7051_3 (m.d 1 3) (by simp) with h7088 | h7088
                                  · linarith only [h7017, h7088, hlam]
                                  · rcases p7051_3 (m.d 2 3) (by simp) with h7090 | h7090
                                    · linarith only [h7022, h7090, hlam]
                                    · rcases p7051_3 (m.d 3 4) (by simp) with h7092 | h7092
                                      · rcases p7051_3 (m.d 3 5) (by simp) with h7093 | h7093
                                        · rcases h5bigk with h7094c | h7094c | h7094c | h7094c | h7094c | h7094c | h7094c | h7094c | h7094c | h7094c | h7094c | h7094c | h7094c | h7094c | h7094c | h7094c | h7094c | h7094c | h7094c | h7094c | h7094c | h7094c | h7094c | h7094c | h7094c
                                          · have p7094_0 := h7094c.1
                                            have p7094_1 := h7094c.2.1
                                            have p7094_2 := h7094c.2.2.1
                                            have p7094_3 := h7094c.2.2.2
                                            linarith only [hlam, p7094_0]
                                          · have p7094_0 := h7094c.1
                                            have p7094_1 := h7094c.2.1
                                            have p7094_2 := h7094c.2.2.1
                                            have p7094_3 := h7094c.2.2.2
                                            linarith only [h6193, h6194, h6856, h7, hc23, hc34, hlam, hphi, p7094_1]
                                          · have p7094_0 := h7094c.1
                                            have p7094_1 := h7094c.2.1
                                            have p7094_2 := h7094c.2.2.1
                                            have p7094_3 := h7094c.2.2.2
                                            linarith only [h6193, h6194, h6856, h7, hc23, hc34, hlam, hphi, p7094_1]
                                          · have p7094_0 := h7094c.1
                                            have p7094_1 := h7094c.2.1
                                            have p7094_2 := h7094c.2.2.1
                                            have p7094_3 := h7094c.2.2.2
                                            linarith only [h5823, hlam, p7094_1]
                                          · have p7094_0 := h7094c.1
                                            have p7094_1 := h7094c.2.1
                                            have p7094_2 := h7094c.2.2.1
                                            have p7094_3 := h7094c.2.2.2
                                            rcases p7094_3 (m.d 0 5) (by simp) with h7099 | h7099
                                            · rcases p7094_3 (m.d 1 5) (by simp) with h7100 | h7100
                                              · linarith only [h3, h7100, hlam]
                                              · linarith only [h7019, h7100, hlam]
                                            · linarith only [h6193, h7099, hlam]
                                          · have p7094_0 := h7094c.1
                                            have p7094_1 := h7094c.2.1
                                            have p7094_2 := h7094c.2.2.1
                                            have p7094_3 := h7094c.2.2.2
                                            linarith only [h3, hlam, p7094_0]
                                          · have p7094_0 := h7094c.1
                                            have p7094_1 := h7094c.2.1
                                            have p7094_2 := h7094c.2.2.1
                                            have p7094_3 := h7094c.2.2.2
                                            linarith only [hlam, p7094_0]
                                          · have p7094_0 := h7094c.1
                                            have p7094_1 := h7094c.2.1
                                            have p7094_2 := h7094c.2.2.1
                                            have p7094_3 := h7094c.2.2.2
                                            linarith only [h6856, hlam, p7094_0]
                                          · have p7094_0 := h7094c.1
                                            have p7094_1 := h7094c.2.1
                                            have p7094_2 := h7094c.2.2.1
                                            have p7094_3 := h7094c.2.2.2
                                            linarith only [h7017, hlam, p7094_1]
                                          · have p7094_0 := h7094c.1
                                            have p7094_1 := h7094c.2.1
                                            have p7094_2 := h7094c.2.2.1
                                            have p7094_3 := h7094c.2.2.2
                                            linarith only [h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p7094_1]
                                          · have p7094_0 := h7094c.1
                                            have p7094_1 := h7094c.2.1
                                            have p7094_2 := h7094c.2.2.1
                                            have p7094_3 := h7094c.2.2.2
                                            linarith only [h6, hlam, p7094_1]
                                          · have p7094_0 := h7094c.1
                                            have p7094_1 := h7094c.2.1
                                            have p7094_2 := h7094c.2.2.1
                                            have p7094_3 := h7094c.2.2.2
                                            linarith only [h0, h6, hc01, hc15, hlam, hphi, ht0b, ht5b, p7094_1]
                                          · have p7094_0 := h7094c.1
                                            have p7094_1 := h7094c.2.1
                                            have p7094_2 := h7094c.2.2.1
                                            have p7094_3 := h7094c.2.2.2
                                            linarith only [hlam, p7094_0]
                                          · have p7094_0 := h7094c.1
                                            have p7094_1 := h7094c.2.1
                                            have p7094_2 := h7094c.2.2.1
                                            have p7094_3 := h7094c.2.2.2
                                            linarith only [h7022, hlam, p7094_1]
                                          · have p7094_0 := h7094c.1
                                            have p7094_1 := h7094c.2.1
                                            have p7094_2 := h7094c.2.2.1
                                            have p7094_3 := h7094c.2.2.2
                                            linarith only [h0, h5, h7024, hc01, hc45, hlam, hphi, ht0b, ht5b, p7094_1]
                                          · have p7094_0 := h7094c.1
                                            have p7094_1 := h7094c.2.1
                                            have p7094_2 := h7094c.2.2.1
                                            have p7094_3 := h7094c.2.2.2
                                            linarith only [h3, h6194, h6856, hc23, hc35, hlam, hphi, p7094_1]
                                          · have p7094_0 := h7094c.1
                                            have p7094_1 := h7094c.2.1
                                            have p7094_2 := h7094c.2.2.1
                                            have p7094_3 := h7094c.2.2.2
                                            linarith only [h6194, h6856, hc23, hc35, hlam, hphi, p7094_1]
                                          · have p7094_0 := h7094c.1
                                            have p7094_1 := h7094c.2.1
                                            have p7094_2 := h7094c.2.2.1
                                            have p7094_3 := h7094c.2.2.2
                                            linarith only [h6194, h6856, hc23, hc35, hlam, hphi, p7094_1]
                                          · have p7094_0 := h7094c.1
                                            have p7094_1 := h7094c.2.1
                                            have p7094_2 := h7094c.2.2.1
                                            have p7094_3 := h7094c.2.2.2
                                            linarith only [hlam, p7094_0]
                                          · have p7094_0 := h7094c.1
                                            have p7094_1 := h7094c.2.1
                                            have p7094_2 := h7094c.2.2.1
                                            have p7094_3 := h7094c.2.2.2
                                            rcases p7094_3 (m.d 0 5) (by simp) with h7118 | h7118
                                            · linarith only [h5823, h7118, hlam]
                                            · linarith only [h6193, h7118, hlam]
                                          · have p7094_0 := h7094c.1
                                            have p7094_1 := h7094c.2.1
                                            have p7094_2 := h7094c.2.2.1
                                            have p7094_3 := h7094c.2.2.2
                                            linarith only [h6193, hlam, p7094_0]
                                          · have p7094_0 := h7094c.1
                                            have p7094_1 := h7094c.2.1
                                            have p7094_2 := h7094c.2.2.1
                                            have p7094_3 := h7094c.2.2.2
                                            linarith only [h7019, hlam, p7094_0]
                                          · have p7094_0 := h7094c.1
                                            have p7094_1 := h7094c.2.1
                                            have p7094_2 := h7094c.2.2.1
                                            have p7094_3 := h7094c.2.2.2
                                            linarith only [h7024, hlam, p7094_0]
                                          · have p7094_0 := h7094c.1
                                            have p7094_1 := h7094c.2.1
                                            have p7094_2 := h7094c.2.2.1
                                            have p7094_3 := h7094c.2.2.2
                                            linarith only [h7025, hlam, p7094_0]
                                          · have p7094_0 := h7094c.1
                                            have p7094_1 := h7094c.2.1
                                            have p7094_2 := h7094c.2.2.1
                                            have p7094_3 := h7094c.2.2.2
                                            linarith only [hlam, p7094_0]
                                        · linarith only [h7093, hlam, p7051_0]
                                      · linarith only [h7, h7092, hlam]
                              · have p7051_0 := h7051c.1
                                have p7051_1 := h7051c.2.1
                                have p7051_2 := h7051c.2.2.1
                                have p7051_3 := h7051c.2.2.2
                                rcases p7051_3 (m.d 0 3) (by simp) with h7128 | h7128
                                · linarith only [h5823, h7128, hlam]
                                · linarith only [h1, h7128, hlam]
                              · have p7051_0 := h7051c.1
                                have p7051_1 := h7051c.2.1
                                have p7051_2 := h7051c.2.2.1
                                have p7051_3 := h7051c.2.2.2
                                rcases p7051_3 (m.d 0 3) (by simp) with h7131 | h7131
                                · linarith only [h5823, h7131, hlam]
                                · linarith only [h4, h7131, hlam]
                              · have p7051_0 := h7051c.1
                                have p7051_1 := h7051c.2.1
                                have p7051_2 := h7051c.2.2.1
                                have p7051_3 := h7051c.2.2.2
                                linarith only [h7025, hlam, p7051_0]
                              · have p7051_0 := h7051c.1
                                have p7051_1 := h7051c.2.1
                                have p7051_2 := h7051c.2.2.1
                                have p7051_3 := h7051c.2.2.2
                                linarith only [hlam, p7051_0]
                    · linarith only [h7042, hlam, p7026_0]
                  · have p7026_0 := h7026c.1
                    have p7026_1 := h7026c.2.1
                    have p7026_2 := h7026c.2.2.1
                    have p7026_3 := h7026c.2.2.2
                    rcases p7026_3 (m.d 0 1) (by simp) with h7137 | h7137
                    · rcases p7026_3 (m.d 1 2) (by simp) with h7138 | h7138
                      · linarith only [h0, h7138, hlam]
                      · rcases p7026_3 (m.d 1 3) (by simp) with h7140 | h7140
                        · linarith only [h1, h7140, hlam]
                        · rcases p7026_3 (m.d 1 4) (by simp) with h7142 | h7142
                          · linarith only [h2, h7142, hlam]
                          · linarith only [h7019, h7142, hlam]
                    · linarith only [h7137, hlam, p7026_0]
                  · have p7026_0 := h7026c.1
                    have p7026_1 := h7026c.2.1
                    have p7026_2 := h7026c.2.2.1
                    have p7026_3 := h7026c.2.2.2
                    linarith only [h0, hlam, p7026_0]
                  · have p7026_0 := h7026c.1
                    have p7026_1 := h7026c.2.1
                    have p7026_2 := h7026c.2.2.1
                    have p7026_3 := h7026c.2.2.2
                    linarith only [hlam, p7026_0]
                  · have p7026_0 := h7026c.1
                    have p7026_1 := h7026c.2.1
                    have p7026_2 := h7026c.2.2.1
                    have p7026_3 := h7026c.2.2.2
                    linarith only [h0, h5, h6194, h6856, h7024, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7026_1]
                  · have p7026_0 := h7026c.1
                    have p7026_1 := h7026c.2.1
                    have p7026_2 := h7026c.2.2.1
                    have p7026_3 := h7026c.2.2.2
                    linarith only [h6195, hlam, p7026_0]
                  · have p7026_0 := h7026c.1
                    have p7026_1 := h7026c.2.1
                    have p7026_2 := h7026c.2.2.1
                    have p7026_3 := h7026c.2.2.2
                    linarith only [h6856, hlam, p7026_0]
                  · have p7026_0 := h7026c.1
                    have p7026_1 := h7026c.2.1
                    have p7026_2 := h7026c.2.2.1
                    have p7026_3 := h7026c.2.2.2
                    linarith only [h1, hlam, p7026_0]
                  · have p7026_0 := h7026c.1
                    have p7026_1 := h7026c.2.1
                    have p7026_2 := h7026c.2.2.1
                    have p7026_3 := h7026c.2.2.2
                    linarith only [h6194, hlam, p7026_1]
                  · have p7026_0 := h7026c.1
                    have p7026_1 := h7026c.2.1
                    have p7026_2 := h7026c.2.2.1
                    have p7026_3 := h7026c.2.2.2
                    linarith only [hlam, p7026_0]
                  · have p7026_0 := h7026c.1
                    have p7026_1 := h7026c.2.1
                    have p7026_2 := h7026c.2.2.1
                    have p7026_3 := h7026c.2.2.2
                    linarith only [h7015, hlam, p7026_1]
                  · have p7026_0 := h7026c.1
                    have p7026_1 := h7026c.2.1
                    have p7026_2 := h7026c.2.2.1
                    have p7026_3 := h7026c.2.2.2
                    linarith only [h7017, hlam, p7026_1]
                  · have p7026_0 := h7026c.1
                    have p7026_1 := h7026c.2.1
                    have p7026_2 := h7026c.2.2.1
                    have p7026_3 := h7026c.2.2.2
                    linarith only [h2, hlam, p7026_0]
                  · have p7026_0 := h7026c.1
                    have p7026_1 := h7026c.2.1
                    have p7026_2 := h7026c.2.2.1
                    have p7026_3 := h7026c.2.2.2
                    linarith only [h2, h6194, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7026_1]
                  · have p7026_0 := h7026c.1
                    have p7026_1 := h7026c.2.1
                    have p7026_2 := h7026c.2.2.1
                    have p7026_3 := h7026c.2.2.2
                    rcases p7026_3 (m.d 0 1) (by simp) with h7158 | h7158
                    · rcases p7026_3 (m.d 1 2) (by simp) with h7159 | h7159
                      · linarith only [h6195, h7159, hlam]
                      · linarith only [h6194, h7159, hlam]
                    · linarith only [h1, h7158, hlam]
                  · have p7026_0 := h7026c.1
                    have p7026_1 := h7026c.2.1
                    have p7026_2 := h7026c.2.2.1
                    have p7026_3 := h7026c.2.2.2
                    linarith only [hlam, p7026_0]
                  · have p7026_0 := h7026c.1
                    have p7026_1 := h7026c.2.1
                    have p7026_2 := h7026c.2.2.1
                    have p7026_3 := h7026c.2.2.2
                    linarith only [h0, h5, h6194, h6195, h6856, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7026_1]
                  · have p7026_0 := h7026c.1
                    have p7026_1 := h7026c.2.1
                    have p7026_2 := h7026c.2.2.1
                    have p7026_3 := h7026c.2.2.2
                    linarith only [h3, hlam, p7026_0]
                  · have p7026_0 := h7026c.1
                    have p7026_1 := h7026c.2.1
                    have p7026_2 := h7026c.2.2.1
                    have p7026_3 := h7026c.2.2.2
                    linarith only [h3, h6194, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7026_1]
                  · have p7026_0 := h7026c.1
                    have p7026_1 := h7026c.2.1
                    have p7026_2 := h7026c.2.2.1
                    have p7026_3 := h7026c.2.2.2
                    rcases p7026_3 (m.d 0 1) (by simp) with h7167 | h7167
                    · rcases p7026_3 (m.d 1 2) (by simp) with h7168 | h7168
                      · linarith only [h6856, h7168, hlam]
                      · linarith only [h6194, h7168, hlam]
                    · linarith only [h1, h7167, hlam]
                  · have p7026_0 := h7026c.1
                    have p7026_1 := h7026c.2.1
                    have p7026_2 := h7026c.2.2.1
                    have p7026_3 := h7026c.2.2.2
                    linarith only [h7019, hlam, p7026_0]
                  · have p7026_0 := h7026c.1
                    have p7026_1 := h7026c.2.1
                    have p7026_2 := h7026c.2.2.1
                    have p7026_3 := h7026c.2.2.2
                    linarith only [hlam, p7026_0]
                · linarith only [h6193, h7, h7025, hlam]
              · linarith only [h6195, h7019, h7024, hlam]
        · linarith only [h6193, h6194, h6195, h7, h7019, hc23, hc34, hlam, hphi]

set_option maxHeartbeats 16094000 in
set_option maxHeartbeats 16094000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s6_x1_x1_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h5823 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h6193 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h6194 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 2 4 (by decide) (by decide) with h6195 | h6195
  · exact r1l7_11_13_25_L_I_L_I_H_I_s6_x1_x1_x0_x0_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h5823 h6193 h6194 h6195
  · exact r1l7_11_13_25_L_I_L_I_H_I_s6_x1_x1_x0_x0_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h5823 h6193 h6194 h6195

set_option maxHeartbeats 16094000 in
set_option maxHeartbeats 16094000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s6_x1_x1_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h5823 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h6193 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h6194 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 2 4 (by decide) (by decide) with h7177 | h7177
  · rcases m.htr 1 2 5 (by decide) (by decide) with h7178 | h7178
    · rcases m.htr 1 3 4 (by decide) (by decide) with h7179 | h7179
      · linarith only [h4, h6194, h7, h7177, h7179, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
      · linarith only [h6194, h7177, h7179, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h7182 | h7182
      · linarith only [h4, h6194, h7, h7177, h7182, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
      · linarith only [h6194, h7177, h7182, hlam]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h7185 | h7185
    · rcases m.htr 1 3 4 (by decide) (by decide) with h7186 | h7186
      · linarith only [h1, h7, h7186, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h7188 | h7188
        · linarith only [h4, h5823, h6194, h7188, hlam]
        · linarith only [h6194, h7185, h7188, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h7191 | h7191
      · linarith only [h1, h4, h6194, h7, h7191, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h7193 | h7193
        · linarith only [h4, h5823, h6194, h7193, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h7195 | h7195
          · rcases m.htr 2 3 4 (by decide) (by decide) with h7196 | h7196
            · linarith only [h4, h7, h7196, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h7198 | h7198
              · linarith only [h4, h5823, h7198, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h7200 | h7200
                · rcases m.htr 3 4 5 (by decide) (by decide) with h7201 | h7201
                  · rcases h1bigk with h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c | h7202c
                    · have p7202_0 := h7202c.1
                      have p7202_1 := h7202c.2.1
                      have p7202_2 := h7202c.2.2.1
                      have p7202_3 := h7202c.2.2.2
                      linarith only [hlam, p7202_0]
                    · have p7202_0 := h7202c.1
                      have p7202_1 := h7202c.2.1
                      have p7202_2 := h7202c.2.2.1
                      have p7202_3 := h7202c.2.2.2
                      rcases p7202_3 (m.d 0 1) (by simp) with h7204 | h7204
                      · rcases p7202_3 (m.d 1 2) (by simp) with h7205 | h7205
                        · linarith only [h7205, hlam, p7202_0]
                        · rcases p7202_3 (m.d 1 3) (by simp) with h7207 | h7207
                          · linarith only [h1, h7207, hlam]
                          · linarith only [h6194, h7207, hlam]
                      · linarith only [h7204, hlam, p7202_0]
                    · have p7202_0 := h7202c.1
                      have p7202_1 := h7202c.2.1
                      have p7202_2 := h7202c.2.2.1
                      have p7202_3 := h7202c.2.2.2
                      rcases p7202_3 (m.d 0 1) (by simp) with h7211 | h7211
                      · rcases p7202_3 (m.d 1 2) (by simp) with h7212 | h7212
                        · linarith only [h0, h7212, hlam]
                        · rcases p7202_3 (m.d 1 3) (by simp) with h7214 | h7214
                          · linarith only [h7214, hlam, p7202_0]
                          · rcases p7202_3 (m.d 1 4) (by simp) with h7216 | h7216
                            · linarith only [h2, h7216, hlam]
                            · linarith only [h7191, h7216, hlam]
                      · linarith only [h7211, hlam, p7202_0]
                    · have p7202_0 := h7202c.1
                      have p7202_1 := h7202c.2.1
                      have p7202_2 := h7202c.2.2.1
                      have p7202_3 := h7202c.2.2.2
                      rcases p7202_3 (m.d 0 1) (by simp) with h7220 | h7220
                      · rcases p7202_3 (m.d 1 2) (by simp) with h7221 | h7221
                        · linarith only [h0, h7221, hlam]
                        · rcases p7202_3 (m.d 1 3) (by simp) with h7223 | h7223
                          · linarith only [h1, h7223, hlam]
                          · rcases p7202_3 (m.d 1 4) (by simp) with h7225 | h7225
                            · linarith only [h7225, hlam, p7202_0]
                            · rcases p7202_3 (m.d 1 5) (by simp) with h7227 | h7227
                              · linarith only [h3, h7227, hlam]
                              · rcases h3bigk with h7229c | h7229c | h7229c | h7229c | h7229c | h7229c | h7229c | h7229c | h7229c | h7229c | h7229c | h7229c | h7229c | h7229c | h7229c | h7229c | h7229c | h7229c | h7229c | h7229c | h7229c | h7229c | h7229c | h7229c | h7229c
                                · have p7229_0 := h7229c.1
                                  have p7229_1 := h7229c.2.1
                                  have p7229_2 := h7229c.2.2.1
                                  have p7229_3 := h7229c.2.2.2
                                  linarith only [hlam, p7229_0]
                                · have p7229_0 := h7229c.1
                                  have p7229_1 := h7229c.2.1
                                  have p7229_2 := h7229c.2.2.1
                                  have p7229_3 := h7229c.2.2.2
                                  linarith only [h5823, h7201, hc13, hc34, hlam, hphi, p7229_1]
                                · have p7229_0 := h7229c.1
                                  have p7229_1 := h7229c.2.1
                                  have p7229_2 := h7229c.2.2.1
                                  have p7229_3 := h7229c.2.2.2
                                  linarith only [h5823, h6194, h7201, hc12, hc34, hlam, hphi, ht23, p7229_1]
                                · have p7229_0 := h7229c.1
                                  have p7229_1 := h7229c.2.1
                                  have p7229_2 := h7229c.2.2.1
                                  have p7229_3 := h7229c.2.2.2
                                  linarith only [h7, hlam, p7229_0]
                                · have p7229_0 := h7229c.1
                                  have p7229_1 := h7229c.2.1
                                  have p7229_2 := h7229c.2.2.1
                                  have p7229_3 := h7229c.2.2.2
                                  linarith only [h5823, hlam, p7229_0]
                                · have p7229_0 := h7229c.1
                                  have p7229_1 := h7229c.2.1
                                  have p7229_2 := h7229c.2.2.1
                                  have p7229_3 := h7229c.2.2.2
                                  linarith only [h1, hlam, p7229_0]
                                · have p7229_0 := h7229c.1
                                  have p7229_1 := h7229c.2.1
                                  have p7229_2 := h7229c.2.2.1
                                  have p7229_3 := h7229c.2.2.2
                                  linarith only [hlam, p7229_0]
                                · have p7229_0 := h7229c.1
                                  have p7229_1 := h7229c.2.1
                                  have p7229_2 := h7229c.2.2.1
                                  have p7229_3 := h7229c.2.2.2
                                  linarith only [h6194, hlam, p7229_1]
                                · have p7229_0 := h7229c.1
                                  have p7229_1 := h7229c.2.1
                                  have p7229_2 := h7229c.2.2.1
                                  have p7229_3 := h7229c.2.2.2
                                  linarith only [h7191, hlam, p7229_0]
                                · have p7229_0 := h7229c.1
                                  have p7229_1 := h7229c.2.1
                                  have p7229_2 := h7229c.2.2.1
                                  have p7229_3 := h7229c.2.2.2
                                  linarith only [h7193, hlam, p7229_0]
                                · have p7229_0 := h7229c.1
                                  have p7229_1 := h7229c.2.1
                                  have p7229_2 := h7229c.2.2.1
                                  have p7229_3 := h7229c.2.2.2
                                  linarith only [h4, hlam, p7229_0]
                                · have p7229_0 := h7229c.1
                                  have p7229_1 := h7229c.2.1
                                  have p7229_2 := h7229c.2.2.1
                                  have p7229_3 := h7229c.2.2.2
                                  linarith only [h4, h5823, h7201, hc13, hc34, hlam, hphi, p7229_1]
                                · have p7229_0 := h7229c.1
                                  have p7229_1 := h7229c.2.1
                                  have p7229_2 := h7229c.2.2.1
                                  have p7229_3 := h7229c.2.2.2
                                  linarith only [hlam, p7229_0]
                                · have p7229_0 := h7229c.1
                                  have p7229_1 := h7229c.2.1
                                  have p7229_2 := h7229c.2.2.1
                                  have p7229_3 := h7229c.2.2.2
                                  linarith only [h7196, hlam, p7229_0]
                                · have p7229_0 := h7229c.1
                                  have p7229_1 := h7229c.2.1
                                  have p7229_2 := h7229c.2.2.1
                                  have p7229_3 := h7229c.2.2.2
                                  linarith only [h7198, hlam, p7229_0]
                                · have p7229_0 := h7229c.1
                                  have p7229_1 := h7229c.2.1
                                  have p7229_2 := h7229c.2.2.1
                                  have p7229_3 := h7229c.2.2.2
                                  linarith only [h4, h6194, hc12, hc34, hlam, hphi, ht23, p7229_1]
                                · have p7229_0 := h7229c.1
                                  have p7229_1 := h7229c.2.1
                                  have p7229_2 := h7229c.2.2.1
                                  have p7229_3 := h7229c.2.2.2
                                  rcases p7229_3 (m.d 0 3) (by simp) with h7246 | h7246
                                  · linarith only [h7, h7246, hlam]
                                  · linarith only [h1, h7246, hlam]
                                · have p7229_0 := h7229c.1
                                  have p7229_1 := h7229c.2.1
                                  have p7229_2 := h7229c.2.2.1
                                  have p7229_3 := h7229c.2.2.2
                                  linarith only [h6194, hc12, hc34, hlam, hphi, ht23, p7229_1]
                                · have p7229_0 := h7229c.1
                                  have p7229_1 := h7229c.2.1
                                  have p7229_2 := h7229c.2.2.1
                                  have p7229_3 := h7229c.2.2.2
                                  linarith only [hlam, p7229_0]
                                · have p7229_0 := h7229c.1
                                  have p7229_1 := h7229c.2.1
                                  have p7229_2 := h7229c.2.2.1
                                  have p7229_3 := h7229c.2.2.2
                                  linarith only [h4, h5823, h6194, hc12, hc34, hlam, hphi, ht23, p7229_1]
                                · have p7229_0 := h7229c.1
                                  have p7229_1 := h7229c.2.1
                                  have p7229_2 := h7229c.2.2.1
                                  have p7229_3 := h7229c.2.2.2
                                  linarith only [h4, h6194, hc12, hc35, hlam, hphi, ht23, p7229_1]
                                · have p7229_0 := h7229c.1
                                  have p7229_1 := h7229c.2.1
                                  have p7229_2 := h7229c.2.2.1
                                  have p7229_3 := h7229c.2.2.2
                                  rcases p7229_3 (m.d 0 3) (by simp) with h7253 | h7253
                                  · linarith only [h5823, h7253, hlam]
                                  · linarith only [h1, h7253, hlam]
                                · have p7229_0 := h7229c.1
                                  have p7229_1 := h7229c.2.1
                                  have p7229_2 := h7229c.2.2.1
                                  have p7229_3 := h7229c.2.2.2
                                  linarith only [h6194, h7201, hc12, hc34, hlam, hphi, ht23, p7229_1]
                                · have p7229_0 := h7229c.1
                                  have p7229_1 := h7229c.2.1
                                  have p7229_2 := h7229c.2.2.1
                                  have p7229_3 := h7229c.2.2.2
                                  linarith only [h7201, hlam, p7229_0]
                                · have p7229_0 := h7229c.1
                                  have p7229_1 := h7229c.2.1
                                  have p7229_2 := h7229c.2.2.1
                                  have p7229_3 := h7229c.2.2.2
                                  linarith only [hlam, p7229_0]
                      · linarith only [h7220, hlam, p7202_0]
                    · have p7202_0 := h7202c.1
                      have p7202_1 := h7202c.2.1
                      have p7202_2 := h7202c.2.2.1
                      have p7202_3 := h7202c.2.2.2
                      rcases p7202_3 (m.d 0 1) (by simp) with h7260 | h7260
                      · rcases p7202_3 (m.d 1 2) (by simp) with h7261 | h7261
                        · linarith only [h0, h7261, hlam]
                        · rcases p7202_3 (m.d 1 3) (by simp) with h7263 | h7263
                          · linarith only [h1, h7263, hlam]
                          · rcases p7202_3 (m.d 1 4) (by simp) with h7265 | h7265
                            · linarith only [h2, h7265, hlam]
                            · linarith only [h7195, h7265, hlam]
                      · linarith only [h7260, hlam, p7202_0]
                    · have p7202_0 := h7202c.1
                      have p7202_1 := h7202c.2.1
                      have p7202_2 := h7202c.2.2.1
                      have p7202_3 := h7202c.2.2.2
                      linarith only [h0, hlam, p7202_0]
                    · have p7202_0 := h7202c.1
                      have p7202_1 := h7202c.2.1
                      have p7202_2 := h7202c.2.2.1
                      have p7202_3 := h7202c.2.2.2
                      linarith only [hlam, p7202_0]
                    · have p7202_0 := h7202c.1
                      have p7202_1 := h7202c.2.1
                      have p7202_2 := h7202c.2.2.1
                      have p7202_3 := h7202c.2.2.2
                      linarith only [h6194, hlam, p7202_0]
                    · have p7202_0 := h7202c.1
                      have p7202_1 := h7202c.2.1
                      have p7202_2 := h7202c.2.2.1
                      have p7202_3 := h7202c.2.2.2
                      linarith only [h7177, hlam, p7202_0]
                    · have p7202_0 := h7202c.1
                      have p7202_1 := h7202c.2.1
                      have p7202_2 := h7202c.2.2.1
                      have p7202_3 := h7202c.2.2.2
                      linarith only [h7185, hlam, p7202_0]
                    · have p7202_0 := h7202c.1
                      have p7202_1 := h7202c.2.1
                      have p7202_2 := h7202c.2.2.1
                      have p7202_3 := h7202c.2.2.2
                      linarith only [h1, hlam, p7202_0]
                    · have p7202_0 := h7202c.1
                      have p7202_1 := h7202c.2.1
                      have p7202_2 := h7202c.2.2.1
                      have p7202_3 := h7202c.2.2.2
                      linarith only [h1, h7, hc12, hc34, hlam, hphi, ht23, p7202_1]
                    · have p7202_0 := h7202c.1
                      have p7202_1 := h7202c.2.1
                      have p7202_2 := h7202c.2.2.1
                      have p7202_3 := h7202c.2.2.2
                      linarith only [hlam, p7202_0]
                    · have p7202_0 := h7202c.1
                      have p7202_1 := h7202c.2.1
                      have p7202_2 := h7202c.2.2.1
                      have p7202_3 := h7202c.2.2.2
                      linarith only [h7191, hlam, p7202_1]
                    · have p7202_0 := h7202c.1
                      have p7202_1 := h7202c.2.1
                      have p7202_2 := h7202c.2.2.1
                      have p7202_3 := h7202c.2.2.2
                      linarith only [h7193, hlam, p7202_1]
                    · have p7202_0 := h7202c.1
                      have p7202_1 := h7202c.2.1
                      have p7202_2 := h7202c.2.2.1
                      have p7202_3 := h7202c.2.2.2
                      linarith only [h2, hlam, p7202_0]
                    · have p7202_0 := h7202c.1
                      have p7202_1 := h7202c.2.1
                      have p7202_2 := h7202c.2.2.1
                      have p7202_3 := h7202c.2.2.2
                      rcases p7202_3 (m.d 0 1) (by simp) with h7280 | h7280
                      · rcases p7202_3 (m.d 1 2) (by simp) with h7281 | h7281
                        · linarith only [h7177, h7281, hlam]
                        · rcases p7202_3 (m.d 1 3) (by simp) with h7283 | h7283
                          · linarith only [h7191, h7283, hlam]
                          · linarith only [h6194, h7283, hlam]
                      · linarith only [h0, h7280, hlam]
                    · have p7202_0 := h7202c.1
                      have p7202_1 := h7202c.2.1
                      have p7202_2 := h7202c.2.2.1
                      have p7202_3 := h7202c.2.2.2
                      rcases p7202_3 (m.d 0 1) (by simp) with h7287 | h7287
                      · rcases p7202_3 (m.d 1 2) (by simp) with h7288 | h7288
                        · linarith only [h7177, h7288, hlam]
                        · rcases p7202_3 (m.d 1 3) (by simp) with h7290 | h7290
                          · linarith only [h7191, h7290, hlam]
                          · rcases p7202_3 (m.d 1 4) (by simp) with h7292 | h7292
                            · rcases p7202_3 (m.d 1 5) (by simp) with h7293 | h7293
                              · linarith only [h7195, h7293, hlam]
                              · linarith only [h7193, h7293, hlam]
                            · linarith only [h7191, h7292, hlam]
                      · linarith only [h1, h7287, hlam]
                    · have p7202_0 := h7202c.1
                      have p7202_1 := h7202c.2.1
                      have p7202_2 := h7202c.2.2.1
                      have p7202_3 := h7202c.2.2.2
                      linarith only [hlam, p7202_0]
                    · have p7202_0 := h7202c.1
                      have p7202_1 := h7202c.2.1
                      have p7202_2 := h7202c.2.2.1
                      have p7202_3 := h7202c.2.2.2
                      rcases p7202_3 (m.d 0 1) (by simp) with h7299 | h7299
                      · rcases p7202_3 (m.d 1 2) (by simp) with h7300 | h7300
                        · linarith only [h7177, h7300, hlam]
                        · rcases p7202_3 (m.d 1 3) (by simp) with h7302 | h7302
                          · linarith only [h7191, h7302, hlam]
                          · rcases p7202_3 (m.d 1 4) (by simp) with h7304 | h7304
                            · rcases p7202_3 (m.d 1 5) (by simp) with h7305 | h7305
                              · linarith only [h7195, h7305, hlam]
                              · rcases h3bigk with h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c
                                · have p7307_0 := h7307c.1
                                  have p7307_1 := h7307c.2.1
                                  have p7307_2 := h7307c.2.2.1
                                  have p7307_3 := h7307c.2.2.2
                                  linarith only [hlam, p7307_0]
                                · have p7307_0 := h7307c.1
                                  have p7307_1 := h7307c.2.1
                                  have p7307_2 := h7307c.2.2.1
                                  have p7307_3 := h7307c.2.2.2
                                  linarith only [h5823, h6194, h7201, hc12, hc34, hlam, hphi, ht23, p7307_1]
                                · have p7307_0 := h7307c.1
                                  have p7307_1 := h7307c.2.1
                                  have p7307_2 := h7307c.2.2.1
                                  have p7307_3 := h7307c.2.2.2
                                  linarith only [h5823, h6194, h7201, hc12, hc34, hlam, hphi, ht23, p7307_1]
                                · have p7307_0 := h7307c.1
                                  have p7307_1 := h7307c.2.1
                                  have p7307_2 := h7307c.2.2.1
                                  have p7307_3 := h7307c.2.2.2
                                  linarith only [h7, hlam, p7307_0]
                                · have p7307_0 := h7307c.1
                                  have p7307_1 := h7307c.2.1
                                  have p7307_2 := h7307c.2.2.1
                                  have p7307_3 := h7307c.2.2.2
                                  linarith only [h5823, hlam, p7307_0]
                                · have p7307_0 := h7307c.1
                                  have p7307_1 := h7307c.2.1
                                  have p7307_2 := h7307c.2.2.1
                                  have p7307_3 := h7307c.2.2.2
                                  linarith only [h1, hlam, p7307_0]
                                · have p7307_0 := h7307c.1
                                  have p7307_1 := h7307c.2.1
                                  have p7307_2 := h7307c.2.2.1
                                  have p7307_3 := h7307c.2.2.2
                                  linarith only [hlam, p7307_0]
                                · have p7307_0 := h7307c.1
                                  have p7307_1 := h7307c.2.1
                                  have p7307_2 := h7307c.2.2.1
                                  have p7307_3 := h7307c.2.2.2
                                  linarith only [h6194, hlam, p7307_1]
                                · have p7307_0 := h7307c.1
                                  have p7307_1 := h7307c.2.1
                                  have p7307_2 := h7307c.2.2.1
                                  have p7307_3 := h7307c.2.2.2
                                  linarith only [h7191, hlam, p7307_0]
                                · have p7307_0 := h7307c.1
                                  have p7307_1 := h7307c.2.1
                                  have p7307_2 := h7307c.2.2.1
                                  have p7307_3 := h7307c.2.2.2
                                  linarith only [h7193, hlam, p7307_0]
                                · have p7307_0 := h7307c.1
                                  have p7307_1 := h7307c.2.1
                                  have p7307_2 := h7307c.2.2.1
                                  have p7307_3 := h7307c.2.2.2
                                  linarith only [h4, hlam, p7307_0]
                                · have p7307_0 := h7307c.1
                                  have p7307_1 := h7307c.2.1
                                  have p7307_2 := h7307c.2.2.1
                                  have p7307_3 := h7307c.2.2.2
                                  linarith only [h4, h5823, h6194, h7201, hc12, hc34, hlam, hphi, ht23, p7307_1]
                                · have p7307_0 := h7307c.1
                                  have p7307_1 := h7307c.2.1
                                  have p7307_2 := h7307c.2.2.1
                                  have p7307_3 := h7307c.2.2.2
                                  linarith only [hlam, p7307_0]
                                · have p7307_0 := h7307c.1
                                  have p7307_1 := h7307c.2.1
                                  have p7307_2 := h7307c.2.2.1
                                  have p7307_3 := h7307c.2.2.2
                                  linarith only [h7196, hlam, p7307_0]
                                · have p7307_0 := h7307c.1
                                  have p7307_1 := h7307c.2.1
                                  have p7307_2 := h7307c.2.2.1
                                  have p7307_3 := h7307c.2.2.2
                                  linarith only [h7198, hlam, p7307_0]
                                · have p7307_0 := h7307c.1
                                  have p7307_1 := h7307c.2.1
                                  have p7307_2 := h7307c.2.2.1
                                  have p7307_3 := h7307c.2.2.2
                                  linarith only [h4, h6194, hc12, hc34, hlam, hphi, ht23, p7307_1]
                                · have p7307_0 := h7307c.1
                                  have p7307_1 := h7307c.2.1
                                  have p7307_2 := h7307c.2.2.1
                                  have p7307_3 := h7307c.2.2.2
                                  rcases p7307_3 (m.d 0 3) (by simp) with h7324 | h7324
                                  · linarith only [h7, h7324, hlam]
                                  · linarith only [h1, h7324, hlam]
                                · have p7307_0 := h7307c.1
                                  have p7307_1 := h7307c.2.1
                                  have p7307_2 := h7307c.2.2.1
                                  have p7307_3 := h7307c.2.2.2
                                  linarith only [h6194, hc12, hc34, hlam, hphi, ht23, p7307_1]
                                · have p7307_0 := h7307c.1
                                  have p7307_1 := h7307c.2.1
                                  have p7307_2 := h7307c.2.2.1
                                  have p7307_3 := h7307c.2.2.2
                                  linarith only [hlam, p7307_0]
                                · have p7307_0 := h7307c.1
                                  have p7307_1 := h7307c.2.1
                                  have p7307_2 := h7307c.2.2.1
                                  have p7307_3 := h7307c.2.2.2
                                  linarith only [h4, h5823, h6194, hc12, hc34, hlam, hphi, ht23, p7307_1]
                                · have p7307_0 := h7307c.1
                                  have p7307_1 := h7307c.2.1
                                  have p7307_2 := h7307c.2.2.1
                                  have p7307_3 := h7307c.2.2.2
                                  linarith only [h4, h6194, hc12, hc35, hlam, hphi, ht23, p7307_1]
                                · have p7307_0 := h7307c.1
                                  have p7307_1 := h7307c.2.1
                                  have p7307_2 := h7307c.2.2.1
                                  have p7307_3 := h7307c.2.2.2
                                  rcases p7307_3 (m.d 0 3) (by simp) with h7331 | h7331
                                  · linarith only [h5823, h7331, hlam]
                                  · linarith only [h1, h7331, hlam]
                                · have p7307_0 := h7307c.1
                                  have p7307_1 := h7307c.2.1
                                  have p7307_2 := h7307c.2.2.1
                                  have p7307_3 := h7307c.2.2.2
                                  linarith only [h6194, h7201, hc12, hc34, hlam, hphi, ht23, p7307_1]
                                · have p7307_0 := h7307c.1
                                  have p7307_1 := h7307c.2.1
                                  have p7307_2 := h7307c.2.2.1
                                  have p7307_3 := h7307c.2.2.2
                                  linarith only [h7201, hlam, p7307_0]
                                · have p7307_0 := h7307c.1
                                  have p7307_1 := h7307c.2.1
                                  have p7307_2 := h7307c.2.2.1
                                  have p7307_3 := h7307c.2.2.2
                                  linarith only [hlam, p7307_0]
                            · linarith only [h7195, h7304, hlam]
                      · linarith only [h3, h7299, hlam]
                    · have p7202_0 := h7202c.1
                      have p7202_1 := h7202c.2.1
                      have p7202_2 := h7202c.2.2.1
                      have p7202_3 := h7202c.2.2.2
                      linarith only [h3, hlam, p7202_0]
                    · have p7202_0 := h7202c.1
                      have p7202_1 := h7202c.2.1
                      have p7202_2 := h7202c.2.2.1
                      have p7202_3 := h7202c.2.2.2
                      rcases p7202_3 (m.d 0 1) (by simp) with h7340 | h7340
                      · rcases p7202_3 (m.d 1 2) (by simp) with h7341 | h7341
                        · linarith only [h7185, h7341, hlam]
                        · rcases p7202_3 (m.d 1 3) (by simp) with h7343 | h7343
                          · linarith only [h7193, h7343, hlam]
                          · linarith only [h6194, h7343, hlam]
                      · linarith only [h0, h7340, hlam]
                    · have p7202_0 := h7202c.1
                      have p7202_1 := h7202c.2.1
                      have p7202_2 := h7202c.2.2.1
                      have p7202_3 := h7202c.2.2.2
                      rcases p7202_3 (m.d 0 1) (by simp) with h7347 | h7347
                      · rcases p7202_3 (m.d 1 2) (by simp) with h7348 | h7348
                        · linarith only [h7185, h7348, hlam]
                        · rcases p7202_3 (m.d 1 3) (by simp) with h7350 | h7350
                          · linarith only [h7193, h7350, hlam]
                          · rcases p7202_3 (m.d 1 4) (by simp) with h7352 | h7352
                            · rcases p7202_3 (m.d 1 5) (by simp) with h7353 | h7353
                              · rcases h3bigk with h7354c | h7354c | h7354c | h7354c | h7354c | h7354c | h7354c | h7354c | h7354c | h7354c | h7354c | h7354c | h7354c | h7354c | h7354c | h7354c | h7354c | h7354c | h7354c | h7354c | h7354c | h7354c | h7354c | h7354c | h7354c
                                · have p7354_0 := h7354c.1
                                  have p7354_1 := h7354c.2.1
                                  have p7354_2 := h7354c.2.2.1
                                  have p7354_3 := h7354c.2.2.2
                                  linarith only [hlam, p7354_0]
                                · have p7354_0 := h7354c.1
                                  have p7354_1 := h7354c.2.1
                                  have p7354_2 := h7354c.2.2.1
                                  have p7354_3 := h7354c.2.2.2
                                  linarith only [h6194, h7, hc12, hc34, hlam, hphi, ht23, p7354_1]
                                · have p7354_0 := h7354c.1
                                  have p7354_1 := h7354c.2.1
                                  have p7354_2 := h7354c.2.2.1
                                  have p7354_3 := h7354c.2.2.2
                                  linarith only [h6194, h7, hc12, hc34, hlam, hphi, ht23, p7354_1]
                                · have p7354_0 := h7354c.1
                                  have p7354_1 := h7354c.2.1
                                  have p7354_2 := h7354c.2.2.1
                                  have p7354_3 := h7354c.2.2.2
                                  linarith only [h7, hlam, p7354_0]
                                · have p7354_0 := h7354c.1
                                  have p7354_1 := h7354c.2.1
                                  have p7354_2 := h7354c.2.2.1
                                  have p7354_3 := h7354c.2.2.2
                                  linarith only [h5823, hlam, p7354_0]
                                · have p7354_0 := h7354c.1
                                  have p7354_1 := h7354c.2.1
                                  have p7354_2 := h7354c.2.2.1
                                  have p7354_3 := h7354c.2.2.2
                                  linarith only [h1, hlam, p7354_0]
                                · have p7354_0 := h7354c.1
                                  have p7354_1 := h7354c.2.1
                                  have p7354_2 := h7354c.2.2.1
                                  have p7354_3 := h7354c.2.2.2
                                  linarith only [hlam, p7354_0]
                                · have p7354_0 := h7354c.1
                                  have p7354_1 := h7354c.2.1
                                  have p7354_2 := h7354c.2.2.1
                                  have p7354_3 := h7354c.2.2.2
                                  linarith only [h6194, hlam, p7354_1]
                                · have p7354_0 := h7354c.1
                                  have p7354_1 := h7354c.2.1
                                  have p7354_2 := h7354c.2.2.1
                                  have p7354_3 := h7354c.2.2.2
                                  linarith only [h7191, hlam, p7354_0]
                                · have p7354_0 := h7354c.1
                                  have p7354_1 := h7354c.2.1
                                  have p7354_2 := h7354c.2.2.1
                                  have p7354_3 := h7354c.2.2.2
                                  linarith only [h7193, hlam, p7354_0]
                                · have p7354_0 := h7354c.1
                                  have p7354_1 := h7354c.2.1
                                  have p7354_2 := h7354c.2.2.1
                                  have p7354_3 := h7354c.2.2.2
                                  linarith only [h4, hlam, p7354_0]
                                · have p7354_0 := h7354c.1
                                  have p7354_1 := h7354c.2.1
                                  have p7354_2 := h7354c.2.2.1
                                  have p7354_3 := h7354c.2.2.2
                                  linarith only [h4, h5823, h6194, h7201, hc12, hc34, hlam, hphi, ht23, p7354_1]
                                · have p7354_0 := h7354c.1
                                  have p7354_1 := h7354c.2.1
                                  have p7354_2 := h7354c.2.2.1
                                  have p7354_3 := h7354c.2.2.2
                                  linarith only [hlam, p7354_0]
                                · have p7354_0 := h7354c.1
                                  have p7354_1 := h7354c.2.1
                                  have p7354_2 := h7354c.2.2.1
                                  have p7354_3 := h7354c.2.2.2
                                  linarith only [h7196, hlam, p7354_0]
                                · have p7354_0 := h7354c.1
                                  have p7354_1 := h7354c.2.1
                                  have p7354_2 := h7354c.2.2.1
                                  have p7354_3 := h7354c.2.2.2
                                  linarith only [h7198, hlam, p7354_0]
                                · have p7354_0 := h7354c.1
                                  have p7354_1 := h7354c.2.1
                                  have p7354_2 := h7354c.2.2.1
                                  have p7354_3 := h7354c.2.2.2
                                  linarith only [h4, h6194, hc12, hc34, hlam, hphi, ht23, p7354_1]
                                · have p7354_0 := h7354c.1
                                  have p7354_1 := h7354c.2.1
                                  have p7354_2 := h7354c.2.2.1
                                  have p7354_3 := h7354c.2.2.2
                                  rcases p7354_3 (m.d 0 3) (by simp) with h7371 | h7371
                                  · linarith only [h7, h7371, hlam]
                                  · linarith only [h1, h7371, hlam]
                                · have p7354_0 := h7354c.1
                                  have p7354_1 := h7354c.2.1
                                  have p7354_2 := h7354c.2.2.1
                                  have p7354_3 := h7354c.2.2.2
                                  linarith only [h6194, hc12, hc34, hlam, hphi, ht23, p7354_1]
                                · have p7354_0 := h7354c.1
                                  have p7354_1 := h7354c.2.1
                                  have p7354_2 := h7354c.2.2.1
                                  have p7354_3 := h7354c.2.2.2
                                  linarith only [hlam, p7354_0]
                                · have p7354_0 := h7354c.1
                                  have p7354_1 := h7354c.2.1
                                  have p7354_2 := h7354c.2.2.1
                                  have p7354_3 := h7354c.2.2.2
                                  linarith only [h4, h5823, h6194, hc12, hc34, hlam, hphi, ht23, p7354_1]
                                · have p7354_0 := h7354c.1
                                  have p7354_1 := h7354c.2.1
                                  have p7354_2 := h7354c.2.2.1
                                  have p7354_3 := h7354c.2.2.2
                                  linarith only [h4, h6194, hc12, hc35, hlam, hphi, ht23, p7354_1]
                                · have p7354_0 := h7354c.1
                                  have p7354_1 := h7354c.2.1
                                  have p7354_2 := h7354c.2.2.1
                                  have p7354_3 := h7354c.2.2.2
                                  rcases p7354_3 (m.d 0 3) (by simp) with h7378 | h7378
                                  · linarith only [h5823, h7378, hlam]
                                  · linarith only [h1, h7378, hlam]
                                · have p7354_0 := h7354c.1
                                  have p7354_1 := h7354c.2.1
                                  have p7354_2 := h7354c.2.2.1
                                  have p7354_3 := h7354c.2.2.2
                                  linarith only [h6194, h7201, hc12, hc34, hlam, hphi, ht23, p7354_1]
                                · have p7354_0 := h7354c.1
                                  have p7354_1 := h7354c.2.1
                                  have p7354_2 := h7354c.2.2.1
                                  have p7354_3 := h7354c.2.2.2
                                  linarith only [h7201, hlam, p7354_0]
                                · have p7354_0 := h7354c.1
                                  have p7354_1 := h7354c.2.1
                                  have p7354_2 := h7354c.2.2.1
                                  have p7354_3 := h7354c.2.2.2
                                  linarith only [hlam, p7354_0]
                              · linarith only [h7193, h7353, hlam]
                            · linarith only [h7191, h7352, hlam]
                      · linarith only [h1, h7347, hlam]
                    · have p7202_0 := h7202c.1
                      have p7202_1 := h7202c.2.1
                      have p7202_2 := h7202c.2.2.1
                      have p7202_3 := h7202c.2.2.2
                      linarith only [h7195, hlam, p7202_0]
                    · have p7202_0 := h7202c.1
                      have p7202_1 := h7202c.2.1
                      have p7202_2 := h7202c.2.2.1
                      have p7202_3 := h7202c.2.2.2
                      linarith only [hlam, p7202_0]
                  · linarith only [h4, h6194, h7, h7201, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h7177, h7195, h7200, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h7391 | h7391
            · linarith only [h0, h4, h6193, h7, h7195, h7391, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h7393 | h7393
              · linarith only [h4, h5823, h7393, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h7395 | h7395
                · rcases m.htr 3 4 5 (by decide) (by decide) with h7396 | h7396
                  · rcases h1bigk with h7397c | h7397c | h7397c | h7397c | h7397c | h7397c | h7397c | h7397c | h7397c | h7397c | h7397c | h7397c | h7397c | h7397c | h7397c | h7397c | h7397c | h7397c | h7397c | h7397c | h7397c | h7397c | h7397c | h7397c | h7397c
                    · have p7397_0 := h7397c.1
                      have p7397_1 := h7397c.2.1
                      have p7397_2 := h7397c.2.2.1
                      have p7397_3 := h7397c.2.2.2
                      linarith only [hlam, p7397_0]
                    · have p7397_0 := h7397c.1
                      have p7397_1 := h7397c.2.1
                      have p7397_2 := h7397c.2.2.1
                      have p7397_3 := h7397c.2.2.2
                      linarith only [h0, h5, h6194, h7191, h7195, h7395, hlam, p7397_2]
                    · have p7397_0 := h7397c.1
                      have p7397_1 := h7397c.2.1
                      have p7397_2 := h7397c.2.2.1
                      have p7397_3 := h7397c.2.2.2
                      linarith only [h0, h5, h7191, h7195, h7395, hlam, p7397_2]
                    · have p7397_0 := h7397c.1
                      have p7397_1 := h7397c.2.1
                      have p7397_2 := h7397c.2.2.1
                      have p7397_3 := h7397c.2.2.2
                      linarith only [h0, h5, h7195, h7395, hlam, p7397_2]
                    · have p7397_0 := h7397c.1
                      have p7397_1 := h7397c.2.1
                      have p7397_2 := h7397c.2.2.1
                      have p7397_3 := h7397c.2.2.2
                      rcases p7397_3 (m.d 0 1) (by simp) with h7402 | h7402
                      · rcases p7397_3 (m.d 1 2) (by simp) with h7403 | h7403
                        · linarith only [h0, h7403, hlam]
                        · rcases p7397_3 (m.d 1 3) (by simp) with h7405 | h7405
                          · linarith only [h1, h7405, hlam]
                          · rcases p7397_3 (m.d 1 4) (by simp) with h7407 | h7407
                            · linarith only [h2, h7407, hlam]
                            · rcases p7397_3 (m.d 1 5) (by simp) with h7409 | h7409
                              · linarith only [h7409, hlam, p7397_0]
                              · rcases h3bigk with h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c
                                · have p7411_0 := h7411c.1
                                  have p7411_1 := h7411c.2.1
                                  have p7411_2 := h7411c.2.2.1
                                  have p7411_3 := h7411c.2.2.2
                                  linarith only [hlam, p7411_0]
                                · have p7411_0 := h7411c.1
                                  have p7411_1 := h7411c.2.1
                                  have p7411_2 := h7411c.2.2.1
                                  have p7411_3 := h7411c.2.2.2
                                  linarith only [h5823, h6194, h7396, hc12, hc34, hlam, hphi, ht23, p7411_1]
                                · have p7411_0 := h7411c.1
                                  have p7411_1 := h7411c.2.1
                                  have p7411_2 := h7411c.2.2.1
                                  have p7411_3 := h7411c.2.2.2
                                  linarith only [h5823, h7396, hc23, hc34, hlam, hphi, p7411_1]
                                · have p7411_0 := h7411c.1
                                  have p7411_1 := h7411c.2.1
                                  have p7411_2 := h7411c.2.2.1
                                  have p7411_3 := h7411c.2.2.2
                                  linarith only [h7, hlam, p7411_0]
                                · have p7411_0 := h7411c.1
                                  have p7411_1 := h7411c.2.1
                                  have p7411_2 := h7411c.2.2.1
                                  have p7411_3 := h7411c.2.2.2
                                  linarith only [h5823, hlam, p7411_0]
                                · have p7411_0 := h7411c.1
                                  have p7411_1 := h7411c.2.1
                                  have p7411_2 := h7411c.2.2.1
                                  have p7411_3 := h7411c.2.2.2
                                  linarith only [h1, hlam, p7411_0]
                                · have p7411_0 := h7411c.1
                                  have p7411_1 := h7411c.2.1
                                  have p7411_2 := h7411c.2.2.1
                                  have p7411_3 := h7411c.2.2.2
                                  linarith only [hlam, p7411_0]
                                · have p7411_0 := h7411c.1
                                  have p7411_1 := h7411c.2.1
                                  have p7411_2 := h7411c.2.2.1
                                  have p7411_3 := h7411c.2.2.2
                                  linarith only [h6194, hlam, p7411_1]
                                · have p7411_0 := h7411c.1
                                  have p7411_1 := h7411c.2.1
                                  have p7411_2 := h7411c.2.2.1
                                  have p7411_3 := h7411c.2.2.2
                                  linarith only [h7191, hlam, p7411_0]
                                · have p7411_0 := h7411c.1
                                  have p7411_1 := h7411c.2.1
                                  have p7411_2 := h7411c.2.2.1
                                  have p7411_3 := h7411c.2.2.2
                                  linarith only [h7193, hlam, p7411_0]
                                · have p7411_0 := h7411c.1
                                  have p7411_1 := h7411c.2.1
                                  have p7411_2 := h7411c.2.2.1
                                  have p7411_3 := h7411c.2.2.2
                                  linarith only [h4, hlam, p7411_0]
                                · have p7411_0 := h7411c.1
                                  have p7411_1 := h7411c.2.1
                                  have p7411_2 := h7411c.2.2.1
                                  have p7411_3 := h7411c.2.2.2
                                  linarith only [h4, h5823, h6194, h7396, hc12, hc34, hlam, hphi, ht23, p7411_1]
                                · have p7411_0 := h7411c.1
                                  have p7411_1 := h7411c.2.1
                                  have p7411_2 := h7411c.2.2.1
                                  have p7411_3 := h7411c.2.2.2
                                  linarith only [hlam, p7411_0]
                                · have p7411_0 := h7411c.1
                                  have p7411_1 := h7411c.2.1
                                  have p7411_2 := h7411c.2.2.1
                                  have p7411_3 := h7411c.2.2.2
                                  linarith only [h7391, hlam, p7411_0]
                                · have p7411_0 := h7411c.1
                                  have p7411_1 := h7411c.2.1
                                  have p7411_2 := h7411c.2.2.1
                                  have p7411_3 := h7411c.2.2.2
                                  linarith only [h7393, hlam, p7411_0]
                                · have p7411_0 := h7411c.1
                                  have p7411_1 := h7411c.2.1
                                  have p7411_2 := h7411c.2.2.1
                                  have p7411_3 := h7411c.2.2.2
                                  linarith only [h4, h6194, hc12, hc34, hlam, hphi, ht23, p7411_1]
                                · have p7411_0 := h7411c.1
                                  have p7411_1 := h7411c.2.1
                                  have p7411_2 := h7411c.2.2.1
                                  have p7411_3 := h7411c.2.2.2
                                  rcases p7411_3 (m.d 0 3) (by simp) with h7428 | h7428
                                  · linarith only [h7, h7428, hlam]
                                  · linarith only [h1, h7428, hlam]
                                · have p7411_0 := h7411c.1
                                  have p7411_1 := h7411c.2.1
                                  have p7411_2 := h7411c.2.2.1
                                  have p7411_3 := h7411c.2.2.2
                                  linarith only [h6194, hc12, hc34, hlam, hphi, ht23, p7411_1]
                                · have p7411_0 := h7411c.1
                                  have p7411_1 := h7411c.2.1
                                  have p7411_2 := h7411c.2.2.1
                                  have p7411_3 := h7411c.2.2.2
                                  linarith only [hlam, p7411_0]
                                · have p7411_0 := h7411c.1
                                  have p7411_1 := h7411c.2.1
                                  have p7411_2 := h7411c.2.2.1
                                  have p7411_3 := h7411c.2.2.2
                                  linarith only [h4, h5823, h6194, hc12, hc34, hlam, hphi, ht23, p7411_1]
                                · have p7411_0 := h7411c.1
                                  have p7411_1 := h7411c.2.1
                                  have p7411_2 := h7411c.2.2.1
                                  have p7411_3 := h7411c.2.2.2
                                  linarith only [h4, h6194, hc12, hc35, hlam, hphi, ht23, p7411_1]
                                · have p7411_0 := h7411c.1
                                  have p7411_1 := h7411c.2.1
                                  have p7411_2 := h7411c.2.2.1
                                  have p7411_3 := h7411c.2.2.2
                                  rcases p7411_3 (m.d 0 3) (by simp) with h7435 | h7435
                                  · linarith only [h5823, h7435, hlam]
                                  · linarith only [h1, h7435, hlam]
                                · have p7411_0 := h7411c.1
                                  have p7411_1 := h7411c.2.1
                                  have p7411_2 := h7411c.2.2.1
                                  have p7411_3 := h7411c.2.2.2
                                  linarith only [h6194, h7396, hc12, hc34, hlam, hphi, ht23, p7411_1]
                                · have p7411_0 := h7411c.1
                                  have p7411_1 := h7411c.2.1
                                  have p7411_2 := h7411c.2.2.1
                                  have p7411_3 := h7411c.2.2.2
                                  linarith only [h7396, hlam, p7411_0]
                                · have p7411_0 := h7411c.1
                                  have p7411_1 := h7411c.2.1
                                  have p7411_2 := h7411c.2.2.1
                                  have p7411_3 := h7411c.2.2.2
                                  linarith only [hlam, p7411_0]
                      · linarith only [h7402, hlam, p7397_0]
                    · have p7397_0 := h7397c.1
                      have p7397_1 := h7397c.2.1
                      have p7397_2 := h7397c.2.2.1
                      have p7397_3 := h7397c.2.2.2
                      linarith only [h0, hlam, p7397_0]
                    · have p7397_0 := h7397c.1
                      have p7397_1 := h7397c.2.1
                      have p7397_2 := h7397c.2.2.1
                      have p7397_3 := h7397c.2.2.2
                      linarith only [hlam, p7397_0]
                    · have p7397_0 := h7397c.1
                      have p7397_1 := h7397c.2.1
                      have p7397_2 := h7397c.2.2.1
                      have p7397_3 := h7397c.2.2.2
                      linarith only [h6194, hlam, p7397_0]
                    · have p7397_0 := h7397c.1
                      have p7397_1 := h7397c.2.1
                      have p7397_2 := h7397c.2.2.1
                      have p7397_3 := h7397c.2.2.2
                      linarith only [h7177, hlam, p7397_0]
                    · have p7397_0 := h7397c.1
                      have p7397_1 := h7397c.2.1
                      have p7397_2 := h7397c.2.2.1
                      have p7397_3 := h7397c.2.2.2
                      linarith only [h7185, hlam, p7397_0]
                    · have p7397_0 := h7397c.1
                      have p7397_1 := h7397c.2.1
                      have p7397_2 := h7397c.2.2.1
                      have p7397_3 := h7397c.2.2.2
                      linarith only [h1, hlam, p7397_0]
                    · have p7397_0 := h7397c.1
                      have p7397_1 := h7397c.2.1
                      have p7397_2 := h7397c.2.2.1
                      have p7397_3 := h7397c.2.2.2
                      linarith only [h0, h5, h7191, h7195, h7395, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7397_1]
                    · have p7397_0 := h7397c.1
                      have p7397_1 := h7397c.2.1
                      have p7397_2 := h7397c.2.2.1
                      have p7397_3 := h7397c.2.2.2
                      linarith only [hlam, p7397_0]
                    · have p7397_0 := h7397c.1
                      have p7397_1 := h7397c.2.1
                      have p7397_2 := h7397c.2.2.1
                      have p7397_3 := h7397c.2.2.2
                      linarith only [h7191, hlam, p7397_1]
                    · have p7397_0 := h7397c.1
                      have p7397_1 := h7397c.2.1
                      have p7397_2 := h7397c.2.2.1
                      have p7397_3 := h7397c.2.2.2
                      linarith only [h7193, hlam, p7397_1]
                    · have p7397_0 := h7397c.1
                      have p7397_1 := h7397c.2.1
                      have p7397_2 := h7397c.2.2.1
                      have p7397_3 := h7397c.2.2.2
                      linarith only [h2, hlam, p7397_0]
                    · have p7397_0 := h7397c.1
                      have p7397_1 := h7397c.2.1
                      have p7397_2 := h7397c.2.2.1
                      have p7397_3 := h7397c.2.2.2
                      linarith only [h0, h5, h7195, h7395, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7397_1]
                    · have p7397_0 := h7397c.1
                      have p7397_1 := h7397c.2.1
                      have p7397_2 := h7397c.2.2.1
                      have p7397_3 := h7397c.2.2.2
                      linarith only [h0, h5, h7195, h7395, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p7397_1]
                    · have p7397_0 := h7397c.1
                      have p7397_1 := h7397c.2.1
                      have p7397_2 := h7397c.2.2.1
                      have p7397_3 := h7397c.2.2.2
                      linarith only [hlam, p7397_0]
                    · have p7397_0 := h7397c.1
                      have p7397_1 := h7397c.2.1
                      have p7397_2 := h7397c.2.2.1
                      have p7397_3 := h7397c.2.2.2
                      linarith only [h7195, hlam, p7397_1]
                    · have p7397_0 := h7397c.1
                      have p7397_1 := h7397c.2.1
                      have p7397_2 := h7397c.2.2.1
                      have p7397_3 := h7397c.2.2.2
                      linarith only [h3, hlam, p7397_0]
                    · have p7397_0 := h7397c.1
                      have p7397_1 := h7397c.2.1
                      have p7397_2 := h7397c.2.2.1
                      have p7397_3 := h7397c.2.2.2
                      linarith only [h0, h5, h7195, h7395, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7397_1]
                    · have p7397_0 := h7397c.1
                      have p7397_1 := h7397c.2.1
                      have p7397_2 := h7397c.2.2.1
                      have p7397_3 := h7397c.2.2.2
                      linarith only [h0, h5, h6194, h7195, h7395, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7397_1]
                    · have p7397_0 := h7397c.1
                      have p7397_1 := h7397c.2.1
                      have p7397_2 := h7397c.2.2.1
                      have p7397_3 := h7397c.2.2.2
                      linarith only [h0, h5, h7195, h7395, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p7397_1]
                    · have p7397_0 := h7397c.1
                      have p7397_1 := h7397c.2.1
                      have p7397_2 := h7397c.2.2.1
                      have p7397_3 := h7397c.2.2.2
                      linarith only [hlam, p7397_0]
                  · linarith only [h0, h4, h5, h6194, h7, h7395, h7396, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h6193, h7, h7177, h7395, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 16094000 in
set_option maxHeartbeats 16094000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s6_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h5823 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h6193 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 2 3 (by decide) (by decide) with h6194 | h6194
  · exact r1l7_11_13_25_L_I_L_I_H_I_s6_x1_x1_x0_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h5823 h6193 h6194
  · exact r1l7_11_13_25_L_I_L_I_H_I_s6_x1_x1_x0_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h5823 h6193 h6194

end R2N4
