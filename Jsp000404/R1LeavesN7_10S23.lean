import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 14456000 in
set_option maxHeartbeats 14456000 in
theorem r1l7_12_24_L_I_H_I_s6_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h6874 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6875 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6876 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6877 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6878 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6879 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  rcases m.htr 1 2 3 (by decide) (by decide) with h6880 | h6880
  · rcases m.htr 1 2 4 (by decide) (by decide) with h6881 | h6881
    · rcases m.htr 1 2 5 (by decide) (by decide) with h6882 | h6882
      · rcases m.htr 1 3 4 (by decide) (by decide) with h6883 | h6883
        · rcases m.htr 1 4 5 (by decide) (by decide) with h6884 | h6884
          · rcases m.htr 2 3 4 (by decide) (by decide) with h6885 | h6885
            · rcases m.htr 2 3 5 (by decide) (by decide) with h6886 | h6886
              · rcases m.htr 2 4 5 (by decide) (by decide) with h6887 | h6887
                · rcases m.htr 3 4 5 (by decide) (by decide) with h6888 | h6888
                  · rcases h2bigk with h6889c | h6889c | h6889c | h6889c | h6889c | h6889c | h6889c | h6889c | h6889c | h6889c | h6889c | h6889c | h6889c | h6889c | h6889c | h6889c | h6889c | h6889c | h6889c | h6889c | h6889c | h6889c | h6889c | h6889c | h6889c
                    · have p6889_0 := h6889c.1
                      have p6889_1 := h6889c.2.1
                      have p6889_2 := h6889c.2.2.1
                      have p6889_3 := h6889c.2.2.2
                      linarith only [hlam, p6889_0]
                    · have p6889_0 := h6889c.1
                      have p6889_1 := h6889c.2.1
                      have p6889_2 := h6889c.2.2.1
                      have p6889_3 := h6889c.2.2.2
                      linarith only [h0, hlam, p6889_0]
                    · have p6889_0 := h6889c.1
                      have p6889_1 := h6889c.2.1
                      have p6889_2 := h6889c.2.2.1
                      have p6889_3 := h6889c.2.2.2
                      linarith only [h6885, h6888, hc02, hc45, hlam, hphi, ht0b, ht5b, p6889_1]
                    · have p6889_0 := h6889c.1
                      have p6889_1 := h6889c.2.1
                      have p6889_2 := h6889c.2.2.1
                      have p6889_3 := h6889c.2.2.2
                      rcases p6889_3 (m.d 0 2) (by simp) with h6893 | h6893
                      · rcases p6889_3 (m.d 1 2) (by simp) with h6894 | h6894
                        · rcases p6889_3 (m.d 2 3) (by simp) with h6895 | h6895
                          · linarith only [h6875, h6895, hlam]
                          · linarith only [h6885, h6895, hlam]
                        · linarith only [h6881, h6894, hlam]
                      · linarith only [h6893, hlam, p6889_0]
                    · have p6889_0 := h6889c.1
                      have p6889_1 := h6889c.2.1
                      have p6889_2 := h6889c.2.2.1
                      have p6889_3 := h6889c.2.2.2
                      rcases p6889_3 (m.d 0 2) (by simp) with h6900 | h6900
                      · rcases p6889_3 (m.d 1 2) (by simp) with h6901 | h6901
                        · rcases p6889_3 (m.d 2 3) (by simp) with h6902 | h6902
                          · linarith only [h6875, h6902, hlam]
                          · linarith only [h6886, h6902, hlam]
                        · linarith only [h6882, h6901, hlam]
                      · linarith only [h6900, hlam, p6889_0]
                    · have p6889_0 := h6889c.1
                      have p6889_1 := h6889c.2.1
                      have p6889_2 := h6889c.2.2.1
                      have p6889_3 := h6889c.2.2.2
                      linarith only [h0, h6874, h6881, h6885, h6888, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6889_1]
                    · have p6889_0 := h6889c.1
                      have p6889_1 := h6889c.2.1
                      have p6889_2 := h6889c.2.2.1
                      have p6889_3 := h6889c.2.2.2
                      linarith only [hlam, p6889_0]
                    · have p6889_0 := h6889c.1
                      have p6889_1 := h6889c.2.1
                      have p6889_2 := h6889c.2.2.1
                      have p6889_3 := h6889c.2.2.2
                      linarith only [h6885, h6888, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6889_1]
                    · have p6889_0 := h6889c.1
                      have p6889_1 := h6889c.2.1
                      have p6889_2 := h6889c.2.2.1
                      have p6889_3 := h6889c.2.2.2
                      rcases p6889_3 (m.d 0 2) (by simp) with h6910 | h6910
                      · linarith only [h0, h6910, hlam]
                      · linarith only [h6876, h6910, hlam]
                    · have p6889_0 := h6889c.1
                      have p6889_1 := h6889c.2.1
                      have p6889_2 := h6889c.2.2.1
                      have p6889_3 := h6889c.2.2.2
                      rcases p6889_3 (m.d 0 2) (by simp) with h6913 | h6913
                      · linarith only [h0, h6913, hlam]
                      · linarith only [h6877, h6913, hlam]
                    · have p6889_0 := h6889c.1
                      have p6889_1 := h6889c.2.1
                      have p6889_2 := h6889c.2.2.1
                      have p6889_3 := h6889c.2.2.2
                      linarith only [h6875, hlam, p6889_0]
                    · have p6889_0 := h6889c.1
                      have p6889_1 := h6889c.2.1
                      have p6889_2 := h6889c.2.2.1
                      have p6889_3 := h6889c.2.2.2
                      linarith only [h6880, hlam, p6889_0]
                    · have p6889_0 := h6889c.1
                      have p6889_1 := h6889c.2.1
                      have p6889_2 := h6889c.2.2.1
                      have p6889_3 := h6889c.2.2.2
                      linarith only [hlam, p6889_0]
                    · have p6889_0 := h6889c.1
                      have p6889_1 := h6889c.2.1
                      have p6889_2 := h6889c.2.2.1
                      have p6889_3 := h6889c.2.2.2
                      linarith only [h6875, h6885, h6888, hc02, hc45, hlam, hphi, ht0b, ht5b, p6889_1]
                    · have p6889_0 := h6889c.1
                      have p6889_1 := h6889c.2.1
                      have p6889_2 := h6889c.2.2.1
                      have p6889_3 := h6889c.2.2.2
                      rcases p6889_3 (m.d 0 2) (by simp) with h6920 | h6920
                      · rcases p6889_3 (m.d 1 2) (by simp) with h6921 | h6921
                        · rcases p6889_3 (m.d 2 3) (by simp) with h6922 | h6922
                          · rcases p6889_3 (m.d 2 4) (by simp) with h6923 | h6923
                            · linarith only [h6885, h6923, hlam]
                            · linarith only [h6887, h6923, hlam]
                          · linarith only [h6886, h6922, hlam]
                        · linarith only [h6882, h6921, hlam]
                      · linarith only [h6877, h6920, hlam]
                    · have p6889_0 := h6889c.1
                      have p6889_1 := h6889c.2.1
                      have p6889_2 := h6889c.2.2.1
                      have p6889_3 := h6889c.2.2.2
                      linarith only [h6876, hlam, p6889_0]
                    · have p6889_0 := h6889c.1
                      have p6889_1 := h6889c.2.1
                      have p6889_2 := h6889c.2.2.1
                      have p6889_3 := h6889c.2.2.2
                      linarith only [h6881, hlam, p6889_0]
                    · have p6889_0 := h6889c.1
                      have p6889_1 := h6889c.2.1
                      have p6889_2 := h6889c.2.2.1
                      have p6889_3 := h6889c.2.2.2
                      linarith only [h6885, hlam, p6889_0]
                    · have p6889_0 := h6889c.1
                      have p6889_1 := h6889c.2.1
                      have p6889_2 := h6889c.2.2.1
                      have p6889_3 := h6889c.2.2.2
                      linarith only [hlam, p6889_0]
                    · have p6889_0 := h6889c.1
                      have p6889_1 := h6889c.2.1
                      have p6889_2 := h6889c.2.2.1
                      have p6889_3 := h6889c.2.2.2
                      linarith only [h0, h6874, h6881, h6886, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p6889_1]
                    · have p6889_0 := h6889c.1
                      have p6889_1 := h6889c.2.1
                      have p6889_2 := h6889c.2.2.1
                      have p6889_3 := h6889c.2.2.2
                      linarith only [h6877, hlam, p6889_0]
                    · have p6889_0 := h6889c.1
                      have p6889_1 := h6889c.2.1
                      have p6889_2 := h6889c.2.2.1
                      have p6889_3 := h6889c.2.2.2
                      linarith only [h6882, hlam, p6889_0]
                    · have p6889_0 := h6889c.1
                      have p6889_1 := h6889c.2.1
                      have p6889_2 := h6889c.2.2.1
                      have p6889_3 := h6889c.2.2.2
                      linarith only [h6886, hlam, p6889_0]
                    · have p6889_0 := h6889c.1
                      have p6889_1 := h6889c.2.1
                      have p6889_2 := h6889c.2.2.1
                      have p6889_3 := h6889c.2.2.2
                      linarith only [h6887, hlam, p6889_1]
                    · have p6889_0 := h6889c.1
                      have p6889_1 := h6889c.2.1
                      have p6889_2 := h6889c.2.2.1
                      have p6889_3 := h6889c.2.2.2
                      linarith only [hlam, p6889_0]
                  · linarith only [h0, h6874, h6884, h6888, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h0, h6874, h6884, h6887, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h6941 | h6941
                · linarith only [h6885, h6886, h6941, hlam]
                · linarith only [h0, h6874, h6884, h6941, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h6944 | h6944
              · linarith only [h0, h6874, h6883, h6885, h6944, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h6946 | h6946
                · rcases m.htr 3 4 5 (by decide) (by decide) with h6947 | h6947
                  · rcases h2bigk with h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c
                    · have p6948_0 := h6948c.1
                      have p6948_1 := h6948c.2.1
                      have p6948_2 := h6948c.2.2.1
                      have p6948_3 := h6948c.2.2.2
                      linarith only [hlam, p6948_0]
                    · have p6948_0 := h6948c.1
                      have p6948_1 := h6948c.2.1
                      have p6948_2 := h6948c.2.2.1
                      have p6948_3 := h6948c.2.2.2
                      linarith only [h0, hlam, p6948_0]
                    · have p6948_0 := h6948c.1
                      have p6948_1 := h6948c.2.1
                      have p6948_2 := h6948c.2.2.1
                      have p6948_3 := h6948c.2.2.2
                      rcases p6948_3 (m.d 0 2) (by simp) with h6951 | h6951
                      · rcases p6948_3 (m.d 1 2) (by simp) with h6952 | h6952
                        · rcases p6948_3 (m.d 2 3) (by simp) with h6953 | h6953
                          · linarith only [h6953, hlam, p6948_0]
                          · rcases p6948_3 (m.d 2 4) (by simp) with h6955 | h6955
                            · linarith only [h6876, h6955, hlam]
                            · linarith only [h6885, h6955, hlam]
                        · linarith only [h6880, h6952, hlam]
                      · linarith only [h6951, hlam, p6948_0]
                    · have p6948_0 := h6948c.1
                      have p6948_1 := h6948c.2.1
                      have p6948_2 := h6948c.2.2.1
                      have p6948_3 := h6948c.2.2.2
                      rcases p6948_3 (m.d 0 2) (by simp) with h6960 | h6960
                      · rcases p6948_3 (m.d 1 2) (by simp) with h6961 | h6961
                        · rcases p6948_3 (m.d 2 3) (by simp) with h6962 | h6962
                          · linarith only [h6875, h6962, hlam]
                          · rcases p6948_3 (m.d 2 4) (by simp) with h6964 | h6964
                            · linarith only [h6964, hlam, p6948_0]
                            · rcases p6948_3 (m.d 2 5) (by simp) with h6966 | h6966
                              · linarith only [h6877, h6966, hlam]
                              · rcases h4bigk with h6968c | h6968c | h6968c | h6968c | h6968c | h6968c | h6968c | h6968c | h6968c | h6968c | h6968c | h6968c | h6968c | h6968c | h6968c | h6968c | h6968c | h6968c | h6968c | h6968c | h6968c | h6968c | h6968c | h6968c | h6968c
                                · have p6968_0 := h6968c.1
                                  have p6968_1 := h6968c.2.1
                                  have p6968_2 := h6968c.2.2.1
                                  have p6968_3 := h6968c.2.2.2
                                  linarith only [hlam, p6968_0]
                                · have p6968_0 := h6968c.1
                                  have p6968_1 := h6968c.2.1
                                  have p6968_2 := h6968c.2.2.1
                                  have p6968_3 := h6968c.2.2.2
                                  linarith only [h0, h6874, h6883, h6944, h6947, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6968_1]
                                · have p6968_0 := h6968c.1
                                  have p6968_1 := h6968c.2.1
                                  have p6968_2 := h6968c.2.2.1
                                  have p6968_3 := h6968c.2.2.2
                                  linarith only [h0, h6874, h6946, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6968_1]
                                · have p6968_0 := h6968c.1
                                  have p6968_1 := h6968c.2.1
                                  have p6968_2 := h6968c.2.2.1
                                  have p6968_3 := h6968c.2.2.2
                                  linarith only [h0, h6874, h6944, h6947, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6968_1]
                                · have p6968_0 := h6968c.1
                                  have p6968_1 := h6968c.2.1
                                  have p6968_2 := h6968c.2.2.1
                                  have p6968_3 := h6968c.2.2.2
                                  linarith only [h0, h6874, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6968_1]
                                · have p6968_0 := h6968c.1
                                  have p6968_1 := h6968c.2.1
                                  have p6968_2 := h6968c.2.2.1
                                  have p6968_3 := h6968c.2.2.2
                                  linarith only [h6874, hlam, p6968_0]
                                · have p6968_0 := h6968c.1
                                  have p6968_1 := h6968c.2.1
                                  have p6968_2 := h6968c.2.2.1
                                  have p6968_3 := h6968c.2.2.2
                                  linarith only [hlam, p6968_0]
                                · have p6968_0 := h6968c.1
                                  have p6968_1 := h6968c.2.1
                                  have p6968_2 := h6968c.2.2.1
                                  have p6968_3 := h6968c.2.2.2
                                  linarith only [h6946, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p6968_1]
                                · have p6968_0 := h6968c.1
                                  have p6968_1 := h6968c.2.1
                                  have p6968_2 := h6968c.2.2.1
                                  have p6968_3 := h6968c.2.2.2
                                  linarith only [h0, h6874, h6944, h6947, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6968_1]
                                · have p6968_0 := h6968c.1
                                  have p6968_1 := h6968c.2.1
                                  have p6968_2 := h6968c.2.2.1
                                  have p6968_3 := h6968c.2.2.2
                                  linarith only [h0, h6874, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6968_1]
                                · have p6968_0 := h6968c.1
                                  have p6968_1 := h6968c.2.1
                                  have p6968_2 := h6968c.2.2.1
                                  have p6968_3 := h6968c.2.2.2
                                  linarith only [h6876, hlam, p6968_0]
                                · have p6968_0 := h6968c.1
                                  have p6968_1 := h6968c.2.1
                                  have p6968_2 := h6968c.2.2.1
                                  have p6968_3 := h6968c.2.2.2
                                  linarith only [h6881, hlam, p6968_0]
                                · have p6968_0 := h6968c.1
                                  have p6968_1 := h6968c.2.1
                                  have p6968_2 := h6968c.2.2.1
                                  have p6968_3 := h6968c.2.2.2
                                  linarith only [hlam, p6968_0]
                                · have p6968_0 := h6968c.1
                                  have p6968_1 := h6968c.2.1
                                  have p6968_2 := h6968c.2.2.1
                                  have p6968_3 := h6968c.2.2.2
                                  linarith only [h6885, hlam, p6968_1]
                                · have p6968_0 := h6968c.1
                                  have p6968_1 := h6968c.2.1
                                  have p6968_2 := h6968c.2.2.1
                                  have p6968_3 := h6968c.2.2.2
                                  linarith only [hc02, hc45, hlam, hphi, ht0b, ht5b, p6948_1, p6968_1]
                                · have p6968_0 := h6968c.1
                                  have p6968_1 := h6968c.2.1
                                  have p6968_2 := h6968c.2.2.1
                                  have p6968_3 := h6968c.2.2.2
                                  linarith only [h6878, hlam, p6968_0]
                                · have p6968_0 := h6968c.1
                                  have p6968_1 := h6968c.2.1
                                  have p6968_2 := h6968c.2.2.1
                                  have p6968_3 := h6968c.2.2.2
                                  linarith only [h6883, hlam, p6968_0]
                                · have p6968_0 := h6968c.1
                                  have p6968_1 := h6968c.2.1
                                  have p6968_2 := h6968c.2.2.1
                                  have p6968_3 := h6968c.2.2.2
                                  linarith only [h6883, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p6968_1]
                                · have p6968_0 := h6968c.1
                                  have p6968_1 := h6968c.2.1
                                  have p6968_2 := h6968c.2.2.1
                                  have p6968_3 := h6968c.2.2.2
                                  linarith only [hlam, p6968_0]
                                · have p6968_0 := h6968c.1
                                  have p6968_1 := h6968c.2.1
                                  have p6968_2 := h6968c.2.2.1
                                  have p6968_3 := h6968c.2.2.2
                                  linarith only [h0, h6874, h6883, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6968_1]
                                · have p6968_0 := h6968c.1
                                  have p6968_1 := h6968c.2.1
                                  have p6968_2 := h6968c.2.2.1
                                  have p6968_3 := h6968c.2.2.2
                                  linarith only [h6879, hlam, p6968_0]
                                · have p6968_0 := h6968c.1
                                  have p6968_1 := h6968c.2.1
                                  have p6968_2 := h6968c.2.2.1
                                  have p6968_3 := h6968c.2.2.2
                                  linarith only [h6884, hlam, p6968_0]
                                · have p6968_0 := h6968c.1
                                  have p6968_1 := h6968c.2.1
                                  have p6968_2 := h6968c.2.2.1
                                  have p6968_3 := h6968c.2.2.2
                                  linarith only [h6946, hlam, p6968_0]
                                · have p6968_0 := h6968c.1
                                  have p6968_1 := h6968c.2.1
                                  have p6968_2 := h6968c.2.2.1
                                  have p6968_3 := h6968c.2.2.2
                                  linarith only [h6947, hlam, p6968_0]
                                · have p6968_0 := h6968c.1
                                  have p6968_1 := h6968c.2.1
                                  have p6968_2 := h6968c.2.2.1
                                  have p6968_3 := h6968c.2.2.2
                                  linarith only [hlam, p6968_0]
                        · linarith only [h6881, h6961, hlam]
                      · linarith only [h6960, hlam, p6948_0]
                    · have p6948_0 := h6948c.1
                      have p6948_1 := h6948c.2.1
                      have p6948_2 := h6948c.2.2.1
                      have p6948_3 := h6948c.2.2.2
                      rcases p6948_3 (m.d 0 2) (by simp) with h6996 | h6996
                      · rcases p6948_3 (m.d 1 2) (by simp) with h6997 | h6997
                        · rcases p6948_3 (m.d 2 3) (by simp) with h6998 | h6998
                          · linarith only [h6875, h6998, hlam]
                          · rcases p6948_3 (m.d 2 4) (by simp) with h7000 | h7000
                            · linarith only [h6876, h7000, hlam]
                            · linarith only [h6946, h7000, hlam]
                        · linarith only [h6882, h6997, hlam]
                      · linarith only [h6996, hlam, p6948_0]
                    · have p6948_0 := h6948c.1
                      have p6948_1 := h6948c.2.1
                      have p6948_2 := h6948c.2.2.1
                      have p6948_3 := h6948c.2.2.2
                      linarith only [h6876, h6946, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6948_1]
                    · have p6948_0 := h6948c.1
                      have p6948_1 := h6948c.2.1
                      have p6948_2 := h6948c.2.2.1
                      have p6948_3 := h6948c.2.2.2
                      linarith only [hlam, p6948_0]
                    · have p6948_0 := h6948c.1
                      have p6948_1 := h6948c.2.1
                      have p6948_2 := h6948c.2.2.1
                      have p6948_3 := h6948c.2.2.2
                      linarith only [h0, h6874, h6883, h6885, hlam, p6948_2]
                    · have p6948_0 := h6948c.1
                      have p6948_1 := h6948c.2.1
                      have p6948_2 := h6948c.2.2.1
                      have p6948_3 := h6948c.2.2.2
                      rcases p6948_3 (m.d 0 2) (by simp) with h7008 | h7008
                      · linarith only [h0, h7008, hlam]
                      · linarith only [h6876, h7008, hlam]
                    · have p6948_0 := h6948c.1
                      have p6948_1 := h6948c.2.1
                      have p6948_2 := h6948c.2.2.1
                      have p6948_3 := h6948c.2.2.2
                      rcases p6948_3 (m.d 0 2) (by simp) with h7011 | h7011
                      · linarith only [h0, h7011, hlam]
                      · linarith only [h6877, h7011, hlam]
                    · have p6948_0 := h6948c.1
                      have p6948_1 := h6948c.2.1
                      have p6948_2 := h6948c.2.2.1
                      have p6948_3 := h6948c.2.2.2
                      linarith only [h6875, hlam, p6948_0]
                    · have p6948_0 := h6948c.1
                      have p6948_1 := h6948c.2.1
                      have p6948_2 := h6948c.2.2.1
                      have p6948_3 := h6948c.2.2.2
                      linarith only [h6880, hlam, p6948_0]
                    · have p6948_0 := h6948c.1
                      have p6948_1 := h6948c.2.1
                      have p6948_2 := h6948c.2.2.1
                      have p6948_3 := h6948c.2.2.2
                      linarith only [hlam, p6948_0]
                    · have p6948_0 := h6948c.1
                      have p6948_1 := h6948c.2.1
                      have p6948_2 := h6948c.2.2.1
                      have p6948_3 := h6948c.2.2.2
                      linarith only [h6885, hlam, p6948_1]
                    · have p6948_0 := h6948c.1
                      have p6948_1 := h6948c.2.1
                      have p6948_2 := h6948c.2.2.1
                      have p6948_3 := h6948c.2.2.2
                      linarith only [h6944, hlam, p6948_1]
                    · have p6948_0 := h6948c.1
                      have p6948_1 := h6948c.2.1
                      have p6948_2 := h6948c.2.2.1
                      have p6948_3 := h6948c.2.2.2
                      linarith only [h6876, hlam, p6948_0]
                    · have p6948_0 := h6948c.1
                      have p6948_1 := h6948c.2.1
                      have p6948_2 := h6948c.2.2.1
                      have p6948_3 := h6948c.2.2.2
                      linarith only [h6881, hlam, p6948_0]
                    · have p6948_0 := h6948c.1
                      have p6948_1 := h6948c.2.1
                      have p6948_2 := h6948c.2.2.1
                      have p6948_3 := h6948c.2.2.2
                      linarith only [h0, h6874, h6881, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6948_1]
                    · have p6948_0 := h6948c.1
                      have p6948_1 := h6948c.2.1
                      have p6948_2 := h6948c.2.2.1
                      have p6948_3 := h6948c.2.2.2
                      linarith only [hlam, p6948_0]
                    · have p6948_0 := h6948c.1
                      have p6948_1 := h6948c.2.1
                      have p6948_2 := h6948c.2.2.1
                      have p6948_3 := h6948c.2.2.2
                      linarith only [h0, h6874, h6881, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p6948_1]
                    · have p6948_0 := h6948c.1
                      have p6948_1 := h6948c.2.1
                      have p6948_2 := h6948c.2.2.1
                      have p6948_3 := h6948c.2.2.2
                      linarith only [h6877, hlam, p6948_0]
                    · have p6948_0 := h6948c.1
                      have p6948_1 := h6948c.2.1
                      have p6948_2 := h6948c.2.2.1
                      have p6948_3 := h6948c.2.2.2
                      linarith only [h6882, hlam, p6948_0]
                    · have p6948_0 := h6948c.1
                      have p6948_1 := h6948c.2.1
                      have p6948_2 := h6948c.2.2.1
                      have p6948_3 := h6948c.2.2.2
                      linarith only [h0, h6874, h6882, h6884, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6948_1]
                    · have p6948_0 := h6948c.1
                      have p6948_1 := h6948c.2.1
                      have p6948_2 := h6948c.2.2.1
                      have p6948_3 := h6948c.2.2.2
                      linarith only [h6946, hlam, p6948_1]
                    · have p6948_0 := h6948c.1
                      have p6948_1 := h6948c.2.1
                      have p6948_2 := h6948c.2.2.1
                      have p6948_3 := h6948c.2.2.2
                      linarith only [hlam, p6948_0]
                  · linarith only [h0, h6874, h6884, h6885, h6947, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h0, h6874, h6884, h6885, h6946, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h7031 | h7031
            · rcases m.htr 2 3 5 (by decide) (by decide) with h7032 | h7032
              · rcases m.htr 2 4 5 (by decide) (by decide) with h7033 | h7033
                · linarith only [h6881, h6884, h7033, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h7035 | h7035
                  · linarith only [h6875, h6884, h7031, h7035, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases h2bigk with h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c | h7037c
                    · have p7037_0 := h7037c.1
                      have p7037_1 := h7037c.2.1
                      have p7037_2 := h7037c.2.2.1
                      have p7037_3 := h7037c.2.2.2
                      linarith only [hlam, p7037_0]
                    · have p7037_0 := h7037c.1
                      have p7037_1 := h7037c.2.1
                      have p7037_2 := h7037c.2.2.1
                      have p7037_3 := h7037c.2.2.2
                      linarith only [h0, hlam, p7037_0]
                    · have p7037_0 := h7037c.1
                      have p7037_1 := h7037c.2.1
                      have p7037_2 := h7037c.2.2.1
                      have p7037_3 := h7037c.2.2.2
                      rcases p7037_3 (m.d 0 2) (by simp) with h7040 | h7040
                      · rcases p7037_3 (m.d 1 2) (by simp) with h7041 | h7041
                        · rcases p7037_3 (m.d 2 3) (by simp) with h7042 | h7042
                          · linarith only [h7042, hlam, p7037_0]
                          · rcases p7037_3 (m.d 2 4) (by simp) with h7044 | h7044
                            · linarith only [h6876, h7044, hlam]
                            · rcases p7037_3 (m.d 2 5) (by simp) with h7046 | h7046
                              · linarith only [h6877, h7046, hlam]
                              · rcases h4bigk with h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c | h7048c
                                · have p7048_0 := h7048c.1
                                  have p7048_1 := h7048c.2.1
                                  have p7048_2 := h7048c.2.2.1
                                  have p7048_3 := h7048c.2.2.2
                                  linarith only [hlam, p7048_0]
                                · have p7048_0 := h7048c.1
                                  have p7048_1 := h7048c.2.1
                                  have p7048_2 := h7048c.2.2.1
                                  have p7048_3 := h7048c.2.2.2
                                  linarith only [h0, h6874, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p7048_1]
                                · have p7048_0 := h7048c.1
                                  have p7048_1 := h7048c.2.1
                                  have p7048_2 := h7048c.2.2.1
                                  have p7048_3 := h7048c.2.2.2
                                  linarith only [h0, h6874, h7031, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7048_1]
                                · have p7048_0 := h7048c.1
                                  have p7048_1 := h7048c.2.1
                                  have p7048_2 := h7048c.2.2.1
                                  have p7048_3 := h7048c.2.2.2
                                  linarith only [h0, h6874, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7048_1]
                                · have p7048_0 := h7048c.1
                                  have p7048_1 := h7048c.2.1
                                  have p7048_2 := h7048c.2.2.1
                                  have p7048_3 := h7048c.2.2.2
                                  linarith only [h0, h6874, h6884, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p7048_1]
                                · have p7048_0 := h7048c.1
                                  have p7048_1 := h7048c.2.1
                                  have p7048_2 := h7048c.2.2.1
                                  have p7048_3 := h7048c.2.2.2
                                  linarith only [h6874, hlam, p7048_0]
                                · have p7048_0 := h7048c.1
                                  have p7048_1 := h7048c.2.1
                                  have p7048_2 := h7048c.2.2.1
                                  have p7048_3 := h7048c.2.2.2
                                  linarith only [hlam, p7048_0]
                                · have p7048_0 := h7048c.1
                                  have p7048_1 := h7048c.2.1
                                  have p7048_2 := h7048c.2.2.1
                                  have p7048_3 := h7048c.2.2.2
                                  linarith only [h0, h6874, h7031, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7048_1]
                                · have p7048_0 := h7048c.1
                                  have p7048_1 := h7048c.2.1
                                  have p7048_2 := h7048c.2.2.1
                                  have p7048_3 := h7048c.2.2.2
                                  linarith only [h0, h6874, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7048_1]
                                · have p7048_0 := h7048c.1
                                  have p7048_1 := h7048c.2.1
                                  have p7048_2 := h7048c.2.2.1
                                  have p7048_3 := h7048c.2.2.2
                                  linarith only [h6884, hlam, p7048_0]
                                · have p7048_0 := h7048c.1
                                  have p7048_1 := h7048c.2.1
                                  have p7048_2 := h7048c.2.2.1
                                  have p7048_3 := h7048c.2.2.2
                                  linarith only [h6876, hlam, p7048_0]
                                · have p7048_0 := h7048c.1
                                  have p7048_1 := h7048c.2.1
                                  have p7048_2 := h7048c.2.2.1
                                  have p7048_3 := h7048c.2.2.2
                                  linarith only [h6881, hlam, p7048_0]
                                · have p7048_0 := h7048c.1
                                  have p7048_1 := h7048c.2.1
                                  have p7048_2 := h7048c.2.2.1
                                  have p7048_3 := h7048c.2.2.2
                                  linarith only [hlam, p7048_0]
                                · have p7048_0 := h7048c.1
                                  have p7048_1 := h7048c.2.1
                                  have p7048_2 := h7048c.2.2.1
                                  have p7048_3 := h7048c.2.2.2
                                  linarith only [h6882, h6884, h7033, hc34, hc45, hlam, hphi, p7048_1]
                                · have p7048_0 := h7048c.1
                                  have p7048_1 := h7048c.2.1
                                  have p7048_2 := h7048c.2.2.1
                                  have p7048_3 := h7048c.2.2.2
                                  linarith only [h7033, hlam, p7048_0]
                                · have p7048_0 := h7048c.1
                                  have p7048_1 := h7048c.2.1
                                  have p7048_2 := h7048c.2.2.1
                                  have p7048_3 := h7048c.2.2.2
                                  linarith only [h6878, hlam, p7048_0]
                                · have p7048_0 := h7048c.1
                                  have p7048_1 := h7048c.2.1
                                  have p7048_2 := h7048c.2.2.1
                                  have p7048_3 := h7048c.2.2.2
                                  linarith only [h6883, hlam, p7048_0]
                                · have p7048_0 := h7048c.1
                                  have p7048_1 := h7048c.2.1
                                  have p7048_2 := h7048c.2.2.1
                                  have p7048_3 := h7048c.2.2.2
                                  linarith only [h7031, hlam, p7048_0]
                                · have p7048_0 := h7048c.1
                                  have p7048_1 := h7048c.2.1
                                  have p7048_2 := h7048c.2.2.1
                                  have p7048_3 := h7048c.2.2.2
                                  linarith only [hlam, p7048_0]
                                · have p7048_0 := h7048c.1
                                  have p7048_1 := h7048c.2.1
                                  have p7048_2 := h7048c.2.2.1
                                  have p7048_3 := h7048c.2.2.2
                                  linarith only [h7035, hlam, p7048_0]
                                · have p7048_0 := h7048c.1
                                  have p7048_1 := h7048c.2.1
                                  have p7048_2 := h7048c.2.2.1
                                  have p7048_3 := h7048c.2.2.2
                                  linarith only [h6879, hlam, p7048_0]
                                · have p7048_0 := h7048c.1
                                  have p7048_1 := h7048c.2.1
                                  have p7048_2 := h7048c.2.2.1
                                  have p7048_3 := h7048c.2.2.2
                                  linarith only [h0, h6874, h6879, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p7048_1]
                                · have p7048_0 := h7048c.1
                                  have p7048_1 := h7048c.2.1
                                  have p7048_2 := h7048c.2.2.1
                                  have p7048_3 := h7048c.2.2.2
                                  linarith only [h0, h6874, h6879, h7031, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7048_1]
                                · have p7048_0 := h7048c.1
                                  have p7048_1 := h7048c.2.1
                                  have p7048_2 := h7048c.2.2.1
                                  have p7048_3 := h7048c.2.2.2
                                  linarith only [h0, h6874, h6879, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7048_1]
                                · have p7048_0 := h7048c.1
                                  have p7048_1 := h7048c.2.1
                                  have p7048_2 := h7048c.2.2.1
                                  have p7048_3 := h7048c.2.2.2
                                  linarith only [hlam, p7048_0]
                        · linarith only [h6880, h7041, hlam]
                      · linarith only [h7040, hlam, p7037_0]
                    · have p7037_0 := h7037c.1
                      have p7037_1 := h7037c.2.1
                      have p7037_2 := h7037c.2.2.1
                      have p7037_3 := h7037c.2.2.2
                      rcases p7037_3 (m.d 0 2) (by simp) with h7076 | h7076
                      · rcases p7037_3 (m.d 1 2) (by simp) with h7077 | h7077
                        · rcases p7037_3 (m.d 2 3) (by simp) with h7078 | h7078
                          · linarith only [h6875, h7078, hlam]
                          · linarith only [h7031, h7078, hlam]
                        · linarith only [h6881, h7077, hlam]
                      · linarith only [h7076, hlam, p7037_0]
                    · have p7037_0 := h7037c.1
                      have p7037_1 := h7037c.2.1
                      have p7037_2 := h7037c.2.2.1
                      have p7037_3 := h7037c.2.2.2
                      rcases p7037_3 (m.d 0 2) (by simp) with h7083 | h7083
                      · rcases p7037_3 (m.d 1 2) (by simp) with h7084 | h7084
                        · rcases p7037_3 (m.d 2 3) (by simp) with h7085 | h7085
                          · linarith only [h6875, h7085, hlam]
                          · linarith only [h7032, h7085, hlam]
                        · linarith only [h6882, h7084, hlam]
                      · linarith only [h7083, hlam, p7037_0]
                    · have p7037_0 := h7037c.1
                      have p7037_1 := h7037c.2.1
                      have p7037_2 := h7037c.2.2.1
                      have p7037_3 := h7037c.2.2.2
                      linarith only [h0, h6874, h6879, h6884, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p7037_1]
                    · have p7037_0 := h7037c.1
                      have p7037_1 := h7037c.2.1
                      have p7037_2 := h7037c.2.2.1
                      have p7037_3 := h7037c.2.2.2
                      linarith only [hlam, p7037_0]
                    · have p7037_0 := h7037c.1
                      have p7037_1 := h7037c.2.1
                      have p7037_2 := h7037c.2.2.1
                      have p7037_3 := h7037c.2.2.2
                      rcases p7037_3 (m.d 0 2) (by simp) with h7092 | h7092
                      · linarith only [h0, h7092, hlam]
                      · linarith only [h6875, h7092, hlam]
                    · have p7037_0 := h7037c.1
                      have p7037_1 := h7037c.2.1
                      have p7037_2 := h7037c.2.2.1
                      have p7037_3 := h7037c.2.2.2
                      linarith only [h0, h6874, h6879, h6881, h6884, hlam, p7037_2]
                    · have p7037_0 := h7037c.1
                      have p7037_1 := h7037c.2.1
                      have p7037_2 := h7037c.2.2.1
                      have p7037_3 := h7037c.2.2.2
                      rcases p7037_3 (m.d 0 2) (by simp) with h7096 | h7096
                      · linarith only [h0, h7096, hlam]
                      · linarith only [h6877, h7096, hlam]
                    · have p7037_0 := h7037c.1
                      have p7037_1 := h7037c.2.1
                      have p7037_2 := h7037c.2.2.1
                      have p7037_3 := h7037c.2.2.2
                      linarith only [h6875, hlam, p7037_0]
                    · have p7037_0 := h7037c.1
                      have p7037_1 := h7037c.2.1
                      have p7037_2 := h7037c.2.2.1
                      have p7037_3 := h7037c.2.2.2
                      linarith only [h6880, hlam, p7037_0]
                    · have p7037_0 := h7037c.1
                      have p7037_1 := h7037c.2.1
                      have p7037_2 := h7037c.2.2.1
                      have p7037_3 := h7037c.2.2.2
                      linarith only [hlam, p7037_0]
                    · have p7037_0 := h7037c.1
                      have p7037_1 := h7037c.2.1
                      have p7037_2 := h7037c.2.2.1
                      have p7037_3 := h7037c.2.2.2
                      rcases p7037_3 (m.d 0 2) (by simp) with h7102 | h7102
                      · rcases p7037_3 (m.d 1 2) (by simp) with h7103 | h7103
                        · rcases p7037_3 (m.d 2 3) (by simp) with h7104 | h7104
                          · rcases p7037_3 (m.d 2 4) (by simp) with h7105 | h7105
                            · linarith only [h7031, h7105, hlam]
                            · rcases p7037_3 (m.d 2 5) (by simp) with h7107 | h7107
                              · linarith only [h7032, h7107, hlam]
                              · linarith only [h7033, h7107, hlam]
                          · linarith only [h7031, h7104, hlam]
                        · linarith only [h6881, h7103, hlam]
                      · linarith only [h6876, h7102, hlam]
                    · have p7037_0 := h7037c.1
                      have p7037_1 := h7037c.2.1
                      have p7037_2 := h7037c.2.2.1
                      have p7037_3 := h7037c.2.2.2
                      rcases p7037_3 (m.d 0 2) (by simp) with h7113 | h7113
                      · rcases p7037_3 (m.d 1 2) (by simp) with h7114 | h7114
                        · rcases p7037_3 (m.d 2 3) (by simp) with h7115 | h7115
                          · rcases p7037_3 (m.d 2 4) (by simp) with h7116 | h7116
                            · linarith only [h7031, h7116, hlam]
                            · rcases p7037_3 (m.d 2 5) (by simp) with h7118 | h7118
                              · linarith only [h7032, h7118, hlam]
                              · rcases h4bigk with h7120c | h7120c | h7120c | h7120c | h7120c | h7120c | h7120c | h7120c | h7120c | h7120c | h7120c | h7120c | h7120c | h7120c | h7120c | h7120c | h7120c | h7120c | h7120c | h7120c | h7120c | h7120c | h7120c | h7120c | h7120c
                                · have p7120_0 := h7120c.1
                                  have p7120_1 := h7120c.2.1
                                  have p7120_2 := h7120c.2.2.1
                                  have p7120_3 := h7120c.2.2.2
                                  linarith only [hlam, p7120_0]
                                · have p7120_0 := h7120c.1
                                  have p7120_1 := h7120c.2.1
                                  have p7120_2 := h7120c.2.2.1
                                  have p7120_3 := h7120c.2.2.2
                                  linarith only [h0, h6874, h6881, h7031, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7120_1]
                                · have p7120_0 := h7120c.1
                                  have p7120_1 := h7120c.2.1
                                  have p7120_2 := h7120c.2.2.1
                                  have p7120_3 := h7120c.2.2.2
                                  linarith only [h0, h6874, h7031, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7120_1]
                                · have p7120_0 := h7120c.1
                                  have p7120_1 := h7120c.2.1
                                  have p7120_2 := h7120c.2.2.1
                                  have p7120_3 := h7120c.2.2.2
                                  linarith only [h0, h6874, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7120_1]
                                · have p7120_0 := h7120c.1
                                  have p7120_1 := h7120c.2.1
                                  have p7120_2 := h7120c.2.2.1
                                  have p7120_3 := h7120c.2.2.2
                                  linarith only [h0, h6874, h6881, h6884, h7031, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7120_1]
                                · have p7120_0 := h7120c.1
                                  have p7120_1 := h7120c.2.1
                                  have p7120_2 := h7120c.2.2.1
                                  have p7120_3 := h7120c.2.2.2
                                  linarith only [h6874, hlam, p7120_0]
                                · have p7120_0 := h7120c.1
                                  have p7120_1 := h7120c.2.1
                                  have p7120_2 := h7120c.2.2.1
                                  have p7120_3 := h7120c.2.2.2
                                  linarith only [hlam, p7120_0]
                                · have p7120_0 := h7120c.1
                                  have p7120_1 := h7120c.2.1
                                  have p7120_2 := h7120c.2.2.1
                                  have p7120_3 := h7120c.2.2.2
                                  linarith only [h6884, h7031, hc34, hc45, hlam, hphi, p7120_1]
                                · have p7120_0 := h7120c.1
                                  have p7120_1 := h7120c.2.1
                                  have p7120_2 := h7120c.2.2.1
                                  have p7120_3 := h7120c.2.2.2
                                  linarith only [h0, h6874, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7120_1]
                                · have p7120_0 := h7120c.1
                                  have p7120_1 := h7120c.2.1
                                  have p7120_2 := h7120c.2.2.1
                                  have p7120_3 := h7120c.2.2.2
                                  linarith only [h6884, hlam, p7120_0]
                                · have p7120_0 := h7120c.1
                                  have p7120_1 := h7120c.2.1
                                  have p7120_2 := h7120c.2.2.1
                                  have p7120_3 := h7120c.2.2.2
                                  linarith only [h6876, hlam, p7120_0]
                                · have p7120_0 := h7120c.1
                                  have p7120_1 := h7120c.2.1
                                  have p7120_2 := h7120c.2.2.1
                                  have p7120_3 := h7120c.2.2.2
                                  linarith only [h6881, hlam, p7120_0]
                                · have p7120_0 := h7120c.1
                                  have p7120_1 := h7120c.2.1
                                  have p7120_2 := h7120c.2.2.1
                                  have p7120_3 := h7120c.2.2.2
                                  linarith only [hlam, p7120_0]
                                · have p7120_0 := h7120c.1
                                  have p7120_1 := h7120c.2.1
                                  have p7120_2 := h7120c.2.2.1
                                  have p7120_3 := h7120c.2.2.2
                                  linarith only [h6876, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p7120_1]
                                · have p7120_0 := h7120c.1
                                  have p7120_1 := h7120c.2.1
                                  have p7120_2 := h7120c.2.2.1
                                  have p7120_3 := h7120c.2.2.2
                                  linarith only [h7033, hlam, p7120_0]
                                · have p7120_0 := h7120c.1
                                  have p7120_1 := h7120c.2.1
                                  have p7120_2 := h7120c.2.2.1
                                  have p7120_3 := h7120c.2.2.2
                                  linarith only [h6878, hlam, p7120_0]
                                · have p7120_0 := h7120c.1
                                  have p7120_1 := h7120c.2.1
                                  have p7120_2 := h7120c.2.2.1
                                  have p7120_3 := h7120c.2.2.2
                                  linarith only [h6883, hlam, p7120_0]
                                · have p7120_0 := h7120c.1
                                  have p7120_1 := h7120c.2.1
                                  have p7120_2 := h7120c.2.2.1
                                  have p7120_3 := h7120c.2.2.2
                                  linarith only [h7031, hlam, p7120_0]
                                · have p7120_0 := h7120c.1
                                  have p7120_1 := h7120c.2.1
                                  have p7120_2 := h7120c.2.2.1
                                  have p7120_3 := h7120c.2.2.2
                                  linarith only [hlam, p7120_0]
                                · have p7120_0 := h7120c.1
                                  have p7120_1 := h7120c.2.1
                                  have p7120_2 := h7120c.2.2.1
                                  have p7120_3 := h7120c.2.2.2
                                  linarith only [h7035, hlam, p7120_0]
                                · have p7120_0 := h7120c.1
                                  have p7120_1 := h7120c.2.1
                                  have p7120_2 := h7120c.2.2.1
                                  have p7120_3 := h7120c.2.2.2
                                  linarith only [h6879, hlam, p7120_0]
                                · have p7120_0 := h7120c.1
                                  have p7120_1 := h7120c.2.1
                                  have p7120_2 := h7120c.2.2.1
                                  have p7120_3 := h7120c.2.2.2
                                  linarith only [h0, h6874, h6879, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p7120_1]
                                · have p7120_0 := h7120c.1
                                  have p7120_1 := h7120c.2.1
                                  have p7120_2 := h7120c.2.2.1
                                  have p7120_3 := h7120c.2.2.2
                                  linarith only [h0, h6874, h6879, h7031, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7120_1]
                                · have p7120_0 := h7120c.1
                                  have p7120_1 := h7120c.2.1
                                  have p7120_2 := h7120c.2.2.1
                                  have p7120_3 := h7120c.2.2.2
                                  linarith only [h0, h6874, h6879, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7120_1]
                                · have p7120_0 := h7120c.1
                                  have p7120_1 := h7120c.2.1
                                  have p7120_2 := h7120c.2.2.1
                                  have p7120_3 := h7120c.2.2.2
                                  linarith only [hlam, p7120_0]
                          · linarith only [h7032, h7115, hlam]
                        · linarith only [h6882, h7114, hlam]
                      · linarith only [h6877, h7113, hlam]
                    · have p7037_0 := h7037c.1
                      have p7037_1 := h7037c.2.1
                      have p7037_2 := h7037c.2.2.1
                      have p7037_3 := h7037c.2.2.2
                      linarith only [h6876, hlam, p7037_0]
                    · have p7037_0 := h7037c.1
                      have p7037_1 := h7037c.2.1
                      have p7037_2 := h7037c.2.2.1
                      have p7037_3 := h7037c.2.2.2
                      linarith only [h6881, hlam, p7037_0]
                    · have p7037_0 := h7037c.1
                      have p7037_1 := h7037c.2.1
                      have p7037_2 := h7037c.2.2.1
                      have p7037_3 := h7037c.2.2.2
                      linarith only [h7031, hlam, p7037_0]
                    · have p7037_0 := h7037c.1
                      have p7037_1 := h7037c.2.1
                      have p7037_2 := h7037c.2.2.1
                      have p7037_3 := h7037c.2.2.2
                      linarith only [hlam, p7037_0]
                    · have p7037_0 := h7037c.1
                      have p7037_1 := h7037c.2.1
                      have p7037_2 := h7037c.2.2.1
                      have p7037_3 := h7037c.2.2.2
                      linarith only [h7033, hlam, p7037_0]
                    · have p7037_0 := h7037c.1
                      have p7037_1 := h7037c.2.1
                      have p7037_2 := h7037c.2.2.1
                      have p7037_3 := h7037c.2.2.2
                      linarith only [h6877, hlam, p7037_0]
                    · have p7037_0 := h7037c.1
                      have p7037_1 := h7037c.2.1
                      have p7037_2 := h7037c.2.2.1
                      have p7037_3 := h7037c.2.2.2
                      linarith only [h6882, hlam, p7037_0]
                    · have p7037_0 := h7037c.1
                      have p7037_1 := h7037c.2.1
                      have p7037_2 := h7037c.2.2.1
                      have p7037_3 := h7037c.2.2.2
                      linarith only [h7032, hlam, p7037_0]
                    · have p7037_0 := h7037c.1
                      have p7037_1 := h7037c.2.1
                      have p7037_2 := h7037c.2.2.1
                      have p7037_3 := h7037c.2.2.2
                      linarith only [h0, h6874, h6879, h6882, h6884, h7031, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7037_1]
                    · have p7037_0 := h7037c.1
                      have p7037_1 := h7037c.2.1
                      have p7037_2 := h7037c.2.2.1
                      have p7037_3 := h7037c.2.2.2
                      linarith only [hlam, p7037_0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h7159 | h7159
                · linarith only [h6881, h6884, h7159, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h7161 | h7161
                  · linarith only [h6882, h6884, h7031, h7032, h7161, hlam]
                  · linarith only [h0, h6874, h6879, h7031, h7032, h7161, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · linarith only [h0, h6874, h6879, h6883, h6884, h7031, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h7165 | h7165
          · rcases m.htr 2 3 4 (by decide) (by decide) with h7166 | h7166
            · linarith only [h6880, h6883, h7166, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h7168 | h7168
              · rcases m.htr 2 4 5 (by decide) (by decide) with h7169 | h7169
                · rcases m.htr 3 4 5 (by decide) (by decide) with h7170 | h7170
                  · rcases h2bigk with h7171c | h7171c | h7171c | h7171c | h7171c | h7171c | h7171c | h7171c | h7171c | h7171c | h7171c | h7171c | h7171c | h7171c | h7171c | h7171c | h7171c | h7171c | h7171c | h7171c | h7171c | h7171c | h7171c | h7171c | h7171c
                    · have p7171_0 := h7171c.1
                      have p7171_1 := h7171c.2.1
                      have p7171_2 := h7171c.2.2.1
                      have p7171_3 := h7171c.2.2.2
                      linarith only [hlam, p7171_0]
                    · have p7171_0 := h7171c.1
                      have p7171_1 := h7171c.2.1
                      have p7171_2 := h7171c.2.2.1
                      have p7171_3 := h7171c.2.2.2
                      linarith only [h0, hlam, p7171_0]
                    · have p7171_0 := h7171c.1
                      have p7171_1 := h7171c.2.1
                      have p7171_2 := h7171c.2.2.1
                      have p7171_3 := h7171c.2.2.2
                      rcases p7171_3 (m.d 0 2) (by simp) with h7174 | h7174
                      · rcases p7171_3 (m.d 1 2) (by simp) with h7175 | h7175
                        · rcases p7171_3 (m.d 2 3) (by simp) with h7176 | h7176
                          · linarith only [h7176, hlam, p7171_0]
                          · rcases p7171_3 (m.d 2 4) (by simp) with h7178 | h7178
                            · linarith only [h6876, h7178, hlam]
                            · linarith only [h7166, h7178, hlam]
                        · linarith only [h6880, h7175, hlam]
                      · linarith only [h7174, hlam, p7171_0]
                    · have p7171_0 := h7171c.1
                      have p7171_1 := h7171c.2.1
                      have p7171_2 := h7171c.2.2.1
                      have p7171_3 := h7171c.2.2.2
                      rcases p7171_3 (m.d 0 2) (by simp) with h7183 | h7183
                      · rcases p7171_3 (m.d 1 2) (by simp) with h7184 | h7184
                        · rcases p7171_3 (m.d 2 3) (by simp) with h7185 | h7185
                          · linarith only [h6875, h7185, hlam]
                          · rcases p7171_3 (m.d 2 4) (by simp) with h7187 | h7187
                            · linarith only [h7187, hlam, p7171_0]
                            · rcases p7171_3 (m.d 2 5) (by simp) with h7189 | h7189
                              · linarith only [h6877, h7189, hlam]
                              · rcases h4bigk with h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c
                                · have p7191_0 := h7191c.1
                                  have p7191_1 := h7191c.2.1
                                  have p7191_2 := h7191c.2.2.1
                                  have p7191_3 := h7191c.2.2.2
                                  linarith only [hlam, p7191_0]
                                · have p7191_0 := h7191c.1
                                  have p7191_1 := h7191c.2.1
                                  have p7191_2 := h7191c.2.2.1
                                  have p7191_3 := h7191c.2.2.2
                                  linarith only [h0, h6874, h6881, h7166, h7168, h7170, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7191_1]
                                · have p7191_0 := h7191c.1
                                  have p7191_1 := h7191c.2.1
                                  have p7191_2 := h7191c.2.2.1
                                  have p7191_3 := h7191c.2.2.2
                                  linarith only [h0, h6874, h7166, h7168, h7170, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7191_1]
                                · have p7191_0 := h7191c.1
                                  have p7191_1 := h7191c.2.1
                                  have p7191_2 := h7191c.2.2.1
                                  have p7191_3 := h7191c.2.2.2
                                  linarith only [h0, h6874, h6880, h6883, h7168, h7170, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7191_1]
                                · have p7191_0 := h7191c.1
                                  have p7191_1 := h7191c.2.1
                                  have p7191_2 := h7191c.2.2.1
                                  have p7191_3 := h7191c.2.2.2
                                  linarith only [h0, h6874, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7191_1]
                                · have p7191_0 := h7191c.1
                                  have p7191_1 := h7191c.2.1
                                  have p7191_2 := h7191c.2.2.1
                                  have p7191_3 := h7191c.2.2.2
                                  linarith only [h6874, hlam, p7191_0]
                                · have p7191_0 := h7191c.1
                                  have p7191_1 := h7191c.2.1
                                  have p7191_2 := h7191c.2.2.1
                                  have p7191_3 := h7191c.2.2.2
                                  linarith only [hlam, p7191_0]
                                · have p7191_0 := h7191c.1
                                  have p7191_1 := h7191c.2.1
                                  have p7191_2 := h7191c.2.2.1
                                  have p7191_3 := h7191c.2.2.2
                                  linarith only [h7166, h7168, h7170, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p7191_1]
                                · have p7191_0 := h7191c.1
                                  have p7191_1 := h7191c.2.1
                                  have p7191_2 := h7191c.2.2.1
                                  have p7191_3 := h7191c.2.2.2
                                  linarith only [h6883, hlam, p7191_1]
                                · have p7191_0 := h7191c.1
                                  have p7191_1 := h7191c.2.1
                                  have p7191_2 := h7191c.2.2.1
                                  have p7191_3 := h7191c.2.2.2
                                  linarith only [h0, h6874, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7191_1]
                                · have p7191_0 := h7191c.1
                                  have p7191_1 := h7191c.2.1
                                  have p7191_2 := h7191c.2.2.1
                                  have p7191_3 := h7191c.2.2.2
                                  linarith only [h6876, hlam, p7191_0]
                                · have p7191_0 := h7191c.1
                                  have p7191_1 := h7191c.2.1
                                  have p7191_2 := h7191c.2.2.1
                                  have p7191_3 := h7191c.2.2.2
                                  linarith only [h6881, hlam, p7191_0]
                                · have p7191_0 := h7191c.1
                                  have p7191_1 := h7191c.2.1
                                  have p7191_2 := h7191c.2.2.1
                                  have p7191_3 := h7191c.2.2.2
                                  linarith only [hlam, p7191_0]
                                · have p7191_0 := h7191c.1
                                  have p7191_1 := h7191c.2.1
                                  have p7191_2 := h7191c.2.2.1
                                  have p7191_3 := h7191c.2.2.2
                                  linarith only [h7166, hlam, p7191_1]
                                · have p7191_0 := h7191c.1
                                  have p7191_1 := h7191c.2.1
                                  have p7191_2 := h7191c.2.2.1
                                  have p7191_3 := h7191c.2.2.2
                                  linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7171_1, p7191_1]
                                · have p7191_0 := h7191c.1
                                  have p7191_1 := h7191c.2.1
                                  have p7191_2 := h7191c.2.2.1
                                  have p7191_3 := h7191c.2.2.2
                                  linarith only [h6878, hlam, p7191_0]
                                · have p7191_0 := h7191c.1
                                  have p7191_1 := h7191c.2.1
                                  have p7191_2 := h7191c.2.2.1
                                  have p7191_3 := h7191c.2.2.2
                                  linarith only [h6878, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b, p7191_1]
                                · have p7191_0 := h7191c.1
                                  have p7191_1 := h7191c.2.1
                                  have p7191_2 := h7191c.2.2.1
                                  have p7191_3 := h7191c.2.2.2
                                  linarith only [h6875, h6878, hlam, p7171_2, p7191_1]
                                · have p7191_0 := h7191c.1
                                  have p7191_1 := h7191c.2.1
                                  have p7191_2 := h7191c.2.2.1
                                  have p7191_3 := h7191c.2.2.2
                                  linarith only [hlam, p7191_0]
                                · have p7191_0 := h7191c.1
                                  have p7191_1 := h7191c.2.1
                                  have p7191_2 := h7191c.2.2.1
                                  have p7191_3 := h7191c.2.2.2
                                  linarith only [h0, h6875, h6878, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7191_1]
                                · have p7191_0 := h7191c.1
                                  have p7191_1 := h7191c.2.1
                                  have p7191_2 := h7191c.2.2.1
                                  have p7191_3 := h7191c.2.2.2
                                  linarith only [h6879, hlam, p7191_0]
                                · have p7191_0 := h7191c.1
                                  have p7191_1 := h7191c.2.1
                                  have p7191_2 := h7191c.2.2.1
                                  have p7191_3 := h7191c.2.2.2
                                  linarith only [h7165, hlam, p7191_0]
                                · have p7191_0 := h7191c.1
                                  have p7191_1 := h7191c.2.1
                                  have p7191_2 := h7191c.2.2.1
                                  have p7191_3 := h7191c.2.2.2
                                  linarith only [h7169, hlam, p7191_0]
                                · have p7191_0 := h7191c.1
                                  have p7191_1 := h7191c.2.1
                                  have p7191_2 := h7191c.2.2.1
                                  have p7191_3 := h7191c.2.2.2
                                  linarith only [h7170, hlam, p7191_0]
                                · have p7191_0 := h7191c.1
                                  have p7191_1 := h7191c.2.1
                                  have p7191_2 := h7191c.2.2.1
                                  have p7191_3 := h7191c.2.2.2
                                  linarith only [hlam, p7191_0]
                        · linarith only [h6881, h7184, hlam]
                      · linarith only [h7183, hlam, p7171_0]
                    · have p7171_0 := h7171c.1
                      have p7171_1 := h7171c.2.1
                      have p7171_2 := h7171c.2.2.1
                      have p7171_3 := h7171c.2.2.2
                      rcases p7171_3 (m.d 0 2) (by simp) with h7219 | h7219
                      · rcases p7171_3 (m.d 1 2) (by simp) with h7220 | h7220
                        · rcases p7171_3 (m.d 2 3) (by simp) with h7221 | h7221
                          · linarith only [h6875, h7221, hlam]
                          · linarith only [h7168, h7221, hlam]
                        · linarith only [h6882, h7220, hlam]
                      · linarith only [h7219, hlam, p7171_0]
                    · have p7171_0 := h7171c.1
                      have p7171_1 := h7171c.2.1
                      have p7171_2 := h7171c.2.2.1
                      have p7171_3 := h7171c.2.2.2
                      linarith only [h0, h6874, h6880, h6883, h7168, h7170, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7171_1]
                    · have p7171_0 := h7171c.1
                      have p7171_1 := h7171c.2.1
                      have p7171_2 := h7171c.2.2.1
                      have p7171_3 := h7171c.2.2.2
                      linarith only [hlam, p7171_0]
                    · have p7171_0 := h7171c.1
                      have p7171_1 := h7171c.2.1
                      have p7171_2 := h7171c.2.2.1
                      have p7171_3 := h7171c.2.2.2
                      rcases p7171_3 (m.d 0 2) (by simp) with h7228 | h7228
                      · linarith only [h0, h7228, hlam]
                      · linarith only [h6875, h7228, hlam]
                    · have p7171_0 := h7171c.1
                      have p7171_1 := h7171c.2.1
                      have p7171_2 := h7171c.2.2.1
                      have p7171_3 := h7171c.2.2.2
                      rcases p7171_3 (m.d 0 2) (by simp) with h7231 | h7231
                      · linarith only [h0, h7231, hlam]
                      · linarith only [h6876, h7231, hlam]
                    · have p7171_0 := h7171c.1
                      have p7171_1 := h7171c.2.1
                      have p7171_2 := h7171c.2.2.1
                      have p7171_3 := h7171c.2.2.2
                      rcases p7171_3 (m.d 0 2) (by simp) with h7234 | h7234
                      · linarith only [h0, h7234, hlam]
                      · linarith only [h6877, h7234, hlam]
                    · have p7171_0 := h7171c.1
                      have p7171_1 := h7171c.2.1
                      have p7171_2 := h7171c.2.2.1
                      have p7171_3 := h7171c.2.2.2
                      linarith only [h6875, hlam, p7171_0]
                    · have p7171_0 := h7171c.1
                      have p7171_1 := h7171c.2.1
                      have p7171_2 := h7171c.2.2.1
                      have p7171_3 := h7171c.2.2.2
                      linarith only [h6880, hlam, p7171_0]
                    · have p7171_0 := h7171c.1
                      have p7171_1 := h7171c.2.1
                      have p7171_2 := h7171c.2.2.1
                      have p7171_3 := h7171c.2.2.2
                      linarith only [hlam, p7171_0]
                    · have p7171_0 := h7171c.1
                      have p7171_1 := h7171c.2.1
                      have p7171_2 := h7171c.2.2.1
                      have p7171_3 := h7171c.2.2.2
                      linarith only [h7166, hlam, p7171_1]
                    · have p7171_0 := h7171c.1
                      have p7171_1 := h7171c.2.1
                      have p7171_2 := h7171c.2.2.1
                      have p7171_3 := h7171c.2.2.2
                      linarith only [h6875, h6878, h6880, h6883, hc02, hc25, hlam, hphi, ht0b, ht5b, p7171_1]
                    · have p7171_0 := h7171c.1
                      have p7171_1 := h7171c.2.1
                      have p7171_2 := h7171c.2.2.1
                      have p7171_3 := h7171c.2.2.2
                      linarith only [h6876, hlam, p7171_0]
                    · have p7171_0 := h7171c.1
                      have p7171_1 := h7171c.2.1
                      have p7171_2 := h7171c.2.2.1
                      have p7171_3 := h7171c.2.2.2
                      linarith only [h6881, hlam, p7171_0]
                    · have p7171_0 := h7171c.1
                      have p7171_1 := h7171c.2.1
                      have p7171_2 := h7171c.2.2.1
                      have p7171_3 := h7171c.2.2.2
                      linarith only [h6876, h7168, hc02, hc35, hlam, hphi, ht0b, ht5b, p7171_1]
                    · have p7171_0 := h7171c.1
                      have p7171_1 := h7171c.2.1
                      have p7171_2 := h7171c.2.2.1
                      have p7171_3 := h7171c.2.2.2
                      linarith only [hlam, p7171_0]
                    · have p7171_0 := h7171c.1
                      have p7171_1 := h7171c.2.1
                      have p7171_2 := h7171c.2.2.1
                      have p7171_3 := h7171c.2.2.2
                      linarith only [h0, h6874, h6881, h7168, h7170, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7171_1]
                    · have p7171_0 := h7171c.1
                      have p7171_1 := h7171c.2.1
                      have p7171_2 := h7171c.2.2.1
                      have p7171_3 := h7171c.2.2.2
                      linarith only [h6877, hlam, p7171_0]
                    · have p7171_0 := h7171c.1
                      have p7171_1 := h7171c.2.1
                      have p7171_2 := h7171c.2.2.1
                      have p7171_3 := h7171c.2.2.2
                      linarith only [h6882, hlam, p7171_0]
                    · have p7171_0 := h7171c.1
                      have p7171_1 := h7171c.2.1
                      have p7171_2 := h7171c.2.2.1
                      have p7171_3 := h7171c.2.2.2
                      linarith only [h7168, hlam, p7171_0]
                    · have p7171_0 := h7171c.1
                      have p7171_1 := h7171c.2.1
                      have p7171_2 := h7171c.2.2.1
                      have p7171_3 := h7171c.2.2.2
                      linarith only [h7169, hlam, p7171_1]
                    · have p7171_0 := h7171c.1
                      have p7171_1 := h7171c.2.1
                      have p7171_2 := h7171c.2.2.1
                      have p7171_3 := h7171c.2.2.2
                      linarith only [hlam, p7171_0]
                  · linarith only [h6879, h6880, h6883, h7168, h7170, hc04, hc35, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h6874, h7165, h7169, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h7254 | h7254
                · rcases m.htr 3 4 5 (by decide) (by decide) with h7255 | h7255
                  · rcases h2bigk with h7256c | h7256c | h7256c | h7256c | h7256c | h7256c | h7256c | h7256c | h7256c | h7256c | h7256c | h7256c | h7256c | h7256c | h7256c | h7256c | h7256c | h7256c | h7256c | h7256c | h7256c | h7256c | h7256c | h7256c | h7256c
                    · have p7256_0 := h7256c.1
                      have p7256_1 := h7256c.2.1
                      have p7256_2 := h7256c.2.2.1
                      have p7256_3 := h7256c.2.2.2
                      linarith only [hlam, p7256_0]
                    · have p7256_0 := h7256c.1
                      have p7256_1 := h7256c.2.1
                      have p7256_2 := h7256c.2.2.1
                      have p7256_3 := h7256c.2.2.2
                      linarith only [h0, hlam, p7256_0]
                    · have p7256_0 := h7256c.1
                      have p7256_1 := h7256c.2.1
                      have p7256_2 := h7256c.2.2.1
                      have p7256_3 := h7256c.2.2.2
                      rcases p7256_3 (m.d 0 2) (by simp) with h7259 | h7259
                      · rcases p7256_3 (m.d 1 2) (by simp) with h7260 | h7260
                        · rcases p7256_3 (m.d 2 3) (by simp) with h7261 | h7261
                          · linarith only [h7261, hlam, p7256_0]
                          · rcases p7256_3 (m.d 2 4) (by simp) with h7263 | h7263
                            · linarith only [h6876, h7263, hlam]
                            · linarith only [h7166, h7263, hlam]
                        · linarith only [h6880, h7260, hlam]
                      · linarith only [h7259, hlam, p7256_0]
                    · have p7256_0 := h7256c.1
                      have p7256_1 := h7256c.2.1
                      have p7256_2 := h7256c.2.2.1
                      have p7256_3 := h7256c.2.2.2
                      rcases p7256_3 (m.d 0 2) (by simp) with h7268 | h7268
                      · rcases p7256_3 (m.d 1 2) (by simp) with h7269 | h7269
                        · rcases p7256_3 (m.d 2 3) (by simp) with h7270 | h7270
                          · linarith only [h6875, h7270, hlam]
                          · rcases p7256_3 (m.d 2 4) (by simp) with h7272 | h7272
                            · linarith only [h7272, hlam, p7256_0]
                            · rcases p7256_3 (m.d 2 5) (by simp) with h7274 | h7274
                              · linarith only [h6877, h7274, hlam]
                              · rcases h4bigk with h7276c | h7276c | h7276c | h7276c | h7276c | h7276c | h7276c | h7276c | h7276c | h7276c | h7276c | h7276c | h7276c | h7276c | h7276c | h7276c | h7276c | h7276c | h7276c | h7276c | h7276c | h7276c | h7276c | h7276c | h7276c
                                · have p7276_0 := h7276c.1
                                  have p7276_1 := h7276c.2.1
                                  have p7276_2 := h7276c.2.2.1
                                  have p7276_3 := h7276c.2.2.2
                                  linarith only [hlam, p7276_0]
                                · have p7276_0 := h7276c.1
                                  have p7276_1 := h7276c.2.1
                                  have p7276_2 := h7276c.2.2.1
                                  have p7276_3 := h7276c.2.2.2
                                  linarith only [h0, h6874, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p7276_1]
                                · have p7276_0 := h7276c.1
                                  have p7276_1 := h7276c.2.1
                                  have p7276_2 := h7276c.2.2.1
                                  have p7276_3 := h7276c.2.2.2
                                  linarith only [h0, h6874, h7168, h7254, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7276_1]
                                · have p7276_0 := h7276c.1
                                  have p7276_1 := h7276c.2.1
                                  have p7276_2 := h7276c.2.2.1
                                  have p7276_3 := h7276c.2.2.2
                                  linarith only [h0, h6874, h6883, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7276_1]
                                · have p7276_0 := h7276c.1
                                  have p7276_1 := h7276c.2.1
                                  have p7276_2 := h7276c.2.2.1
                                  have p7276_3 := h7276c.2.2.2
                                  linarith only [h0, h6874, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7276_1]
                                · have p7276_0 := h7276c.1
                                  have p7276_1 := h7276c.2.1
                                  have p7276_2 := h7276c.2.2.1
                                  have p7276_3 := h7276c.2.2.2
                                  linarith only [h6874, hlam, p7276_0]
                                · have p7276_0 := h7276c.1
                                  have p7276_1 := h7276c.2.1
                                  have p7276_2 := h7276c.2.2.1
                                  have p7276_3 := h7276c.2.2.2
                                  linarith only [hlam, p7276_0]
                                · have p7276_0 := h7276c.1
                                  have p7276_1 := h7276c.2.1
                                  have p7276_2 := h7276c.2.2.1
                                  have p7276_3 := h7276c.2.2.2
                                  linarith only [h7254, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p7276_1]
                                · have p7276_0 := h7276c.1
                                  have p7276_1 := h7276c.2.1
                                  have p7276_2 := h7276c.2.2.1
                                  have p7276_3 := h7276c.2.2.2
                                  linarith only [h6883, hlam, p7276_1]
                                · have p7276_0 := h7276c.1
                                  have p7276_1 := h7276c.2.1
                                  have p7276_2 := h7276c.2.2.1
                                  have p7276_3 := h7276c.2.2.2
                                  linarith only [h0, h6874, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7276_1]
                                · have p7276_0 := h7276c.1
                                  have p7276_1 := h7276c.2.1
                                  have p7276_2 := h7276c.2.2.1
                                  have p7276_3 := h7276c.2.2.2
                                  linarith only [h6876, hlam, p7276_0]
                                · have p7276_0 := h7276c.1
                                  have p7276_1 := h7276c.2.1
                                  have p7276_2 := h7276c.2.2.1
                                  have p7276_3 := h7276c.2.2.2
                                  linarith only [h6881, hlam, p7276_0]
                                · have p7276_0 := h7276c.1
                                  have p7276_1 := h7276c.2.1
                                  have p7276_2 := h7276c.2.2.1
                                  have p7276_3 := h7276c.2.2.2
                                  linarith only [hlam, p7276_0]
                                · have p7276_0 := h7276c.1
                                  have p7276_1 := h7276c.2.1
                                  have p7276_2 := h7276c.2.2.1
                                  have p7276_3 := h7276c.2.2.2
                                  linarith only [h7166, hlam, p7276_1]
                                · have p7276_0 := h7276c.1
                                  have p7276_1 := h7276c.2.1
                                  have p7276_2 := h7276c.2.2.1
                                  have p7276_3 := h7276c.2.2.2
                                  linarith only [hc02, hc45, hlam, hphi, ht0b, ht5b, p7256_1, p7276_1]
                                · have p7276_0 := h7276c.1
                                  have p7276_1 := h7276c.2.1
                                  have p7276_2 := h7276c.2.2.1
                                  have p7276_3 := h7276c.2.2.2
                                  linarith only [h6878, hlam, p7276_0]
                                · have p7276_0 := h7276c.1
                                  have p7276_1 := h7276c.2.1
                                  have p7276_2 := h7276c.2.2.1
                                  have p7276_3 := h7276c.2.2.2
                                  linarith only [h6878, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b, p7276_1]
                                · have p7276_0 := h7276c.1
                                  have p7276_1 := h7276c.2.1
                                  have p7276_2 := h7276c.2.2.1
                                  have p7276_3 := h7276c.2.2.2
                                  linarith only [h6875, h6878, hlam, p7256_2, p7276_1]
                                · have p7276_0 := h7276c.1
                                  have p7276_1 := h7276c.2.1
                                  have p7276_2 := h7276c.2.2.1
                                  have p7276_3 := h7276c.2.2.2
                                  linarith only [hlam, p7276_0]
                                · have p7276_0 := h7276c.1
                                  have p7276_1 := h7276c.2.1
                                  have p7276_2 := h7276c.2.2.1
                                  have p7276_3 := h7276c.2.2.2
                                  linarith only [h0, h6875, h6878, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7276_1]
                                · have p7276_0 := h7276c.1
                                  have p7276_1 := h7276c.2.1
                                  have p7276_2 := h7276c.2.2.1
                                  have p7276_3 := h7276c.2.2.2
                                  linarith only [h6879, hlam, p7276_0]
                                · have p7276_0 := h7276c.1
                                  have p7276_1 := h7276c.2.1
                                  have p7276_2 := h7276c.2.2.1
                                  have p7276_3 := h7276c.2.2.2
                                  linarith only [h7165, hlam, p7276_0]
                                · have p7276_0 := h7276c.1
                                  have p7276_1 := h7276c.2.1
                                  have p7276_2 := h7276c.2.2.1
                                  have p7276_3 := h7276c.2.2.2
                                  linarith only [h7254, hlam, p7276_0]
                                · have p7276_0 := h7276c.1
                                  have p7276_1 := h7276c.2.1
                                  have p7276_2 := h7276c.2.2.1
                                  have p7276_3 := h7276c.2.2.2
                                  linarith only [h7255, hlam, p7276_0]
                                · have p7276_0 := h7276c.1
                                  have p7276_1 := h7276c.2.1
                                  have p7276_2 := h7276c.2.2.1
                                  have p7276_3 := h7276c.2.2.2
                                  linarith only [hlam, p7276_0]
                        · linarith only [h6881, h7269, hlam]
                      · linarith only [h7268, hlam, p7256_0]
                    · have p7256_0 := h7256c.1
                      have p7256_1 := h7256c.2.1
                      have p7256_2 := h7256c.2.2.1
                      have p7256_3 := h7256c.2.2.2
                      rcases p7256_3 (m.d 0 2) (by simp) with h7304 | h7304
                      · rcases p7256_3 (m.d 1 2) (by simp) with h7305 | h7305
                        · rcases p7256_3 (m.d 2 3) (by simp) with h7306 | h7306
                          · linarith only [h6875, h7306, hlam]
                          · rcases p7256_3 (m.d 2 4) (by simp) with h7308 | h7308
                            · linarith only [h6876, h7308, hlam]
                            · linarith only [h7254, h7308, hlam]
                        · linarith only [h6882, h7305, hlam]
                      · linarith only [h7304, hlam, p7256_0]
                    · have p7256_0 := h7256c.1
                      have p7256_1 := h7256c.2.1
                      have p7256_2 := h7256c.2.2.1
                      have p7256_3 := h7256c.2.2.2
                      linarith only [h0, h6874, h6881, h7254, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7256_1]
                    · have p7256_0 := h7256c.1
                      have p7256_1 := h7256c.2.1
                      have p7256_2 := h7256c.2.2.1
                      have p7256_3 := h7256c.2.2.2
                      linarith only [hlam, p7256_0]
                    · have p7256_0 := h7256c.1
                      have p7256_1 := h7256c.2.1
                      have p7256_2 := h7256c.2.2.1
                      have p7256_3 := h7256c.2.2.2
                      rcases p7256_3 (m.d 0 2) (by simp) with h7315 | h7315
                      · linarith only [h0, h7315, hlam]
                      · linarith only [h6875, h7315, hlam]
                    · have p7256_0 := h7256c.1
                      have p7256_1 := h7256c.2.1
                      have p7256_2 := h7256c.2.2.1
                      have p7256_3 := h7256c.2.2.2
                      rcases p7256_3 (m.d 0 2) (by simp) with h7318 | h7318
                      · linarith only [h0, h7318, hlam]
                      · linarith only [h6876, h7318, hlam]
                    · have p7256_0 := h7256c.1
                      have p7256_1 := h7256c.2.1
                      have p7256_2 := h7256c.2.2.1
                      have p7256_3 := h7256c.2.2.2
                      rcases p7256_3 (m.d 0 2) (by simp) with h7321 | h7321
                      · linarith only [h0, h7321, hlam]
                      · linarith only [h6877, h7321, hlam]
                    · have p7256_0 := h7256c.1
                      have p7256_1 := h7256c.2.1
                      have p7256_2 := h7256c.2.2.1
                      have p7256_3 := h7256c.2.2.2
                      linarith only [h6875, hlam, p7256_0]
                    · have p7256_0 := h7256c.1
                      have p7256_1 := h7256c.2.1
                      have p7256_2 := h7256c.2.2.1
                      have p7256_3 := h7256c.2.2.2
                      linarith only [h6880, hlam, p7256_0]
                    · have p7256_0 := h7256c.1
                      have p7256_1 := h7256c.2.1
                      have p7256_2 := h7256c.2.2.1
                      have p7256_3 := h7256c.2.2.2
                      linarith only [hlam, p7256_0]
                    · have p7256_0 := h7256c.1
                      have p7256_1 := h7256c.2.1
                      have p7256_2 := h7256c.2.2.1
                      have p7256_3 := h7256c.2.2.2
                      linarith only [h7166, hlam, p7256_1]
                    · have p7256_0 := h7256c.1
                      have p7256_1 := h7256c.2.1
                      have p7256_2 := h7256c.2.2.1
                      have p7256_3 := h7256c.2.2.2
                      linarith only [h7168, hlam, p7256_1]
                    · have p7256_0 := h7256c.1
                      have p7256_1 := h7256c.2.1
                      have p7256_2 := h7256c.2.2.1
                      have p7256_3 := h7256c.2.2.2
                      linarith only [h6876, hlam, p7256_0]
                    · have p7256_0 := h7256c.1
                      have p7256_1 := h7256c.2.1
                      have p7256_2 := h7256c.2.2.1
                      have p7256_3 := h7256c.2.2.2
                      linarith only [h6881, hlam, p7256_0]
                    · have p7256_0 := h7256c.1
                      have p7256_1 := h7256c.2.1
                      have p7256_2 := h7256c.2.2.1
                      have p7256_3 := h7256c.2.2.2
                      linarith only [h0, h6874, h6881, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7256_1]
                    · have p7256_0 := h7256c.1
                      have p7256_1 := h7256c.2.1
                      have p7256_2 := h7256c.2.2.1
                      have p7256_3 := h7256c.2.2.2
                      linarith only [hlam, p7256_0]
                    · have p7256_0 := h7256c.1
                      have p7256_1 := h7256c.2.1
                      have p7256_2 := h7256c.2.2.1
                      have p7256_3 := h7256c.2.2.2
                      linarith only [h0, h6874, h6881, h7168, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7256_1]
                    · have p7256_0 := h7256c.1
                      have p7256_1 := h7256c.2.1
                      have p7256_2 := h7256c.2.2.1
                      have p7256_3 := h7256c.2.2.2
                      linarith only [h6877, hlam, p7256_0]
                    · have p7256_0 := h7256c.1
                      have p7256_1 := h7256c.2.1
                      have p7256_2 := h7256c.2.2.1
                      have p7256_3 := h7256c.2.2.2
                      linarith only [h6882, hlam, p7256_0]
                    · have p7256_0 := h7256c.1
                      have p7256_1 := h7256c.2.1
                      have p7256_2 := h7256c.2.2.1
                      have p7256_3 := h7256c.2.2.2
                      linarith only [h0, h6874, h6882, h7165, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7256_1]
                    · have p7256_0 := h7256c.1
                      have p7256_1 := h7256c.2.1
                      have p7256_2 := h7256c.2.2.1
                      have p7256_3 := h7256c.2.2.2
                      linarith only [h7254, hlam, p7256_1]
                    · have p7256_0 := h7256c.1
                      have p7256_1 := h7256c.2.1
                      have p7256_2 := h7256c.2.2.1
                      have p7256_3 := h7256c.2.2.2
                      linarith only [hlam, p7256_0]
                  · linarith only [h0, h6874, h6879, h6880, h6883, h7255, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h6874, h7165, h7254, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h7341 | h7341
            · linarith only [h6880, h6883, h7341, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h7343 | h7343
              · linarith only [h0, h6874, h6879, h6881, h7165, h7341, h7343, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h7345 | h7345
                · linarith only [h6881, h7165, h7345, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h7347 | h7347
                  · rcases h2bigk with h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c
                    · have p7348_0 := h7348c.1
                      have p7348_1 := h7348c.2.1
                      have p7348_2 := h7348c.2.2.1
                      have p7348_3 := h7348c.2.2.2
                      linarith only [hlam, p7348_0]
                    · have p7348_0 := h7348c.1
                      have p7348_1 := h7348c.2.1
                      have p7348_2 := h7348c.2.2.1
                      have p7348_3 := h7348c.2.2.2
                      linarith only [h0, hlam, p7348_0]
                    · have p7348_0 := h7348c.1
                      have p7348_1 := h7348c.2.1
                      have p7348_2 := h7348c.2.2.1
                      have p7348_3 := h7348c.2.2.2
                      linarith only [h6875, h6878, h6881, h7165, h7341, h7347, hlam, p7348_2]
                    · have p7348_0 := h7348c.1
                      have p7348_1 := h7348c.2.1
                      have p7348_2 := h7348c.2.2.1
                      have p7348_3 := h7348c.2.2.2
                      linarith only [h6875, h6878, h6881, h7165, h7347, hlam, p7348_2]
                    · have p7348_0 := h7348c.1
                      have p7348_1 := h7348c.2.1
                      have p7348_2 := h7348c.2.2.1
                      have p7348_3 := h7348c.2.2.2
                      rcases p7348_3 (m.d 0 2) (by simp) with h7353 | h7353
                      · rcases p7348_3 (m.d 1 2) (by simp) with h7354 | h7354
                        · rcases p7348_3 (m.d 2 3) (by simp) with h7355 | h7355
                          · linarith only [h6875, h7355, hlam]
                          · rcases p7348_3 (m.d 2 4) (by simp) with h7357 | h7357
                            · linarith only [h6876, h7357, hlam]
                            · rcases p7348_3 (m.d 2 5) (by simp) with h7359 | h7359
                              · linarith only [h7359, hlam, p7348_0]
                              · rcases h4bigk with h7361c | h7361c | h7361c | h7361c | h7361c | h7361c | h7361c | h7361c | h7361c | h7361c | h7361c | h7361c | h7361c | h7361c | h7361c | h7361c | h7361c | h7361c | h7361c | h7361c | h7361c | h7361c | h7361c | h7361c | h7361c
                                · have p7361_0 := h7361c.1
                                  have p7361_1 := h7361c.2.1
                                  have p7361_2 := h7361c.2.2.1
                                  have p7361_3 := h7361c.2.2.2
                                  linarith only [hlam, p7361_0]
                                · have p7361_0 := h7361c.1
                                  have p7361_1 := h7361c.2.1
                                  have p7361_2 := h7361c.2.2.1
                                  have p7361_3 := h7361c.2.2.2
                                  linarith only [h0, h6874, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p7361_1]
                                · have p7361_0 := h7361c.1
                                  have p7361_1 := h7361c.2.1
                                  have p7361_2 := h7361c.2.2.1
                                  have p7361_3 := h7361c.2.2.2
                                  linarith only [h0, h6874, h7341, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7361_1]
                                · have p7361_0 := h7361c.1
                                  have p7361_1 := h7361c.2.1
                                  have p7361_2 := h7361c.2.2.1
                                  have p7361_3 := h7361c.2.2.2
                                  linarith only [h0, h6874, h6881, h7165, h7341, h7347, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7361_1]
                                · have p7361_0 := h7361c.1
                                  have p7361_1 := h7361c.2.1
                                  have p7361_2 := h7361c.2.2.1
                                  have p7361_3 := h7361c.2.2.2
                                  linarith only [h0, h6874, h6881, h7165, h7341, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7361_1]
                                · have p7361_0 := h7361c.1
                                  have p7361_1 := h7361c.2.1
                                  have p7361_2 := h7361c.2.2.1
                                  have p7361_3 := h7361c.2.2.2
                                  linarith only [h6874, hlam, p7361_0]
                                · have p7361_0 := h7361c.1
                                  have p7361_1 := h7361c.2.1
                                  have p7361_2 := h7361c.2.2.1
                                  have p7361_3 := h7361c.2.2.2
                                  linarith only [hlam, p7361_0]
                                · have p7361_0 := h7361c.1
                                  have p7361_1 := h7361c.2.1
                                  have p7361_2 := h7361c.2.2.1
                                  have p7361_3 := h7361c.2.2.2
                                  linarith only [h6875, h6878, h7165, h7341, h7347, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7361_1]
                                · have p7361_0 := h7361c.1
                                  have p7361_1 := h7361c.2.1
                                  have p7361_2 := h7361c.2.2.1
                                  have p7361_3 := h7361c.2.2.2
                                  linarith only [h6883, hlam, p7361_1]
                                · have p7361_0 := h7361c.1
                                  have p7361_1 := h7361c.2.1
                                  have p7361_2 := h7361c.2.2.1
                                  have p7361_3 := h7361c.2.2.2
                                  linarith only [h7165, hlam, p7361_0]
                                · have p7361_0 := h7361c.1
                                  have p7361_1 := h7361c.2.1
                                  have p7361_2 := h7361c.2.2.1
                                  have p7361_3 := h7361c.2.2.2
                                  linarith only [h6876, hlam, p7361_0]
                                · have p7361_0 := h7361c.1
                                  have p7361_1 := h7361c.2.1
                                  have p7361_2 := h7361c.2.2.1
                                  have p7361_3 := h7361c.2.2.2
                                  linarith only [h6881, hlam, p7361_0]
                                · have p7361_0 := h7361c.1
                                  have p7361_1 := h7361c.2.1
                                  have p7361_2 := h7361c.2.2.1
                                  have p7361_3 := h7361c.2.2.2
                                  linarith only [hlam, p7361_0]
                                · have p7361_0 := h7361c.1
                                  have p7361_1 := h7361c.2.1
                                  have p7361_2 := h7361c.2.2.1
                                  have p7361_3 := h7361c.2.2.2
                                  linarith only [h7341, hlam, p7361_1]
                                · have p7361_0 := h7361c.1
                                  have p7361_1 := h7361c.2.1
                                  have p7361_2 := h7361c.2.2.1
                                  have p7361_3 := h7361c.2.2.2
                                  linarith only [h7345, hlam, p7361_0]
                                · have p7361_0 := h7361c.1
                                  have p7361_1 := h7361c.2.1
                                  have p7361_2 := h7361c.2.2.1
                                  have p7361_3 := h7361c.2.2.2
                                  linarith only [h6878, hlam, p7361_0]
                                · have p7361_0 := h7361c.1
                                  have p7361_1 := h7361c.2.1
                                  have p7361_2 := h7361c.2.2.1
                                  have p7361_3 := h7361c.2.2.2
                                  linarith only [h0, h6875, h6878, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p7361_1]
                                · have p7361_0 := h7361c.1
                                  have p7361_1 := h7361c.2.1
                                  have p7361_2 := h7361c.2.2.1
                                  have p7361_3 := h7361c.2.2.2
                                  linarith only [h0, h6875, h6878, h7341, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7361_1]
                                · have p7361_0 := h7361c.1
                                  have p7361_1 := h7361c.2.1
                                  have p7361_2 := h7361c.2.2.1
                                  have p7361_3 := h7361c.2.2.2
                                  linarith only [hlam, p7361_0]
                                · have p7361_0 := h7361c.1
                                  have p7361_1 := h7361c.2.1
                                  have p7361_2 := h7361c.2.2.1
                                  have p7361_3 := h7361c.2.2.2
                                  linarith only [h0, h6875, h6878, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7361_1]
                                · have p7361_0 := h7361c.1
                                  have p7361_1 := h7361c.2.1
                                  have p7361_2 := h7361c.2.2.1
                                  have p7361_3 := h7361c.2.2.2
                                  linarith only [h6879, hlam, p7361_0]
                                · have p7361_0 := h7361c.1
                                  have p7361_1 := h7361c.2.1
                                  have p7361_2 := h7361c.2.2.1
                                  have p7361_3 := h7361c.2.2.2
                                  linarith only [h6881, h7341, hc23, hc45, hlam, hphi, ht34, p7361_1]
                                · have p7361_0 := h7361c.1
                                  have p7361_1 := h7361c.2.1
                                  have p7361_2 := h7361c.2.2.1
                                  have p7361_3 := h7361c.2.2.2
                                  linarith only [h0, h6874, h6879, h7341, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7361_1]
                                · have p7361_0 := h7361c.1
                                  have p7361_1 := h7361c.2.1
                                  have p7361_2 := h7361c.2.2.1
                                  have p7361_3 := h7361c.2.2.2
                                  linarith only [h7347, hlam, p7361_0]
                                · have p7361_0 := h7361c.1
                                  have p7361_1 := h7361c.2.1
                                  have p7361_2 := h7361c.2.2.1
                                  have p7361_3 := h7361c.2.2.2
                                  linarith only [hlam, p7361_0]
                        · linarith only [h6882, h7354, hlam]
                      · linarith only [h7353, hlam, p7348_0]
                    · have p7348_0 := h7348c.1
                      have p7348_1 := h7348c.2.1
                      have p7348_2 := h7348c.2.2.1
                      have p7348_3 := h7348c.2.2.2
                      linarith only [h6875, h6878, h6880, h6883, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7348_1]
                    · have p7348_0 := h7348c.1
                      have p7348_1 := h7348c.2.1
                      have p7348_2 := h7348c.2.2.1
                      have p7348_3 := h7348c.2.2.2
                      linarith only [hlam, p7348_0]
                    · have p7348_0 := h7348c.1
                      have p7348_1 := h7348c.2.1
                      have p7348_2 := h7348c.2.2.1
                      have p7348_3 := h7348c.2.2.2
                      linarith only [h0, h6874, h6879, h6881, h7165, h7341, hlam, p7348_2]
                    · have p7348_0 := h7348c.1
                      have p7348_1 := h7348c.2.1
                      have p7348_2 := h7348c.2.2.1
                      have p7348_3 := h7348c.2.2.2
                      linarith only [h0, h6874, h6879, h6881, h7165, hlam, p7348_2]
                    · have p7348_0 := h7348c.1
                      have p7348_1 := h7348c.2.1
                      have p7348_2 := h7348c.2.2.1
                      have p7348_3 := h7348c.2.2.2
                      rcases p7348_3 (m.d 0 2) (by simp) with h7393 | h7393
                      · linarith only [h0, h7393, hlam]
                      · linarith only [h6877, h7393, hlam]
                    · have p7348_0 := h7348c.1
                      have p7348_1 := h7348c.2.1
                      have p7348_2 := h7348c.2.2.1
                      have p7348_3 := h7348c.2.2.2
                      linarith only [h6875, hlam, p7348_0]
                    · have p7348_0 := h7348c.1
                      have p7348_1 := h7348c.2.1
                      have p7348_2 := h7348c.2.2.1
                      have p7348_3 := h7348c.2.2.2
                      linarith only [h6880, hlam, p7348_0]
                    · have p7348_0 := h7348c.1
                      have p7348_1 := h7348c.2.1
                      have p7348_2 := h7348c.2.2.1
                      have p7348_3 := h7348c.2.2.2
                      linarith only [hlam, p7348_0]
                    · have p7348_0 := h7348c.1
                      have p7348_1 := h7348c.2.1
                      have p7348_2 := h7348c.2.2.1
                      have p7348_3 := h7348c.2.2.2
                      linarith only [h7341, hlam, p7348_1]
                    · have p7348_0 := h7348c.1
                      have p7348_1 := h7348c.2.1
                      have p7348_2 := h7348c.2.2.1
                      have p7348_3 := h7348c.2.2.2
                      linarith only [h7343, hlam, p7348_1]
                    · have p7348_0 := h7348c.1
                      have p7348_1 := h7348c.2.1
                      have p7348_2 := h7348c.2.2.1
                      have p7348_3 := h7348c.2.2.2
                      linarith only [h6876, hlam, p7348_0]
                    · have p7348_0 := h7348c.1
                      have p7348_1 := h7348c.2.1
                      have p7348_2 := h7348c.2.2.1
                      have p7348_3 := h7348c.2.2.2
                      linarith only [h6881, hlam, p7348_0]
                    · have p7348_0 := h7348c.1
                      have p7348_1 := h7348c.2.1
                      have p7348_2 := h7348c.2.2.1
                      have p7348_3 := h7348c.2.2.2
                      linarith only [h0, h6875, h6878, h6881, h7165, h7347, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7348_1]
                    · have p7348_0 := h7348c.1
                      have p7348_1 := h7348c.2.1
                      have p7348_2 := h7348c.2.2.1
                      have p7348_3 := h7348c.2.2.2
                      linarith only [hlam, p7348_0]
                    · have p7348_0 := h7348c.1
                      have p7348_1 := h7348c.2.1
                      have p7348_2 := h7348c.2.2.1
                      have p7348_3 := h7348c.2.2.2
                      linarith only [h7345, hlam, p7348_0]
                    · have p7348_0 := h7348c.1
                      have p7348_1 := h7348c.2.1
                      have p7348_2 := h7348c.2.2.1
                      have p7348_3 := h7348c.2.2.2
                      linarith only [h6877, hlam, p7348_0]
                    · have p7348_0 := h7348c.1
                      have p7348_1 := h7348c.2.1
                      have p7348_2 := h7348c.2.2.1
                      have p7348_3 := h7348c.2.2.2
                      linarith only [h6882, hlam, p7348_0]
                    · have p7348_0 := h7348c.1
                      have p7348_1 := h7348c.2.1
                      have p7348_2 := h7348c.2.2.1
                      have p7348_3 := h7348c.2.2.2
                      linarith only [h0, h6875, h6878, h6882, h7165, h7347, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7348_1]
                    · have p7348_0 := h7348c.1
                      have p7348_1 := h7348c.2.1
                      have p7348_2 := h7348c.2.2.1
                      have p7348_3 := h7348c.2.2.2
                      linarith only [h0, h6875, h6878, h6882, h7165, h7347, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p7348_1]
                    · have p7348_0 := h7348c.1
                      have p7348_1 := h7348c.2.1
                      have p7348_2 := h7348c.2.2.1
                      have p7348_3 := h7348c.2.2.2
                      linarith only [hlam, p7348_0]
                  · linarith only [h0, h6874, h6879, h6880, h6883, h7347, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
      · linarith only [h0, h6877, h6882, hlam]
    · linarith only [h0, h6876, h6881, hlam]
  · linarith only [h0, h6875, h6880, hlam]

end R2N4
