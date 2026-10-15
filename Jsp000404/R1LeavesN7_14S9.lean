import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7862000 in
set_option maxHeartbeats 7862000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s7_x0_x0_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg4610 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6681 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg7494 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8056 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8057 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8058 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8059 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h8881 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h4610 := hg4610
  have h6681 := hg6681
  have h7494 := hg7494
  rcases m.htr 0 4 5 (by decide) (by decide) with h8882 | h8882
  · rcases m.htr 1 2 3 (by decide) (by decide) with h8883 | h8883
    · rcases m.htr 1 2 4 (by decide) (by decide) with h8884 | h8884
      · rcases m.htr 1 2 5 (by decide) (by decide) with h8885 | h8885
        · rcases m.htr 1 3 4 (by decide) (by decide) with h8886 | h8886
          · rcases m.htr 1 3 5 (by decide) (by decide) with h8887 | h8887
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8888 | h8888
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8889 | h8889
                · linarith only [h8056, h8059, h8889, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8891 | h8891
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h8892 | h8892
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8893 | h8893
                      · rcases h0bigk with h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c
                        · have p8894_0 := h8894c.1
                          have p8894_1 := h8894c.2.1
                          have p8894_2 := h8894c.2.2.1
                          have p8894_3 := h8894c.2.2.2
                          linarith only [hlam, p8894_0]
                        · have p8894_0 := h8894c.1
                          have p8894_1 := h8894c.2.1
                          have p8894_2 := h8894c.2.2.1
                          have p8894_3 := h8894c.2.2.2
                          linarith only [h0, hlam, p8894_1]
                        · have p8894_0 := h8894c.1
                          have p8894_1 := h8894c.2.1
                          have p8894_2 := h8894c.2.2.1
                          have p8894_3 := h8894c.2.2.2
                          linarith only [h4610, hlam, p8894_0]
                        · have p8894_0 := h8894c.1
                          have p8894_1 := h8894c.2.1
                          have p8894_2 := h8894c.2.2.1
                          have p8894_3 := h8894c.2.2.2
                          linarith only [h6681, hlam, p8894_1]
                        · have p8894_0 := h8894c.1
                          have p8894_1 := h8894c.2.1
                          have p8894_2 := h8894c.2.2.1
                          have p8894_3 := h8894c.2.2.2
                          linarith only [h7494, hlam, p8894_1]
                        · have p8894_0 := h8894c.1
                          have p8894_1 := h8894c.2.1
                          have p8894_2 := h8894c.2.2.1
                          have p8894_3 := h8894c.2.2.2
                          rcases p8894_3 (m.d 0 1) (by simp) with h8900 | h8900
                          · linarith only [h0, h8900, hlam]
                          · rcases p8894_3 (m.d 0 2) (by simp) with h8902 | h8902
                            · rcases p8894_3 (m.d 0 3) (by simp) with h8903 | h8903
                              · linarith only [h8056, h8903, hlam]
                              · linarith only [h4610, h8903, hlam]
                            · linarith only [h0, h8902, hlam]
                        · have p8894_0 := h8894c.1
                          have p8894_1 := h8894c.2.1
                          have p8894_2 := h8894c.2.2.1
                          have p8894_3 := h8894c.2.2.2
                          linarith only [hlam, p8894_0]
                        · have p8894_0 := h8894c.1
                          have p8894_1 := h8894c.2.1
                          have p8894_2 := h8894c.2.2.1
                          have p8894_3 := h8894c.2.2.2
                          linarith only [h8056, h8891, hc35, hlam, hphi, ht0b, ht5b, p8894_1, u0elo1]
                        · have p8894_0 := h8894c.1
                          have p8894_1 := h8894c.2.1
                          have p8894_2 := h8894c.2.2.1
                          have p8894_3 := h8894c.2.2.2
                          linarith only [h8056, h8059, h8891, h8893, hc45, hlam, hphi, ht0b, ht5b, p8894_1, u0elo1]
                        · have p8894_0 := h8894c.1
                          have p8894_1 := h8894c.2.1
                          have p8894_2 := h8894c.2.2.1
                          have p8894_3 := h8894c.2.2.2
                          rcases p8894_3 (m.d 0 1) (by simp) with h8910 | h8910
                          · linarith only [h0, h8910, hlam]
                          · rcases p8894_3 (m.d 0 2) (by simp) with h8912 | h8912
                            · rcases p8894_3 (m.d 0 3) (by simp) with h8913 | h8913
                              · linarith only [h8056, h8913, hlam]
                              · linarith only [h8881, h8913, hlam]
                            · linarith only [h8058, h8912, hlam]
                        · have p8894_0 := h8894c.1
                          have p8894_1 := h8894c.2.1
                          have p8894_2 := h8894c.2.2.1
                          have p8894_3 := h8894c.2.2.2
                          linarith only [h8059, h8883, h8886, hc01, hc12, hlam, hphi, p8894_1]
                        · have p8894_0 := h8894c.1
                          have p8894_1 := h8894c.2.1
                          have p8894_2 := h8894c.2.2.1
                          have p8894_3 := h8894c.2.2.2
                          linarith only [h8056, hlam, p8894_1]
                        · have p8894_0 := h8894c.1
                          have p8894_1 := h8894c.2.1
                          have p8894_2 := h8894c.2.2.1
                          have p8894_3 := h8894c.2.2.2
                          linarith only [hlam, p8894_0]
                        · have p8894_0 := h8894c.1
                          have p8894_1 := h8894c.2.1
                          have p8894_2 := h8894c.2.2.1
                          have p8894_3 := h8894c.2.2.2
                          linarith only [h8059, hlam, p8894_1]
                        · have p8894_0 := h8894c.1
                          have p8894_1 := h8894c.2.1
                          have p8894_2 := h8894c.2.2.1
                          have p8894_3 := h8894c.2.2.2
                          linarith only [h8059, h8883, h8886, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p8894_1]
                        · have p8894_0 := h8894c.1
                          have p8894_1 := h8894c.2.1
                          have p8894_2 := h8894c.2.2.1
                          have p8894_3 := h8894c.2.2.2
                          linarith only [h8059, h8883, h8886, hc01, hc12, hlam, hphi, p8894_1]
                        · have p8894_0 := h8894c.1
                          have p8894_1 := h8894c.2.1
                          have p8894_2 := h8894c.2.2.1
                          have p8894_3 := h8894c.2.2.2
                          linarith only [h8057, hlam, p8894_0]
                        · have p8894_0 := h8894c.1
                          have p8894_1 := h8894c.2.1
                          have p8894_2 := h8894c.2.2.1
                          have p8894_3 := h8894c.2.2.2
                          linarith only [h8056, h8059, h8883, h8886, h8891, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p8894_1]
                        · have p8894_0 := h8894c.1
                          have p8894_1 := h8894c.2.1
                          have p8894_2 := h8894c.2.2.1
                          have p8894_3 := h8894c.2.2.2
                          linarith only [hlam, p8894_0]
                        · have p8894_0 := h8894c.1
                          have p8894_1 := h8894c.2.1
                          have p8894_2 := h8894c.2.2.1
                          have p8894_3 := h8894c.2.2.2
                          linarith only [h7494, h8059, h8883, h8886, hc01, hc12, hlam, hphi, p8894_1]
                        · have p8894_0 := h8894c.1
                          have p8894_1 := h8894c.2.1
                          have p8894_2 := h8894c.2.2.1
                          have p8894_3 := h8894c.2.2.2
                          linarith only [h8059, h8881, h8883, h8886, hc01, hc12, hlam, hphi, p8894_1]
                        · have p8894_0 := h8894c.1
                          have p8894_1 := h8894c.2.1
                          have p8894_2 := h8894c.2.2.1
                          have p8894_3 := h8894c.2.2.2
                          linarith only [h8058, hlam, p8894_1]
                        · have p8894_0 := h8894c.1
                          have p8894_1 := h8894c.2.1
                          have p8894_2 := h8894c.2.2.1
                          have p8894_3 := h8894c.2.2.2
                          linarith only [h8881, hlam, p8894_0]
                        · have p8894_0 := h8894c.1
                          have p8894_1 := h8894c.2.1
                          have p8894_2 := h8894c.2.2.1
                          have p8894_3 := h8894c.2.2.2
                          linarith only [h8882, hlam, p8894_1]
                        · have p8894_0 := h8894c.1
                          have p8894_1 := h8894c.2.1
                          have p8894_2 := h8894c.2.2.1
                          have p8894_3 := h8894c.2.2.2
                          linarith only [hlam, p8894_0]
                      · linarith only [h8057, h8059, h8882, h8893, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h8059, h8881, h8882, h8883, h8886, h8889, h8891, h8892, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h8059, h8881, h8883, h8886, h8891, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h8059, h8881, h8882, h8886, h8888, hlam]
            · linarith only [h8059, h8881, h8886, h8887, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h8937 | h8937
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8938 | h8938
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8939 | h8939
                · linarith only [h7494, h8886, h8937, h8939, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8941 | h8941
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h8942 | h8942
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8943 | h8943
                      · rcases h0bigk with h8944c | h8944c | h8944c | h8944c | h8944c | h8944c | h8944c | h8944c | h8944c | h8944c | h8944c | h8944c | h8944c | h8944c | h8944c | h8944c | h8944c | h8944c | h8944c | h8944c | h8944c | h8944c | h8944c | h8944c | h8944c
                        · have p8944_0 := h8944c.1
                          have p8944_1 := h8944c.2.1
                          have p8944_2 := h8944c.2.2.1
                          have p8944_3 := h8944c.2.2.2
                          linarith only [hlam, p8944_0]
                        · have p8944_0 := h8944c.1
                          have p8944_1 := h8944c.2.1
                          have p8944_2 := h8944c.2.2.1
                          have p8944_3 := h8944c.2.2.2
                          linarith only [h0, hlam, p8944_1]
                        · have p8944_0 := h8944c.1
                          have p8944_1 := h8944c.2.1
                          have p8944_2 := h8944c.2.2.1
                          have p8944_3 := h8944c.2.2.2
                          linarith only [h4610, hlam, p8944_0]
                        · have p8944_0 := h8944c.1
                          have p8944_1 := h8944c.2.1
                          have p8944_2 := h8944c.2.2.1
                          have p8944_3 := h8944c.2.2.2
                          linarith only [h6681, hlam, p8944_1]
                        · have p8944_0 := h8944c.1
                          have p8944_1 := h8944c.2.1
                          have p8944_2 := h8944c.2.2.1
                          have p8944_3 := h8944c.2.2.2
                          linarith only [h7494, hlam, p8944_1]
                        · have p8944_0 := h8944c.1
                          have p8944_1 := h8944c.2.1
                          have p8944_2 := h8944c.2.2.1
                          have p8944_3 := h8944c.2.2.2
                          rcases p8944_3 (m.d 0 1) (by simp) with h8950 | h8950
                          · linarith only [h0, h8950, hlam]
                          · rcases p8944_3 (m.d 0 2) (by simp) with h8952 | h8952
                            · rcases p8944_3 (m.d 0 3) (by simp) with h8953 | h8953
                              · linarith only [h8056, h8953, hlam]
                              · linarith only [h4610, h8953, hlam]
                            · linarith only [h0, h8952, hlam]
                        · have p8944_0 := h8944c.1
                          have p8944_1 := h8944c.2.1
                          have p8944_2 := h8944c.2.2.1
                          have p8944_3 := h8944c.2.2.2
                          linarith only [hlam, p8944_0]
                        · have p8944_0 := h8944c.1
                          have p8944_1 := h8944c.2.1
                          have p8944_2 := h8944c.2.2.1
                          have p8944_3 := h8944c.2.2.2
                          linarith only [h8881, h8943, hc45, hlam, hphi, ht0b, ht5b, p8944_1, u0elo1]
                        · have p8944_0 := h8944c.1
                          have p8944_1 := h8944c.2.1
                          have p8944_2 := h8944c.2.2.1
                          have p8944_3 := h8944c.2.2.2
                          linarith only [h8059, h8881, h8943, hc45, hlam, hphi, ht0b, ht5b, p8944_1, u0elo1]
                        · have p8944_0 := h8944c.1
                          have p8944_1 := h8944c.2.1
                          have p8944_2 := h8944c.2.2.1
                          have p8944_3 := h8944c.2.2.2
                          rcases p8944_3 (m.d 0 1) (by simp) with h8960 | h8960
                          · linarith only [h0, h8960, hlam]
                          · rcases p8944_3 (m.d 0 2) (by simp) with h8962 | h8962
                            · rcases p8944_3 (m.d 0 3) (by simp) with h8963 | h8963
                              · linarith only [h8056, h8963, hlam]
                              · linarith only [h8881, h8963, hlam]
                            · linarith only [h8058, h8962, hlam]
                        · have p8944_0 := h8944c.1
                          have p8944_1 := h8944c.2.1
                          have p8944_2 := h8944c.2.2.1
                          have p8944_3 := h8944c.2.2.2
                          linarith only [h4610, h8886, hc01, hc34, hlam, hphi, ht12, ht23, p8944_1]
                        · have p8944_0 := h8944c.1
                          have p8944_1 := h8944c.2.1
                          have p8944_2 := h8944c.2.2.1
                          have p8944_3 := h8944c.2.2.2
                          linarith only [h8056, hlam, p8944_1]
                        · have p8944_0 := h8944c.1
                          have p8944_1 := h8944c.2.1
                          have p8944_2 := h8944c.2.2.1
                          have p8944_3 := h8944c.2.2.2
                          linarith only [hlam, p8944_0]
                        · have p8944_0 := h8944c.1
                          have p8944_1 := h8944c.2.1
                          have p8944_2 := h8944c.2.2.1
                          have p8944_3 := h8944c.2.2.2
                          linarith only [h8059, hlam, p8944_1]
                        · have p8944_0 := h8944c.1
                          have p8944_1 := h8944c.2.1
                          have p8944_2 := h8944c.2.2.1
                          have p8944_3 := h8944c.2.2.2
                          linarith only [h4610, h7494, h8886, hc01, hc34, hlam, hphi, ht12, ht23, p8944_1]
                        · have p8944_0 := h8944c.1
                          have p8944_1 := h8944c.2.1
                          have p8944_2 := h8944c.2.2.1
                          have p8944_3 := h8944c.2.2.2
                          rcases p8944_3 (m.d 0 1) (by simp) with h8972 | h8972
                          · linarith only [h6681, h8972, hlam]
                          · rcases p8944_3 (m.d 0 2) (by simp) with h8974 | h8974
                            · rcases p8944_3 (m.d 0 3) (by simp) with h8975 | h8975
                              · linarith only [h8059, h8975, hlam]
                              · linarith only [h4610, h8975, hlam]
                            · linarith only [h0, h8974, hlam]
                        · have p8944_0 := h8944c.1
                          have p8944_1 := h8944c.2.1
                          have p8944_2 := h8944c.2.2.1
                          have p8944_3 := h8944c.2.2.2
                          linarith only [h8057, hlam, p8944_0]
                        · have p8944_0 := h8944c.1
                          have p8944_1 := h8944c.2.1
                          have p8944_2 := h8944c.2.2.1
                          have p8944_3 := h8944c.2.2.2
                          linarith only [h8056, h8941, h8943, hc45, hlam, hphi, ht0b, ht5b, p8944_1, u0elo3]
                        · have p8944_0 := h8944c.1
                          have p8944_1 := h8944c.2.1
                          have p8944_2 := h8944c.2.2.1
                          have p8944_3 := h8944c.2.2.2
                          linarith only [hlam, p8944_0]
                        · have p8944_0 := h8944c.1
                          have p8944_1 := h8944c.2.1
                          have p8944_2 := h8944c.2.2.1
                          have p8944_3 := h8944c.2.2.2
                          rcases p8944_3 (m.d 0 1) (by simp) with h8982 | h8982
                          · linarith only [h6681, h8982, hlam]
                          · rcases p8944_3 (m.d 0 2) (by simp) with h8984 | h8984
                            · rcases p8944_3 (m.d 0 3) (by simp) with h8985 | h8985
                              · linarith only [h8059, h8985, hlam]
                              · linarith only [h8881, h8985, hlam]
                            · linarith only [h8058, h8984, hlam]
                        · have p8944_0 := h8944c.1
                          have p8944_1 := h8944c.2.1
                          have p8944_2 := h8944c.2.2.1
                          have p8944_3 := h8944c.2.2.2
                          linarith only [h7494, h8886, h8937, hc01, hc34, hlam, hphi, ht12, ht23, p8944_1]
                        · have p8944_0 := h8944c.1
                          have p8944_1 := h8944c.2.1
                          have p8944_2 := h8944c.2.2.1
                          have p8944_3 := h8944c.2.2.2
                          linarith only [h8058, hlam, p8944_1]
                        · have p8944_0 := h8944c.1
                          have p8944_1 := h8944c.2.1
                          have p8944_2 := h8944c.2.2.1
                          have p8944_3 := h8944c.2.2.2
                          linarith only [h8881, hlam, p8944_0]
                        · have p8944_0 := h8944c.1
                          have p8944_1 := h8944c.2.1
                          have p8944_2 := h8944c.2.2.1
                          have p8944_3 := h8944c.2.2.2
                          linarith only [h8882, hlam, p8944_1]
                        · have p8944_0 := h8944c.1
                          have p8944_1 := h8944c.2.1
                          have p8944_2 := h8944c.2.2.1
                          have p8944_3 := h8944c.2.2.2
                          linarith only [hlam, p8944_0]
                      · linarith only [h4610, h8886, h8943, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h8057, h8882, h8939, h8941, h8942, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                  · linarith only [h4610, h8881, h8886, h8941, hc23, hc34, hlam, hphi]
              · linarith only [h6681, h8057, h8882, h8938, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h4610, h8881, h8937, hlam]
        · linarith only [h0, h8058, h8885, hlam]
      · linarith only [h0, h8057, h8884, hlam]
    · linarith only [h0, h8056, h8883, hlam]
  · linarith only [h8059, h8881, h8882, hlam]

end R2N4
