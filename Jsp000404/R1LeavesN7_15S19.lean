import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_15S10
import Jsp000404.R1LeavesN7_15S17
import Jsp000404.R1LeavesN7_15S18

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10280000 in
set_option maxHeartbeats 10280000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s7_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h6253 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h6254 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h6874 | h6874
  · rcases m.htr 0 2 3 (by decide) (by decide) with h6875 | h6875
    · rcases m.htr 0 2 4 (by decide) (by decide) with h6876 | h6876
      · rcases m.htr 0 2 5 (by decide) (by decide) with h6877 | h6877
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6878 | h6878
          · linarith only [h6253, h6254, h6878, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6880 | h6880
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6881 | h6881
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6882 | h6882
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6883 | h6883
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6884 | h6884
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6885 | h6885
                      · linarith only [h6253, h6254, h6878, h6885, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6887 | h6887
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6888 | h6888
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6889 | h6889
                            · linarith only [h6253, h6254, h6882, h6885, h6889, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6891 | h6891
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6892 | h6892
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6893 | h6893
                                  · rcases h0bigk with h6894c | h6894c | h6894c | h6894c | h6894c | h6894c | h6894c | h6894c | h6894c | h6894c | h6894c | h6894c | h6894c | h6894c | h6894c | h6894c | h6894c | h6894c | h6894c | h6894c | h6894c | h6894c | h6894c | h6894c | h6894c
                                    · have p6894_0 := h6894c.1
                                      have p6894_1 := h6894c.2.1
                                      have p6894_2 := h6894c.2.2.1
                                      have p6894_3 := h6894c.2.2.2
                                      linarith only [hlam, p6894_0]
                                    · have p6894_0 := h6894c.1
                                      have p6894_1 := h6894c.2.1
                                      have p6894_2 := h6894c.2.2.1
                                      have p6894_3 := h6894c.2.2.2
                                      linarith only [h0, hlam, p6894_1]
                                    · have p6894_0 := h6894c.1
                                      have p6894_1 := h6894c.2.1
                                      have p6894_2 := h6894c.2.2.1
                                      have p6894_3 := h6894c.2.2.2
                                      linarith only [h6253, h6254, h6882, h6885, h6891, h6893, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p6894_1]
                                    · have p6894_0 := h6894c.1
                                      have p6894_1 := h6894c.2.1
                                      have p6894_2 := h6894c.2.2.1
                                      have p6894_3 := h6894c.2.2.2
                                      linarith only [h6254, hlam, p6894_1]
                                    · have p6894_0 := h6894c.1
                                      have p6894_1 := h6894c.2.1
                                      have p6894_2 := h6894c.2.2.1
                                      have p6894_3 := h6894c.2.2.2
                                      linarith only [h6254, h6885, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p6894_1]
                                    · have p6894_0 := h6894c.1
                                      have p6894_1 := h6894c.2.1
                                      have p6894_2 := h6894c.2.2.1
                                      have p6894_3 := h6894c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p6894_1]
                                    · have p6894_0 := h6894c.1
                                      have p6894_1 := h6894c.2.1
                                      have p6894_2 := h6894c.2.2.1
                                      have p6894_3 := h6894c.2.2.2
                                      linarith only [hlam, p6894_0]
                                    · have p6894_0 := h6894c.1
                                      have p6894_1 := h6894c.2.1
                                      have p6894_2 := h6894c.2.2.1
                                      have p6894_3 := h6894c.2.2.2
                                      linarith only [h0, h6253, h6882, h6891, h6893, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6894_1]
                                    · have p6894_0 := h6894c.1
                                      have p6894_1 := h6894c.2.1
                                      have p6894_2 := h6894c.2.2.1
                                      have p6894_3 := h6894c.2.2.2
                                      linarith only [h0, h6253, h6254, h6882, h6891, h6893, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6894_1]
                                    · have p6894_0 := h6894c.1
                                      have p6894_1 := h6894c.2.1
                                      have p6894_2 := h6894c.2.2.1
                                      have p6894_3 := h6894c.2.2.2
                                      rcases p6894_3 (m.d 0 1) (by simp) with h6904 | h6904
                                      · linarith only [h0, h6904, hlam]
                                      · linarith only [h6874, h6904, hlam]
                                    · have p6894_0 := h6894c.1
                                      have p6894_1 := h6894c.2.1
                                      have p6894_2 := h6894c.2.2.1
                                      have p6894_3 := h6894c.2.2.2
                                      linarith only [h6253, hlam, p6894_1]
                                    · have p6894_0 := h6894c.1
                                      have p6894_1 := h6894c.2.1
                                      have p6894_2 := h6894c.2.2.1
                                      have p6894_3 := h6894c.2.2.2
                                      linarith only [h6875, hlam, p6894_1]
                                    · have p6894_0 := h6894c.1
                                      have p6894_1 := h6894c.2.1
                                      have p6894_2 := h6894c.2.2.1
                                      have p6894_3 := h6894c.2.2.2
                                      linarith only [hlam, p6894_0]
                                    · have p6894_0 := h6894c.1
                                      have p6894_1 := h6894c.2.1
                                      have p6894_2 := h6894c.2.2.1
                                      have p6894_3 := h6894c.2.2.2
                                      linarith only [h6878, hlam, p6894_1]
                                    · have p6894_0 := h6894c.1
                                      have p6894_1 := h6894c.2.1
                                      have p6894_2 := h6894c.2.2.1
                                      have p6894_3 := h6894c.2.2.2
                                      linarith only [h0, h6253, h6874, h6884, h6891, h6893, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6894_1]
                                    · have p6894_0 := h6894c.1
                                      have p6894_1 := h6894c.2.1
                                      have p6894_2 := h6894c.2.2.1
                                      have p6894_3 := h6894c.2.2.2
                                      linarith only [h6253, h6882, h6891, h6893, hc04, hc45, hlam, hphi, ht0b, ht5b, p6894_1]
                                    · have p6894_0 := h6894c.1
                                      have p6894_1 := h6894c.2.1
                                      have p6894_2 := h6894c.2.2.1
                                      have p6894_3 := h6894c.2.2.2
                                      linarith only [h6876, hlam, p6894_0]
                                    · have p6894_0 := h6894c.1
                                      have p6894_1 := h6894c.2.1
                                      have p6894_2 := h6894c.2.2.1
                                      have p6894_3 := h6894c.2.2.2
                                      linarith only [h6254, h6885, hc03, hc34, hlam, hphi, p6894_1]
                                    · have p6894_0 := h6894c.1
                                      have p6894_1 := h6894c.2.1
                                      have p6894_2 := h6894c.2.2.1
                                      have p6894_3 := h6894c.2.2.2
                                      linarith only [hlam, p6894_0]
                                    · have p6894_0 := h6894c.1
                                      have p6894_1 := h6894c.2.1
                                      have p6894_2 := h6894c.2.2.1
                                      have p6894_3 := h6894c.2.2.2
                                      rcases p6894_3 (m.d 0 1) (by simp) with h6916 | h6916
                                      · linarith only [h6254, h6916, hlam]
                                      · linarith only [h6874, h6916, hlam]
                                    · have p6894_0 := h6894c.1
                                      have p6894_1 := h6894c.2.1
                                      have p6894_2 := h6894c.2.2.1
                                      have p6894_3 := h6894c.2.2.2
                                      linarith only [h6874, hlam, p6894_0]
                                    · have p6894_0 := h6894c.1
                                      have p6894_1 := h6894c.2.1
                                      have p6894_2 := h6894c.2.2.1
                                      have p6894_3 := h6894c.2.2.2
                                      linarith only [h6877, hlam, p6894_1]
                                    · have p6894_0 := h6894c.1
                                      have p6894_1 := h6894c.2.1
                                      have p6894_2 := h6894c.2.2.1
                                      have p6894_3 := h6894c.2.2.2
                                      linarith only [h6880, hlam, p6894_0]
                                    · have p6894_0 := h6894c.1
                                      have p6894_1 := h6894c.2.1
                                      have p6894_2 := h6894c.2.2.1
                                      have p6894_3 := h6894c.2.2.2
                                      linarith only [h6881, hlam, p6894_1]
                                    · have p6894_0 := h6894c.1
                                      have p6894_1 := h6894c.2.1
                                      have p6894_2 := h6894c.2.2.1
                                      have p6894_3 := h6894c.2.2.2
                                      linarith only [hlam, p6894_0]
                                  · linarith only [h6253, h6254, h6885, h6893, hc13, hc45, hlam, hphi, ht34]
                                · linarith only [h6254, h6874, h6885, h6888, h6889, h6891, h6892, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h6253, h6254, h6880, h6885, h6891, hc23, hc34, hlam, hphi]
                          · linarith only [h6253, h6254, h6888, hc13, hc45, hlam, hphi, ht34]
                        · linarith only [h6253, h6254, h6880, h6885, h6887, hc13, hc34, hlam, hphi]
                    · linarith only [h0, h6877, h6884, hlam]
                  · linarith only [h0, h6876, h6883, hlam]
                · linarith only [h0, h6875, h6882, hlam]
              · linarith only [h6254, h6874, h6881, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6933 | h6933
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6934 | h6934
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6935 | h6935
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6936 | h6936
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6937 | h6937
                      · linarith only [h6253, h6254, h6878, h6935, h6937, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6939 | h6939
                        · linarith only [h6253, h6880, h6939, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6941 | h6941
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6942 | h6942
                            · linarith only [h6254, h6874, h6875, h6937, h6939, h6942, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6944 | h6944
                              · linarith only [h6253, h6880, h6934, h6944, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6946 | h6946
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6947 | h6947
                                  · rcases h0bigk with h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c | h6948c
                                    · have p6948_0 := h6948c.1
                                      have p6948_1 := h6948c.2.1
                                      have p6948_2 := h6948c.2.2.1
                                      have p6948_3 := h6948c.2.2.2
                                      linarith only [hlam, p6948_0]
                                    · have p6948_0 := h6948c.1
                                      have p6948_1 := h6948c.2.1
                                      have p6948_2 := h6948c.2.2.1
                                      have p6948_3 := h6948c.2.2.2
                                      linarith only [h0, hlam, p6948_1]
                                    · have p6948_0 := h6948c.1
                                      have p6948_1 := h6948c.2.1
                                      have p6948_2 := h6948c.2.2.1
                                      have p6948_3 := h6948c.2.2.2
                                      linarith only [h6253, h6254, h6934, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6948_1]
                                    · have p6948_0 := h6948c.1
                                      have p6948_1 := h6948c.2.1
                                      have p6948_2 := h6948c.2.2.1
                                      have p6948_3 := h6948c.2.2.2
                                      linarith only [h6254, hlam, p6948_1]
                                    · have p6948_0 := h6948c.1
                                      have p6948_1 := h6948c.2.1
                                      have p6948_2 := h6948c.2.2.1
                                      have p6948_3 := h6948c.2.2.2
                                      linarith only [h6253, h6254, h6880, h6934, h6937, hc23, hc34, hlam, hphi, p6948_1]
                                    · have p6948_0 := h6948c.1
                                      have p6948_1 := h6948c.2.1
                                      have p6948_2 := h6948c.2.2.1
                                      have p6948_3 := h6948c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p6948_1]
                                    · have p6948_0 := h6948c.1
                                      have p6948_1 := h6948c.2.1
                                      have p6948_2 := h6948c.2.2.1
                                      have p6948_3 := h6948c.2.2.2
                                      linarith only [hlam, p6948_0]
                                    · have p6948_0 := h6948c.1
                                      have p6948_1 := h6948c.2.1
                                      have p6948_2 := h6948c.2.2.1
                                      have p6948_3 := h6948c.2.2.2
                                      rcases p6948_3 (m.d 0 1) (by simp) with h6956 | h6956
                                      · linarith only [h0, h6956, hlam]
                                      · linarith only [h6253, h6956, hlam]
                                    · have p6948_0 := h6948c.1
                                      have p6948_1 := h6948c.2.1
                                      have p6948_2 := h6948c.2.2.1
                                      have p6948_3 := h6948c.2.2.2
                                      linarith only [h0, h6254, h6874, h6934, h6939, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6948_1]
                                    · have p6948_0 := h6948c.1
                                      have p6948_1 := h6948c.2.1
                                      have p6948_2 := h6948c.2.2.1
                                      have p6948_3 := h6948c.2.2.2
                                      rcases p6948_3 (m.d 0 1) (by simp) with h6960 | h6960
                                      · linarith only [h0, h6960, hlam]
                                      · linarith only [h6874, h6960, hlam]
                                    · have p6948_0 := h6948c.1
                                      have p6948_1 := h6948c.2.1
                                      have p6948_2 := h6948c.2.2.1
                                      have p6948_3 := h6948c.2.2.2
                                      linarith only [h6253, hlam, p6948_1]
                                    · have p6948_0 := h6948c.1
                                      have p6948_1 := h6948c.2.1
                                      have p6948_2 := h6948c.2.2.1
                                      have p6948_3 := h6948c.2.2.2
                                      linarith only [h6875, hlam, p6948_1]
                                    · have p6948_0 := h6948c.1
                                      have p6948_1 := h6948c.2.1
                                      have p6948_2 := h6948c.2.2.1
                                      have p6948_3 := h6948c.2.2.2
                                      linarith only [hlam, p6948_0]
                                    · have p6948_0 := h6948c.1
                                      have p6948_1 := h6948c.2.1
                                      have p6948_2 := h6948c.2.2.1
                                      have p6948_3 := h6948c.2.2.2
                                      linarith only [h6878, hlam, p6948_1]
                                    · have p6948_0 := h6948c.1
                                      have p6948_1 := h6948c.2.1
                                      have p6948_2 := h6948c.2.2.1
                                      have p6948_3 := h6948c.2.2.2
                                      linarith only [h6880, hlam, p6948_1]
                                    · have p6948_0 := h6948c.1
                                      have p6948_1 := h6948c.2.1
                                      have p6948_2 := h6948c.2.2.1
                                      have p6948_3 := h6948c.2.2.2
                                      linarith only [h6874, h6934, h6939, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6948_1]
                                    · have p6948_0 := h6948c.1
                                      have p6948_1 := h6948c.2.1
                                      have p6948_2 := h6948c.2.2.1
                                      have p6948_3 := h6948c.2.2.2
                                      linarith only [h6876, hlam, p6948_0]
                                    · have p6948_0 := h6948c.1
                                      have p6948_1 := h6948c.2.1
                                      have p6948_2 := h6948c.2.2.1
                                      have p6948_3 := h6948c.2.2.2
                                      linarith only [h6253, h6254, h6934, h6937, hc23, hc34, hlam, hphi, p6948_1]
                                    · have p6948_0 := h6948c.1
                                      have p6948_1 := h6948c.2.1
                                      have p6948_2 := h6948c.2.2.1
                                      have p6948_3 := h6948c.2.2.2
                                      linarith only [hlam, p6948_0]
                                    · have p6948_0 := h6948c.1
                                      have p6948_1 := h6948c.2.1
                                      have p6948_2 := h6948c.2.2.1
                                      have p6948_3 := h6948c.2.2.2
                                      linarith only [h6253, h6254, h6880, h6934, h6937, hc23, hc34, hlam, hphi, p6948_1]
                                    · have p6948_0 := h6948c.1
                                      have p6948_1 := h6948c.2.1
                                      have p6948_2 := h6948c.2.2.1
                                      have p6948_3 := h6948c.2.2.2
                                      linarith only [h6874, hlam, p6948_0]
                                    · have p6948_0 := h6948c.1
                                      have p6948_1 := h6948c.2.1
                                      have p6948_2 := h6948c.2.2.1
                                      have p6948_3 := h6948c.2.2.2
                                      linarith only [h6877, hlam, p6948_1]
                                    · have p6948_0 := h6948c.1
                                      have p6948_1 := h6948c.2.1
                                      have p6948_2 := h6948c.2.2.1
                                      have p6948_3 := h6948c.2.2.2
                                      linarith only [h0, h6253, h6874, h6934, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6948_1]
                                    · have p6948_0 := h6948c.1
                                      have p6948_1 := h6948c.2.1
                                      have p6948_2 := h6948c.2.2.1
                                      have p6948_3 := h6948c.2.2.2
                                      linarith only [h6933, hlam, p6948_1]
                                    · have p6948_0 := h6948c.1
                                      have p6948_1 := h6948c.2.1
                                      have p6948_2 := h6948c.2.2.1
                                      have p6948_3 := h6948c.2.2.2
                                      linarith only [hlam, p6948_0]
                                  · linarith only [h6253, h6254, h6934, h6937, h6947, hc23, hc45, hlam, hphi, ht34]
                                · linarith only [h6254, h6874, h6937, h6941, h6942, h6946, hc23, hc34, hlam, hphi]
                          · linarith only [h6254, h6874, h6939, h6941, hc13, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h6877, h6936, hlam]
                  · linarith only [h0, h6876, h6935, hlam]
                · linarith only [h0, h6875, h6934, hlam]
              · linarith only [h6254, h6874, h6933, hlam]
        · linarith only [h0, h6874, h6877, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h6986 | h6986
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6987 | h6987
          · linarith only [h0, h6253, h6876, h6987, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6989 | h6989
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6990 | h6990
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6991 | h6991
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6992 | h6992
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6993 | h6993
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6994 | h6994
                      · linarith only [h0, h6253, h6876, h6987, h6992, h6994, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6996 | h6996
                        · linarith only [h0, h6253, h6876, h6992, h6996, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h0, h6253, h6876, h6989, h6991, h6992, h6996, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h6876, h6992, h6993, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7000 | h7000
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7001 | h7001
                      · linarith only [h0, h6253, h6876, h6987, h6992, h7001, hc02, hc24, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7003 | h7003
                        · linarith only [h0, h6253, h6992, h7003, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h0, h6253, h6989, h6992, h7003, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h0, h6874, h6876, h6986, h7000, hc04, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h6875, h6991, hlam]
              · linarith only [h0, h6253, h6876, h6989, h6990, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7009 | h7009
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7010 | h7010
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7011 | h7011
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7012 | h7012
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7013 | h7013
                      · linarith only [h0, h6253, h6876, h6987, h7011, h7013, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7015 | h7015
                        · linarith only [h0, h6253, h6876, h6989, h7011, h7015, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7017 | h7017
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7018 | h7018
                            · linarith only [h6254, h6874, h6875, h7013, h7015, h7018, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7020 | h7020
                              · linarith only [h0, h6874, h6876, h6989, h7010, h7011, h7015, h7020, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7022 | h7022
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7023 | h7023
                                  · rcases h0bigk with h7024c | h7024c | h7024c | h7024c | h7024c | h7024c | h7024c | h7024c | h7024c | h7024c | h7024c | h7024c | h7024c | h7024c | h7024c | h7024c | h7024c | h7024c | h7024c | h7024c | h7024c | h7024c | h7024c | h7024c | h7024c
                                    · have p7024_0 := h7024c.1
                                      have p7024_1 := h7024c.2.1
                                      have p7024_2 := h7024c.2.2.1
                                      have p7024_3 := h7024c.2.2.2
                                      linarith only [hlam, p7024_0]
                                    · have p7024_0 := h7024c.1
                                      have p7024_1 := h7024c.2.1
                                      have p7024_2 := h7024c.2.2.1
                                      have p7024_3 := h7024c.2.2.2
                                      linarith only [h0, hlam, p7024_1]
                                    · have p7024_0 := h7024c.1
                                      have p7024_1 := h7024c.2.1
                                      have p7024_2 := h7024c.2.2.1
                                      have p7024_3 := h7024c.2.2.2
                                      linarith only [h0, h6876, h7011, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7024_1]
                                    · have p7024_0 := h7024c.1
                                      have p7024_1 := h7024c.2.1
                                      have p7024_2 := h7024c.2.2.1
                                      have p7024_3 := h7024c.2.2.2
                                      linarith only [h6254, hlam, p7024_1]
                                    · have p7024_0 := h7024c.1
                                      have p7024_1 := h7024c.2.1
                                      have p7024_2 := h7024c.2.2.1
                                      have p7024_3 := h7024c.2.2.2
                                      linarith only [h0, h6876, h7011, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p7024_1]
                                    · have p7024_0 := h7024c.1
                                      have p7024_1 := h7024c.2.1
                                      have p7024_2 := h7024c.2.2.1
                                      have p7024_3 := h7024c.2.2.2
                                      linarith only [h6876, h7011, hc01, hc12, hlam, hphi, p7024_1]
                                    · have p7024_0 := h7024c.1
                                      have p7024_1 := h7024c.2.1
                                      have p7024_2 := h7024c.2.2.1
                                      have p7024_3 := h7024c.2.2.2
                                      linarith only [hlam, p7024_0]
                                    · have p7024_0 := h7024c.1
                                      have p7024_1 := h7024c.2.1
                                      have p7024_2 := h7024c.2.2.1
                                      have p7024_3 := h7024c.2.2.2
                                      linarith only [h6253, h6876, h7010, h7011, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7024_1]
                                    · have p7024_0 := h7024c.1
                                      have p7024_1 := h7024c.2.1
                                      have p7024_2 := h7024c.2.2.1
                                      have p7024_3 := h7024c.2.2.2
                                      linarith only [h6876, hlam, p7024_1]
                                    · have p7024_0 := h7024c.1
                                      have p7024_1 := h7024c.2.1
                                      have p7024_2 := h7024c.2.2.1
                                      have p7024_3 := h7024c.2.2.2
                                      linarith only [h6874, h6876, h7011, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p7024_1]
                                    · have p7024_0 := h7024c.1
                                      have p7024_1 := h7024c.2.1
                                      have p7024_2 := h7024c.2.2.1
                                      have p7024_3 := h7024c.2.2.2
                                      linarith only [h6253, hlam, p7024_1]
                                    · have p7024_0 := h7024c.1
                                      have p7024_1 := h7024c.2.1
                                      have p7024_2 := h7024c.2.2.1
                                      have p7024_3 := h7024c.2.2.2
                                      linarith only [h6875, hlam, p7024_1]
                                    · have p7024_0 := h7024c.1
                                      have p7024_1 := h7024c.2.1
                                      have p7024_2 := h7024c.2.2.1
                                      have p7024_3 := h7024c.2.2.2
                                      linarith only [hlam, p7024_0]
                                    · have p7024_0 := h7024c.1
                                      have p7024_1 := h7024c.2.1
                                      have p7024_2 := h7024c.2.2.1
                                      have p7024_3 := h7024c.2.2.2
                                      linarith only [h6987, hlam, p7024_1]
                                    · have p7024_0 := h7024c.1
                                      have p7024_1 := h7024c.2.1
                                      have p7024_2 := h7024c.2.2.1
                                      have p7024_3 := h7024c.2.2.2
                                      linarith only [h6989, hlam, p7024_1]
                                    · have p7024_0 := h7024c.1
                                      have p7024_1 := h7024c.2.1
                                      have p7024_2 := h7024c.2.2.1
                                      have p7024_3 := h7024c.2.2.2
                                      linarith only [h6253, h6876, h7010, h7011, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7024_1]
                                    · have p7024_0 := h7024c.1
                                      have p7024_1 := h7024c.2.1
                                      have p7024_2 := h7024c.2.2.1
                                      have p7024_3 := h7024c.2.2.2
                                      linarith only [h6876, h7011, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p7024_1]
                                    · have p7024_0 := h7024c.1
                                      have p7024_1 := h7024c.2.1
                                      have p7024_2 := h7024c.2.2.1
                                      have p7024_3 := h7024c.2.2.2
                                      linarith only [h6253, h6876, h7010, h7011, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7024_1]
                                    · have p7024_0 := h7024c.1
                                      have p7024_1 := h7024c.2.1
                                      have p7024_2 := h7024c.2.2.1
                                      have p7024_3 := h7024c.2.2.2
                                      linarith only [hlam, p7024_0]
                                    · have p7024_0 := h7024c.1
                                      have p7024_1 := h7024c.2.1
                                      have p7024_2 := h7024c.2.2.1
                                      have p7024_3 := h7024c.2.2.2
                                      linarith only [h6253, h6876, h6989, h7010, h7011, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7024_1]
                                    · have p7024_0 := h7024c.1
                                      have p7024_1 := h7024c.2.1
                                      have p7024_2 := h7024c.2.2.1
                                      have p7024_3 := h7024c.2.2.2
                                      linarith only [h6874, hlam, p7024_0]
                                    · have p7024_0 := h7024c.1
                                      have p7024_1 := h7024c.2.1
                                      have p7024_2 := h7024c.2.2.1
                                      have p7024_3 := h7024c.2.2.2
                                      linarith only [h6986, hlam, p7024_1]
                                    · have p7024_0 := h7024c.1
                                      have p7024_1 := h7024c.2.1
                                      have p7024_2 := h7024c.2.2.1
                                      have p7024_3 := h7024c.2.2.2
                                      linarith only [h0, h6253, h6874, h7010, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7024_1]
                                    · have p7024_0 := h7024c.1
                                      have p7024_1 := h7024c.2.1
                                      have p7024_2 := h7024c.2.2.1
                                      have p7024_3 := h7024c.2.2.2
                                      linarith only [h7009, hlam, p7024_1]
                                    · have p7024_0 := h7024c.1
                                      have p7024_1 := h7024c.2.1
                                      have p7024_2 := h7024c.2.2.1
                                      have p7024_3 := h7024c.2.2.2
                                      linarith only [hlam, p7024_0]
                                  · linarith only [h6253, h6254, h7010, h7013, h7023, hc23, hc45, hlam, hphi, ht34]
                                · linarith only [h0, h6874, h6876, h7010, h7015, h7022, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h0, h6874, h6876, h7009, h7011, h7017, hlam]
                    · linarith only [h6876, h6986, h7012, hc12, hc24, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7054 | h7054
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7055 | h7055
                      · linarith only [h0, h6253, h6987, h7011, h7055, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7057 | h7057
                        · linarith only [h6253, h6989, h7057, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7059 | h7059
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7060 | h7060
                            · linarith only [h0, h6874, h7010, h7011, h7055, h7057, h7060, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h6874, h7010, h7011, h7057, h7060, hc23, hc34, hlam, hphi]
                          · linarith only [h0, h6874, h7010, h7011, h7057, h7059, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h6874, h6876, h6986, h7054, hc04, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h6875, h7010, hlam]
              · linarith only [h0, h6874, h6876, h7009, hlam]
        · linarith only [h0, h6874, h6986, hlam]
    · linarith only [h0, h6253, h6875, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h7069 | h7069
    · rcases m.htr 0 2 4 (by decide) (by decide) with h7070 | h7070
      · rcases m.htr 0 2 5 (by decide) (by decide) with h7071 | h7071
        · rcases m.htr 0 3 4 (by decide) (by decide) with h7072 | h7072
          · linarith only [h6253, h6254, h7072, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h7074 | h7074
            · linarith only [h6253, h6874, h7074, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7076 | h7076
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7077 | h7077
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7078 | h7078
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7079 | h7079
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7080 | h7080
                      · linarith only [h6253, h6254, h7072, h7078, h7080, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7082 | h7082
                        · linarith only [h6253, h6874, h7074, h7082, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7084 | h7084
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7085 | h7085
                            · linarith only [h6253, h6874, h7069, h7080, h7084, h7085, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7087 | h7087
                              · linarith only [h6253, h6874, h7077, h7082, h7087, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7089 | h7089
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7090 | h7090
                                  · rcases h0bigk with h7091c | h7091c | h7091c | h7091c | h7091c | h7091c | h7091c | h7091c | h7091c | h7091c | h7091c | h7091c | h7091c | h7091c | h7091c | h7091c | h7091c | h7091c | h7091c | h7091c | h7091c | h7091c | h7091c | h7091c | h7091c
                                    · have p7091_0 := h7091c.1
                                      have p7091_1 := h7091c.2.1
                                      have p7091_2 := h7091c.2.2.1
                                      have p7091_3 := h7091c.2.2.2
                                      linarith only [hlam, p7091_0]
                                    · have p7091_0 := h7091c.1
                                      have p7091_1 := h7091c.2.1
                                      have p7091_2 := h7091c.2.2.1
                                      have p7091_3 := h7091c.2.2.2
                                      linarith only [h0, hlam, p7091_1]
                                    · have p7091_0 := h7091c.1
                                      have p7091_1 := h7091c.2.1
                                      have p7091_2 := h7091c.2.2.1
                                      have p7091_3 := h7091c.2.2.2
                                      linarith only [h6253, h6874, h7077, h7084, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7091_1]
                                    · have p7091_0 := h7091c.1
                                      have p7091_1 := h7091c.2.1
                                      have p7091_2 := h7091c.2.2.1
                                      have p7091_3 := h7091c.2.2.2
                                      linarith only [h6254, hlam, p7091_1]
                                    · have p7091_0 := h7091c.1
                                      have p7091_1 := h7091c.2.1
                                      have p7091_2 := h7091c.2.2.1
                                      have p7091_3 := h7091c.2.2.2
                                      linarith only [h6874, hlam, p7091_1]
                                    · have p7091_0 := h7091c.1
                                      have p7091_1 := h7091c.2.1
                                      have p7091_2 := h7091c.2.2.1
                                      have p7091_3 := h7091c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p7091_1]
                                    · have p7091_0 := h7091c.1
                                      have p7091_1 := h7091c.2.1
                                      have p7091_2 := h7091c.2.2.1
                                      have p7091_3 := h7091c.2.2.2
                                      linarith only [hlam, p7091_0]
                                    · have p7091_0 := h7091c.1
                                      have p7091_1 := h7091c.2.1
                                      have p7091_2 := h7091c.2.2.1
                                      have p7091_3 := h7091c.2.2.2
                                      rcases p7091_3 (m.d 0 1) (by simp) with h7099 | h7099
                                      · linarith only [h0, h7099, hlam]
                                      · linarith only [h6253, h7099, hlam]
                                    · have p7091_0 := h7091c.1
                                      have p7091_1 := h7091c.2.1
                                      have p7091_2 := h7091c.2.2.1
                                      have p7091_3 := h7091c.2.2.2
                                      linarith only [h0, h6253, h6874, h7076, h7077, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7091_1]
                                    · have p7091_0 := h7091c.1
                                      have p7091_1 := h7091c.2.1
                                      have p7091_2 := h7091c.2.2.1
                                      have p7091_3 := h7091c.2.2.2
                                      linarith only [h0, h6253, h6874, h7077, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7091_1]
                                    · have p7091_0 := h7091c.1
                                      have p7091_1 := h7091c.2.1
                                      have p7091_2 := h7091c.2.2.1
                                      have p7091_3 := h7091c.2.2.2
                                      linarith only [h6253, hlam, p7091_1]
                                    · have p7091_0 := h7091c.1
                                      have p7091_1 := h7091c.2.1
                                      have p7091_2 := h7091c.2.2.1
                                      have p7091_3 := h7091c.2.2.2
                                      linarith only [h7069, hlam, p7091_1]
                                    · have p7091_0 := h7091c.1
                                      have p7091_1 := h7091c.2.1
                                      have p7091_2 := h7091c.2.2.1
                                      have p7091_3 := h7091c.2.2.2
                                      linarith only [hlam, p7091_0]
                                    · have p7091_0 := h7091c.1
                                      have p7091_1 := h7091c.2.1
                                      have p7091_2 := h7091c.2.2.1
                                      have p7091_3 := h7091c.2.2.2
                                      linarith only [h7072, hlam, p7091_1]
                                    · have p7091_0 := h7091c.1
                                      have p7091_1 := h7091c.2.1
                                      have p7091_2 := h7091c.2.2.1
                                      have p7091_3 := h7091c.2.2.2
                                      linarith only [h7074, hlam, p7091_1]
                                    · have p7091_0 := h7091c.1
                                      have p7091_1 := h7091c.2.1
                                      have p7091_2 := h7091c.2.2.1
                                      have p7091_3 := h7091c.2.2.2
                                      linarith only [h6253, h7077, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7091_1]
                                    · have p7091_0 := h7091c.1
                                      have p7091_1 := h7091c.2.1
                                      have p7091_2 := h7091c.2.2.1
                                      have p7091_3 := h7091c.2.2.2
                                      linarith only [h7070, hlam, p7091_0]
                                    · have p7091_0 := h7091c.1
                                      have p7091_1 := h7091c.2.1
                                      have p7091_2 := h7091c.2.2.1
                                      have p7091_3 := h7091c.2.2.2
                                      linarith only [h6253, h6254, h7077, h7080, hc23, hc34, hlam, hphi, p7091_1]
                                    · have p7091_0 := h7091c.1
                                      have p7091_1 := h7091c.2.1
                                      have p7091_2 := h7091c.2.2.1
                                      have p7091_3 := h7091c.2.2.2
                                      linarith only [hlam, p7091_0]
                                    · have p7091_0 := h7091c.1
                                      have p7091_1 := h7091c.2.1
                                      have p7091_2 := h7091c.2.2.1
                                      have p7091_3 := h7091c.2.2.2
                                      linarith only [h6253, h6254, h6874, h7077, h7080, hc23, hc34, hlam, hphi, p7091_1]
                                    · have p7091_0 := h7091c.1
                                      have p7091_1 := h7091c.2.1
                                      have p7091_2 := h7091c.2.2.1
                                      have p7091_3 := h7091c.2.2.2
                                      linarith only [h6253, h7077, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7091_1]
                                    · have p7091_0 := h7091c.1
                                      have p7091_1 := h7091c.2.1
                                      have p7091_2 := h7091c.2.2.1
                                      have p7091_3 := h7091c.2.2.2
                                      linarith only [h7071, hlam, p7091_1]
                                    · have p7091_0 := h7091c.1
                                      have p7091_1 := h7091c.2.1
                                      have p7091_2 := h7091c.2.2.1
                                      have p7091_3 := h7091c.2.2.2
                                      linarith only [h6253, h6874, h7077, h7082, hc23, hc35, hlam, hphi, p7091_1]
                                    · have p7091_0 := h7091c.1
                                      have p7091_1 := h7091c.2.1
                                      have p7091_2 := h7091c.2.2.1
                                      have p7091_3 := h7091c.2.2.2
                                      linarith only [h7076, hlam, p7091_1]
                                    · have p7091_0 := h7091c.1
                                      have p7091_1 := h7091c.2.1
                                      have p7091_2 := h7091c.2.2.1
                                      have p7091_3 := h7091c.2.2.2
                                      linarith only [hlam, p7091_0]
                                  · linarith only [h6253, h6254, h7077, h7080, h7090, hc23, hc45, hlam, hphi, ht34]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7120 | h7120
                                  · rcases h0bigk with h7121c | h7121c | h7121c | h7121c | h7121c | h7121c | h7121c | h7121c | h7121c | h7121c | h7121c | h7121c | h7121c | h7121c | h7121c | h7121c | h7121c | h7121c | h7121c | h7121c | h7121c | h7121c | h7121c | h7121c | h7121c
                                    · have p7121_0 := h7121c.1
                                      have p7121_1 := h7121c.2.1
                                      have p7121_2 := h7121c.2.2.1
                                      have p7121_3 := h7121c.2.2.2
                                      linarith only [hlam, p7121_0]
                                    · have p7121_0 := h7121c.1
                                      have p7121_1 := h7121c.2.1
                                      have p7121_2 := h7121c.2.2.1
                                      have p7121_3 := h7121c.2.2.2
                                      linarith only [h0, hlam, p7121_1]
                                    · have p7121_0 := h7121c.1
                                      have p7121_1 := h7121c.2.1
                                      have p7121_2 := h7121c.2.2.1
                                      have p7121_3 := h7121c.2.2.2
                                      linarith only [h6253, h6874, h7077, h7084, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7121_1]
                                    · have p7121_0 := h7121c.1
                                      have p7121_1 := h7121c.2.1
                                      have p7121_2 := h7121c.2.2.1
                                      have p7121_3 := h7121c.2.2.2
                                      linarith only [h6254, hlam, p7121_1]
                                    · have p7121_0 := h7121c.1
                                      have p7121_1 := h7121c.2.1
                                      have p7121_2 := h7121c.2.2.1
                                      have p7121_3 := h7121c.2.2.2
                                      linarith only [h6874, hlam, p7121_1]
                                    · have p7121_0 := h7121c.1
                                      have p7121_1 := h7121c.2.1
                                      have p7121_2 := h7121c.2.2.1
                                      have p7121_3 := h7121c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p7121_1]
                                    · have p7121_0 := h7121c.1
                                      have p7121_1 := h7121c.2.1
                                      have p7121_2 := h7121c.2.2.1
                                      have p7121_3 := h7121c.2.2.2
                                      linarith only [hlam, p7121_0]
                                    · have p7121_0 := h7121c.1
                                      have p7121_1 := h7121c.2.1
                                      have p7121_2 := h7121c.2.2.1
                                      have p7121_3 := h7121c.2.2.2
                                      rcases p7121_3 (m.d 0 1) (by simp) with h7129 | h7129
                                      · linarith only [h0, h7129, hlam]
                                      · linarith only [h6253, h7129, hlam]
                                    · have p7121_0 := h7121c.1
                                      have p7121_1 := h7121c.2.1
                                      have p7121_2 := h7121c.2.2.1
                                      have p7121_3 := h7121c.2.2.2
                                      linarith only [h0, h7076, h7089, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p7121_1]
                                    · have p7121_0 := h7121c.1
                                      have p7121_1 := h7121c.2.1
                                      have p7121_2 := h7121c.2.2.1
                                      have p7121_3 := h7121c.2.2.2
                                      linarith only [h0, h6253, h6874, h7077, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7121_1]
                                    · have p7121_0 := h7121c.1
                                      have p7121_1 := h7121c.2.1
                                      have p7121_2 := h7121c.2.2.1
                                      have p7121_3 := h7121c.2.2.2
                                      linarith only [h6253, hlam, p7121_1]
                                    · have p7121_0 := h7121c.1
                                      have p7121_1 := h7121c.2.1
                                      have p7121_2 := h7121c.2.2.1
                                      have p7121_3 := h7121c.2.2.2
                                      linarith only [h7069, hlam, p7121_1]
                                    · have p7121_0 := h7121c.1
                                      have p7121_1 := h7121c.2.1
                                      have p7121_2 := h7121c.2.2.1
                                      have p7121_3 := h7121c.2.2.2
                                      linarith only [hlam, p7121_0]
                                    · have p7121_0 := h7121c.1
                                      have p7121_1 := h7121c.2.1
                                      have p7121_2 := h7121c.2.2.1
                                      have p7121_3 := h7121c.2.2.2
                                      linarith only [h7072, hlam, p7121_1]
                                    · have p7121_0 := h7121c.1
                                      have p7121_1 := h7121c.2.1
                                      have p7121_2 := h7121c.2.2.1
                                      have p7121_3 := h7121c.2.2.2
                                      linarith only [h7074, hlam, p7121_1]
                                    · have p7121_0 := h7121c.1
                                      have p7121_1 := h7121c.2.1
                                      have p7121_2 := h7121c.2.2.1
                                      have p7121_3 := h7121c.2.2.2
                                      linarith only [h6253, h7077, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7121_1]
                                    · have p7121_0 := h7121c.1
                                      have p7121_1 := h7121c.2.1
                                      have p7121_2 := h7121c.2.2.1
                                      have p7121_3 := h7121c.2.2.2
                                      linarith only [h7070, hlam, p7121_0]
                                    · have p7121_0 := h7121c.1
                                      have p7121_1 := h7121c.2.1
                                      have p7121_2 := h7121c.2.2.1
                                      have p7121_3 := h7121c.2.2.2
                                      linarith only [h6253, h6254, h7077, h7080, hc23, hc34, hlam, hphi, p7121_1]
                                    · have p7121_0 := h7121c.1
                                      have p7121_1 := h7121c.2.1
                                      have p7121_2 := h7121c.2.2.1
                                      have p7121_3 := h7121c.2.2.2
                                      linarith only [hlam, p7121_0]
                                    · have p7121_0 := h7121c.1
                                      have p7121_1 := h7121c.2.1
                                      have p7121_2 := h7121c.2.2.1
                                      have p7121_3 := h7121c.2.2.2
                                      linarith only [h6253, h6254, h6874, h7077, h7080, hc23, hc34, hlam, hphi, p7121_1]
                                    · have p7121_0 := h7121c.1
                                      have p7121_1 := h7121c.2.1
                                      have p7121_2 := h7121c.2.2.1
                                      have p7121_3 := h7121c.2.2.2
                                      linarith only [h6253, h7077, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7121_1]
                                    · have p7121_0 := h7121c.1
                                      have p7121_1 := h7121c.2.1
                                      have p7121_2 := h7121c.2.2.1
                                      have p7121_3 := h7121c.2.2.2
                                      linarith only [h7071, hlam, p7121_1]
                                    · have p7121_0 := h7121c.1
                                      have p7121_1 := h7121c.2.1
                                      have p7121_2 := h7121c.2.2.1
                                      have p7121_3 := h7121c.2.2.2
                                      linarith only [h6253, h6874, h7077, h7080, h7084, hc23, hc34, hlam, hphi, p7121_1]
                                    · have p7121_0 := h7121c.1
                                      have p7121_1 := h7121c.2.1
                                      have p7121_2 := h7121c.2.2.1
                                      have p7121_3 := h7121c.2.2.2
                                      linarith only [h7076, hlam, p7121_1]
                                    · have p7121_0 := h7121c.1
                                      have p7121_1 := h7121c.2.1
                                      have p7121_2 := h7121c.2.2.1
                                      have p7121_3 := h7121c.2.2.2
                                      linarith only [hlam, p7121_0]
                                  · linarith only [h6253, h6254, h7077, h7080, h7120, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h6254, h7076, h7084, hlam]
                    · linarith only [h0, h7070, h7071, h7076, h7079, hlam]
                  · linarith only [h0, h7070, h7078, hlam]
                · linarith only [h0, h6253, h7069, h7077, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7154 | h7154
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7155 | h7155
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7156 | h7156
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7157 | h7157
                      · linarith only [h6253, h6254, h7072, h7157, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7159 | h7159
                        · linarith only [h6253, h6254, h7074, h7076, h7159, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7161 | h7161
                          · linarith only [h6253, h6254, h7076, h7154, h7157, h7161, hc23, hc34, hlam, hphi]
                          · linarith only [h6253, h6254, h7154, h7161, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h7071, h7156, hlam]
                  · linarith only [h0, h7070, h7155, hlam]
                · linarith only [h0, h7069, h7154, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h7167 | h7167
          · linarith only [h6253, h6254, h7167, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h7169 | h7169
            · linarith only [h0, h6253, h7071, h7169, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7171 | h7171
              · linarith only [h7070, h7071, h7171, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7173 | h7173
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7174 | h7174
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7175 | h7175
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7176 | h7176
                      · linarith only [h6253, h6254, h7070, h7071, h7167, h7175, h7176, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7178 | h7178
                        · linarith only [h6253, h6254, h7070, h7071, h7169, h7178, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7180 | h7180
                          · linarith only [h6253, h6254, h7171, h7173, h7176, h7180, hc23, hc34, hlam, hphi]
                          · linarith only [h6253, h6254, h7173, h7180, hc23, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7183 | h7183
                      · linarith only [h0, h6253, h7175, h7183, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7185 | h7185
                        · linarith only [h6253, h6254, h7174, h7175, h7185, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7187 | h7187
                          · linarith only [h6253, h6254, h7171, h7173, h7174, h7175, h7187, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                          · linarith only [h6253, h6254, h7173, h7187, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h6253, h7070, h7173, h7174, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h7069, h7173, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h7192 | h7192
        · rcases m.htr 0 3 4 (by decide) (by decide) with h7193 | h7193
          · linarith only [h0, h6253, h7070, h7193, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h7195 | h7195
            · linarith only [h6253, h6874, h7195, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7197 | h7197
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7198 | h7198
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7199 | h7199
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7200 | h7200
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7201 | h7201
                      · linarith only [h6253, h6874, h7070, h7192, h7193, h7199, h7201, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7203 | h7203
                        · linarith only [h6253, h6874, h7195, h7203, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7205 | h7205
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7206 | h7206
                            · linarith only [h6253, h6874, h7070, h7192, h7198, h7199, h7201, h7206, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7208 | h7208
                              · linarith only [h6253, h6874, h7070, h7192, h7198, h7199, h7208, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7210 | h7210
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7211 | h7211
                                  · rcases h0bigk with h7212c | h7212c | h7212c | h7212c | h7212c | h7212c | h7212c | h7212c | h7212c | h7212c | h7212c | h7212c | h7212c | h7212c | h7212c | h7212c | h7212c | h7212c | h7212c | h7212c | h7212c | h7212c | h7212c | h7212c | h7212c
                                    · have p7212_0 := h7212c.1
                                      have p7212_1 := h7212c.2.1
                                      have p7212_2 := h7212c.2.2.1
                                      have p7212_3 := h7212c.2.2.2
                                      linarith only [hlam, p7212_0]
                                    · have p7212_0 := h7212c.1
                                      have p7212_1 := h7212c.2.1
                                      have p7212_2 := h7212c.2.2.1
                                      have p7212_3 := h7212c.2.2.2
                                      linarith only [h0, hlam, p7212_1]
                                    · have p7212_0 := h7212c.1
                                      have p7212_1 := h7212c.2.1
                                      have p7212_2 := h7212c.2.2.1
                                      have p7212_3 := h7212c.2.2.2
                                      linarith only [h6253, h6874, h7070, h7192, h7198, h7199, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7212_1]
                                    · have p7212_0 := h7212c.1
                                      have p7212_1 := h7212c.2.1
                                      have p7212_2 := h7212c.2.2.1
                                      have p7212_3 := h7212c.2.2.2
                                      linarith only [h6254, hlam, p7212_1]
                                    · have p7212_0 := h7212c.1
                                      have p7212_1 := h7212c.2.1
                                      have p7212_2 := h7212c.2.2.1
                                      have p7212_3 := h7212c.2.2.2
                                      linarith only [h6874, hlam, p7212_1]
                                    · have p7212_0 := h7212c.1
                                      have p7212_1 := h7212c.2.1
                                      have p7212_2 := h7212c.2.2.1
                                      have p7212_3 := h7212c.2.2.2
                                      linarith only [h7070, h7199, hc01, hc12, hlam, hphi, p7212_1]
                                    · have p7212_0 := h7212c.1
                                      have p7212_1 := h7212c.2.1
                                      have p7212_2 := h7212c.2.2.1
                                      have p7212_3 := h7212c.2.2.2
                                      linarith only [hlam, p7212_0]
                                    · have p7212_0 := h7212c.1
                                      have p7212_1 := h7212c.2.1
                                      have p7212_2 := h7212c.2.2.1
                                      have p7212_3 := h7212c.2.2.2
                                      linarith only [h6253, h7070, h7198, h7199, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7212_1]
                                    · have p7212_0 := h7212c.1
                                      have p7212_1 := h7212c.2.1
                                      have p7212_2 := h7212c.2.2.1
                                      have p7212_3 := h7212c.2.2.2
                                      linarith only [h7070, hlam, p7212_1]
                                    · have p7212_0 := h7212c.1
                                      have p7212_1 := h7212c.2.1
                                      have p7212_2 := h7212c.2.2.1
                                      have p7212_3 := h7212c.2.2.2
                                      linarith only [h7070, h7199, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p7212_1]
                                    · have p7212_0 := h7212c.1
                                      have p7212_1 := h7212c.2.1
                                      have p7212_2 := h7212c.2.2.1
                                      have p7212_3 := h7212c.2.2.2
                                      linarith only [h6253, hlam, p7212_1]
                                    · have p7212_0 := h7212c.1
                                      have p7212_1 := h7212c.2.1
                                      have p7212_2 := h7212c.2.2.1
                                      have p7212_3 := h7212c.2.2.2
                                      linarith only [h7069, hlam, p7212_1]
                                    · have p7212_0 := h7212c.1
                                      have p7212_1 := h7212c.2.1
                                      have p7212_2 := h7212c.2.2.1
                                      have p7212_3 := h7212c.2.2.2
                                      linarith only [hlam, p7212_0]
                                    · have p7212_0 := h7212c.1
                                      have p7212_1 := h7212c.2.1
                                      have p7212_2 := h7212c.2.2.1
                                      have p7212_3 := h7212c.2.2.2
                                      linarith only [h7193, hlam, p7212_1]
                                    · have p7212_0 := h7212c.1
                                      have p7212_1 := h7212c.2.1
                                      have p7212_2 := h7212c.2.2.1
                                      have p7212_3 := h7212c.2.2.2
                                      linarith only [h7195, hlam, p7212_1]
                                    · have p7212_0 := h7212c.1
                                      have p7212_1 := h7212c.2.1
                                      have p7212_2 := h7212c.2.2.1
                                      have p7212_3 := h7212c.2.2.2
                                      linarith only [h6253, h7198, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7212_1]
                                    · have p7212_0 := h7212c.1
                                      have p7212_1 := h7212c.2.1
                                      have p7212_2 := h7212c.2.2.1
                                      have p7212_3 := h7212c.2.2.2
                                      linarith only [h7070, h7199, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p7212_1]
                                    · have p7212_0 := h7212c.1
                                      have p7212_1 := h7212c.2.1
                                      have p7212_2 := h7212c.2.2.1
                                      have p7212_3 := h7212c.2.2.2
                                      linarith only [h6253, h7070, h7198, h7199, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7212_1]
                                    · have p7212_0 := h7212c.1
                                      have p7212_1 := h7212c.2.1
                                      have p7212_2 := h7212c.2.2.1
                                      have p7212_3 := h7212c.2.2.2
                                      linarith only [hlam, p7212_0]
                                    · have p7212_0 := h7212c.1
                                      have p7212_1 := h7212c.2.1
                                      have p7212_2 := h7212c.2.2.1
                                      have p7212_3 := h7212c.2.2.2
                                      linarith only [h6253, h6874, h7070, h7198, h7199, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7212_1]
                                    · have p7212_0 := h7212c.1
                                      have p7212_1 := h7212c.2.1
                                      have p7212_2 := h7212c.2.2.1
                                      have p7212_3 := h7212c.2.2.2
                                      linarith only [h6253, h7192, h7198, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7212_1]
                                    · have p7212_0 := h7212c.1
                                      have p7212_1 := h7212c.2.1
                                      have p7212_2 := h7212c.2.2.1
                                      have p7212_3 := h7212c.2.2.2
                                      linarith only [h7192, hlam, p7212_1]
                                    · have p7212_0 := h7212c.1
                                      have p7212_1 := h7212c.2.1
                                      have p7212_2 := h7212c.2.2.1
                                      have p7212_3 := h7212c.2.2.2
                                      linarith only [h6253, h7070, h7192, h7198, h7199, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7212_1]
                                    · have p7212_0 := h7212c.1
                                      have p7212_1 := h7212c.2.1
                                      have p7212_2 := h7212c.2.2.1
                                      have p7212_3 := h7212c.2.2.2
                                      linarith only [h7197, hlam, p7212_1]
                                    · have p7212_0 := h7212c.1
                                      have p7212_1 := h7212c.2.1
                                      have p7212_2 := h7212c.2.2.1
                                      have p7212_3 := h7212c.2.2.2
                                      linarith only [hlam, p7212_0]
                                  · linarith only [h0, h6253, h7070, h7198, h7199, h7201, h7211, hc23, hc45, hlam, hphi, ht34]
                                · linarith only [h7070, h7192, h7197, h7210, hlam]
                          · linarith only [h7070, h7192, h7197, h7199, h7205, hlam]
                    · linarith only [h7070, h7192, h7199, h7200, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7242 | h7242
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7243 | h7243
                      · linarith only [h6253, h6874, h7193, h7199, h7242, h7243, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7245 | h7245
                        · linarith only [h6253, h6874, h7199, h7242, h7245, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7247 | h7247
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7248 | h7248
                            · linarith only [h6253, h6874, h7198, h7199, h7242, h7243, h7248, hlam]
                            · linarith only [h6253, h6874, h7198, h7199, h7242, h7248, hc23, hc34, hlam, hphi]
                          · linarith only [h6253, h6874, h7197, h7198, h7199, h7242, h7247, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h6253, h7192, h7198, h7242, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h7069, h7198, hlam]
              · linarith only [h7070, h7192, h7197, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h7255 | h7255
          · linarith only [h0, h6253, h7070, h7255, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h7257 | h7257
            · linarith only [h0, h6253, h7192, h7257, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7259 | h7259
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7260 | h7260
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7261 | h7261
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7262 | h7262
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7263 | h7263
                      · linarith only [h0, h6253, h7070, h7255, h7261, h7263, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7265 | h7265
                        · linarith only [h0, h6253, h7192, h7257, h7265, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7267 | h7267
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7268 | h7268
                            · linarith only [h7069, h7192, h7262, h7263, h7267, h7268, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7270 | h7270
                              · linarith only [h0, h6253, h7192, h7260, h7262, h7265, h7270, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7272 | h7272
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7273 | h7273
                                  · rcases h0bigk with h7274c | h7274c | h7274c | h7274c | h7274c | h7274c | h7274c | h7274c | h7274c | h7274c | h7274c | h7274c | h7274c | h7274c | h7274c | h7274c | h7274c | h7274c | h7274c | h7274c | h7274c | h7274c | h7274c | h7274c | h7274c
                                    · have p7274_0 := h7274c.1
                                      have p7274_1 := h7274c.2.1
                                      have p7274_2 := h7274c.2.2.1
                                      have p7274_3 := h7274c.2.2.2
                                      linarith only [hlam, p7274_0]
                                    · have p7274_0 := h7274c.1
                                      have p7274_1 := h7274c.2.1
                                      have p7274_2 := h7274c.2.2.1
                                      have p7274_3 := h7274c.2.2.2
                                      linarith only [h0, hlam, p7274_1]
                                    · have p7274_0 := h7274c.1
                                      have p7274_1 := h7274c.2.1
                                      have p7274_2 := h7274c.2.2.1
                                      have p7274_3 := h7274c.2.2.2
                                      linarith only [h0, h7192, h7261, h7272, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7274_1]
                                    · have p7274_0 := h7274c.1
                                      have p7274_1 := h7274c.2.1
                                      have p7274_2 := h7274c.2.2.1
                                      have p7274_3 := h7274c.2.2.2
                                      linarith only [h6254, hlam, p7274_1]
                                    · have p7274_0 := h7274c.1
                                      have p7274_1 := h7274c.2.1
                                      have p7274_2 := h7274c.2.2.1
                                      have p7274_3 := h7274c.2.2.2
                                      linarith only [h6874, hlam, p7274_1]
                                    · have p7274_0 := h7274c.1
                                      have p7274_1 := h7274c.2.1
                                      have p7274_2 := h7274c.2.2.1
                                      have p7274_3 := h7274c.2.2.2
                                      linarith only [h7192, h7261, h7272, hc01, hc12, hlam, hphi, p7274_1]
                                    · have p7274_0 := h7274c.1
                                      have p7274_1 := h7274c.2.1
                                      have p7274_2 := h7274c.2.2.1
                                      have p7274_3 := h7274c.2.2.2
                                      linarith only [hlam, p7274_0]
                                    · have p7274_0 := h7274c.1
                                      have p7274_1 := h7274c.2.1
                                      have p7274_2 := h7274c.2.2.1
                                      have p7274_3 := h7274c.2.2.2
                                      linarith only [h6253, h7192, h7260, h7261, h7272, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7274_1]
                                    · have p7274_0 := h7274c.1
                                      have p7274_1 := h7274c.2.1
                                      have p7274_2 := h7274c.2.2.1
                                      have p7274_3 := h7274c.2.2.2
                                      linarith only [h7070, hlam, p7274_1]
                                    · have p7274_0 := h7274c.1
                                      have p7274_1 := h7274c.2.1
                                      have p7274_2 := h7274c.2.2.1
                                      have p7274_3 := h7274c.2.2.2
                                      linarith only [h7192, hlam, p7274_0]
                                    · have p7274_0 := h7274c.1
                                      have p7274_1 := h7274c.2.1
                                      have p7274_2 := h7274c.2.2.1
                                      have p7274_3 := h7274c.2.2.2
                                      linarith only [h6253, hlam, p7274_1]
                                    · have p7274_0 := h7274c.1
                                      have p7274_1 := h7274c.2.1
                                      have p7274_2 := h7274c.2.2.1
                                      have p7274_3 := h7274c.2.2.2
                                      linarith only [h7069, hlam, p7274_1]
                                    · have p7274_0 := h7274c.1
                                      have p7274_1 := h7274c.2.1
                                      have p7274_2 := h7274c.2.2.1
                                      have p7274_3 := h7274c.2.2.2
                                      linarith only [hlam, p7274_0]
                                    · have p7274_0 := h7274c.1
                                      have p7274_1 := h7274c.2.1
                                      have p7274_2 := h7274c.2.2.1
                                      have p7274_3 := h7274c.2.2.2
                                      linarith only [h7255, hlam, p7274_1]
                                    · have p7274_0 := h7274c.1
                                      have p7274_1 := h7274c.2.1
                                      have p7274_2 := h7274c.2.2.1
                                      have p7274_3 := h7274c.2.2.2
                                      linarith only [h7257, hlam, p7274_1]
                                    · have p7274_0 := h7274c.1
                                      have p7274_1 := h7274c.2.1
                                      have p7274_2 := h7274c.2.2.1
                                      have p7274_3 := h7274c.2.2.2
                                      linarith only [h6253, h7260, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7274_1]
                                    · have p7274_0 := h7274c.1
                                      have p7274_1 := h7274c.2.1
                                      have p7274_2 := h7274c.2.2.1
                                      have p7274_3 := h7274c.2.2.2
                                      linarith only [h7070, h7261, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p7274_1]
                                    · have p7274_0 := h7274c.1
                                      have p7274_1 := h7274c.2.1
                                      have p7274_2 := h7274c.2.2.1
                                      have p7274_3 := h7274c.2.2.2
                                      linarith only [h6253, h7070, h7260, h7261, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7274_1]
                                    · have p7274_0 := h7274c.1
                                      have p7274_1 := h7274c.2.1
                                      have p7274_2 := h7274c.2.2.1
                                      have p7274_3 := h7274c.2.2.2
                                      linarith only [hlam, p7274_0]
                                    · have p7274_0 := h7274c.1
                                      have p7274_1 := h7274c.2.1
                                      have p7274_2 := h7274c.2.2.1
                                      have p7274_3 := h7274c.2.2.2
                                      linarith only [h0, h6253, h7070, h7192, h7260, h7261, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7274_1]
                                    · have p7274_0 := h7274c.1
                                      have p7274_1 := h7274c.2.1
                                      have p7274_2 := h7274c.2.2.1
                                      have p7274_3 := h7274c.2.2.2
                                      linarith only [h6253, h7260, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7274_1]
                                    · have p7274_0 := h7274c.1
                                      have p7274_1 := h7274c.2.1
                                      have p7274_2 := h7274c.2.2.1
                                      have p7274_3 := h7274c.2.2.2
                                      linarith only [h0, h6253, h7192, h7260, h7261, h7272, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7274_1]
                                    · have p7274_0 := h7274c.1
                                      have p7274_1 := h7274c.2.1
                                      have p7274_2 := h7274c.2.2.1
                                      have p7274_3 := h7274c.2.2.2
                                      linarith only [h6253, h7192, h7260, h7261, h7272, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7274_1]
                                    · have p7274_0 := h7274c.1
                                      have p7274_1 := h7274c.2.1
                                      have p7274_2 := h7274c.2.2.1
                                      have p7274_3 := h7274c.2.2.2
                                      linarith only [h7259, hlam, p7274_1]
                                    · have p7274_0 := h7274c.1
                                      have p7274_1 := h7274c.2.1
                                      have p7274_2 := h7274c.2.2.1
                                      have p7274_3 := h7274c.2.2.2
                                      linarith only [hlam, p7274_0]
                                  · linarith only [h6253, h6254, h7070, h7259, h7260, h7261, h7263, h7273, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                · linarith only [h7070, h7259, h7272, hlam]
                          · linarith only [h6253, h6254, h7259, h7260, h7267, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h6253, h7070, h7260, h7261, h7262, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7304 | h7304
                    · linarith only [h0, h6253, h7192, h7260, h7261, h7304, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7306 | h7306
                      · linarith only [h0, h6253, h7255, h7261, h7306, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7308 | h7308
                        · linarith only [h0, h6253, h7192, h7257, h7308, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7310 | h7310
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7311 | h7311
                            · linarith only [h0, h6253, h7260, h7304, h7306, h7310, h7311, hlam]
                            · linarith only [h0, h6253, h7260, h7261, h7311, hc23, hc34, hlam, hphi]
                          · linarith only [h6253, h6254, h7260, h7310, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h6253, h7069, h7192, h7259, h7260, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7316 | h7316
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7317 | h7317
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7318 | h7318
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7319 | h7319
                      · linarith only [h0, h6253, h7070, h7317, h7319, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7321 | h7321
                        · linarith only [h0, h6253, h7070, h7317, h7321, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7323 | h7323
                          · linarith only [h0, h6253, h7070, h7259, h7316, h7319, h7323, hc23, hc34, hlam, hphi]
                          · linarith only [h6253, h6254, h7316, h7323, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h6253, h7070, h7316, h7317, h7318, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7327 | h7327
                    · linarith only [h0, h6253, h7192, h7316, h7317, h7327, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7329 | h7329
                      · linarith only [h0, h6253, h7317, h7329, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7331 | h7331
                        · linarith only [h0, h6253, h7317, h7331, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7333 | h7333
                          · linarith only [h0, h6253, h7070, h7259, h7316, h7329, h7333, hc23, hc34, hlam, hphi]
                          · linarith only [h6253, h6254, h7316, h7333, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h6253, h7069, h7070, h7259, h7316, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · linarith only [h0, h6253, h7069, hlam]

set_option maxHeartbeats 10280000 in
set_option maxHeartbeats 10280000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s7_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h6253 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h6254 | h6254
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s7_x0_x0 m hb0 hb1 hb3 hb4 hg0 h6253 h6254
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s7_x0_x1 m hb0 hb1 hb3 hb4 hg0 h6253 h6254

set_option maxHeartbeats 10280000 in
set_option maxHeartbeats 10280000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s7_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h6253 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h0 := hg0
  exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s8 m hb0 hb1 hb3 hb4 h0 h6253

set_option maxHeartbeats 10280000 in
set_option maxHeartbeats 10280000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s7 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h6253 | h6253
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s7_x0 m hb0 hb1 hb3 hb4 hg0 h6253
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s7_x1 m hb0 hb1 hb3 hb4 hg0 h6253

set_option maxHeartbeats 22786000 in
set_option maxHeartbeats 22786000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s0 m hb0 hb1 hb3 hb4 h0
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s7 m hb0 hb1 hb3 hb4 h0

end R2N4
