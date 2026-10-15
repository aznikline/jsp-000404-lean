import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_4S12

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5858000 in
set_option maxHeartbeats 5858000 in
theorem r1l7_11_23_L_I_H_I_s10_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg6364 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h7232 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7233 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h6364 := hg6364
  rcases m.htr 0 4 5 (by decide) (by decide) with h8885 | h8885
  · linarith only [h7232, h7233, h8885, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h8887 | h8887
    · linarith only [h0, h4, h8887, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h8889 | h8889
      · linarith only [h0, h6364, h8889, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h8891 | h8891
        · rcases m.htr 1 3 4 (by decide) (by decide) with h8892 | h8892
          · rcases m.htr 1 3 5 (by decide) (by decide) with h8893 | h8893
            · linarith only [h1, h7233, h8893, hlam]
            · linarith only [h8887, h8891, h8893, hlam]
          · linarith only [h7232, h7233, h8887, h8892, hc12, hc35, hlam, hphi, ht23]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h8897 | h8897
          · rcases m.htr 1 3 5 (by decide) (by decide) with h8898 | h8898
            · linarith only [h1, h7233, h8898, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8900 | h8900
              · linarith only [h2, h7232, h7233, h8885, h8900, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8902 | h8902
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8903 | h8903
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h8904 | h8904
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8905 | h8905
                      · linarith only [h7232, h7233, h8885, h8903, h8905, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases h1bigk with h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c
                        · have p8907_0 := h8907c.1
                          have p8907_1 := h8907c.2.1
                          have p8907_2 := h8907c.2.2.1
                          have p8907_3 := h8907c.2.2.2
                          linarith only [hlam, p8907_0]
                        · have p8907_0 := h8907c.1
                          have p8907_1 := h8907c.2.1
                          have p8907_2 := h8907c.2.2.1
                          have p8907_3 := h8907c.2.2.2
                          rcases p8907_3 (m.d 0 1) (by simp) with h8909 | h8909
                          · rcases p8907_3 (m.d 1 2) (by simp) with h8910 | h8910
                            · linarith only [h8910, hlam, p8907_0]
                            · rcases p8907_3 (m.d 1 3) (by simp) with h8912 | h8912
                              · linarith only [h1, h8912, hlam]
                              · linarith only [h8887, h8912, hlam]
                          · linarith only [h8909, hlam, p8907_0]
                        · have p8907_0 := h8907c.1
                          have p8907_1 := h8907c.2.1
                          have p8907_2 := h8907c.2.2.1
                          have p8907_3 := h8907c.2.2.2
                          rcases p8907_3 (m.d 0 1) (by simp) with h8916 | h8916
                          · rcases p8907_3 (m.d 1 2) (by simp) with h8917 | h8917
                            · linarith only [h0, h8917, hlam]
                            · rcases p8907_3 (m.d 1 3) (by simp) with h8919 | h8919
                              · linarith only [h8919, hlam, p8907_0]
                              · rcases p8907_3 (m.d 1 4) (by simp) with h8921 | h8921
                                · linarith only [h2, h8921, hlam]
                                · rcases p8907_3 (m.d 1 5) (by simp) with h8923 | h8923
                                  · linarith only [h3, h8923, hlam]
                                  · linarith only [h8898, h8923, hlam]
                          · linarith only [h8916, hlam, p8907_0]
                        · have p8907_0 := h8907c.1
                          have p8907_1 := h8907c.2.1
                          have p8907_2 := h8907c.2.2.1
                          have p8907_3 := h8907c.2.2.2
                          rcases p8907_3 (m.d 0 1) (by simp) with h8927 | h8927
                          · rcases p8907_3 (m.d 1 2) (by simp) with h8928 | h8928
                            · linarith only [h0, h8928, hlam]
                            · rcases p8907_3 (m.d 1 3) (by simp) with h8930 | h8930
                              · linarith only [h1, h8930, hlam]
                              · linarith only [h8897, h8930, hlam]
                          · linarith only [h8927, hlam, p8907_0]
                        · have p8907_0 := h8907c.1
                          have p8907_1 := h8907c.2.1
                          have p8907_2 := h8907c.2.2.1
                          have p8907_3 := h8907c.2.2.2
                          rcases p8907_3 (m.d 0 1) (by simp) with h8934 | h8934
                          · rcases p8907_3 (m.d 1 2) (by simp) with h8935 | h8935
                            · linarith only [h0, h8935, hlam]
                            · rcases p8907_3 (m.d 1 3) (by simp) with h8937 | h8937
                              · linarith only [h1, h8937, hlam]
                              · rcases p8907_3 (m.d 1 4) (by simp) with h8939 | h8939
                                · linarith only [h2, h8939, hlam]
                                · rcases p8907_3 (m.d 1 5) (by simp) with h8941 | h8941
                                  · linarith only [h8941, hlam, p8907_0]
                                  · rcases h3bigk with h8943c | h8943c | h8943c | h8943c | h8943c | h8943c | h8943c | h8943c | h8943c | h8943c | h8943c | h8943c | h8943c | h8943c | h8943c | h8943c | h8943c | h8943c | h8943c | h8943c | h8943c | h8943c | h8943c | h8943c | h8943c
                                    · have p8943_0 := h8943c.1
                                      have p8943_1 := h8943c.2.1
                                      have p8943_2 := h8943c.2.2.1
                                      have p8943_3 := h8943c.2.2.2
                                      linarith only [hlam, p8943_0]
                                    · have p8943_0 := h8943c.1
                                      have p8943_1 := h8943c.2.1
                                      have p8943_2 := h8943c.2.2.1
                                      have p8943_3 := h8943c.2.2.2
                                      linarith only [h7233, h8902, h8904, h8905, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p8943_1]
                                    · have p8943_0 := h8943c.1
                                      have p8943_1 := h8943c.2.1
                                      have p8943_2 := h8943c.2.2.1
                                      have p8943_3 := h8943c.2.2.2
                                      linarith only [h4, hlam, p8943_1]
                                    · have p8943_0 := h8943c.1
                                      have p8943_1 := h8943c.2.1
                                      have p8943_2 := h8943c.2.2.1
                                      have p8943_3 := h8943c.2.2.2
                                      linarith only [h7233, h8902, h8904, h8905, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8943_1]
                                    · have p8943_0 := h8943c.1
                                      have p8943_1 := h8943c.2.1
                                      have p8943_2 := h8943c.2.2.1
                                      have p8943_3 := h8943c.2.2.2
                                      linarith only [h7233, hlam, p8943_0]
                                    · have p8943_0 := h8943c.1
                                      have p8943_1 := h8943c.2.1
                                      have p8943_2 := h8943c.2.2.1
                                      have p8943_3 := h8943c.2.2.2
                                      linarith only [h1, hlam, p8943_0]
                                    · have p8943_0 := h8943c.1
                                      have p8943_1 := h8943c.2.1
                                      have p8943_2 := h8943c.2.2.1
                                      have p8943_3 := h8943c.2.2.2
                                      linarith only [hlam, p8943_0]
                                    · have p8943_0 := h8943c.1
                                      have p8943_1 := h8943c.2.1
                                      have p8943_2 := h8943c.2.2.1
                                      have p8943_3 := h8943c.2.2.2
                                      linarith only [h8887, hlam, p8943_1]
                                    · have p8943_0 := h8943c.1
                                      have p8943_1 := h8943c.2.1
                                      have p8943_2 := h8943c.2.2.1
                                      have p8943_3 := h8943c.2.2.2
                                      linarith only [h8898, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8907_1, p8943_1]
                                    · have p8943_0 := h8943c.1
                                      have p8943_1 := h8943c.2.1
                                      have p8943_2 := h8943c.2.2.1
                                      have p8943_3 := h8943c.2.2.2
                                      linarith only [h8898, hlam, p8943_0]
                                    · have p8943_0 := h8943c.1
                                      have p8943_1 := h8943c.2.1
                                      have p8943_2 := h8943c.2.2.1
                                      have p8943_3 := h8943c.2.2.2
                                      linarith only [h0, h4, hc12, hc23, hlam, hphi, p8943_1]
                                    · have p8943_0 := h8943c.1
                                      have p8943_1 := h8943c.2.1
                                      have p8943_2 := h8943c.2.2.1
                                      have p8943_3 := h8943c.2.2.2
                                      linarith only [h8887, hc12, hc23, hlam, hphi, p8943_1]
                                    · have p8943_0 := h8943c.1
                                      have p8943_1 := h8943c.2.1
                                      have p8943_2 := h8943c.2.2.1
                                      have p8943_3 := h8943c.2.2.2
                                      linarith only [hlam, p8943_0]
                                    · have p8943_0 := h8943c.1
                                      have p8943_1 := h8943c.2.1
                                      have p8943_2 := h8943c.2.2.1
                                      have p8943_3 := h8943c.2.2.2
                                      rcases p8943_3 (m.d 0 3) (by simp) with h8957 | h8957
                                      · linarith only [h4, h8957, hlam]
                                      · linarith only [h7232, h8957, hlam]
                                    · have p8943_0 := h8943c.1
                                      have p8943_1 := h8943c.2.1
                                      have p8943_2 := h8943c.2.2.1
                                      have p8943_3 := h8943c.2.2.2
                                      linarith only [h1, h7233, h8897, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8943_1]
                                    · have p8943_0 := h8943c.1
                                      have p8943_1 := h8943c.2.1
                                      have p8943_2 := h8943c.2.2.1
                                      have p8943_3 := h8943c.2.2.2
                                      linarith only [h7232, hlam, p8943_0]
                                    · have p8943_0 := h8943c.1
                                      have p8943_1 := h8943c.2.1
                                      have p8943_2 := h8943c.2.2.1
                                      have p8943_3 := h8943c.2.2.2
                                      linarith only [h8897, hlam, p8943_0]
                                    · have p8943_0 := h8943c.1
                                      have p8943_1 := h8943c.2.1
                                      have p8943_2 := h8943c.2.2.1
                                      have p8943_3 := h8943c.2.2.2
                                      linarith only [h8902, hlam, p8943_0]
                                    · have p8943_0 := h8943c.1
                                      have p8943_1 := h8943c.2.1
                                      have p8943_2 := h8943c.2.2.1
                                      have p8943_3 := h8943c.2.2.2
                                      linarith only [hlam, p8943_0]
                                    · have p8943_0 := h8943c.1
                                      have p8943_1 := h8943c.2.1
                                      have p8943_2 := h8943c.2.2.1
                                      have p8943_3 := h8943c.2.2.2
                                      linarith only [h8905, hlam, p8943_1]
                                    · have p8943_0 := h8943c.1
                                      have p8943_1 := h8943c.2.1
                                      have p8943_2 := h8943c.2.2.1
                                      have p8943_3 := h8943c.2.2.2
                                      linarith only [h1, h8897, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p8943_1]
                                    · have p8943_0 := h8943c.1
                                      have p8943_1 := h8943c.2.1
                                      have p8943_2 := h8943c.2.2.1
                                      have p8943_3 := h8943c.2.2.2
                                      linarith only [h8897, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p8943_1]
                                    · have p8943_0 := h8943c.1
                                      have p8943_1 := h8943c.2.1
                                      have p8943_2 := h8943c.2.2.1
                                      have p8943_3 := h8943c.2.2.2
                                      linarith only [h8903, hlam, p8943_0]
                                    · have p8943_0 := h8943c.1
                                      have p8943_1 := h8943c.2.1
                                      have p8943_2 := h8943c.2.2.1
                                      have p8943_3 := h8943c.2.2.2
                                      linarith only [h8902, h8904, h8905, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8943_1]
                                    · have p8943_0 := h8943c.1
                                      have p8943_1 := h8943c.2.1
                                      have p8943_2 := h8943c.2.2.1
                                      have p8943_3 := h8943c.2.2.2
                                      linarith only [hlam, p8943_0]
                          · linarith only [h8934, hlam, p8907_0]
                        · have p8907_0 := h8907c.1
                          have p8907_1 := h8907c.2.1
                          have p8907_2 := h8907c.2.2.1
                          have p8907_3 := h8907c.2.2.2
                          linarith only [h0, hlam, p8907_0]
                        · have p8907_0 := h8907c.1
                          have p8907_1 := h8907c.2.1
                          have p8907_2 := h8907c.2.2.1
                          have p8907_3 := h8907c.2.2.2
                          linarith only [hlam, p8907_0]
                        · have p8907_0 := h8907c.1
                          have p8907_1 := h8907c.2.1
                          have p8907_2 := h8907c.2.2.1
                          have p8907_3 := h8907c.2.2.2
                          linarith only [h8887, hlam, p8907_0]
                        · have p8907_0 := h8907c.1
                          have p8907_1 := h8907c.2.1
                          have p8907_2 := h8907c.2.2.1
                          have p8907_3 := h8907c.2.2.2
                          linarith only [h8889, hlam, p8907_0]
                        · have p8907_0 := h8907c.1
                          have p8907_1 := h8907c.2.1
                          have p8907_2 := h8907c.2.2.1
                          have p8907_3 := h8907c.2.2.2
                          linarith only [h8891, hlam, p8907_0]
                        · have p8907_0 := h8907c.1
                          have p8907_1 := h8907c.2.1
                          have p8907_2 := h8907c.2.2.1
                          have p8907_3 := h8907c.2.2.2
                          linarith only [h1, hlam, p8907_0]
                        · have p8907_0 := h8907c.1
                          have p8907_1 := h8907c.2.1
                          have p8907_2 := h8907c.2.2.1
                          have p8907_3 := h8907c.2.2.2
                          linarith only [h1, h7233, h8902, h8904, h8905, hc12, hc23, hlam, hphi, p8907_1]
                        · have p8907_0 := h8907c.1
                          have p8907_1 := h8907c.2.1
                          have p8907_2 := h8907c.2.2.1
                          have p8907_3 := h8907c.2.2.2
                          linarith only [hlam, p8907_0]
                        · have p8907_0 := h8907c.1
                          have p8907_1 := h8907c.2.1
                          have p8907_2 := h8907c.2.2.1
                          have p8907_3 := h8907c.2.2.2
                          linarith only [h1, h7233, h8889, h8902, h8904, h8905, hc12, hc23, hlam, hphi, p8907_1]
                        · have p8907_0 := h8907c.1
                          have p8907_1 := h8907c.2.1
                          have p8907_2 := h8907c.2.2.1
                          have p8907_3 := h8907c.2.2.2
                          linarith only [h8898, hlam, p8907_1]
                        · have p8907_0 := h8907c.1
                          have p8907_1 := h8907c.2.1
                          have p8907_2 := h8907c.2.2.1
                          have p8907_3 := h8907c.2.2.2
                          linarith only [h2, hlam, p8907_0]
                        · have p8907_0 := h8907c.1
                          have p8907_1 := h8907c.2.1
                          have p8907_2 := h8907c.2.2.1
                          have p8907_3 := h8907c.2.2.2
                          linarith only [h2, h7232, h7233, h8902, h8904, h8905, hc12, hc23, hlam, hphi, p8907_1]
                        · have p8907_0 := h8907c.1
                          have p8907_1 := h8907c.2.1
                          have p8907_2 := h8907c.2.2.1
                          have p8907_3 := h8907c.2.2.2
                          linarith only [h8897, hlam, p8907_0]
                        · have p8907_0 := h8907c.1
                          have p8907_1 := h8907c.2.1
                          have p8907_2 := h8907c.2.2.1
                          have p8907_3 := h8907c.2.2.2
                          linarith only [hlam, p8907_0]
                        · have p8907_0 := h8907c.1
                          have p8907_1 := h8907c.2.1
                          have p8907_2 := h8907c.2.2.1
                          have p8907_3 := h8907c.2.2.2
                          linarith only [h8900, hlam, p8907_1]
                        · have p8907_0 := h8907c.1
                          have p8907_1 := h8907c.2.1
                          have p8907_2 := h8907c.2.2.1
                          have p8907_3 := h8907c.2.2.2
                          linarith only [h3, hlam, p8907_0]
                        · have p8907_0 := h8907c.1
                          have p8907_1 := h8907c.2.1
                          have p8907_2 := h8907c.2.2.1
                          have p8907_3 := h8907c.2.2.2
                          linarith only [h3, h7233, h8902, h8904, h8905, hc12, hc23, hlam, hphi, p8907_1]
                        · have p8907_0 := h8907c.1
                          have p8907_1 := h8907c.2.1
                          have p8907_2 := h8907c.2.2.1
                          have p8907_3 := h8907c.2.2.2
                          linarith only [h3, h7233, h8887, h8902, h8904, h8905, hc12, hc23, hlam, hphi, p8907_1]
                        · have p8907_0 := h8907c.1
                          have p8907_1 := h8907c.2.1
                          have p8907_2 := h8907c.2.2.1
                          have p8907_3 := h8907c.2.2.2
                          linarith only [h3, h7233, h8889, h8902, h8904, h8905, hc12, hc23, hlam, hphi, p8907_1]
                        · have p8907_0 := h8907c.1
                          have p8907_1 := h8907c.2.1
                          have p8907_2 := h8907c.2.2.1
                          have p8907_3 := h8907c.2.2.2
                          linarith only [hlam, p8907_0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8992 | h8992
                      · linarith only [h0, h6364, h8897, h8904, h8992, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases h1bigk with h8994c | h8994c | h8994c | h8994c | h8994c | h8994c | h8994c | h8994c | h8994c | h8994c | h8994c | h8994c | h8994c | h8994c | h8994c | h8994c | h8994c | h8994c | h8994c | h8994c | h8994c | h8994c | h8994c | h8994c | h8994c
                        · have p8994_0 := h8994c.1
                          have p8994_1 := h8994c.2.1
                          have p8994_2 := h8994c.2.2.1
                          have p8994_3 := h8994c.2.2.2
                          linarith only [hlam, p8994_0]
                        · have p8994_0 := h8994c.1
                          have p8994_1 := h8994c.2.1
                          have p8994_2 := h8994c.2.2.1
                          have p8994_3 := h8994c.2.2.2
                          rcases p8994_3 (m.d 0 1) (by simp) with h8996 | h8996
                          · rcases p8994_3 (m.d 1 2) (by simp) with h8997 | h8997
                            · linarith only [h8997, hlam, p8994_0]
                            · rcases p8994_3 (m.d 1 3) (by simp) with h8999 | h8999
                              · linarith only [h1, h8999, hlam]
                              · linarith only [h8887, h8999, hlam]
                          · linarith only [h8996, hlam, p8994_0]
                        · have p8994_0 := h8994c.1
                          have p8994_1 := h8994c.2.1
                          have p8994_2 := h8994c.2.2.1
                          have p8994_3 := h8994c.2.2.2
                          rcases p8994_3 (m.d 0 1) (by simp) with h9003 | h9003
                          · rcases p8994_3 (m.d 1 2) (by simp) with h9004 | h9004
                            · linarith only [h0, h9004, hlam]
                            · rcases p8994_3 (m.d 1 3) (by simp) with h9006 | h9006
                              · linarith only [h9006, hlam, p8994_0]
                              · rcases p8994_3 (m.d 1 4) (by simp) with h9008 | h9008
                                · linarith only [h2, h9008, hlam]
                                · rcases p8994_3 (m.d 1 5) (by simp) with h9010 | h9010
                                  · linarith only [h3, h9010, hlam]
                                  · linarith only [h8898, h9010, hlam]
                          · linarith only [h9003, hlam, p8994_0]
                        · have p8994_0 := h8994c.1
                          have p8994_1 := h8994c.2.1
                          have p8994_2 := h8994c.2.2.1
                          have p8994_3 := h8994c.2.2.2
                          rcases p8994_3 (m.d 0 1) (by simp) with h9014 | h9014
                          · rcases p8994_3 (m.d 1 2) (by simp) with h9015 | h9015
                            · linarith only [h0, h9015, hlam]
                            · rcases p8994_3 (m.d 1 3) (by simp) with h9017 | h9017
                              · linarith only [h1, h9017, hlam]
                              · linarith only [h8897, h9017, hlam]
                          · linarith only [h9014, hlam, p8994_0]
                        · have p8994_0 := h8994c.1
                          have p8994_1 := h8994c.2.1
                          have p8994_2 := h8994c.2.2.1
                          have p8994_3 := h8994c.2.2.2
                          rcases p8994_3 (m.d 0 1) (by simp) with h9021 | h9021
                          · rcases p8994_3 (m.d 1 2) (by simp) with h9022 | h9022
                            · linarith only [h0, h9022, hlam]
                            · rcases p8994_3 (m.d 1 3) (by simp) with h9024 | h9024
                              · linarith only [h1, h9024, hlam]
                              · rcases p8994_3 (m.d 1 4) (by simp) with h9026 | h9026
                                · linarith only [h2, h9026, hlam]
                                · rcases p8994_3 (m.d 1 5) (by simp) with h9028 | h9028
                                  · linarith only [h9028, hlam, p8994_0]
                                  · rcases h3bigk with h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c | h9030c
                                    · have p9030_0 := h9030c.1
                                      have p9030_1 := h9030c.2.1
                                      have p9030_2 := h9030c.2.2.1
                                      have p9030_3 := h9030c.2.2.2
                                      linarith only [hlam, p9030_0]
                                    · have p9030_0 := h9030c.1
                                      have p9030_1 := h9030c.2.1
                                      have p9030_2 := h9030c.2.2.1
                                      have p9030_3 := h9030c.2.2.2
                                      linarith only [h8897, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p9030_1]
                                    · have p9030_0 := h9030c.1
                                      have p9030_1 := h9030c.2.1
                                      have p9030_2 := h9030c.2.2.1
                                      have p9030_3 := h9030c.2.2.2
                                      linarith only [h4, hlam, p9030_1]
                                    · have p9030_0 := h9030c.1
                                      have p9030_1 := h9030c.2.1
                                      have p9030_2 := h9030c.2.2.1
                                      have p9030_3 := h9030c.2.2.2
                                      linarith only [h7233, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p9030_1]
                                    · have p9030_0 := h9030c.1
                                      have p9030_1 := h9030c.2.1
                                      have p9030_2 := h9030c.2.2.1
                                      have p9030_3 := h9030c.2.2.2
                                      linarith only [h7233, hlam, p9030_0]
                                    · have p9030_0 := h9030c.1
                                      have p9030_1 := h9030c.2.1
                                      have p9030_2 := h9030c.2.2.1
                                      have p9030_3 := h9030c.2.2.2
                                      linarith only [h1, hlam, p9030_0]
                                    · have p9030_0 := h9030c.1
                                      have p9030_1 := h9030c.2.1
                                      have p9030_2 := h9030c.2.2.1
                                      have p9030_3 := h9030c.2.2.2
                                      linarith only [hlam, p9030_0]
                                    · have p9030_0 := h9030c.1
                                      have p9030_1 := h9030c.2.1
                                      have p9030_2 := h9030c.2.2.1
                                      have p9030_3 := h9030c.2.2.2
                                      linarith only [h8887, hlam, p9030_1]
                                    · have p9030_0 := h9030c.1
                                      have p9030_1 := h9030c.2.1
                                      have p9030_2 := h9030c.2.2.1
                                      have p9030_3 := h9030c.2.2.2
                                      linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9030_1]
                                    · have p9030_0 := h9030c.1
                                      have p9030_1 := h9030c.2.1
                                      have p9030_2 := h9030c.2.2.1
                                      have p9030_3 := h9030c.2.2.2
                                      linarith only [h8898, hlam, p9030_0]
                                    · have p9030_0 := h9030c.1
                                      have p9030_1 := h9030c.2.1
                                      have p9030_2 := h9030c.2.2.1
                                      have p9030_3 := h9030c.2.2.2
                                      linarith only [h0, h4, hc12, hc23, hlam, hphi, p9030_1]
                                    · have p9030_0 := h9030c.1
                                      have p9030_1 := h9030c.2.1
                                      have p9030_2 := h9030c.2.2.1
                                      have p9030_3 := h9030c.2.2.2
                                      linarith only [h8887, hc12, hc23, hlam, hphi, p9030_1]
                                    · have p9030_0 := h9030c.1
                                      have p9030_1 := h9030c.2.1
                                      have p9030_2 := h9030c.2.2.1
                                      have p9030_3 := h9030c.2.2.2
                                      linarith only [hlam, p9030_0]
                                    · have p9030_0 := h9030c.1
                                      have p9030_1 := h9030c.2.1
                                      have p9030_2 := h9030c.2.2.1
                                      have p9030_3 := h9030c.2.2.2
                                      rcases p9030_3 (m.d 0 3) (by simp) with h9044 | h9044
                                      · linarith only [h4, h9044, hlam]
                                      · linarith only [h7232, h9044, hlam]
                                    · have p9030_0 := h9030c.1
                                      have p9030_1 := h9030c.2.1
                                      have p9030_2 := h9030c.2.2.1
                                      have p9030_3 := h9030c.2.2.2
                                      linarith only [h1, h7233, h8897, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9030_1]
                                    · have p9030_0 := h9030c.1
                                      have p9030_1 := h9030c.2.1
                                      have p9030_2 := h9030c.2.2.1
                                      have p9030_3 := h9030c.2.2.2
                                      linarith only [h7232, hlam, p9030_0]
                                    · have p9030_0 := h9030c.1
                                      have p9030_1 := h9030c.2.1
                                      have p9030_2 := h9030c.2.2.1
                                      have p9030_3 := h9030c.2.2.2
                                      linarith only [h8897, hlam, p9030_0]
                                    · have p9030_0 := h9030c.1
                                      have p9030_1 := h9030c.2.1
                                      have p9030_2 := h9030c.2.2.1
                                      have p9030_3 := h9030c.2.2.2
                                      linarith only [h8902, hlam, p9030_0]
                                    · have p9030_0 := h9030c.1
                                      have p9030_1 := h9030c.2.1
                                      have p9030_2 := h9030c.2.2.1
                                      have p9030_3 := h9030c.2.2.2
                                      linarith only [hlam, p9030_0]
                                    · have p9030_0 := h9030c.1
                                      have p9030_1 := h9030c.2.1
                                      have p9030_2 := h9030c.2.2.1
                                      have p9030_3 := h9030c.2.2.2
                                      linarith only [h8992, hlam, p9030_1]
                                    · have p9030_0 := h9030c.1
                                      have p9030_1 := h9030c.2.1
                                      have p9030_2 := h9030c.2.2.1
                                      have p9030_3 := h9030c.2.2.2
                                      linarith only [h1, h8897, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p9030_1]
                                    · have p9030_0 := h9030c.1
                                      have p9030_1 := h9030c.2.1
                                      have p9030_2 := h9030c.2.2.1
                                      have p9030_3 := h9030c.2.2.2
                                      linarith only [h8897, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p9030_1]
                                    · have p9030_0 := h9030c.1
                                      have p9030_1 := h9030c.2.1
                                      have p9030_2 := h9030c.2.2.1
                                      have p9030_3 := h9030c.2.2.2
                                      linarith only [h8903, hlam, p9030_0]
                                    · have p9030_0 := h9030c.1
                                      have p9030_1 := h9030c.2.1
                                      have p9030_2 := h9030c.2.2.1
                                      have p9030_3 := h9030c.2.2.2
                                      linarith only [h8903, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9030_1]
                                    · have p9030_0 := h9030c.1
                                      have p9030_1 := h9030c.2.1
                                      have p9030_2 := h9030c.2.2.1
                                      have p9030_3 := h9030c.2.2.2
                                      linarith only [hlam, p9030_0]
                          · linarith only [h9021, hlam, p8994_0]
                        · have p8994_0 := h8994c.1
                          have p8994_1 := h8994c.2.1
                          have p8994_2 := h8994c.2.2.1
                          have p8994_3 := h8994c.2.2.2
                          linarith only [h0, hlam, p8994_0]
                        · have p8994_0 := h8994c.1
                          have p8994_1 := h8994c.2.1
                          have p8994_2 := h8994c.2.2.1
                          have p8994_3 := h8994c.2.2.2
                          linarith only [hlam, p8994_0]
                        · have p8994_0 := h8994c.1
                          have p8994_1 := h8994c.2.1
                          have p8994_2 := h8994c.2.2.1
                          have p8994_3 := h8994c.2.2.2
                          linarith only [h8887, hlam, p8994_0]
                        · have p8994_0 := h8994c.1
                          have p8994_1 := h8994c.2.1
                          have p8994_2 := h8994c.2.2.1
                          have p8994_3 := h8994c.2.2.2
                          linarith only [h8889, hlam, p8994_0]
                        · have p8994_0 := h8994c.1
                          have p8994_1 := h8994c.2.1
                          have p8994_2 := h8994c.2.2.1
                          have p8994_3 := h8994c.2.2.2
                          linarith only [h8891, hlam, p8994_0]
                        · have p8994_0 := h8994c.1
                          have p8994_1 := h8994c.2.1
                          have p8994_2 := h8994c.2.2.1
                          have p8994_3 := h8994c.2.2.2
                          linarith only [h1, hlam, p8994_0]
                        · have p8994_0 := h8994c.1
                          have p8994_1 := h8994c.2.1
                          have p8994_2 := h8994c.2.2.1
                          have p8994_3 := h8994c.2.2.2
                          linarith only [h1, h7233, h8903, hc12, hc23, hlam, hphi, p8994_1]
                        · have p8994_0 := h8994c.1
                          have p8994_1 := h8994c.2.1
                          have p8994_2 := h8994c.2.2.1
                          have p8994_3 := h8994c.2.2.2
                          linarith only [hlam, p8994_0]
                        · have p8994_0 := h8994c.1
                          have p8994_1 := h8994c.2.1
                          have p8994_2 := h8994c.2.2.1
                          have p8994_3 := h8994c.2.2.2
                          linarith only [h1, h7233, h8889, h8903, hc12, hc23, hlam, hphi, p8994_1]
                        · have p8994_0 := h8994c.1
                          have p8994_1 := h8994c.2.1
                          have p8994_2 := h8994c.2.2.1
                          have p8994_3 := h8994c.2.2.2
                          linarith only [h8898, hlam, p8994_1]
                        · have p8994_0 := h8994c.1
                          have p8994_1 := h8994c.2.1
                          have p8994_2 := h8994c.2.2.1
                          have p8994_3 := h8994c.2.2.2
                          linarith only [h2, hlam, p8994_0]
                        · have p8994_0 := h8994c.1
                          have p8994_1 := h8994c.2.1
                          have p8994_2 := h8994c.2.2.1
                          have p8994_3 := h8994c.2.2.2
                          linarith only [h2, h7232, h7233, h8903, hc12, hc23, hlam, hphi, p8994_1]
                        · have p8994_0 := h8994c.1
                          have p8994_1 := h8994c.2.1
                          have p8994_2 := h8994c.2.2.1
                          have p8994_3 := h8994c.2.2.2
                          linarith only [h8897, hlam, p8994_0]
                        · have p8994_0 := h8994c.1
                          have p8994_1 := h8994c.2.1
                          have p8994_2 := h8994c.2.2.1
                          have p8994_3 := h8994c.2.2.2
                          linarith only [hlam, p8994_0]
                        · have p8994_0 := h8994c.1
                          have p8994_1 := h8994c.2.1
                          have p8994_2 := h8994c.2.2.1
                          have p8994_3 := h8994c.2.2.2
                          linarith only [h8900, hlam, p8994_1]
                        · have p8994_0 := h8994c.1
                          have p8994_1 := h8994c.2.1
                          have p8994_2 := h8994c.2.2.1
                          have p8994_3 := h8994c.2.2.2
                          linarith only [h3, hlam, p8994_0]
                        · have p8994_0 := h8994c.1
                          have p8994_1 := h8994c.2.1
                          have p8994_2 := h8994c.2.2.1
                          have p8994_3 := h8994c.2.2.2
                          linarith only [h3, h7233, h8903, hc12, hc23, hlam, hphi, p8994_1]
                        · have p8994_0 := h8994c.1
                          have p8994_1 := h8994c.2.1
                          have p8994_2 := h8994c.2.2.1
                          have p8994_3 := h8994c.2.2.2
                          linarith only [h3, h7233, h8887, h8903, hc12, hc23, hlam, hphi, p8994_1]
                        · have p8994_0 := h8994c.1
                          have p8994_1 := h8994c.2.1
                          have p8994_2 := h8994c.2.2.1
                          have p8994_3 := h8994c.2.2.2
                          linarith only [h3, h7233, h8889, h8903, hc12, hc23, hlam, hphi, p8994_1]
                        · have p8994_0 := h8994c.1
                          have p8994_1 := h8994c.2.1
                          have p8994_2 := h8994c.2.2.1
                          have p8994_3 := h8994c.2.2.2
                          linarith only [hlam, p8994_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9079 | h9079
                    · linarith only [h2, h8885, h8889, h8902, h8903, h9079, hc12, hc35, hlam, hphi, ht23]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9081 | h9081
                      · linarith only [h0, h6364, h8897, h9079, h9081, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases h1bigk with h9083c | h9083c | h9083c | h9083c | h9083c | h9083c | h9083c | h9083c | h9083c | h9083c | h9083c | h9083c | h9083c | h9083c | h9083c | h9083c | h9083c | h9083c | h9083c | h9083c | h9083c | h9083c | h9083c | h9083c | h9083c
                        · have p9083_0 := h9083c.1
                          have p9083_1 := h9083c.2.1
                          have p9083_2 := h9083c.2.2.1
                          have p9083_3 := h9083c.2.2.2
                          linarith only [hlam, p9083_0]
                        · have p9083_0 := h9083c.1
                          have p9083_1 := h9083c.2.1
                          have p9083_2 := h9083c.2.2.1
                          have p9083_3 := h9083c.2.2.2
                          rcases p9083_3 (m.d 0 1) (by simp) with h9085 | h9085
                          · rcases p9083_3 (m.d 1 2) (by simp) with h9086 | h9086
                            · linarith only [h9086, hlam, p9083_0]
                            · rcases p9083_3 (m.d 1 3) (by simp) with h9088 | h9088
                              · linarith only [h1, h9088, hlam]
                              · linarith only [h8887, h9088, hlam]
                          · linarith only [h9085, hlam, p9083_0]
                        · have p9083_0 := h9083c.1
                          have p9083_1 := h9083c.2.1
                          have p9083_2 := h9083c.2.2.1
                          have p9083_3 := h9083c.2.2.2
                          rcases p9083_3 (m.d 0 1) (by simp) with h9092 | h9092
                          · rcases p9083_3 (m.d 1 2) (by simp) with h9093 | h9093
                            · linarith only [h0, h9093, hlam]
                            · rcases p9083_3 (m.d 1 3) (by simp) with h9095 | h9095
                              · linarith only [h9095, hlam, p9083_0]
                              · rcases p9083_3 (m.d 1 4) (by simp) with h9097 | h9097
                                · linarith only [h2, h9097, hlam]
                                · rcases p9083_3 (m.d 1 5) (by simp) with h9099 | h9099
                                  · linarith only [h3, h9099, hlam]
                                  · linarith only [h8898, h9099, hlam]
                          · linarith only [h9092, hlam, p9083_0]
                        · have p9083_0 := h9083c.1
                          have p9083_1 := h9083c.2.1
                          have p9083_2 := h9083c.2.2.1
                          have p9083_3 := h9083c.2.2.2
                          rcases p9083_3 (m.d 0 1) (by simp) with h9103 | h9103
                          · rcases p9083_3 (m.d 1 2) (by simp) with h9104 | h9104
                            · linarith only [h0, h9104, hlam]
                            · rcases p9083_3 (m.d 1 3) (by simp) with h9106 | h9106
                              · linarith only [h1, h9106, hlam]
                              · linarith only [h8897, h9106, hlam]
                          · linarith only [h9103, hlam, p9083_0]
                        · have p9083_0 := h9083c.1
                          have p9083_1 := h9083c.2.1
                          have p9083_2 := h9083c.2.2.1
                          have p9083_3 := h9083c.2.2.2
                          rcases p9083_3 (m.d 0 1) (by simp) with h9110 | h9110
                          · rcases p9083_3 (m.d 1 2) (by simp) with h9111 | h9111
                            · linarith only [h0, h9111, hlam]
                            · rcases p9083_3 (m.d 1 3) (by simp) with h9113 | h9113
                              · linarith only [h1, h9113, hlam]
                              · rcases p9083_3 (m.d 1 4) (by simp) with h9115 | h9115
                                · linarith only [h2, h9115, hlam]
                                · rcases p9083_3 (m.d 1 5) (by simp) with h9117 | h9117
                                  · linarith only [h9117, hlam, p9083_0]
                                  · rcases h3bigk with h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c | h9119c
                                    · have p9119_0 := h9119c.1
                                      have p9119_1 := h9119c.2.1
                                      have p9119_2 := h9119c.2.2.1
                                      have p9119_3 := h9119c.2.2.2
                                      linarith only [hlam, p9119_0]
                                    · have p9119_0 := h9119c.1
                                      have p9119_1 := h9119c.2.1
                                      have p9119_2 := h9119c.2.2.1
                                      have p9119_3 := h9119c.2.2.2
                                      linarith only [h4, h8903, h9081, hc13, hc45, hlam, hphi, ht34, p9119_1]
                                    · have p9119_0 := h9119c.1
                                      have p9119_1 := h9119c.2.1
                                      have p9119_2 := h9119c.2.2.1
                                      have p9119_3 := h9119c.2.2.2
                                      linarith only [h4, hlam, p9119_1]
                                    · have p9119_0 := h9119c.1
                                      have p9119_1 := h9119c.2.1
                                      have p9119_2 := h9119c.2.2.1
                                      have p9119_3 := h9119c.2.2.2
                                      linarith only [h4, h8903, h9081, hc34, hc45, hlam, hphi, p9119_1]
                                    · have p9119_0 := h9119c.1
                                      have p9119_1 := h9119c.2.1
                                      have p9119_2 := h9119c.2.2.1
                                      have p9119_3 := h9119c.2.2.2
                                      linarith only [h7233, hlam, p9119_0]
                                    · have p9119_0 := h9119c.1
                                      have p9119_1 := h9119c.2.1
                                      have p9119_2 := h9119c.2.2.1
                                      have p9119_3 := h9119c.2.2.2
                                      linarith only [h1, hlam, p9119_0]
                                    · have p9119_0 := h9119c.1
                                      have p9119_1 := h9119c.2.1
                                      have p9119_2 := h9119c.2.2.1
                                      have p9119_3 := h9119c.2.2.2
                                      linarith only [hlam, p9119_0]
                                    · have p9119_0 := h9119c.1
                                      have p9119_1 := h9119c.2.1
                                      have p9119_2 := h9119c.2.2.1
                                      have p9119_3 := h9119c.2.2.2
                                      linarith only [h8887, hlam, p9119_1]
                                    · have p9119_0 := h9119c.1
                                      have p9119_1 := h9119c.2.1
                                      have p9119_2 := h9119c.2.2.1
                                      have p9119_3 := h9119c.2.2.2
                                      linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9119_1]
                                    · have p9119_0 := h9119c.1
                                      have p9119_1 := h9119c.2.1
                                      have p9119_2 := h9119c.2.2.1
                                      have p9119_3 := h9119c.2.2.2
                                      linarith only [h8898, hlam, p9119_0]
                                    · have p9119_0 := h9119c.1
                                      have p9119_1 := h9119c.2.1
                                      have p9119_2 := h9119c.2.2.1
                                      have p9119_3 := h9119c.2.2.2
                                      linarith only [h8903, h9081, hc03, hc45, hlam, hphi, ht34, p9119_1]
                                    · have p9119_0 := h9119c.1
                                      have p9119_1 := h9119c.2.1
                                      have p9119_2 := h9119c.2.2.1
                                      have p9119_3 := h9119c.2.2.2
                                      linarith only [h8903, h9081, hc13, hc45, hlam, hphi, ht34, p9119_1]
                                    · have p9119_0 := h9119c.1
                                      have p9119_1 := h9119c.2.1
                                      have p9119_2 := h9119c.2.2.1
                                      have p9119_3 := h9119c.2.2.2
                                      linarith only [hlam, p9119_0]
                                    · have p9119_0 := h9119c.1
                                      have p9119_1 := h9119c.2.1
                                      have p9119_2 := h9119c.2.2.1
                                      have p9119_3 := h9119c.2.2.2
                                      linarith only [h8903, h9081, hc34, hc45, hlam, hphi, p9119_1]
                                    · have p9119_0 := h9119c.1
                                      have p9119_1 := h9119c.2.1
                                      have p9119_2 := h9119c.2.2.1
                                      have p9119_3 := h9119c.2.2.2
                                      linarith only [h8903, hlam, p9119_0]
                                    · have p9119_0 := h9119c.1
                                      have p9119_1 := h9119c.2.1
                                      have p9119_2 := h9119c.2.2.1
                                      have p9119_3 := h9119c.2.2.2
                                      linarith only [h7232, hlam, p9119_0]
                                    · have p9119_0 := h9119c.1
                                      have p9119_1 := h9119c.2.1
                                      have p9119_2 := h9119c.2.2.1
                                      have p9119_3 := h9119c.2.2.2
                                      linarith only [h8897, hlam, p9119_0]
                                    · have p9119_0 := h9119c.1
                                      have p9119_1 := h9119c.2.1
                                      have p9119_2 := h9119c.2.2.1
                                      have p9119_3 := h9119c.2.2.2
                                      linarith only [h8902, hlam, p9119_0]
                                    · have p9119_0 := h9119c.1
                                      have p9119_1 := h9119c.2.1
                                      have p9119_2 := h9119c.2.2.1
                                      have p9119_3 := h9119c.2.2.2
                                      linarith only [hlam, p9119_0]
                                    · have p9119_0 := h9119c.1
                                      have p9119_1 := h9119c.2.1
                                      have p9119_2 := h9119c.2.2.1
                                      have p9119_3 := h9119c.2.2.2
                                      linarith only [h9081, hlam, p9119_1]
                                    · have p9119_0 := h9119c.1
                                      have p9119_1 := h9119c.2.1
                                      have p9119_2 := h9119c.2.2.1
                                      have p9119_3 := h9119c.2.2.2
                                      linarith only [h9081, hc03, hc45, hlam, hphi, ht34, p9119_1]
                                    · have p9119_0 := h9119c.1
                                      have p9119_1 := h9119c.2.1
                                      have p9119_2 := h9119c.2.2.1
                                      have p9119_3 := h9119c.2.2.2
                                      linarith only [h8897, h9081, hc34, hc45, hlam, hphi, p9119_1]
                                    · have p9119_0 := h9119c.1
                                      have p9119_1 := h9119c.2.1
                                      have p9119_2 := h9119c.2.2.1
                                      have p9119_3 := h9119c.2.2.2
                                      linarith only [h9081, hc23, hc45, hlam, hphi, ht34, p9119_1]
                                    · have p9119_0 := h9119c.1
                                      have p9119_1 := h9119c.2.1
                                      have p9119_2 := h9119c.2.2.1
                                      have p9119_3 := h9119c.2.2.2
                                      linarith only [h9081, hc34, hc45, hlam, hphi, p9119_1]
                                    · have p9119_0 := h9119c.1
                                      have p9119_1 := h9119c.2.1
                                      have p9119_2 := h9119c.2.2.1
                                      have p9119_3 := h9119c.2.2.2
                                      linarith only [hlam, p9119_0]
                          · linarith only [h9110, hlam, p9083_0]
                        · have p9083_0 := h9083c.1
                          have p9083_1 := h9083c.2.1
                          have p9083_2 := h9083c.2.2.1
                          have p9083_3 := h9083c.2.2.2
                          linarith only [h0, hlam, p9083_0]
                        · have p9083_0 := h9083c.1
                          have p9083_1 := h9083c.2.1
                          have p9083_2 := h9083c.2.2.1
                          have p9083_3 := h9083c.2.2.2
                          linarith only [hlam, p9083_0]
                        · have p9083_0 := h9083c.1
                          have p9083_1 := h9083c.2.1
                          have p9083_2 := h9083c.2.2.1
                          have p9083_3 := h9083c.2.2.2
                          linarith only [h8887, hlam, p9083_0]
                        · have p9083_0 := h9083c.1
                          have p9083_1 := h9083c.2.1
                          have p9083_2 := h9083c.2.2.1
                          have p9083_3 := h9083c.2.2.2
                          linarith only [h8889, hlam, p9083_0]
                        · have p9083_0 := h9083c.1
                          have p9083_1 := h9083c.2.1
                          have p9083_2 := h9083c.2.2.1
                          have p9083_3 := h9083c.2.2.2
                          linarith only [h8891, hlam, p9083_0]
                        · have p9083_0 := h9083c.1
                          have p9083_1 := h9083c.2.1
                          have p9083_2 := h9083c.2.2.1
                          have p9083_3 := h9083c.2.2.2
                          linarith only [h1, hlam, p9083_0]
                        · have p9083_0 := h9083c.1
                          have p9083_1 := h9083c.2.1
                          have p9083_2 := h9083c.2.2.1
                          have p9083_3 := h9083c.2.2.2
                          linarith only [h1, h7233, h9081, hc12, hc45, hlam, hphi, ht23, ht34, p9083_1]
                        · have p9083_0 := h9083c.1
                          have p9083_1 := h9083c.2.1
                          have p9083_2 := h9083c.2.2.1
                          have p9083_3 := h9083c.2.2.2
                          linarith only [hlam, p9083_0]
                        · have p9083_0 := h9083c.1
                          have p9083_1 := h9083c.2.1
                          have p9083_2 := h9083c.2.2.1
                          have p9083_3 := h9083c.2.2.2
                          linarith only [h1, h7233, h8889, h9081, hc12, hc45, hlam, hphi, ht23, ht34, p9083_1]
                        · have p9083_0 := h9083c.1
                          have p9083_1 := h9083c.2.1
                          have p9083_2 := h9083c.2.2.1
                          have p9083_3 := h9083c.2.2.2
                          linarith only [h8898, hlam, p9083_1]
                        · have p9083_0 := h9083c.1
                          have p9083_1 := h9083c.2.1
                          have p9083_2 := h9083c.2.2.1
                          have p9083_3 := h9083c.2.2.2
                          linarith only [h2, hlam, p9083_0]
                        · have p9083_0 := h9083c.1
                          have p9083_1 := h9083c.2.1
                          have p9083_2 := h9083c.2.2.1
                          have p9083_3 := h9083c.2.2.2
                          linarith only [h2, h7232, h7233, h9081, hc12, hc45, hlam, hphi, ht23, ht34, p9083_1]
                        · have p9083_0 := h9083c.1
                          have p9083_1 := h9083c.2.1
                          have p9083_2 := h9083c.2.2.1
                          have p9083_3 := h9083c.2.2.2
                          linarith only [h8897, hlam, p9083_0]
                        · have p9083_0 := h9083c.1
                          have p9083_1 := h9083c.2.1
                          have p9083_2 := h9083c.2.2.1
                          have p9083_3 := h9083c.2.2.2
                          linarith only [hlam, p9083_0]
                        · have p9083_0 := h9083c.1
                          have p9083_1 := h9083c.2.1
                          have p9083_2 := h9083c.2.2.1
                          have p9083_3 := h9083c.2.2.2
                          linarith only [h8900, hlam, p9083_1]
                        · have p9083_0 := h9083c.1
                          have p9083_1 := h9083c.2.1
                          have p9083_2 := h9083c.2.2.1
                          have p9083_3 := h9083c.2.2.2
                          linarith only [h3, hlam, p9083_0]
                        · have p9083_0 := h9083c.1
                          have p9083_1 := h9083c.2.1
                          have p9083_2 := h9083c.2.2.1
                          have p9083_3 := h9083c.2.2.2
                          rcases p9083_3 (m.d 0 1) (by simp) with h9162 | h9162
                          · rcases p9083_3 (m.d 1 2) (by simp) with h9163 | h9163
                            · linarith only [h8891, h9163, hlam]
                            · rcases p9083_3 (m.d 1 3) (by simp) with h9165 | h9165
                              · linarith only [h8898, h9165, hlam]
                              · linarith only [h8887, h9165, hlam]
                          · linarith only [h0, h9162, hlam]
                        · have p9083_0 := h9083c.1
                          have p9083_1 := h9083c.2.1
                          have p9083_2 := h9083c.2.2.1
                          have p9083_3 := h9083c.2.2.2
                          linarith only [h3, h8897, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9083_1]
                        · have p9083_0 := h9083c.1
                          have p9083_1 := h9083c.2.1
                          have p9083_2 := h9083c.2.2.1
                          have p9083_3 := h9083c.2.2.2
                          rcases p9083_3 (m.d 0 1) (by simp) with h9170 | h9170
                          · rcases p9083_3 (m.d 1 2) (by simp) with h9171 | h9171
                            · linarith only [h8891, h9171, hlam]
                            · rcases p9083_3 (m.d 1 3) (by simp) with h9173 | h9173
                              · linarith only [h8898, h9173, hlam]
                              · linarith only [h8897, h9173, hlam]
                          · linarith only [h2, h9170, hlam]
                        · have p9083_0 := h9083c.1
                          have p9083_1 := h9083c.2.1
                          have p9083_2 := h9083c.2.2.1
                          have p9083_3 := h9083c.2.2.2
                          linarith only [hlam, p9083_0]
                · linarith only [h1, h4, h8897, h8902, hlam]
          · linarith only [h7232, h7233, h8897, hc13, hc35, hlam, hphi]

set_option maxHeartbeats 5858000 in
set_option maxHeartbeats 5858000 in
theorem r1l7_11_23_L_I_H_I_s10_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg6364 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h7232 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h6364 := hg6364
  rcases m.htr 0 3 5 (by decide) (by decide) with h7233 | h7233
  · exact r1l7_11_23_L_I_H_I_s10_x0_x0 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg6364 h7232 h7233
  · exact r1l7_11_23_L_I_H_I_s10_x0_x1 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg6364 h7232 h7233

set_option maxHeartbeats 5858000 in
set_option maxHeartbeats 5858000 in
theorem r1l7_11_23_L_I_H_I_s10_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg6364 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h7232 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h9180 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h6364 := hg6364
  rcases m.htr 0 4 5 (by decide) (by decide) with h9181 | h9181
  · rcases m.htr 1 2 3 (by decide) (by decide) with h9182 | h9182
    · linarith only [h0, h4, h9182, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h9184 | h9184
      · linarith only [h0, h6364, h9184, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h9186 | h9186
        · rcases m.htr 1 3 4 (by decide) (by decide) with h9187 | h9187
          · linarith only [h1, h7232, h9187, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h9189 | h9189
            · rcases m.htr 1 4 5 (by decide) (by decide) with h9190 | h9190
              · rcases m.htr 2 3 4 (by decide) (by decide) with h9191 | h9191
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9192 | h9192
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9193 | h9193
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9194 | h9194
                      · rcases h1bigk with h9195c | h9195c | h9195c | h9195c | h9195c | h9195c | h9195c | h9195c | h9195c | h9195c | h9195c | h9195c | h9195c | h9195c | h9195c | h9195c | h9195c | h9195c | h9195c | h9195c | h9195c | h9195c | h9195c | h9195c | h9195c
                        · have p9195_0 := h9195c.1
                          have p9195_1 := h9195c.2.1
                          have p9195_2 := h9195c.2.2.1
                          have p9195_3 := h9195c.2.2.2
                          linarith only [hlam, p9195_0]
                        · have p9195_0 := h9195c.1
                          have p9195_1 := h9195c.2.1
                          have p9195_2 := h9195c.2.2.1
                          have p9195_3 := h9195c.2.2.2
                          rcases p9195_3 (m.d 0 1) (by simp) with h9197 | h9197
                          · rcases p9195_3 (m.d 1 2) (by simp) with h9198 | h9198
                            · linarith only [h9198, hlam, p9195_0]
                            · rcases p9195_3 (m.d 1 3) (by simp) with h9200 | h9200
                              · linarith only [h1, h9200, hlam]
                              · linarith only [h9182, h9200, hlam]
                          · linarith only [h9197, hlam, p9195_0]
                        · have p9195_0 := h9195c.1
                          have p9195_1 := h9195c.2.1
                          have p9195_2 := h9195c.2.2.1
                          have p9195_3 := h9195c.2.2.2
                          rcases p9195_3 (m.d 0 1) (by simp) with h9204 | h9204
                          · rcases p9195_3 (m.d 1 2) (by simp) with h9205 | h9205
                            · linarith only [h0, h9205, hlam]
                            · rcases p9195_3 (m.d 1 3) (by simp) with h9207 | h9207
                              · linarith only [h9207, hlam, p9195_0]
                              · rcases p9195_3 (m.d 1 4) (by simp) with h9209 | h9209
                                · linarith only [h2, h9209, hlam]
                                · linarith only [h9187, h9209, hlam]
                          · linarith only [h9204, hlam, p9195_0]
                        · have p9195_0 := h9195c.1
                          have p9195_1 := h9195c.2.1
                          have p9195_2 := h9195c.2.2.1
                          have p9195_3 := h9195c.2.2.2
                          rcases p9195_3 (m.d 0 1) (by simp) with h9213 | h9213
                          · rcases p9195_3 (m.d 1 2) (by simp) with h9214 | h9214
                            · linarith only [h0, h9214, hlam]
                            · rcases p9195_3 (m.d 1 3) (by simp) with h9216 | h9216
                              · linarith only [h1, h9216, hlam]
                              · rcases p9195_3 (m.d 1 4) (by simp) with h9218 | h9218
                                · linarith only [h9218, hlam, p9195_0]
                                · rcases p9195_3 (m.d 1 5) (by simp) with h9220 | h9220
                                  · linarith only [h3, h9220, hlam]
                                  · rcases h3bigk with h9222c | h9222c | h9222c | h9222c | h9222c | h9222c | h9222c | h9222c | h9222c | h9222c | h9222c | h9222c | h9222c | h9222c | h9222c | h9222c | h9222c | h9222c | h9222c | h9222c | h9222c | h9222c | h9222c | h9222c | h9222c
                                    · have p9222_0 := h9222c.1
                                      have p9222_1 := h9222c.2.1
                                      have p9222_2 := h9222c.2.2.1
                                      have p9222_3 := h9222c.2.2.2
                                      linarith only [hlam, p9222_0]
                                    · have p9222_0 := h9222c.1
                                      have p9222_1 := h9222c.2.1
                                      have p9222_2 := h9222c.2.2.1
                                      have p9222_3 := h9222c.2.2.2
                                      linarith only [h7232, h9191, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p9222_1]
                                    · have p9222_0 := h9222c.1
                                      have p9222_1 := h9222c.2.1
                                      have p9222_2 := h9222c.2.2.1
                                      have p9222_3 := h9222c.2.2.2
                                      linarith only [h4, hlam, p9222_1]
                                    · have p9222_0 := h9222c.1
                                      have p9222_1 := h9222c.2.1
                                      have p9222_2 := h9222c.2.2.1
                                      have p9222_3 := h9222c.2.2.2
                                      linarith only [h7232, hlam, p9222_0]
                                    · have p9222_0 := h9222c.1
                                      have p9222_1 := h9222c.2.1
                                      have p9222_2 := h9222c.2.2.1
                                      have p9222_3 := h9222c.2.2.2
                                      linarith only [h7232, h9191, h9194, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9222_1]
                                    · have p9222_0 := h9222c.1
                                      have p9222_1 := h9222c.2.1
                                      have p9222_2 := h9222c.2.2.1
                                      have p9222_3 := h9222c.2.2.2
                                      linarith only [h1, hlam, p9222_0]
                                    · have p9222_0 := h9222c.1
                                      have p9222_1 := h9222c.2.1
                                      have p9222_2 := h9222c.2.2.1
                                      have p9222_3 := h9222c.2.2.2
                                      linarith only [hlam, p9222_0]
                                    · have p9222_0 := h9222c.1
                                      have p9222_1 := h9222c.2.1
                                      have p9222_2 := h9222c.2.2.1
                                      have p9222_3 := h9222c.2.2.2
                                      linarith only [h9182, hlam, p9222_1]
                                    · have p9222_0 := h9222c.1
                                      have p9222_1 := h9222c.2.1
                                      have p9222_2 := h9222c.2.2.1
                                      have p9222_3 := h9222c.2.2.2
                                      linarith only [h9187, hlam, p9222_0]
                                    · have p9222_0 := h9222c.1
                                      have p9222_1 := h9222c.2.1
                                      have p9222_2 := h9222c.2.2.1
                                      have p9222_3 := h9222c.2.2.2
                                      linarith only [h1, h9194, hc01, hc45, hlam, hphi, ht0b, ht5b, p9222_1]
                                    · have p9222_0 := h9222c.1
                                      have p9222_1 := h9222c.2.1
                                      have p9222_2 := h9222c.2.2.1
                                      have p9222_3 := h9222c.2.2.2
                                      linarith only [h0, h4, h9186, h9192, h9194, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9222_1]
                                    · have p9222_0 := h9222c.1
                                      have p9222_1 := h9222c.2.1
                                      have p9222_2 := h9222c.2.2.1
                                      have p9222_3 := h9222c.2.2.2
                                      linarith only [h9182, h9186, h9192, h9194, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9222_1]
                                    · have p9222_0 := h9222c.1
                                      have p9222_1 := h9222c.2.1
                                      have p9222_2 := h9222c.2.2.1
                                      have p9222_3 := h9222c.2.2.2
                                      linarith only [hlam, p9222_0]
                                    · have p9222_0 := h9222c.1
                                      have p9222_1 := h9222c.2.1
                                      have p9222_2 := h9222c.2.2.1
                                      have p9222_3 := h9222c.2.2.2
                                      linarith only [h0, h4, h7232, h9186, h9192, h9194, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9222_1]
                                    · have p9222_0 := h9222c.1
                                      have p9222_1 := h9222c.2.1
                                      have p9222_2 := h9222c.2.2.1
                                      have p9222_3 := h9222c.2.2.2
                                      rcases p9222_3 (m.d 0 3) (by simp) with h9237 | h9237
                                      · linarith only [h4, h9237, hlam]
                                      · linarith only [h9180, h9237, hlam]
                                    · have p9222_0 := h9222c.1
                                      have p9222_1 := h9222c.2.1
                                      have p9222_2 := h9222c.2.2.1
                                      have p9222_3 := h9222c.2.2.2
                                      linarith only [h0, h4, h9186, h9191, h9192, h9194, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9222_1]
                                    · have p9222_0 := h9222c.1
                                      have p9222_1 := h9222c.2.1
                                      have p9222_2 := h9222c.2.2.1
                                      have p9222_3 := h9222c.2.2.2
                                      linarith only [h9182, h9186, h9191, h9192, h9194, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9222_1]
                                    · have p9222_0 := h9222c.1
                                      have p9222_1 := h9222c.2.1
                                      have p9222_2 := h9222c.2.2.1
                                      have p9222_3 := h9222c.2.2.2
                                      linarith only [h9191, hlam, p9222_0]
                                    · have p9222_0 := h9222c.1
                                      have p9222_1 := h9222c.2.1
                                      have p9222_2 := h9222c.2.2.1
                                      have p9222_3 := h9222c.2.2.2
                                      linarith only [hlam, p9222_0]
                                    · have p9222_0 := h9222c.1
                                      have p9222_1 := h9222c.2.1
                                      have p9222_2 := h9222c.2.2.1
                                      have p9222_3 := h9222c.2.2.2
                                      linarith only [h9191, h9194, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9222_1]
                                    · have p9222_0 := h9222c.1
                                      have p9222_1 := h9222c.2.1
                                      have p9222_2 := h9222c.2.2.1
                                      have p9222_3 := h9222c.2.2.2
                                      linarith only [h9180, hlam, p9222_0]
                                    · have p9222_0 := h9222c.1
                                      have p9222_1 := h9222c.2.1
                                      have p9222_2 := h9222c.2.2.1
                                      have p9222_3 := h9222c.2.2.2
                                      linarith only [h9189, hlam, p9222_0]
                                    · have p9222_0 := h9222c.1
                                      have p9222_1 := h9222c.2.1
                                      have p9222_2 := h9222c.2.2.1
                                      have p9222_3 := h9222c.2.2.2
                                      linarith only [h9192, hlam, p9222_0]
                                    · have p9222_0 := h9222c.1
                                      have p9222_1 := h9222c.2.1
                                      have p9222_2 := h9222c.2.2.1
                                      have p9222_3 := h9222c.2.2.2
                                      linarith only [h9194, hlam, p9222_0]
                                    · have p9222_0 := h9222c.1
                                      have p9222_1 := h9222c.2.1
                                      have p9222_2 := h9222c.2.2.1
                                      have p9222_3 := h9222c.2.2.2
                                      linarith only [hlam, p9222_0]
                          · linarith only [h9213, hlam, p9195_0]
                        · have p9195_0 := h9195c.1
                          have p9195_1 := h9195c.2.1
                          have p9195_2 := h9195c.2.2.1
                          have p9195_3 := h9195c.2.2.2
                          rcases p9195_3 (m.d 0 1) (by simp) with h9251 | h9251
                          · rcases p9195_3 (m.d 1 2) (by simp) with h9252 | h9252
                            · linarith only [h0, h9252, hlam]
                            · linarith only [h9186, h9252, hlam]
                          · linarith only [h9251, hlam, p9195_0]
                        · have p9195_0 := h9195c.1
                          have p9195_1 := h9195c.2.1
                          have p9195_2 := h9195c.2.2.1
                          have p9195_3 := h9195c.2.2.2
                          linarith only [h0, hlam, p9195_0]
                        · have p9195_0 := h9195c.1
                          have p9195_1 := h9195c.2.1
                          have p9195_2 := h9195c.2.2.1
                          have p9195_3 := h9195c.2.2.2
                          linarith only [hlam, p9195_0]
                        · have p9195_0 := h9195c.1
                          have p9195_1 := h9195c.2.1
                          have p9195_2 := h9195c.2.2.1
                          have p9195_3 := h9195c.2.2.2
                          linarith only [h9182, hlam, p9195_0]
                        · have p9195_0 := h9195c.1
                          have p9195_1 := h9195c.2.1
                          have p9195_2 := h9195c.2.2.1
                          have p9195_3 := h9195c.2.2.2
                          linarith only [h9184, hlam, p9195_0]
                        · have p9195_0 := h9195c.1
                          have p9195_1 := h9195c.2.1
                          have p9195_2 := h9195c.2.2.1
                          have p9195_3 := h9195c.2.2.2
                          linarith only [h0, h4, h7232, h9191, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p9195_1]
                        · have p9195_0 := h9195c.1
                          have p9195_1 := h9195c.2.1
                          have p9195_2 := h9195c.2.2.1
                          have p9195_3 := h9195c.2.2.2
                          linarith only [h1, hlam, p9195_0]
                        · have p9195_0 := h9195c.1
                          have p9195_1 := h9195c.2.1
                          have p9195_2 := h9195c.2.2.1
                          have p9195_3 := h9195c.2.2.2
                          linarith only [h1, h7232, h9191, hc12, hc23, hlam, hphi, p9195_1]
                        · have p9195_0 := h9195c.1
                          have p9195_1 := h9195c.2.1
                          have p9195_2 := h9195c.2.2.1
                          have p9195_3 := h9195c.2.2.2
                          linarith only [hlam, p9195_0]
                        · have p9195_0 := h9195c.1
                          have p9195_1 := h9195c.2.1
                          have p9195_2 := h9195c.2.2.1
                          have p9195_3 := h9195c.2.2.2
                          linarith only [h9187, hlam, p9195_1]
                        · have p9195_0 := h9195c.1
                          have p9195_1 := h9195c.2.1
                          have p9195_2 := h9195c.2.2.1
                          have p9195_3 := h9195c.2.2.2
                          linarith only [h1, h7232, h9186, h9191, h9192, h9194, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9195_1]
                        · have p9195_0 := h9195c.1
                          have p9195_1 := h9195c.2.1
                          have p9195_2 := h9195c.2.2.1
                          have p9195_3 := h9195c.2.2.2
                          linarith only [h2, hlam, p9195_0]
                        · have p9195_0 := h9195c.1
                          have p9195_1 := h9195c.2.1
                          have p9195_2 := h9195c.2.2.1
                          have p9195_3 := h9195c.2.2.2
                          linarith only [h2, h9186, h9192, h9194, hc01, hc45, hlam, hphi, ht0b, ht5b, p9195_1]
                        · have p9195_0 := h9195c.1
                          have p9195_1 := h9195c.2.1
                          have p9195_2 := h9195c.2.2.1
                          have p9195_3 := h9195c.2.2.2
                          linarith only [h2, h7232, h9182, h9186, h9191, h9192, h9194, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9195_1]
                        · have p9195_0 := h9195c.1
                          have p9195_1 := h9195c.2.1
                          have p9195_2 := h9195c.2.2.1
                          have p9195_3 := h9195c.2.2.2
                          linarith only [hlam, p9195_0]
                        · have p9195_0 := h9195c.1
                          have p9195_1 := h9195c.2.1
                          have p9195_2 := h9195c.2.2.1
                          have p9195_3 := h9195c.2.2.2
                          rcases p9195_3 (m.d 0 1) (by simp) with h9270 | h9270
                          · rcases p9195_3 (m.d 1 2) (by simp) with h9271 | h9271
                            · linarith only [h9184, h9271, hlam]
                            · linarith only [h9186, h9271, hlam]
                          · linarith only [h3, h9270, hlam]
                        · have p9195_0 := h9195c.1
                          have p9195_1 := h9195c.2.1
                          have p9195_2 := h9195c.2.2.1
                          have p9195_3 := h9195c.2.2.2
                          linarith only [h3, hlam, p9195_0]
                        · have p9195_0 := h9195c.1
                          have p9195_1 := h9195c.2.1
                          have p9195_2 := h9195c.2.2.1
                          have p9195_3 := h9195c.2.2.2
                          linarith only [h9186, hlam, p9195_1]
                        · have p9195_0 := h9195c.1
                          have p9195_1 := h9195c.2.1
                          have p9195_2 := h9195c.2.2.1
                          have p9195_3 := h9195c.2.2.2
                          linarith only [h9189, hlam, p9195_0]
                        · have p9195_0 := h9195c.1
                          have p9195_1 := h9195c.2.1
                          have p9195_2 := h9195c.2.2.1
                          have p9195_3 := h9195c.2.2.2
                          linarith only [h9190, hlam, p9195_0]
                        · have p9195_0 := h9195c.1
                          have p9195_1 := h9195c.2.1
                          have p9195_2 := h9195c.2.2.1
                          have p9195_3 := h9195c.2.2.2
                          linarith only [hlam, p9195_0]
                      · linarith only [h7232, h9181, h9194, hlam]
                    · linarith only [h0, h3, h6364, h9186, h9190, h9192, h9193, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · linarith only [h7232, h9180, h9192, hc23, hc34, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9283 | h9283
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9284 | h9284
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9285 | h9285
                      · rcases h1bigk with h9286c | h9286c | h9286c | h9286c | h9286c | h9286c | h9286c | h9286c | h9286c | h9286c | h9286c | h9286c | h9286c | h9286c | h9286c | h9286c | h9286c | h9286c | h9286c | h9286c | h9286c | h9286c | h9286c | h9286c | h9286c
                        · have p9286_0 := h9286c.1
                          have p9286_1 := h9286c.2.1
                          have p9286_2 := h9286c.2.2.1
                          have p9286_3 := h9286c.2.2.2
                          linarith only [hlam, p9286_0]
                        · have p9286_0 := h9286c.1
                          have p9286_1 := h9286c.2.1
                          have p9286_2 := h9286c.2.2.1
                          have p9286_3 := h9286c.2.2.2
                          rcases p9286_3 (m.d 0 1) (by simp) with h9288 | h9288
                          · rcases p9286_3 (m.d 1 2) (by simp) with h9289 | h9289
                            · linarith only [h9289, hlam, p9286_0]
                            · rcases p9286_3 (m.d 1 3) (by simp) with h9291 | h9291
                              · linarith only [h1, h9291, hlam]
                              · linarith only [h9182, h9291, hlam]
                          · linarith only [h9288, hlam, p9286_0]
                        · have p9286_0 := h9286c.1
                          have p9286_1 := h9286c.2.1
                          have p9286_2 := h9286c.2.2.1
                          have p9286_3 := h9286c.2.2.2
                          rcases p9286_3 (m.d 0 1) (by simp) with h9295 | h9295
                          · rcases p9286_3 (m.d 1 2) (by simp) with h9296 | h9296
                            · linarith only [h0, h9296, hlam]
                            · rcases p9286_3 (m.d 1 3) (by simp) with h9298 | h9298
                              · linarith only [h9298, hlam, p9286_0]
                              · rcases p9286_3 (m.d 1 4) (by simp) with h9300 | h9300
                                · linarith only [h2, h9300, hlam]
                                · linarith only [h9187, h9300, hlam]
                          · linarith only [h9295, hlam, p9286_0]
                        · have p9286_0 := h9286c.1
                          have p9286_1 := h9286c.2.1
                          have p9286_2 := h9286c.2.2.1
                          have p9286_3 := h9286c.2.2.2
                          rcases p9286_3 (m.d 0 1) (by simp) with h9304 | h9304
                          · rcases p9286_3 (m.d 1 2) (by simp) with h9305 | h9305
                            · linarith only [h0, h9305, hlam]
                            · rcases p9286_3 (m.d 1 3) (by simp) with h9307 | h9307
                              · linarith only [h1, h9307, hlam]
                              · rcases p9286_3 (m.d 1 4) (by simp) with h9309 | h9309
                                · linarith only [h9309, hlam, p9286_0]
                                · rcases p9286_3 (m.d 1 5) (by simp) with h9311 | h9311
                                  · linarith only [h3, h9311, hlam]
                                  · rcases h3bigk with h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c
                                    · have p9313_0 := h9313c.1
                                      have p9313_1 := h9313c.2.1
                                      have p9313_2 := h9313c.2.2.1
                                      have p9313_3 := h9313c.2.2.2
                                      linarith only [hlam, p9313_0]
                                    · have p9313_0 := h9313c.1
                                      have p9313_1 := h9313c.2.1
                                      have p9313_2 := h9313c.2.2.1
                                      have p9313_3 := h9313c.2.2.2
                                      linarith only [h4, h9191, hc13, hc34, hlam, hphi, p9313_1]
                                    · have p9313_0 := h9313c.1
                                      have p9313_1 := h9313c.2.1
                                      have p9313_2 := h9313c.2.2.1
                                      have p9313_3 := h9313c.2.2.2
                                      linarith only [h4, hlam, p9313_1]
                                    · have p9313_0 := h9313c.1
                                      have p9313_1 := h9313c.2.1
                                      have p9313_2 := h9313c.2.2.1
                                      have p9313_3 := h9313c.2.2.2
                                      linarith only [h7232, hlam, p9313_0]
                                    · have p9313_0 := h9313c.1
                                      have p9313_1 := h9313c.2.1
                                      have p9313_2 := h9313c.2.2.1
                                      have p9313_3 := h9313c.2.2.2
                                      linarith only [h4, h9191, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p9313_1]
                                    · have p9313_0 := h9313c.1
                                      have p9313_1 := h9313c.2.1
                                      have p9313_2 := h9313c.2.2.1
                                      have p9313_3 := h9313c.2.2.2
                                      linarith only [h1, hlam, p9313_0]
                                    · have p9313_0 := h9313c.1
                                      have p9313_1 := h9313c.2.1
                                      have p9313_2 := h9313c.2.2.1
                                      have p9313_3 := h9313c.2.2.2
                                      linarith only [hlam, p9313_0]
                                    · have p9313_0 := h9313c.1
                                      have p9313_1 := h9313c.2.1
                                      have p9313_2 := h9313c.2.2.1
                                      have p9313_3 := h9313c.2.2.2
                                      linarith only [h9182, hlam, p9313_1]
                                    · have p9313_0 := h9313c.1
                                      have p9313_1 := h9313c.2.1
                                      have p9313_2 := h9313c.2.2.1
                                      have p9313_3 := h9313c.2.2.2
                                      linarith only [h9187, hlam, p9313_0]
                                    · have p9313_0 := h9313c.1
                                      have p9313_1 := h9313c.2.1
                                      have p9313_2 := h9313c.2.2.1
                                      have p9313_3 := h9313c.2.2.2
                                      linarith only [h1, h9285, hc01, hc45, hlam, hphi, ht0b, ht5b, p9313_1]
                                    · have p9313_0 := h9313c.1
                                      have p9313_1 := h9313c.2.1
                                      have p9313_2 := h9313c.2.2.1
                                      have p9313_3 := h9313c.2.2.2
                                      linarith only [h9191, hc03, hc34, hlam, hphi, p9313_1]
                                    · have p9313_0 := h9313c.1
                                      have p9313_1 := h9313c.2.1
                                      have p9313_2 := h9313c.2.2.1
                                      have p9313_3 := h9313c.2.2.2
                                      linarith only [h9191, hc13, hc34, hlam, hphi, p9313_1]
                                    · have p9313_0 := h9313c.1
                                      have p9313_1 := h9313c.2.1
                                      have p9313_2 := h9313c.2.2.1
                                      have p9313_3 := h9313c.2.2.2
                                      linarith only [hlam, p9313_0]
                                    · have p9313_0 := h9313c.1
                                      have p9313_1 := h9313c.2.1
                                      have p9313_2 := h9313c.2.2.1
                                      have p9313_3 := h9313c.2.2.2
                                      linarith only [h9191, hlam, p9313_0]
                                    · have p9313_0 := h9313c.1
                                      have p9313_1 := h9313c.2.1
                                      have p9313_2 := h9313c.2.2.1
                                      have p9313_3 := h9313c.2.2.2
                                      linarith only [h9191, h9285, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p9313_1]
                                    · have p9313_0 := h9313c.1
                                      have p9313_1 := h9313c.2.1
                                      have p9313_2 := h9313c.2.2.1
                                      have p9313_3 := h9313c.2.2.2
                                      linarith only [h0, h4, h9186, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p9313_1]
                                    · have p9313_0 := h9313c.1
                                      have p9313_1 := h9313c.2.1
                                      have p9313_2 := h9313c.2.2.1
                                      have p9313_3 := h9313c.2.2.2
                                      linarith only [h9182, h9186, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p9313_1]
                                    · have p9313_0 := h9313c.1
                                      have p9313_1 := h9313c.2.1
                                      have p9313_2 := h9313c.2.2.1
                                      have p9313_3 := h9313c.2.2.2
                                      linarith only [hc23, hc34, hlam, hphi, p9313_1]
                                    · have p9313_0 := h9313c.1
                                      have p9313_1 := h9313c.2.1
                                      have p9313_2 := h9313c.2.2.1
                                      have p9313_3 := h9313c.2.2.2
                                      linarith only [hlam, p9313_0]
                                    · have p9313_0 := h9313c.1
                                      have p9313_1 := h9313c.2.1
                                      have p9313_2 := h9313c.2.2.1
                                      have p9313_3 := h9313c.2.2.2
                                      rcases p9313_3 (m.d 0 3) (by simp) with h9333 | h9333
                                      · linarith only [h7232, h9333, hlam]
                                      · linarith only [h9180, h9333, hlam]
                                    · have p9313_0 := h9313c.1
                                      have p9313_1 := h9313c.2.1
                                      have p9313_2 := h9313c.2.2.1
                                      have p9313_3 := h9313c.2.2.2
                                      linarith only [h9180, hlam, p9313_0]
                                    · have p9313_0 := h9313c.1
                                      have p9313_1 := h9313c.2.1
                                      have p9313_2 := h9313c.2.2.1
                                      have p9313_3 := h9313c.2.2.2
                                      linarith only [h9189, hlam, p9313_0]
                                    · have p9313_0 := h9313c.1
                                      have p9313_1 := h9313c.2.1
                                      have p9313_2 := h9313c.2.2.1
                                      have p9313_3 := h9313c.2.2.2
                                      linarith only [h9283, hlam, p9313_0]
                                    · have p9313_0 := h9313c.1
                                      have p9313_1 := h9313c.2.1
                                      have p9313_2 := h9313c.2.2.1
                                      have p9313_3 := h9313c.2.2.2
                                      linarith only [h9285, hlam, p9313_0]
                                    · have p9313_0 := h9313c.1
                                      have p9313_1 := h9313c.2.1
                                      have p9313_2 := h9313c.2.2.1
                                      have p9313_3 := h9313c.2.2.2
                                      linarith only [hlam, p9313_0]
                          · linarith only [h9304, hlam, p9286_0]
                        · have p9286_0 := h9286c.1
                          have p9286_1 := h9286c.2.1
                          have p9286_2 := h9286c.2.2.1
                          have p9286_3 := h9286c.2.2.2
                          rcases p9286_3 (m.d 0 1) (by simp) with h9342 | h9342
                          · rcases p9286_3 (m.d 1 2) (by simp) with h9343 | h9343
                            · linarith only [h0, h9343, hlam]
                            · linarith only [h9186, h9343, hlam]
                          · linarith only [h9342, hlam, p9286_0]
                        · have p9286_0 := h9286c.1
                          have p9286_1 := h9286c.2.1
                          have p9286_2 := h9286c.2.2.1
                          have p9286_3 := h9286c.2.2.2
                          linarith only [h0, hlam, p9286_0]
                        · have p9286_0 := h9286c.1
                          have p9286_1 := h9286c.2.1
                          have p9286_2 := h9286c.2.2.1
                          have p9286_3 := h9286c.2.2.2
                          linarith only [hlam, p9286_0]
                        · have p9286_0 := h9286c.1
                          have p9286_1 := h9286c.2.1
                          have p9286_2 := h9286c.2.2.1
                          have p9286_3 := h9286c.2.2.2
                          linarith only [h9182, hlam, p9286_0]
                        · have p9286_0 := h9286c.1
                          have p9286_1 := h9286c.2.1
                          have p9286_2 := h9286c.2.2.1
                          have p9286_3 := h9286c.2.2.2
                          linarith only [h9184, hlam, p9286_0]
                        · have p9286_0 := h9286c.1
                          have p9286_1 := h9286c.2.1
                          have p9286_2 := h9286c.2.2.1
                          have p9286_3 := h9286c.2.2.2
                          linarith only [h0, h4, h9186, h9191, h9283, h9285, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p9286_1]
                        · have p9286_0 := h9286c.1
                          have p9286_1 := h9286c.2.1
                          have p9286_2 := h9286c.2.2.1
                          have p9286_3 := h9286c.2.2.2
                          linarith only [h1, hlam, p9286_0]
                        · have p9286_0 := h9286c.1
                          have p9286_1 := h9286c.2.1
                          have p9286_2 := h9286c.2.2.1
                          have p9286_3 := h9286c.2.2.2
                          linarith only [h1, h7232, hc12, hc34, hlam, hphi, ht23, p9286_1]
                        · have p9286_0 := h9286c.1
                          have p9286_1 := h9286c.2.1
                          have p9286_2 := h9286c.2.2.1
                          have p9286_3 := h9286c.2.2.2
                          linarith only [hlam, p9286_0]
                        · have p9286_0 := h9286c.1
                          have p9286_1 := h9286c.2.1
                          have p9286_2 := h9286c.2.2.1
                          have p9286_3 := h9286c.2.2.2
                          linarith only [h9187, hlam, p9286_1]
                        · have p9286_0 := h9286c.1
                          have p9286_1 := h9286c.2.1
                          have p9286_2 := h9286c.2.2.1
                          have p9286_3 := h9286c.2.2.2
                          rcases p9286_3 (m.d 0 1) (by simp) with h9356 | h9356
                          · rcases p9286_3 (m.d 1 2) (by simp) with h9357 | h9357
                            · linarith only [h9182, h9357, hlam]
                            · linarith only [h9186, h9357, hlam]
                          · linarith only [h3, h9356, hlam]
                        · have p9286_0 := h9286c.1
                          have p9286_1 := h9286c.2.1
                          have p9286_2 := h9286c.2.2.1
                          have p9286_3 := h9286c.2.2.2
                          linarith only [h2, hlam, p9286_0]
                        · have p9286_0 := h9286c.1
                          have p9286_1 := h9286c.2.1
                          have p9286_2 := h9286c.2.2.1
                          have p9286_3 := h9286c.2.2.2
                          linarith only [h2, h9186, h9283, h9285, hc01, hc45, hlam, hphi, ht0b, ht5b, p9286_1]
                        · have p9286_0 := h9286c.1
                          have p9286_1 := h9286c.2.1
                          have p9286_2 := h9286c.2.2.1
                          have p9286_3 := h9286c.2.2.2
                          linarith only [h2, h9182, h9186, h9283, h9285, hc01, hc45, hlam, hphi, ht0b, ht5b, p9286_1]
                        · have p9286_0 := h9286c.1
                          have p9286_1 := h9286c.2.1
                          have p9286_2 := h9286c.2.2.1
                          have p9286_3 := h9286c.2.2.2
                          linarith only [hlam, p9286_0]
                        · have p9286_0 := h9286c.1
                          have p9286_1 := h9286c.2.1
                          have p9286_2 := h9286c.2.2.1
                          have p9286_3 := h9286c.2.2.2
                          rcases p9286_3 (m.d 0 1) (by simp) with h9365 | h9365
                          · rcases p9286_3 (m.d 1 2) (by simp) with h9366 | h9366
                            · linarith only [h9184, h9366, hlam]
                            · linarith only [h9186, h9366, hlam]
                          · linarith only [h3, h9365, hlam]
                        · have p9286_0 := h9286c.1
                          have p9286_1 := h9286c.2.1
                          have p9286_2 := h9286c.2.2.1
                          have p9286_3 := h9286c.2.2.2
                          linarith only [h3, hlam, p9286_0]
                        · have p9286_0 := h9286c.1
                          have p9286_1 := h9286c.2.1
                          have p9286_2 := h9286c.2.2.1
                          have p9286_3 := h9286c.2.2.2
                          linarith only [h9186, hlam, p9286_1]
                        · have p9286_0 := h9286c.1
                          have p9286_1 := h9286c.2.1
                          have p9286_2 := h9286c.2.2.1
                          have p9286_3 := h9286c.2.2.2
                          linarith only [h9189, hlam, p9286_0]
                        · have p9286_0 := h9286c.1
                          have p9286_1 := h9286c.2.1
                          have p9286_2 := h9286c.2.2.1
                          have p9286_3 := h9286c.2.2.2
                          linarith only [h9190, hlam, p9286_0]
                        · have p9286_0 := h9286c.1
                          have p9286_1 := h9286c.2.1
                          have p9286_2 := h9286c.2.2.1
                          have p9286_3 := h9286c.2.2.2
                          linarith only [hlam, p9286_0]
                      · linarith only [h0, h4, h9186, h9191, h9283, h9285, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                    · linarith only [h6364, h9181, h9284, hlam]
                  · linarith only [h0, h4, h9180, h9186, h9283, hc03, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h9182, h9186, h9187, h9190, hlam]
            · linarith only [h7232, h9180, h9182, h9186, h9189, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h9380 | h9380
          · linarith only [h1, h7232, h9180, h9380, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h9382 | h9382
            · rcases m.htr 1 4 5 (by decide) (by decide) with h9383 | h9383
              · rcases m.htr 2 3 4 (by decide) (by decide) with h9384 | h9384
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9385 | h9385
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9386 | h9386
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9387 | h9387
                      · rcases h1bigk with h9388c | h9388c | h9388c | h9388c | h9388c | h9388c | h9388c | h9388c | h9388c | h9388c | h9388c | h9388c | h9388c | h9388c | h9388c | h9388c | h9388c | h9388c | h9388c | h9388c | h9388c | h9388c | h9388c | h9388c | h9388c
                        · have p9388_0 := h9388c.1
                          have p9388_1 := h9388c.2.1
                          have p9388_2 := h9388c.2.2.1
                          have p9388_3 := h9388c.2.2.2
                          linarith only [hlam, p9388_0]
                        · have p9388_0 := h9388c.1
                          have p9388_1 := h9388c.2.1
                          have p9388_2 := h9388c.2.2.1
                          have p9388_3 := h9388c.2.2.2
                          rcases p9388_3 (m.d 0 1) (by simp) with h9390 | h9390
                          · rcases p9388_3 (m.d 1 2) (by simp) with h9391 | h9391
                            · linarith only [h9391, hlam, p9388_0]
                            · rcases p9388_3 (m.d 1 3) (by simp) with h9393 | h9393
                              · linarith only [h1, h9393, hlam]
                              · linarith only [h9182, h9393, hlam]
                          · linarith only [h9390, hlam, p9388_0]
                        · have p9388_0 := h9388c.1
                          have p9388_1 := h9388c.2.1
                          have p9388_2 := h9388c.2.2.1
                          have p9388_3 := h9388c.2.2.2
                          rcases p9388_3 (m.d 0 1) (by simp) with h9397 | h9397
                          · rcases p9388_3 (m.d 1 2) (by simp) with h9398 | h9398
                            · linarith only [h0, h9398, hlam]
                            · rcases p9388_3 (m.d 1 3) (by simp) with h9400 | h9400
                              · linarith only [h9400, hlam, p9388_0]
                              · rcases p9388_3 (m.d 1 4) (by simp) with h9402 | h9402
                                · linarith only [h2, h9402, hlam]
                                · linarith only [h9380, h9402, hlam]
                          · linarith only [h9397, hlam, p9388_0]
                        · have p9388_0 := h9388c.1
                          have p9388_1 := h9388c.2.1
                          have p9388_2 := h9388c.2.2.1
                          have p9388_3 := h9388c.2.2.2
                          rcases p9388_3 (m.d 0 1) (by simp) with h9406 | h9406
                          · rcases p9388_3 (m.d 1 2) (by simp) with h9407 | h9407
                            · linarith only [h0, h9407, hlam]
                            · rcases p9388_3 (m.d 1 3) (by simp) with h9409 | h9409
                              · linarith only [h1, h9409, hlam]
                              · rcases p9388_3 (m.d 1 4) (by simp) with h9411 | h9411
                                · linarith only [h9411, hlam, p9388_0]
                                · rcases p9388_3 (m.d 1 5) (by simp) with h9413 | h9413
                                  · linarith only [h3, h9413, hlam]
                                  · rcases h3bigk with h9415c | h9415c | h9415c | h9415c | h9415c | h9415c | h9415c | h9415c | h9415c | h9415c | h9415c | h9415c | h9415c | h9415c | h9415c | h9415c | h9415c | h9415c | h9415c | h9415c | h9415c | h9415c | h9415c | h9415c | h9415c
                                    · have p9415_0 := h9415c.1
                                      have p9415_1 := h9415c.2.1
                                      have p9415_2 := h9415c.2.2.1
                                      have p9415_3 := h9415c.2.2.2
                                      linarith only [hlam, p9415_0]
                                    · have p9415_0 := h9415c.1
                                      have p9415_1 := h9415c.2.1
                                      have p9415_2 := h9415c.2.2.1
                                      have p9415_3 := h9415c.2.2.2
                                      linarith only [h9382, h9387, hc03, hc45, hlam, hphi, ht0b, ht5b, p9415_1]
                                    · have p9415_0 := h9415c.1
                                      have p9415_1 := h9415c.2.1
                                      have p9415_2 := h9415c.2.2.1
                                      have p9415_3 := h9415c.2.2.2
                                      linarith only [h4, hlam, p9415_1]
                                    · have p9415_0 := h9415c.1
                                      have p9415_1 := h9415c.2.1
                                      have p9415_2 := h9415c.2.2.1
                                      have p9415_3 := h9415c.2.2.2
                                      linarith only [h7232, hlam, p9415_0]
                                    · have p9415_0 := h9415c.1
                                      have p9415_1 := h9415c.2.1
                                      have p9415_2 := h9415c.2.2.1
                                      have p9415_3 := h9415c.2.2.2
                                      linarith only [h7232, h9384, h9387, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9415_1]
                                    · have p9415_0 := h9415c.1
                                      have p9415_1 := h9415c.2.1
                                      have p9415_2 := h9415c.2.2.1
                                      have p9415_3 := h9415c.2.2.2
                                      linarith only [h1, hlam, p9415_0]
                                    · have p9415_0 := h9415c.1
                                      have p9415_1 := h9415c.2.1
                                      have p9415_2 := h9415c.2.2.1
                                      have p9415_3 := h9415c.2.2.2
                                      linarith only [hlam, p9415_0]
                                    · have p9415_0 := h9415c.1
                                      have p9415_1 := h9415c.2.1
                                      have p9415_2 := h9415c.2.2.1
                                      have p9415_3 := h9415c.2.2.2
                                      linarith only [h9182, hlam, p9415_1]
                                    · have p9415_0 := h9415c.1
                                      have p9415_1 := h9415c.2.1
                                      have p9415_2 := h9415c.2.2.1
                                      have p9415_3 := h9415c.2.2.2
                                      linarith only [h9380, hlam, p9415_0]
                                    · have p9415_0 := h9415c.1
                                      have p9415_1 := h9415c.2.1
                                      have p9415_2 := h9415c.2.2.1
                                      have p9415_3 := h9415c.2.2.2
                                      linarith only [h1, h9387, hc01, hc45, hlam, hphi, ht0b, ht5b, p9415_1]
                                    · have p9415_0 := h9415c.1
                                      have p9415_1 := h9415c.2.1
                                      have p9415_2 := h9415c.2.2.1
                                      have p9415_3 := h9415c.2.2.2
                                      linarith only [h4, hc02, hc23, hlam, hphi, p9415_1]
                                    · have p9415_0 := h9415c.1
                                      have p9415_1 := h9415c.2.1
                                      have p9415_2 := h9415c.2.2.1
                                      have p9415_3 := h9415c.2.2.2
                                      linarith only [h9182, hc12, hc23, hlam, hphi, p9415_1]
                                    · have p9415_0 := h9415c.1
                                      have p9415_1 := h9415c.2.1
                                      have p9415_2 := h9415c.2.2.1
                                      have p9415_3 := h9415c.2.2.2
                                      linarith only [hlam, p9415_0]
                                    · have p9415_0 := h9415c.1
                                      have p9415_1 := h9415c.2.1
                                      have p9415_2 := h9415c.2.2.1
                                      have p9415_3 := h9415c.2.2.2
                                      linarith only [h0, h6364, h7232, hc12, hc23, hlam, hphi, p9415_1]
                                    · have p9415_0 := h9415c.1
                                      have p9415_1 := h9415c.2.1
                                      have p9415_2 := h9415c.2.2.1
                                      have p9415_3 := h9415c.2.2.2
                                      rcases p9415_3 (m.d 0 3) (by simp) with h9430 | h9430
                                      · linarith only [h4, h9430, hlam]
                                      · linarith only [h9180, h9430, hlam]
                                    · have p9415_0 := h9415c.1
                                      have p9415_1 := h9415c.2.1
                                      have p9415_2 := h9415c.2.2.1
                                      have p9415_3 := h9415c.2.2.2
                                      linarith only [h1, h9382, h9387, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p9415_1]
                                    · have p9415_0 := h9415c.1
                                      have p9415_1 := h9415c.2.1
                                      have p9415_2 := h9415c.2.2.1
                                      have p9415_3 := h9415c.2.2.2
                                      linarith only [h9382, h9387, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p9415_1]
                                    · have p9415_0 := h9415c.1
                                      have p9415_1 := h9415c.2.1
                                      have p9415_2 := h9415c.2.2.1
                                      have p9415_3 := h9415c.2.2.2
                                      linarith only [h9384, hlam, p9415_0]
                                    · have p9415_0 := h9415c.1
                                      have p9415_1 := h9415c.2.1
                                      have p9415_2 := h9415c.2.2.1
                                      have p9415_3 := h9415c.2.2.2
                                      linarith only [hlam, p9415_0]
                                    · have p9415_0 := h9415c.1
                                      have p9415_1 := h9415c.2.1
                                      have p9415_2 := h9415c.2.2.1
                                      have p9415_3 := h9415c.2.2.2
                                      linarith only [h9384, h9387, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9415_1]
                                    · have p9415_0 := h9415c.1
                                      have p9415_1 := h9415c.2.1
                                      have p9415_2 := h9415c.2.2.1
                                      have p9415_3 := h9415c.2.2.2
                                      linarith only [h9180, hlam, p9415_0]
                                    · have p9415_0 := h9415c.1
                                      have p9415_1 := h9415c.2.1
                                      have p9415_2 := h9415c.2.2.1
                                      have p9415_3 := h9415c.2.2.2
                                      linarith only [h9382, hlam, p9415_0]
                                    · have p9415_0 := h9415c.1
                                      have p9415_1 := h9415c.2.1
                                      have p9415_2 := h9415c.2.2.1
                                      have p9415_3 := h9415c.2.2.2
                                      linarith only [h9385, hlam, p9415_0]
                                    · have p9415_0 := h9415c.1
                                      have p9415_1 := h9415c.2.1
                                      have p9415_2 := h9415c.2.2.1
                                      have p9415_3 := h9415c.2.2.2
                                      linarith only [h9387, hlam, p9415_0]
                                    · have p9415_0 := h9415c.1
                                      have p9415_1 := h9415c.2.1
                                      have p9415_2 := h9415c.2.2.1
                                      have p9415_3 := h9415c.2.2.2
                                      linarith only [hlam, p9415_0]
                          · linarith only [h9406, hlam, p9388_0]
                        · have p9388_0 := h9388c.1
                          have p9388_1 := h9388c.2.1
                          have p9388_2 := h9388c.2.2.1
                          have p9388_3 := h9388c.2.2.2
                          rcases p9388_3 (m.d 0 1) (by simp) with h9444 | h9444
                          · rcases p9388_3 (m.d 1 2) (by simp) with h9445 | h9445
                            · linarith only [h0, h9445, hlam]
                            · rcases p9388_3 (m.d 1 3) (by simp) with h9447 | h9447
                              · linarith only [h1, h9447, hlam]
                              · linarith only [h9382, h9447, hlam]
                          · linarith only [h9444, hlam, p9388_0]
                        · have p9388_0 := h9388c.1
                          have p9388_1 := h9388c.2.1
                          have p9388_2 := h9388c.2.2.1
                          have p9388_3 := h9388c.2.2.2
                          linarith only [h0, hlam, p9388_0]
                        · have p9388_0 := h9388c.1
                          have p9388_1 := h9388c.2.1
                          have p9388_2 := h9388c.2.2.1
                          have p9388_3 := h9388c.2.2.2
                          linarith only [hlam, p9388_0]
                        · have p9388_0 := h9388c.1
                          have p9388_1 := h9388c.2.1
                          have p9388_2 := h9388c.2.2.1
                          have p9388_3 := h9388c.2.2.2
                          linarith only [h9182, hlam, p9388_0]
                        · have p9388_0 := h9388c.1
                          have p9388_1 := h9388c.2.1
                          have p9388_2 := h9388c.2.2.1
                          have p9388_3 := h9388c.2.2.2
                          linarith only [h9184, hlam, p9388_0]
                        · have p9388_0 := h9388c.1
                          have p9388_1 := h9388c.2.1
                          have p9388_2 := h9388c.2.2.1
                          have p9388_3 := h9388c.2.2.2
                          linarith only [h9186, hlam, p9388_0]
                        · have p9388_0 := h9388c.1
                          have p9388_1 := h9388c.2.1
                          have p9388_2 := h9388c.2.2.1
                          have p9388_3 := h9388c.2.2.2
                          linarith only [h1, hlam, p9388_0]
                        · have p9388_0 := h9388c.1
                          have p9388_1 := h9388c.2.1
                          have p9388_2 := h9388c.2.2.1
                          have p9388_3 := h9388c.2.2.2
                          linarith only [h1, h7232, h9384, hc12, hc23, hlam, hphi, p9388_1]
                        · have p9388_0 := h9388c.1
                          have p9388_1 := h9388c.2.1
                          have p9388_2 := h9388c.2.2.1
                          have p9388_3 := h9388c.2.2.2
                          linarith only [hlam, p9388_0]
                        · have p9388_0 := h9388c.1
                          have p9388_1 := h9388c.2.1
                          have p9388_2 := h9388c.2.2.1
                          have p9388_3 := h9388c.2.2.2
                          linarith only [h9380, hlam, p9388_1]
                        · have p9388_0 := h9388c.1
                          have p9388_1 := h9388c.2.1
                          have p9388_2 := h9388c.2.2.1
                          have p9388_3 := h9388c.2.2.2
                          linarith only [h1, h7232, h9384, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p9388_1]
                        · have p9388_0 := h9388c.1
                          have p9388_1 := h9388c.2.1
                          have p9388_2 := h9388c.2.2.1
                          have p9388_3 := h9388c.2.2.2
                          linarith only [h2, hlam, p9388_0]
                        · have p9388_0 := h9388c.1
                          have p9388_1 := h9388c.2.1
                          have p9388_2 := h9388c.2.2.1
                          have p9388_3 := h9388c.2.2.2
                          linarith only [h2, h7232, h9384, hc12, hc23, hlam, hphi, p9388_1]
                        · have p9388_0 := h9388c.1
                          have p9388_1 := h9388c.2.1
                          have p9388_2 := h9388c.2.2.1
                          have p9388_3 := h9388c.2.2.2
                          linarith only [h2, h7232, h9382, h9384, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p9388_1]
                        · have p9388_0 := h9388c.1
                          have p9388_1 := h9388c.2.1
                          have p9388_2 := h9388c.2.2.1
                          have p9388_3 := h9388c.2.2.2
                          linarith only [hlam, p9388_0]
                        · have p9388_0 := h9388c.1
                          have p9388_1 := h9388c.2.1
                          have p9388_2 := h9388c.2.2.1
                          have p9388_3 := h9388c.2.2.2
                          linarith only [h2, h7232, h9186, h9384, hc12, hc23, hlam, hphi, p9388_1]
                        · have p9388_0 := h9388c.1
                          have p9388_1 := h9388c.2.1
                          have p9388_2 := h9388c.2.2.1
                          have p9388_3 := h9388c.2.2.2
                          linarith only [h3, hlam, p9388_0]
                        · have p9388_0 := h9388c.1
                          have p9388_1 := h9388c.2.1
                          have p9388_2 := h9388c.2.2.1
                          have p9388_3 := h9388c.2.2.2
                          linarith only [h3, h7232, h9180, h9384, hc12, hc23, hlam, hphi, p9388_1]
                        · have p9388_0 := h9388c.1
                          have p9388_1 := h9388c.2.1
                          have p9388_2 := h9388c.2.2.1
                          have p9388_3 := h9388c.2.2.2
                          linarith only [h9382, hlam, p9388_0]
                        · have p9388_0 := h9388c.1
                          have p9388_1 := h9388c.2.1
                          have p9388_2 := h9388c.2.2.1
                          have p9388_3 := h9388c.2.2.2
                          linarith only [h9383, hlam, p9388_0]
                        · have p9388_0 := h9388c.1
                          have p9388_1 := h9388c.2.1
                          have p9388_2 := h9388c.2.2.1
                          have p9388_3 := h9388c.2.2.2
                          linarith only [hlam, p9388_0]
                      · linarith only [h7232, h9181, h9387, hlam]
                    · linarith only [h0, h1, h6364, h7232, h9382, h9383, h9386, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h1, h7232, h9382, h9384, h9385, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9474 | h9474
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9475 | h9475
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9476 | h9476
                      · rcases h1bigk with h9477c | h9477c | h9477c | h9477c | h9477c | h9477c | h9477c | h9477c | h9477c | h9477c | h9477c | h9477c | h9477c | h9477c | h9477c | h9477c | h9477c | h9477c | h9477c | h9477c | h9477c | h9477c | h9477c | h9477c | h9477c
                        · have p9477_0 := h9477c.1
                          have p9477_1 := h9477c.2.1
                          have p9477_2 := h9477c.2.2.1
                          have p9477_3 := h9477c.2.2.2
                          linarith only [hlam, p9477_0]
                        · have p9477_0 := h9477c.1
                          have p9477_1 := h9477c.2.1
                          have p9477_2 := h9477c.2.2.1
                          have p9477_3 := h9477c.2.2.2
                          rcases p9477_3 (m.d 0 1) (by simp) with h9479 | h9479
                          · rcases p9477_3 (m.d 1 2) (by simp) with h9480 | h9480
                            · linarith only [h9480, hlam, p9477_0]
                            · rcases p9477_3 (m.d 1 3) (by simp) with h9482 | h9482
                              · linarith only [h1, h9482, hlam]
                              · linarith only [h9182, h9482, hlam]
                          · linarith only [h9479, hlam, p9477_0]
                        · have p9477_0 := h9477c.1
                          have p9477_1 := h9477c.2.1
                          have p9477_2 := h9477c.2.2.1
                          have p9477_3 := h9477c.2.2.2
                          rcases p9477_3 (m.d 0 1) (by simp) with h9486 | h9486
                          · rcases p9477_3 (m.d 1 2) (by simp) with h9487 | h9487
                            · linarith only [h0, h9487, hlam]
                            · rcases p9477_3 (m.d 1 3) (by simp) with h9489 | h9489
                              · linarith only [h9489, hlam, p9477_0]
                              · rcases p9477_3 (m.d 1 4) (by simp) with h9491 | h9491
                                · linarith only [h2, h9491, hlam]
                                · linarith only [h9380, h9491, hlam]
                          · linarith only [h9486, hlam, p9477_0]
                        · have p9477_0 := h9477c.1
                          have p9477_1 := h9477c.2.1
                          have p9477_2 := h9477c.2.2.1
                          have p9477_3 := h9477c.2.2.2
                          rcases p9477_3 (m.d 0 1) (by simp) with h9495 | h9495
                          · rcases p9477_3 (m.d 1 2) (by simp) with h9496 | h9496
                            · linarith only [h0, h9496, hlam]
                            · rcases p9477_3 (m.d 1 3) (by simp) with h9498 | h9498
                              · linarith only [h1, h9498, hlam]
                              · rcases p9477_3 (m.d 1 4) (by simp) with h9500 | h9500
                                · linarith only [h9500, hlam, p9477_0]
                                · rcases p9477_3 (m.d 1 5) (by simp) with h9502 | h9502
                                  · linarith only [h3, h9502, hlam]
                                  · rcases h3bigk with h9504c | h9504c | h9504c | h9504c | h9504c | h9504c | h9504c | h9504c | h9504c | h9504c | h9504c | h9504c | h9504c | h9504c | h9504c | h9504c | h9504c | h9504c | h9504c | h9504c | h9504c | h9504c | h9504c | h9504c | h9504c
                                    · have p9504_0 := h9504c.1
                                      have p9504_1 := h9504c.2.1
                                      have p9504_2 := h9504c.2.2.1
                                      have p9504_3 := h9504c.2.2.2
                                      linarith only [hlam, p9504_0]
                                    · have p9504_0 := h9504c.1
                                      have p9504_1 := h9504c.2.1
                                      have p9504_2 := h9504c.2.2.1
                                      have p9504_3 := h9504c.2.2.2
                                      linarith only [h4, h9384, hc13, hc34, hlam, hphi, p9504_1]
                                    · have p9504_0 := h9504c.1
                                      have p9504_1 := h9504c.2.1
                                      have p9504_2 := h9504c.2.2.1
                                      have p9504_3 := h9504c.2.2.2
                                      linarith only [h4, hlam, p9504_1]
                                    · have p9504_0 := h9504c.1
                                      have p9504_1 := h9504c.2.1
                                      have p9504_2 := h9504c.2.2.1
                                      have p9504_3 := h9504c.2.2.2
                                      linarith only [h7232, hlam, p9504_0]
                                    · have p9504_0 := h9504c.1
                                      have p9504_1 := h9504c.2.1
                                      have p9504_2 := h9504c.2.2.1
                                      have p9504_3 := h9504c.2.2.2
                                      linarith only [h4, h9384, h9476, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p9504_1]
                                    · have p9504_0 := h9504c.1
                                      have p9504_1 := h9504c.2.1
                                      have p9504_2 := h9504c.2.2.1
                                      have p9504_3 := h9504c.2.2.2
                                      linarith only [h1, hlam, p9504_0]
                                    · have p9504_0 := h9504c.1
                                      have p9504_1 := h9504c.2.1
                                      have p9504_2 := h9504c.2.2.1
                                      have p9504_3 := h9504c.2.2.2
                                      linarith only [hlam, p9504_0]
                                    · have p9504_0 := h9504c.1
                                      have p9504_1 := h9504c.2.1
                                      have p9504_2 := h9504c.2.2.1
                                      have p9504_3 := h9504c.2.2.2
                                      linarith only [h9182, hlam, p9504_1]
                                    · have p9504_0 := h9504c.1
                                      have p9504_1 := h9504c.2.1
                                      have p9504_2 := h9504c.2.2.1
                                      have p9504_3 := h9504c.2.2.2
                                      linarith only [h9380, hlam, p9504_0]
                                    · have p9504_0 := h9504c.1
                                      have p9504_1 := h9504c.2.1
                                      have p9504_2 := h9504c.2.2.1
                                      have p9504_3 := h9504c.2.2.2
                                      linarith only [h1, h9476, hc01, hc45, hlam, hphi, ht0b, ht5b, p9504_1]
                                    · have p9504_0 := h9504c.1
                                      have p9504_1 := h9504c.2.1
                                      have p9504_2 := h9504c.2.2.1
                                      have p9504_3 := h9504c.2.2.2
                                      linarith only [h9384, hc03, hc34, hlam, hphi, p9504_1]
                                    · have p9504_0 := h9504c.1
                                      have p9504_1 := h9504c.2.1
                                      have p9504_2 := h9504c.2.2.1
                                      have p9504_3 := h9504c.2.2.2
                                      linarith only [h9384, hc13, hc34, hlam, hphi, p9504_1]
                                    · have p9504_0 := h9504c.1
                                      have p9504_1 := h9504c.2.1
                                      have p9504_2 := h9504c.2.2.1
                                      have p9504_3 := h9504c.2.2.2
                                      linarith only [hlam, p9504_0]
                                    · have p9504_0 := h9504c.1
                                      have p9504_1 := h9504c.2.1
                                      have p9504_2 := h9504c.2.2.1
                                      have p9504_3 := h9504c.2.2.2
                                      linarith only [h9384, hlam, p9504_0]
                                    · have p9504_0 := h9504c.1
                                      have p9504_1 := h9504c.2.1
                                      have p9504_2 := h9504c.2.2.1
                                      have p9504_3 := h9504c.2.2.2
                                      linarith only [h9384, h9476, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p9504_1]
                                    · have p9504_0 := h9504c.1
                                      have p9504_1 := h9504c.2.1
                                      have p9504_2 := h9504c.2.2.1
                                      have p9504_3 := h9504c.2.2.2
                                      linarith only [hc03, hc34, hlam, hphi, p9504_1]
                                    · have p9504_0 := h9504c.1
                                      have p9504_1 := h9504c.2.1
                                      have p9504_2 := h9504c.2.2.1
                                      have p9504_3 := h9504c.2.2.2
                                      linarith only [h9382, h9476, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p9504_1]
                                    · have p9504_0 := h9504c.1
                                      have p9504_1 := h9504c.2.1
                                      have p9504_2 := h9504c.2.2.1
                                      have p9504_3 := h9504c.2.2.2
                                      linarith only [hc23, hc34, hlam, hphi, p9504_1]
                                    · have p9504_0 := h9504c.1
                                      have p9504_1 := h9504c.2.1
                                      have p9504_2 := h9504c.2.2.1
                                      have p9504_3 := h9504c.2.2.2
                                      linarith only [hlam, p9504_0]
                                    · have p9504_0 := h9504c.1
                                      have p9504_1 := h9504c.2.1
                                      have p9504_2 := h9504c.2.2.1
                                      have p9504_3 := h9504c.2.2.2
                                      rcases p9504_3 (m.d 0 3) (by simp) with h9524 | h9524
                                      · linarith only [h7232, h9524, hlam]
                                      · linarith only [h9180, h9524, hlam]
                                    · have p9504_0 := h9504c.1
                                      have p9504_1 := h9504c.2.1
                                      have p9504_2 := h9504c.2.2.1
                                      have p9504_3 := h9504c.2.2.2
                                      linarith only [h9180, hlam, p9504_0]
                                    · have p9504_0 := h9504c.1
                                      have p9504_1 := h9504c.2.1
                                      have p9504_2 := h9504c.2.2.1
                                      have p9504_3 := h9504c.2.2.2
                                      linarith only [h9382, hlam, p9504_0]
                                    · have p9504_0 := h9504c.1
                                      have p9504_1 := h9504c.2.1
                                      have p9504_2 := h9504c.2.2.1
                                      have p9504_3 := h9504c.2.2.2
                                      linarith only [h9474, hlam, p9504_0]
                                    · have p9504_0 := h9504c.1
                                      have p9504_1 := h9504c.2.1
                                      have p9504_2 := h9504c.2.2.1
                                      have p9504_3 := h9504c.2.2.2
                                      linarith only [h9476, hlam, p9504_0]
                                    · have p9504_0 := h9504c.1
                                      have p9504_1 := h9504c.2.1
                                      have p9504_2 := h9504c.2.2.1
                                      have p9504_3 := h9504c.2.2.2
                                      linarith only [hlam, p9504_0]
                          · linarith only [h9495, hlam, p9477_0]
                        · have p9477_0 := h9477c.1
                          have p9477_1 := h9477c.2.1
                          have p9477_2 := h9477c.2.2.1
                          have p9477_3 := h9477c.2.2.2
                          rcases p9477_3 (m.d 0 1) (by simp) with h9533 | h9533
                          · rcases p9477_3 (m.d 1 2) (by simp) with h9534 | h9534
                            · linarith only [h0, h9534, hlam]
                            · rcases p9477_3 (m.d 1 3) (by simp) with h9536 | h9536
                              · linarith only [h1, h9536, hlam]
                              · linarith only [h9382, h9536, hlam]
                          · linarith only [h9533, hlam, p9477_0]
                        · have p9477_0 := h9477c.1
                          have p9477_1 := h9477c.2.1
                          have p9477_2 := h9477c.2.2.1
                          have p9477_3 := h9477c.2.2.2
                          linarith only [h0, hlam, p9477_0]
                        · have p9477_0 := h9477c.1
                          have p9477_1 := h9477c.2.1
                          have p9477_2 := h9477c.2.2.1
                          have p9477_3 := h9477c.2.2.2
                          linarith only [hlam, p9477_0]
                        · have p9477_0 := h9477c.1
                          have p9477_1 := h9477c.2.1
                          have p9477_2 := h9477c.2.2.1
                          have p9477_3 := h9477c.2.2.2
                          linarith only [h9182, hlam, p9477_0]
                        · have p9477_0 := h9477c.1
                          have p9477_1 := h9477c.2.1
                          have p9477_2 := h9477c.2.2.1
                          have p9477_3 := h9477c.2.2.2
                          linarith only [h9184, hlam, p9477_0]
                        · have p9477_0 := h9477c.1
                          have p9477_1 := h9477c.2.1
                          have p9477_2 := h9477c.2.2.1
                          have p9477_3 := h9477c.2.2.2
                          linarith only [h9186, hlam, p9477_0]
                        · have p9477_0 := h9477c.1
                          have p9477_1 := h9477c.2.1
                          have p9477_2 := h9477c.2.2.1
                          have p9477_3 := h9477c.2.2.2
                          linarith only [h1, hlam, p9477_0]
                        · have p9477_0 := h9477c.1
                          have p9477_1 := h9477c.2.1
                          have p9477_2 := h9477c.2.2.1
                          have p9477_3 := h9477c.2.2.2
                          linarith only [h1, h7232, hc12, hc34, hlam, hphi, ht23, p9477_1]
                        · have p9477_0 := h9477c.1
                          have p9477_1 := h9477c.2.1
                          have p9477_2 := h9477c.2.2.1
                          have p9477_3 := h9477c.2.2.2
                          linarith only [hlam, p9477_0]
                        · have p9477_0 := h9477c.1
                          have p9477_1 := h9477c.2.1
                          have p9477_2 := h9477c.2.2.1
                          have p9477_3 := h9477c.2.2.2
                          linarith only [h9380, hlam, p9477_1]
                        · have p9477_0 := h9477c.1
                          have p9477_1 := h9477c.2.1
                          have p9477_2 := h9477c.2.2.1
                          have p9477_3 := h9477c.2.2.2
                          linarith only [h1, h7232, h9186, hc12, hc34, hlam, hphi, ht23, p9477_1]
                        · have p9477_0 := h9477c.1
                          have p9477_1 := h9477c.2.1
                          have p9477_2 := h9477c.2.2.1
                          have p9477_3 := h9477c.2.2.2
                          linarith only [h2, hlam, p9477_0]
                        · have p9477_0 := h9477c.1
                          have p9477_1 := h9477c.2.1
                          have p9477_2 := h9477c.2.2.1
                          have p9477_3 := h9477c.2.2.2
                          rcases p9477_3 (m.d 0 1) (by simp) with h9551 | h9551
                          · rcases p9477_3 (m.d 1 2) (by simp) with h9552 | h9552
                            · linarith only [h9184, h9552, hlam]
                            · rcases p9477_3 (m.d 1 3) (by simp) with h9554 | h9554
                              · linarith only [h9380, h9554, hlam]
                              · linarith only [h9182, h9554, hlam]
                          · linarith only [h0, h9551, hlam]
                        · have p9477_0 := h9477c.1
                          have p9477_1 := h9477c.2.1
                          have p9477_2 := h9477c.2.2.1
                          have p9477_3 := h9477c.2.2.2
                          linarith only [h2, h9382, h9476, hc01, hc45, hlam, hphi, ht0b, ht5b, p9477_1]
                        · have p9477_0 := h9477c.1
                          have p9477_1 := h9477c.2.1
                          have p9477_2 := h9477c.2.2.1
                          have p9477_3 := h9477c.2.2.2
                          linarith only [hlam, p9477_0]
                        · have p9477_0 := h9477c.1
                          have p9477_1 := h9477c.2.1
                          have p9477_2 := h9477c.2.2.1
                          have p9477_3 := h9477c.2.2.2
                          rcases p9477_3 (m.d 0 1) (by simp) with h9560 | h9560
                          · rcases p9477_3 (m.d 1 2) (by simp) with h9561 | h9561
                            · linarith only [h9184, h9561, hlam]
                            · rcases p9477_3 (m.d 1 3) (by simp) with h9563 | h9563
                              · linarith only [h9380, h9563, hlam]
                              · linarith only [h9382, h9563, hlam]
                          · linarith only [h3, h9560, hlam]
                        · have p9477_0 := h9477c.1
                          have p9477_1 := h9477c.2.1
                          have p9477_2 := h9477c.2.2.1
                          have p9477_3 := h9477c.2.2.2
                          linarith only [h3, hlam, p9477_0]
                        · have p9477_0 := h9477c.1
                          have p9477_1 := h9477c.2.1
                          have p9477_2 := h9477c.2.2.1
                          have p9477_3 := h9477c.2.2.2
                          linarith only [h3, h4, h9180, h9384, hc12, hc34, hlam, hphi, ht23, p9477_1]
                        · have p9477_0 := h9477c.1
                          have p9477_1 := h9477c.2.1
                          have p9477_2 := h9477c.2.2.1
                          have p9477_3 := h9477c.2.2.2
                          linarith only [h9382, hlam, p9477_0]
                        · have p9477_0 := h9477c.1
                          have p9477_1 := h9477c.2.1
                          have p9477_2 := h9477c.2.2.1
                          have p9477_3 := h9477c.2.2.2
                          linarith only [h9383, hlam, p9477_0]
                        · have p9477_0 := h9477c.1
                          have p9477_1 := h9477c.2.1
                          have p9477_2 := h9477c.2.2.1
                          have p9477_3 := h9477c.2.2.2
                          linarith only [hlam, p9477_0]
                      · linarith only [h0, h4, h9384, h9476, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h2, h6364, h9383, h9475, hlam]
                  · linarith only [h4, h9180, h9474, hlam]
              · linarith only [h9380, h9382, h9383, hlam]
            · linarith only [h7232, h9180, h9382, hc13, hc34, hlam, hphi]
  · linarith only [h7232, h9180, h9181, hlam]

end R2N4
