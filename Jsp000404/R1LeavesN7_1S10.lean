import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_1S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5520000 in
set_option maxHeartbeats 5520000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s10_x1_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h4553 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h5072 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h5073 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h5074 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 2 5 (by decide) (by decide) with h5878 | h5878
  · rcases m.htr 1 3 4 (by decide) (by decide) with h5879 | h5879
    · linarith only [h1, h5879, h7, hlam]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h5881 | h5881
      · linarith only [h4553, h5, h5073, h5074, h5881, h7, hc03, hc34, hlam, hphi]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h5883 | h5883
        · rcases m.htr 2 3 4 (by decide) (by decide) with h5884 | h5884
          · linarith only [h1, h5073, h5884, h7, hlam]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5886 | h5886
            · linarith only [h1, h4553, h5073, h5886, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h5888 | h5888
              · rcases m.htr 3 4 5 (by decide) (by decide) with h5889 | h5889
                · rcases h0bigk with h5890c | h5890c | h5890c | h5890c | h5890c | h5890c | h5890c | h5890c | h5890c | h5890c | h5890c | h5890c | h5890c | h5890c | h5890c | h5890c | h5890c | h5890c | h5890c | h5890c | h5890c | h5890c | h5890c | h5890c | h5890c
                  · have p5890_0 := h5890c.1
                    have p5890_1 := h5890c.2.1
                    have p5890_2 := h5890c.2.2.1
                    have p5890_3 := h5890c.2.2.2
                    linarith only [hlam, p5890_0]
                  · have p5890_0 := h5890c.1
                    have p5890_1 := h5890c.2.1
                    have p5890_2 := h5890c.2.2.1
                    have p5890_3 := h5890c.2.2.2
                    linarith only [h5, h5074, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5890_1]
                  · have p5890_0 := h5890c.1
                    have p5890_1 := h5890c.2.1
                    have p5890_2 := h5890c.2.2.1
                    have p5890_3 := h5890c.2.2.2
                    rcases p5890_3 (m.d 0 1) (by simp) with h5893 | h5893
                    · rcases p5890_3 (m.d 0 2) (by simp) with h5894 | h5894
                      · linarith only [h0, h5894, hlam]
                      · linarith only [h4, h5894, hlam]
                    · linarith only [h1, h5893, hlam]
                  · have p5890_0 := h5890c.1
                    have p5890_1 := h5890c.2.1
                    have p5890_2 := h5890c.2.2.1
                    have p5890_3 := h5890c.2.2.2
                    linarith only [h5, h5074, h5878, h5886, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5890_1]
                  · have p5890_0 := h5890c.1
                    have p5890_1 := h5890c.2.1
                    have p5890_2 := h5890c.2.2.1
                    have p5890_3 := h5890c.2.2.2
                    rcases p5890_3 (m.d 0 1) (by simp) with h5899 | h5899
                    · rcases p5890_3 (m.d 0 2) (by simp) with h5900 | h5900
                      · linarith only [h0, h5900, hlam]
                      · linarith only [h5900, h6, hlam]
                    · linarith only [h3, h5899, hlam]
                  · have p5890_0 := h5890c.1
                    have p5890_1 := h5890c.2.1
                    have p5890_2 := h5890c.2.2.1
                    have p5890_3 := h5890c.2.2.2
                    linarith only [h0, hlam, p5890_0]
                  · have p5890_0 := h5890c.1
                    have p5890_1 := h5890c.2.1
                    have p5890_2 := h5890c.2.2.1
                    have p5890_3 := h5890c.2.2.2
                    linarith only [hlam, p5890_0]
                  · have p5890_0 := h5890c.1
                    have p5890_1 := h5890c.2.1
                    have p5890_2 := h5890c.2.2.1
                    have p5890_3 := h5890c.2.2.2
                    rcases p5890_3 (m.d 0 1) (by simp) with h5906 | h5906
                    · rcases p5890_3 (m.d 0 2) (by simp) with h5907 | h5907
                      · rcases p5890_3 (m.d 0 3) (by simp) with h5908 | h5908
                        · linarith only [h4, h5908, hlam]
                        · rcases p5890_3 (m.d 0 4) (by simp) with h5910 | h5910
                          · linarith only [h5, h5910, hlam]
                          · linarith only [h5910, h7, hlam]
                      · linarith only [h4, h5907, hlam]
                    · linarith only [h1, h5906, hlam]
                  · have p5890_0 := h5890c.1
                    have p5890_1 := h5890c.2.1
                    have p5890_2 := h5890c.2.2.1
                    have p5890_3 := h5890c.2.2.2
                    linarith only [h5, h5074, h5878, h5886, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5890_1]
                  · have p5890_0 := h5890c.1
                    have p5890_1 := h5890c.2.1
                    have p5890_2 := h5890c.2.2.1
                    have p5890_3 := h5890c.2.2.2
                    rcases p5890_3 (m.d 0 1) (by simp) with h5916 | h5916
                    · rcases p5890_3 (m.d 0 2) (by simp) with h5917 | h5917
                      · rcases p5890_3 (m.d 0 3) (by simp) with h5918 | h5918
                        · linarith only [h4, h5918, hlam]
                        · rcases p5890_3 (m.d 0 4) (by simp) with h5920 | h5920
                          · linarith only [h5, h5920, hlam]
                          · linarith only [h5072, h5920, hlam]
                      · linarith only [h5917, h6, hlam]
                    · linarith only [h3, h5916, hlam]
                  · have p5890_0 := h5890c.1
                    have p5890_1 := h5890c.2.1
                    have p5890_2 := h5890c.2.2.1
                    have p5890_3 := h5890c.2.2.2
                    linarith only [h1, hlam, p5890_1]
                  · have p5890_0 := h5890c.1
                    have p5890_1 := h5890c.2.1
                    have p5890_2 := h5890c.2.2.1
                    have p5890_3 := h5890c.2.2.2
                    linarith only [h4, hlam, p5890_1]
                  · have p5890_0 := h5890c.1
                    have p5890_1 := h5890c.2.1
                    have p5890_2 := h5890c.2.2.1
                    have p5890_3 := h5890c.2.2.2
                    linarith only [hlam, p5890_0]
                  · have p5890_0 := h5890c.1
                    have p5890_1 := h5890c.2.1
                    have p5890_2 := h5890c.2.2.1
                    have p5890_3 := h5890c.2.2.2
                    linarith only [h7, hlam, p5890_1]
                  · have p5890_0 := h5890c.1
                    have p5890_1 := h5890c.2.1
                    have p5890_2 := h5890c.2.2.1
                    have p5890_3 := h5890c.2.2.2
                    linarith only [h4553, hlam, p5890_1]
                  · have p5890_0 := h5890c.1
                    have p5890_1 := h5890c.2.1
                    have p5890_2 := h5890c.2.2.1
                    have p5890_3 := h5890c.2.2.2
                    linarith only [h2, hlam, p5890_0]
                  · have p5890_0 := h5890c.1
                    have p5890_1 := h5890c.2.1
                    have p5890_2 := h5890c.2.2.1
                    have p5890_3 := h5890c.2.2.2
                    linarith only [h5, hlam, p5890_0]
                  · have p5890_0 := h5890c.1
                    have p5890_1 := h5890c.2.1
                    have p5890_2 := h5890c.2.2.1
                    have p5890_3 := h5890c.2.2.2
                    rcases p5890_3 (m.d 0 1) (by simp) with h5932 | h5932
                    · rcases p5890_3 (m.d 0 2) (by simp) with h5933 | h5933
                      · rcases p5890_3 (m.d 0 3) (by simp) with h5934 | h5934
                        · linarith only [h5934, h7, hlam]
                        · rcases p5890_3 (m.d 0 4) (by simp) with h5936 | h5936
                          · rcases p5890_3 (m.d 0 5) (by simp) with h5937 | h5937
                            · linarith only [h5072, h5937, hlam]
                            · linarith only [h4553, h5937, hlam]
                          · linarith only [h5936, h7, hlam]
                      · linarith only [h4, h5933, hlam]
                    · linarith only [h1, h5932, hlam]
                  · have p5890_0 := h5890c.1
                    have p5890_1 := h5890c.2.1
                    have p5890_2 := h5890c.2.2.1
                    have p5890_3 := h5890c.2.2.2
                    linarith only [hlam, p5890_0]
                  · have p5890_0 := h5890c.1
                    have p5890_1 := h5890c.2.1
                    have p5890_2 := h5890c.2.2.1
                    have p5890_3 := h5890c.2.2.2
                    rcases p5890_3 (m.d 0 1) (by simp) with h5944 | h5944
                    · rcases p5890_3 (m.d 0 2) (by simp) with h5945 | h5945
                      · rcases p5890_3 (m.d 0 3) (by simp) with h5946 | h5946
                        · linarith only [h5946, h7, hlam]
                        · rcases p5890_3 (m.d 0 4) (by simp) with h5948 | h5948
                          · rcases p5890_3 (m.d 0 5) (by simp) with h5949 | h5949
                            · linarith only [h5072, h5949, hlam]
                            · rcases h2bigk with h5951c | h5951c | h5951c | h5951c | h5951c | h5951c | h5951c | h5951c | h5951c | h5951c | h5951c | h5951c | h5951c | h5951c | h5951c | h5951c | h5951c | h5951c | h5951c | h5951c | h5951c | h5951c | h5951c | h5951c | h5951c
                              · have p5951_0 := h5951c.1
                                have p5951_1 := h5951c.2.1
                                have p5951_2 := h5951c.2.2.1
                                have p5951_3 := h5951c.2.2.2
                                linarith only [hlam, p5951_0]
                              · have p5951_0 := h5951c.1
                                have p5951_1 := h5951c.2.1
                                have p5951_2 := h5951c.2.2.1
                                have p5951_3 := h5951c.2.2.2
                                rcases p5951_3 (m.d 0 2) (by simp) with h5953 | h5953
                                · rcases p5951_3 (m.d 1 2) (by simp) with h5954 | h5954
                                  · linarith only [h0, h5954, hlam]
                                  · rcases p5951_3 (m.d 2 3) (by simp) with h5956 | h5956
                                    · linarith only [h4, h5956, hlam]
                                    · rcases p5951_3 (m.d 2 4) (by simp) with h5958 | h5958
                                      · linarith only [h5, h5958, hlam]
                                      · linarith only [h5074, h5958, hlam]
                                · linarith only [h0, h5953, hlam]
                              · have p5951_0 := h5951c.1
                                have p5951_1 := h5951c.2.1
                                have p5951_2 := h5951c.2.2.1
                                have p5951_3 := h5951c.2.2.2
                                linarith only [h5, h5074, h5878, h5886, hlam, p5951_2]
                              · have p5951_0 := h5951c.1
                                have p5951_1 := h5951c.2.1
                                have p5951_2 := h5951c.2.2.1
                                have p5951_3 := h5951c.2.2.2
                                linarith only [h5074, h5878, h5886, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5951_1]
                              · have p5951_0 := h5951c.1
                                have p5951_1 := h5951c.2.1
                                have p5951_2 := h5951c.2.2.1
                                have p5951_3 := h5951c.2.2.2
                                linarith only [h5, h5074, h5878, hlam, p5951_2]
                              · have p5951_0 := h5951c.1
                                have p5951_1 := h5951c.2.1
                                have p5951_2 := h5951c.2.2.1
                                have p5951_3 := h5951c.2.2.2
                                linarith only [h0, hlam, p5951_0]
                              · have p5951_0 := h5951c.1
                                have p5951_1 := h5951c.2.1
                                have p5951_2 := h5951c.2.2.1
                                have p5951_3 := h5951c.2.2.2
                                linarith only [hlam, p5951_0]
                              · have p5951_0 := h5951c.1
                                have p5951_1 := h5951c.2.1
                                have p5951_2 := h5951c.2.2.1
                                have p5951_3 := h5951c.2.2.2
                                linarith only [h5, h5074, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5951_1]
                              · have p5951_0 := h5951c.1
                                have p5951_1 := h5951c.2.1
                                have p5951_2 := h5951c.2.2.1
                                have p5951_3 := h5951c.2.2.2
                                linarith only [h5074, hlam, p5951_0]
                              · have p5951_0 := h5951c.1
                                have p5951_1 := h5951c.2.1
                                have p5951_2 := h5951c.2.2.1
                                have p5951_3 := h5951c.2.2.2
                                linarith only [h0, h5, h5074, h5886, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5951_1]
                              · have p5951_0 := h5951c.1
                                have p5951_1 := h5951c.2.1
                                have p5951_2 := h5951c.2.2.1
                                have p5951_3 := h5951c.2.2.2
                                linarith only [h4, hlam, p5951_0]
                              · have p5951_0 := h5951c.1
                                have p5951_1 := h5951c.2.1
                                have p5951_2 := h5951c.2.2.1
                                have p5951_3 := h5951c.2.2.2
                                linarith only [h5073, hlam, p5951_0]
                              · have p5951_0 := h5951c.1
                                have p5951_1 := h5951c.2.1
                                have p5951_2 := h5951c.2.2.1
                                have p5951_3 := h5951c.2.2.2
                                linarith only [hlam, p5951_0]
                              · have p5951_0 := h5951c.1
                                have p5951_1 := h5951c.2.1
                                have p5951_2 := h5951c.2.2.1
                                have p5951_3 := h5951c.2.2.2
                                linarith only [h5884, hlam, p5951_0]
                              · have p5951_0 := h5951c.1
                                have p5951_1 := h5951c.2.1
                                have p5951_2 := h5951c.2.2.1
                                have p5951_3 := h5951c.2.2.2
                                linarith only [h5886, hlam, p5951_0]
                              · have p5951_0 := h5951c.1
                                have p5951_1 := h5951c.2.1
                                have p5951_2 := h5951c.2.2.1
                                have p5951_3 := h5951c.2.2.2
                                linarith only [h5, hlam, p5951_0]
                              · have p5951_0 := h5951c.1
                                have p5951_1 := h5951c.2.1
                                have p5951_2 := h5951c.2.2.1
                                have p5951_3 := h5951c.2.2.2
                                linarith only [h0, h5, h5073, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5951_1]
                              · have p5951_0 := h5951c.1
                                have p5951_1 := h5951c.2.1
                                have p5951_2 := h5951c.2.2.1
                                have p5951_3 := h5951c.2.2.2
                                rcases p5951_3 (m.d 0 2) (by simp) with h5977 | h5977
                                · rcases p5951_3 (m.d 1 2) (by simp) with h5978 | h5978
                                  · linarith only [h5074, h5978, hlam]
                                  · linarith only [h5073, h5978, hlam]
                                · linarith only [h4, h5977, hlam]
                              · have p5951_0 := h5951c.1
                                have p5951_1 := h5951c.2.1
                                have p5951_2 := h5951c.2.2.1
                                have p5951_3 := h5951c.2.2.2
                                linarith only [hlam, p5951_0]
                              · have p5951_0 := h5951c.1
                                have p5951_1 := h5951c.2.1
                                have p5951_2 := h5951c.2.2.1
                                have p5951_3 := h5951c.2.2.2
                                rcases p5951_3 (m.d 0 2) (by simp) with h5983 | h5983
                                · rcases p5951_3 (m.d 1 2) (by simp) with h5984 | h5984
                                  · linarith only [h5074, h5984, hlam]
                                  · linarith only [h5878, h5984, hlam]
                                · linarith only [h5983, h6, hlam]
                              · have p5951_0 := h5951c.1
                                have p5951_1 := h5951c.2.1
                                have p5951_2 := h5951c.2.2.1
                                have p5951_3 := h5951c.2.2.2
                                linarith only [h6, hlam, p5951_0]
                              · have p5951_0 := h5951c.1
                                have p5951_1 := h5951c.2.1
                                have p5951_2 := h5951c.2.2.1
                                have p5951_3 := h5951c.2.2.2
                                linarith only [h5878, hlam, p5951_0]
                              · have p5951_0 := h5951c.1
                                have p5951_1 := h5951c.2.1
                                have p5951_2 := h5951c.2.2.1
                                have p5951_3 := h5951c.2.2.2
                                linarith only [h0, h5878, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5951_1]
                              · have p5951_0 := h5951c.1
                                have p5951_1 := h5951c.2.1
                                have p5951_2 := h5951c.2.2.1
                                have p5951_3 := h5951c.2.2.2
                                linarith only [h5888, hlam, p5951_0]
                              · have p5951_0 := h5951c.1
                                have p5951_1 := h5951c.2.1
                                have p5951_2 := h5951c.2.2.1
                                have p5951_3 := h5951c.2.2.2
                                linarith only [hlam, p5951_0]
                          · linarith only [h5072, h5948, hlam]
                      · linarith only [h5945, h6, hlam]
                    · linarith only [h3, h5944, hlam]
                  · have p5890_0 := h5890c.1
                    have p5890_1 := h5890c.2.1
                    have p5890_2 := h5890c.2.2.1
                    have p5890_3 := h5890c.2.2.2
                    linarith only [h3, hlam, p5890_0]
                  · have p5890_0 := h5890c.1
                    have p5890_1 := h5890c.2.1
                    have p5890_2 := h5890c.2.2.1
                    have p5890_3 := h5890c.2.2.2
                    linarith only [h6, hlam, p5890_1]
                  · have p5890_0 := h5890c.1
                    have p5890_1 := h5890c.2.1
                    have p5890_2 := h5890c.2.2.1
                    have p5890_3 := h5890c.2.2.2
                    rcases p5890_3 (m.d 0 1) (by simp) with h5998 | h5998
                    · rcases p5890_3 (m.d 0 2) (by simp) with h5999 | h5999
                      · rcases p5890_3 (m.d 0 3) (by simp) with h6000 | h6000
                        · linarith only [h4553, h6000, hlam]
                        · rcases p5890_3 (m.d 0 4) (by simp) with h6002 | h6002
                          · rcases p5890_3 (m.d 0 5) (by simp) with h6003 | h6003
                            · rcases h2bigk with h6004c | h6004c | h6004c | h6004c | h6004c | h6004c | h6004c | h6004c | h6004c | h6004c | h6004c | h6004c | h6004c | h6004c | h6004c | h6004c | h6004c | h6004c | h6004c | h6004c | h6004c | h6004c | h6004c | h6004c | h6004c
                              · have p6004_0 := h6004c.1
                                have p6004_1 := h6004c.2.1
                                have p6004_2 := h6004c.2.2.1
                                have p6004_3 := h6004c.2.2.2
                                linarith only [hlam, p6004_0]
                              · have p6004_0 := h6004c.1
                                have p6004_1 := h6004c.2.1
                                have p6004_2 := h6004c.2.2.1
                                have p6004_3 := h6004c.2.2.2
                                rcases p6004_3 (m.d 0 2) (by simp) with h6006 | h6006
                                · rcases p6004_3 (m.d 1 2) (by simp) with h6007 | h6007
                                  · linarith only [h0, h6007, hlam]
                                  · rcases p6004_3 (m.d 2 3) (by simp) with h6009 | h6009
                                    · linarith only [h4, h6009, hlam]
                                    · rcases p6004_3 (m.d 2 4) (by simp) with h6011 | h6011
                                      · linarith only [h5, h6011, hlam]
                                      · linarith only [h5074, h6011, hlam]
                                · linarith only [h0, h6006, hlam]
                              · have p6004_0 := h6004c.1
                                have p6004_1 := h6004c.2.1
                                have p6004_2 := h6004c.2.2.1
                                have p6004_3 := h6004c.2.2.2
                                linarith only [h5, h5073, h5074, hlam, p6004_2]
                              · have p6004_0 := h6004c.1
                                have p6004_1 := h6004c.2.1
                                have p6004_2 := h6004c.2.2.1
                                have p6004_3 := h6004c.2.2.2
                                linarith only [h0, h5074, h5878, hc01, hc25, hlam, hphi, ht0b, ht5b, p6004_1]
                              · have p6004_0 := h6004c.1
                                have p6004_1 := h6004c.2.1
                                have p6004_2 := h6004c.2.2.1
                                have p6004_3 := h6004c.2.2.2
                                linarith only [h5, h5074, h5878, hlam, p6004_2]
                              · have p6004_0 := h6004c.1
                                have p6004_1 := h6004c.2.1
                                have p6004_2 := h6004c.2.2.1
                                have p6004_3 := h6004c.2.2.2
                                linarith only [h0, hlam, p6004_0]
                              · have p6004_0 := h6004c.1
                                have p6004_1 := h6004c.2.1
                                have p6004_2 := h6004c.2.2.1
                                have p6004_3 := h6004c.2.2.2
                                linarith only [hlam, p6004_0]
                              · have p6004_0 := h6004c.1
                                have p6004_1 := h6004c.2.1
                                have p6004_2 := h6004c.2.2.1
                                have p6004_3 := h6004c.2.2.2
                                linarith only [h0, h5, h5074, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6004_1]
                              · have p6004_0 := h6004c.1
                                have p6004_1 := h6004c.2.1
                                have p6004_2 := h6004c.2.2.1
                                have p6004_3 := h6004c.2.2.2
                                linarith only [h5074, hlam, p6004_0]
                              · have p6004_0 := h6004c.1
                                have p6004_1 := h6004c.2.1
                                have p6004_2 := h6004c.2.2.1
                                have p6004_3 := h6004c.2.2.2
                                linarith only [h0, h5, h5074, hc01, hc25, hlam, hphi, ht0b, ht5b, p6004_1]
                              · have p6004_0 := h6004c.1
                                have p6004_1 := h6004c.2.1
                                have p6004_2 := h6004c.2.2.1
                                have p6004_3 := h6004c.2.2.2
                                linarith only [h4, hlam, p6004_0]
                              · have p6004_0 := h6004c.1
                                have p6004_1 := h6004c.2.1
                                have p6004_2 := h6004c.2.2.1
                                have p6004_3 := h6004c.2.2.2
                                linarith only [h5073, hlam, p6004_0]
                              · have p6004_0 := h6004c.1
                                have p6004_1 := h6004c.2.1
                                have p6004_2 := h6004c.2.2.1
                                have p6004_3 := h6004c.2.2.2
                                linarith only [hlam, p6004_0]
                              · have p6004_0 := h6004c.1
                                have p6004_1 := h6004c.2.1
                                have p6004_2 := h6004c.2.2.1
                                have p6004_3 := h6004c.2.2.2
                                linarith only [h5884, hlam, p6004_0]
                              · have p6004_0 := h6004c.1
                                have p6004_1 := h6004c.2.1
                                have p6004_2 := h6004c.2.2.1
                                have p6004_3 := h6004c.2.2.2
                                linarith only [h5886, hlam, p6004_0]
                              · have p6004_0 := h6004c.1
                                have p6004_1 := h6004c.2.1
                                have p6004_2 := h6004c.2.2.1
                                have p6004_3 := h6004c.2.2.2
                                linarith only [h5, hlam, p6004_0]
                              · have p6004_0 := h6004c.1
                                have p6004_1 := h6004c.2.1
                                have p6004_2 := h6004c.2.2.1
                                have p6004_3 := h6004c.2.2.2
                                linarith only [h5, h5073, h7, hc23, hc34, hlam, hphi, p6004_1]
                              · have p6004_0 := h6004c.1
                                have p6004_1 := h6004c.2.1
                                have p6004_2 := h6004c.2.2.1
                                have p6004_3 := h6004c.2.2.2
                                rcases p6004_3 (m.d 0 2) (by simp) with h6030 | h6030
                                · rcases p6004_3 (m.d 1 2) (by simp) with h6031 | h6031
                                  · linarith only [h5074, h6031, hlam]
                                  · linarith only [h5073, h6031, hlam]
                                · linarith only [h4, h6030, hlam]
                              · have p6004_0 := h6004c.1
                                have p6004_1 := h6004c.2.1
                                have p6004_2 := h6004c.2.2.1
                                have p6004_3 := h6004c.2.2.2
                                linarith only [hlam, p6004_0]
                              · have p6004_0 := h6004c.1
                                have p6004_1 := h6004c.2.1
                                have p6004_2 := h6004c.2.2.1
                                have p6004_3 := h6004c.2.2.2
                                rcases p6004_3 (m.d 0 2) (by simp) with h6036 | h6036
                                · rcases p6004_3 (m.d 1 2) (by simp) with h6037 | h6037
                                  · linarith only [h5074, h6037, hlam]
                                  · linarith only [h5878, h6037, hlam]
                                · linarith only [h6, h6036, hlam]
                              · have p6004_0 := h6004c.1
                                have p6004_1 := h6004c.2.1
                                have p6004_2 := h6004c.2.2.1
                                have p6004_3 := h6004c.2.2.2
                                linarith only [h6, hlam, p6004_0]
                              · have p6004_0 := h6004c.1
                                have p6004_1 := h6004c.2.1
                                have p6004_2 := h6004c.2.2.1
                                have p6004_3 := h6004c.2.2.2
                                linarith only [h5878, hlam, p6004_0]
                              · have p6004_0 := h6004c.1
                                have p6004_1 := h6004c.2.1
                                have p6004_2 := h6004c.2.2.1
                                have p6004_3 := h6004c.2.2.2
                                linarith only [h0, h5878, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6004_1]
                              · have p6004_0 := h6004c.1
                                have p6004_1 := h6004c.2.1
                                have p6004_2 := h6004c.2.2.1
                                have p6004_3 := h6004c.2.2.2
                                linarith only [h5888, hlam, p6004_0]
                              · have p6004_0 := h6004c.1
                                have p6004_1 := h6004c.2.1
                                have p6004_2 := h6004c.2.2.1
                                have p6004_3 := h6004c.2.2.2
                                linarith only [hlam, p6004_0]
                            · linarith only [h4553, h6003, hlam]
                          · linarith only [h6002, h7, hlam]
                      · linarith only [h4, h5999, hlam]
                    · linarith only [h1, h5998, hlam]
                  · have p5890_0 := h5890c.1
                    have p5890_1 := h5890c.2.1
                    have p5890_2 := h5890c.2.2.1
                    have p5890_3 := h5890c.2.2.2
                    linarith only [h5072, hlam, p5890_1]
                  · have p5890_0 := h5890c.1
                    have p5890_1 := h5890c.2.1
                    have p5890_2 := h5890c.2.2.1
                    have p5890_3 := h5890c.2.2.2
                    linarith only [hlam, p5890_0]
                · linarith only [h5072, h5889, h7, hlam]
              · linarith only [h5072, h5074, h5878, h5886, h5888, h7, hc23, hc34, hlam, hphi]
        · linarith only [h5072, h5073, h5074, h5883, h7, hc23, hc34, hlam, hphi]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h6055 | h6055
    · linarith only [h1, h5, h5073, h5074, h6055, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h6057 | h6057
      · linarith only [h1, h4553, h6057, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h6059 | h6059
        · rcases m.htr 2 3 4 (by decide) (by decide) with h6060 | h6060
          · linarith only [h1, h5073, h6060, h7, hlam]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h6062 | h6062
            · linarith only [h4553, h5072, h5073, h5878, h6, h6062, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h6064 | h6064
              · rcases m.htr 3 4 5 (by decide) (by decide) with h6065 | h6065
                · rcases h0bigk with h6066c | h6066c | h6066c | h6066c | h6066c | h6066c | h6066c | h6066c | h6066c | h6066c | h6066c | h6066c | h6066c | h6066c | h6066c | h6066c | h6066c | h6066c | h6066c | h6066c | h6066c | h6066c | h6066c | h6066c | h6066c
                  · have p6066_0 := h6066c.1
                    have p6066_1 := h6066c.2.1
                    have p6066_2 := h6066c.2.2.1
                    have p6066_3 := h6066c.2.2.2
                    linarith only [hlam, p6066_0]
                  · have p6066_0 := h6066c.1
                    have p6066_1 := h6066c.2.1
                    have p6066_2 := h6066c.2.2.1
                    have p6066_3 := h6066c.2.2.2
                    linarith only [h5, h5878, h6064, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6066_1]
                  · have p6066_0 := h6066c.1
                    have p6066_1 := h6066c.2.1
                    have p6066_2 := h6066c.2.2.1
                    have p6066_3 := h6066c.2.2.2
                    rcases p6066_3 (m.d 0 1) (by simp) with h6069 | h6069
                    · rcases p6066_3 (m.d 0 2) (by simp) with h6070 | h6070
                      · linarith only [h0, h6070, hlam]
                      · linarith only [h4, h6070, hlam]
                    · linarith only [h1, h6069, hlam]
                  · have p6066_0 := h6066c.1
                    have p6066_1 := h6066c.2.1
                    have p6066_2 := h6066c.2.2.1
                    have p6066_3 := h6066c.2.2.2
                    linarith only [h5, h5073, h5878, h6064, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6066_1]
                  · have p6066_0 := h6066c.1
                    have p6066_1 := h6066c.2.1
                    have p6066_2 := h6066c.2.2.1
                    have p6066_3 := h6066c.2.2.2
                    linarith only [h5073, h5878, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6066_1]
                  · have p6066_0 := h6066c.1
                    have p6066_1 := h6066c.2.1
                    have p6066_2 := h6066c.2.2.1
                    have p6066_3 := h6066c.2.2.2
                    linarith only [h0, hlam, p6066_0]
                  · have p6066_0 := h6066c.1
                    have p6066_1 := h6066c.2.1
                    have p6066_2 := h6066c.2.2.1
                    have p6066_3 := h6066c.2.2.2
                    linarith only [hlam, p6066_0]
                  · have p6066_0 := h6066c.1
                    have p6066_1 := h6066c.2.1
                    have p6066_2 := h6066c.2.2.1
                    have p6066_3 := h6066c.2.2.2
                    rcases p6066_3 (m.d 0 1) (by simp) with h6078 | h6078
                    · rcases p6066_3 (m.d 0 2) (by simp) with h6079 | h6079
                      · rcases p6066_3 (m.d 0 3) (by simp) with h6080 | h6080
                        · linarith only [h4, h6080, hlam]
                        · rcases p6066_3 (m.d 0 4) (by simp) with h6082 | h6082
                          · linarith only [h5, h6082, hlam]
                          · linarith only [h6082, h7, hlam]
                      · linarith only [h4, h6079, hlam]
                    · linarith only [h1, h6078, hlam]
                  · have p6066_0 := h6066c.1
                    have p6066_1 := h6066c.2.1
                    have p6066_2 := h6066c.2.2.1
                    have p6066_3 := h6066c.2.2.2
                    linarith only [h5, h5073, h5878, h6064, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6066_1]
                  · have p6066_0 := h6066c.1
                    have p6066_1 := h6066c.2.1
                    have p6066_2 := h6066c.2.2.1
                    have p6066_3 := h6066c.2.2.2
                    linarith only [h0, h5073, h5878, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6066_1]
                  · have p6066_0 := h6066c.1
                    have p6066_1 := h6066c.2.1
                    have p6066_2 := h6066c.2.2.1
                    have p6066_3 := h6066c.2.2.2
                    linarith only [h1, hlam, p6066_1]
                  · have p6066_0 := h6066c.1
                    have p6066_1 := h6066c.2.1
                    have p6066_2 := h6066c.2.2.1
                    have p6066_3 := h6066c.2.2.2
                    linarith only [h4, hlam, p6066_1]
                  · have p6066_0 := h6066c.1
                    have p6066_1 := h6066c.2.1
                    have p6066_2 := h6066c.2.2.1
                    have p6066_3 := h6066c.2.2.2
                    linarith only [hlam, p6066_0]
                  · have p6066_0 := h6066c.1
                    have p6066_1 := h6066c.2.1
                    have p6066_2 := h6066c.2.2.1
                    have p6066_3 := h6066c.2.2.2
                    linarith only [h7, hlam, p6066_1]
                  · have p6066_0 := h6066c.1
                    have p6066_1 := h6066c.2.1
                    have p6066_2 := h6066c.2.2.1
                    have p6066_3 := h6066c.2.2.2
                    linarith only [h4553, hlam, p6066_1]
                  · have p6066_0 := h6066c.1
                    have p6066_1 := h6066c.2.1
                    have p6066_2 := h6066c.2.2.1
                    have p6066_3 := h6066c.2.2.2
                    linarith only [h2, hlam, p6066_0]
                  · have p6066_0 := h6066c.1
                    have p6066_1 := h6066c.2.1
                    have p6066_2 := h6066c.2.2.1
                    have p6066_3 := h6066c.2.2.2
                    linarith only [h5, hlam, p6066_0]
                  · have p6066_0 := h6066c.1
                    have p6066_1 := h6066c.2.1
                    have p6066_2 := h6066c.2.2.1
                    have p6066_3 := h6066c.2.2.2
                    rcases p6066_3 (m.d 0 1) (by simp) with h6096 | h6096
                    · rcases p6066_3 (m.d 0 2) (by simp) with h6097 | h6097
                      · rcases p6066_3 (m.d 0 3) (by simp) with h6098 | h6098
                        · linarith only [h6098, h7, hlam]
                        · rcases p6066_3 (m.d 0 4) (by simp) with h6100 | h6100
                          · rcases p6066_3 (m.d 0 5) (by simp) with h6101 | h6101
                            · linarith only [h5072, h6101, hlam]
                            · linarith only [h4553, h6101, hlam]
                          · linarith only [h6100, h7, hlam]
                      · linarith only [h4, h6097, hlam]
                    · linarith only [h1, h6096, hlam]
                  · have p6066_0 := h6066c.1
                    have p6066_1 := h6066c.2.1
                    have p6066_2 := h6066c.2.2.1
                    have p6066_3 := h6066c.2.2.2
                    linarith only [hlam, p6066_0]
                  · have p6066_0 := h6066c.1
                    have p6066_1 := h6066c.2.1
                    have p6066_2 := h6066c.2.2.1
                    have p6066_3 := h6066c.2.2.2
                    linarith only [h5073, h5878, h6, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6066_1]
                  · have p6066_0 := h6066c.1
                    have p6066_1 := h6066c.2.1
                    have p6066_2 := h6066c.2.2.1
                    have p6066_3 := h6066c.2.2.2
                    linarith only [h3, hlam, p6066_0]
                  · have p6066_0 := h6066c.1
                    have p6066_1 := h6066c.2.1
                    have p6066_2 := h6066c.2.2.1
                    have p6066_3 := h6066c.2.2.2
                    linarith only [h6, hlam, p6066_1]
                  · have p6066_0 := h6066c.1
                    have p6066_1 := h6066c.2.1
                    have p6066_2 := h6066c.2.2.1
                    have p6066_3 := h6066c.2.2.2
                    rcases p6066_3 (m.d 0 1) (by simp) with h6111 | h6111
                    · rcases p6066_3 (m.d 0 2) (by simp) with h6112 | h6112
                      · rcases p6066_3 (m.d 0 3) (by simp) with h6113 | h6113
                        · linarith only [h4553, h6113, hlam]
                        · rcases p6066_3 (m.d 0 4) (by simp) with h6115 | h6115
                          · rcases p6066_3 (m.d 0 5) (by simp) with h6116 | h6116
                            · rcases h2bigk with h6117c | h6117c | h6117c | h6117c | h6117c | h6117c | h6117c | h6117c | h6117c | h6117c | h6117c | h6117c | h6117c | h6117c | h6117c | h6117c | h6117c | h6117c | h6117c | h6117c | h6117c | h6117c | h6117c | h6117c | h6117c
                              · have p6117_0 := h6117c.1
                                have p6117_1 := h6117c.2.1
                                have p6117_2 := h6117c.2.2.1
                                have p6117_3 := h6117c.2.2.2
                                linarith only [hlam, p6117_0]
                              · have p6117_0 := h6117c.1
                                have p6117_1 := h6117c.2.1
                                have p6117_2 := h6117c.2.2.1
                                have p6117_3 := h6117c.2.2.2
                                rcases p6117_3 (m.d 0 2) (by simp) with h6119 | h6119
                                · rcases p6117_3 (m.d 1 2) (by simp) with h6120 | h6120
                                  · linarith only [h0, h6120, hlam]
                                  · rcases p6117_3 (m.d 2 3) (by simp) with h6122 | h6122
                                    · linarith only [h4, h6122, hlam]
                                    · rcases p6117_3 (m.d 2 4) (by simp) with h6124 | h6124
                                      · linarith only [h5, h6124, hlam]
                                      · linarith only [h5074, h6124, hlam]
                                · linarith only [h0, h6119, hlam]
                              · have p6117_0 := h6117c.1
                                have p6117_1 := h6117c.2.1
                                have p6117_2 := h6117c.2.2.1
                                have p6117_3 := h6117c.2.2.2
                                linarith only [h5, h5073, h5878, h6064, hlam, p6117_2]
                              · have p6117_0 := h6117c.1
                                have p6117_1 := h6117c.2.1
                                have p6117_2 := h6117c.2.2.1
                                have p6117_3 := h6117c.2.2.2
                                linarith only [h5073, h5878, h6064, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6117_1]
                              · have p6117_0 := h6117c.1
                                have p6117_1 := h6117c.2.1
                                have p6117_2 := h6117c.2.2.1
                                have p6117_3 := h6117c.2.2.2
                                linarith only [h0, h5073, h5878, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6117_1]
                              · have p6117_0 := h6117c.1
                                have p6117_1 := h6117c.2.1
                                have p6117_2 := h6117c.2.2.1
                                have p6117_3 := h6117c.2.2.2
                                linarith only [h0, hlam, p6117_0]
                              · have p6117_0 := h6117c.1
                                have p6117_1 := h6117c.2.1
                                have p6117_2 := h6117c.2.2.1
                                have p6117_3 := h6117c.2.2.2
                                linarith only [hlam, p6117_0]
                              · have p6117_0 := h6117c.1
                                have p6117_1 := h6117c.2.1
                                have p6117_2 := h6117c.2.2.1
                                have p6117_3 := h6117c.2.2.2
                                linarith only [h0, h5, h5878, h6064, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6117_1]
                              · have p6117_0 := h6117c.1
                                have p6117_1 := h6117c.2.1
                                have p6117_2 := h6117c.2.2.1
                                have p6117_3 := h6117c.2.2.2
                                linarith only [h5074, hlam, p6117_0]
                              · have p6117_0 := h6117c.1
                                have p6117_1 := h6117c.2.1
                                have p6117_2 := h6117c.2.2.1
                                have p6117_3 := h6117c.2.2.2
                                linarith only [h5878, hlam, p6117_0]
                              · have p6117_0 := h6117c.1
                                have p6117_1 := h6117c.2.1
                                have p6117_2 := h6117c.2.2.1
                                have p6117_3 := h6117c.2.2.2
                                linarith only [h4, hlam, p6117_0]
                              · have p6117_0 := h6117c.1
                                have p6117_1 := h6117c.2.1
                                have p6117_2 := h6117c.2.2.1
                                have p6117_3 := h6117c.2.2.2
                                linarith only [h5073, hlam, p6117_0]
                              · have p6117_0 := h6117c.1
                                have p6117_1 := h6117c.2.1
                                have p6117_2 := h6117c.2.2.1
                                have p6117_3 := h6117c.2.2.2
                                linarith only [hlam, p6117_0]
                              · have p6117_0 := h6117c.1
                                have p6117_1 := h6117c.2.1
                                have p6117_2 := h6117c.2.2.1
                                have p6117_3 := h6117c.2.2.2
                                linarith only [h6060, hlam, p6117_0]
                              · have p6117_0 := h6117c.1
                                have p6117_1 := h6117c.2.1
                                have p6117_2 := h6117c.2.2.1
                                have p6117_3 := h6117c.2.2.2
                                linarith only [h6062, hlam, p6117_0]
                              · have p6117_0 := h6117c.1
                                have p6117_1 := h6117c.2.1
                                have p6117_2 := h6117c.2.2.1
                                have p6117_3 := h6117c.2.2.2
                                linarith only [h5, hlam, p6117_0]
                              · have p6117_0 := h6117c.1
                                have p6117_1 := h6117c.2.1
                                have p6117_2 := h6117c.2.2.1
                                have p6117_3 := h6117c.2.2.2
                                linarith only [h0, h5, h5073, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6117_1]
                              · have p6117_0 := h6117c.1
                                have p6117_1 := h6117c.2.1
                                have p6117_2 := h6117c.2.2.1
                                have p6117_3 := h6117c.2.2.2
                                rcases p6117_3 (m.d 0 2) (by simp) with h6143 | h6143
                                · rcases p6117_3 (m.d 1 2) (by simp) with h6144 | h6144
                                  · linarith only [h5074, h6144, hlam]
                                  · linarith only [h5073, h6144, hlam]
                                · linarith only [h4, h6143, hlam]
                              · have p6117_0 := h6117c.1
                                have p6117_1 := h6117c.2.1
                                have p6117_2 := h6117c.2.2.1
                                have p6117_3 := h6117c.2.2.2
                                linarith only [hlam, p6117_0]
                              · have p6117_0 := h6117c.1
                                have p6117_1 := h6117c.2.1
                                have p6117_2 := h6117c.2.2.1
                                have p6117_3 := h6117c.2.2.2
                                linarith only [h0, h5, h5073, h5878, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6117_1]
                              · have p6117_0 := h6117c.1
                                have p6117_1 := h6117c.2.1
                                have p6117_2 := h6117c.2.2.1
                                have p6117_3 := h6117c.2.2.2
                                linarith only [h6, hlam, p6117_0]
                              · have p6117_0 := h6117c.1
                                have p6117_1 := h6117c.2.1
                                have p6117_2 := h6117c.2.2.1
                                have p6117_3 := h6117c.2.2.2
                                linarith only [h0, h5073, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6117_1]
                              · have p6117_0 := h6117c.1
                                have p6117_1 := h6117c.2.1
                                have p6117_2 := h6117c.2.2.1
                                have p6117_3 := h6117c.2.2.2
                                rcases p6117_3 (m.d 0 2) (by simp) with h6152 | h6152
                                · rcases p6117_3 (m.d 1 2) (by simp) with h6153 | h6153
                                  · linarith only [h5878, h6153, hlam]
                                  · linarith only [h5073, h6153, hlam]
                                · linarith only [h4, h6152, hlam]
                              · have p6117_0 := h6117c.1
                                have p6117_1 := h6117c.2.1
                                have p6117_2 := h6117c.2.2.1
                                have p6117_3 := h6117c.2.2.2
                                linarith only [h6064, hlam, p6117_0]
                              · have p6117_0 := h6117c.1
                                have p6117_1 := h6117c.2.1
                                have p6117_2 := h6117c.2.2.1
                                have p6117_3 := h6117c.2.2.2
                                linarith only [hlam, p6117_0]
                            · linarith only [h4553, h6116, hlam]
                          · linarith only [h6115, h7, hlam]
                      · linarith only [h4, h6112, hlam]
                    · linarith only [h1, h6111, hlam]
                  · have p6066_0 := h6066c.1
                    have p6066_1 := h6066c.2.1
                    have p6066_2 := h6066c.2.2.1
                    have p6066_3 := h6066c.2.2.2
                    linarith only [h5072, hlam, p6066_1]
                  · have p6066_0 := h6066c.1
                    have p6066_1 := h6066c.2.1
                    have p6066_2 := h6066c.2.2.1
                    have p6066_3 := h6066c.2.2.2
                    linarith only [hlam, p6066_0]
                · linarith only [h5072, h6065, h7, hlam]
              · linarith only [h5074, h6059, h6064, hlam]
        · linarith only [h5072, h5073, h5074, h6059, h7, hc23, hc34, hlam, hphi]

set_option maxHeartbeats 5520000 in
set_option maxHeartbeats 5520000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s10_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h4553 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h5072 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h5073 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 2 4 (by decide) (by decide) with h5074 | h5074
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s10_x1_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h4553 h5072 h5073 h5074
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s10_x1_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h4553 h5072 h5073 h5074

set_option maxHeartbeats 5520000 in
set_option maxHeartbeats 5520000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s10_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h4553 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h5072 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h5073 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 2 4 (by decide) (by decide) with h6168 | h6168
  · rcases m.htr 1 2 5 (by decide) (by decide) with h6169 | h6169
    · rcases m.htr 1 3 4 (by decide) (by decide) with h6170 | h6170
      · linarith only [h4, h5073, h6170, h7, hlam]
      · linarith only [h5073, h6168, h6170, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h6173 | h6173
      · linarith only [h4, h5073, h6168, h6173, h7, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
      · linarith only [h5073, h6168, h6173, hlam]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h6176 | h6176
    · rcases m.htr 1 3 4 (by decide) (by decide) with h6177 | h6177
      · linarith only [h1, h6177, h7, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h6179 | h6179
        · linarith only [h4, h4553, h5073, h6179, hlam]
        · linarith only [h5073, h6176, h6179, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h6182 | h6182
      · linarith only [h1, h4, h5073, h6182, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h6184 | h6184
        · linarith only [h1, h4, h4553, h5073, h6184, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h6186 | h6186
          · rcases m.htr 2 3 4 (by decide) (by decide) with h6187 | h6187
            · linarith only [h4, h6187, h7, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h6189 | h6189
              · linarith only [h4, h4553, h6189, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h6191 | h6191
                · rcases m.htr 3 4 5 (by decide) (by decide) with h6192 | h6192
                  · rcases h0bigk with h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c
                    · have p6193_0 := h6193c.1
                      have p6193_1 := h6193c.2.1
                      have p6193_2 := h6193c.2.2.1
                      have p6193_3 := h6193c.2.2.2
                      linarith only [hlam, p6193_0]
                    · have p6193_0 := h6193c.1
                      have p6193_1 := h6193c.2.1
                      have p6193_2 := h6193c.2.2.1
                      have p6193_3 := h6193c.2.2.2
                      linarith only [h4, h5073, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6193_1]
                    · have p6193_0 := h6193c.1
                      have p6193_1 := h6193c.2.1
                      have p6193_2 := h6193c.2.2.1
                      have p6193_3 := h6193c.2.2.2
                      rcases p6193_3 (m.d 0 1) (by simp) with h6196 | h6196
                      · rcases p6193_3 (m.d 0 2) (by simp) with h6197 | h6197
                        · linarith only [h0, h6197, hlam]
                        · linarith only [h4, h6197, hlam]
                      · linarith only [h1, h6196, hlam]
                    · have p6193_0 := h6193c.1
                      have p6193_1 := h6193c.2.1
                      have p6193_2 := h6193c.2.2.1
                      have p6193_3 := h6193c.2.2.2
                      rcases p6193_3 (m.d 0 1) (by simp) with h6201 | h6201
                      · rcases p6193_3 (m.d 0 2) (by simp) with h6202 | h6202
                        · linarith only [h0, h6202, hlam]
                        · linarith only [h5, h6202, hlam]
                      · linarith only [h2, h6201, hlam]
                    · have p6193_0 := h6193c.1
                      have p6193_1 := h6193c.2.1
                      have p6193_2 := h6193c.2.2.1
                      have p6193_3 := h6193c.2.2.2
                      rcases p6193_3 (m.d 0 1) (by simp) with h6206 | h6206
                      · rcases p6193_3 (m.d 0 2) (by simp) with h6207 | h6207
                        · linarith only [h0, h6207, hlam]
                        · linarith only [h6, h6207, hlam]
                      · linarith only [h3, h6206, hlam]
                    · have p6193_0 := h6193c.1
                      have p6193_1 := h6193c.2.1
                      have p6193_2 := h6193c.2.2.1
                      have p6193_3 := h6193c.2.2.2
                      linarith only [h0, hlam, p6193_0]
                    · have p6193_0 := h6193c.1
                      have p6193_1 := h6193c.2.1
                      have p6193_2 := h6193c.2.2.1
                      have p6193_3 := h6193c.2.2.2
                      linarith only [hlam, p6193_0]
                    · have p6193_0 := h6193c.1
                      have p6193_1 := h6193c.2.1
                      have p6193_2 := h6193c.2.2.1
                      have p6193_3 := h6193c.2.2.2
                      rcases p6193_3 (m.d 0 1) (by simp) with h6213 | h6213
                      · rcases p6193_3 (m.d 0 2) (by simp) with h6214 | h6214
                        · rcases p6193_3 (m.d 0 3) (by simp) with h6215 | h6215
                          · linarith only [h4, h6215, hlam]
                          · rcases p6193_3 (m.d 0 4) (by simp) with h6217 | h6217
                            · linarith only [h5, h6217, hlam]
                            · linarith only [h6217, h7, hlam]
                        · linarith only [h4, h6214, hlam]
                      · linarith only [h1, h6213, hlam]
                    · have p6193_0 := h6193c.1
                      have p6193_1 := h6193c.2.1
                      have p6193_2 := h6193c.2.2.1
                      have p6193_3 := h6193c.2.2.2
                      rcases p6193_3 (m.d 0 1) (by simp) with h6222 | h6222
                      · rcases p6193_3 (m.d 0 2) (by simp) with h6223 | h6223
                        · rcases p6193_3 (m.d 0 3) (by simp) with h6224 | h6224
                          · linarith only [h4, h6224, hlam]
                          · rcases p6193_3 (m.d 0 4) (by simp) with h6226 | h6226
                            · linarith only [h5, h6226, hlam]
                            · rcases p6193_3 (m.d 0 5) (by simp) with h6228 | h6228
                              · linarith only [h6, h6228, hlam]
                              · rcases h2bigk with h6230c | h6230c | h6230c | h6230c | h6230c | h6230c | h6230c | h6230c | h6230c | h6230c | h6230c | h6230c | h6230c | h6230c | h6230c | h6230c | h6230c | h6230c | h6230c | h6230c | h6230c | h6230c | h6230c | h6230c | h6230c
                                · have p6230_0 := h6230c.1
                                  have p6230_1 := h6230c.2.1
                                  have p6230_2 := h6230c.2.2.1
                                  have p6230_3 := h6230c.2.2.2
                                  linarith only [hlam, p6230_0]
                                · have p6230_0 := h6230c.1
                                  have p6230_1 := h6230c.2.1
                                  have p6230_2 := h6230c.2.2.1
                                  have p6230_3 := h6230c.2.2.2
                                  linarith only [h4, h4553, h5072, h5073, hlam, p6193_1, p6230_2]
                                · have p6230_0 := h6230c.1
                                  have p6230_1 := h6230c.2.1
                                  have p6230_2 := h6230c.2.2.1
                                  have p6230_3 := h6230c.2.2.2
                                  rcases p6230_3 (m.d 0 2) (by simp) with h6233 | h6233
                                  · rcases p6230_3 (m.d 1 2) (by simp) with h6234 | h6234
                                    · linarith only [h0, h6234, hlam]
                                    · rcases p6230_3 (m.d 2 3) (by simp) with h6236 | h6236
                                      · linarith only [h6236, hlam, p6230_0]
                                      · rcases p6230_3 (m.d 2 4) (by simp) with h6238 | h6238
                                        · linarith only [h5, h6238, hlam]
                                        · linarith only [h6187, h6238, hlam]
                                  · linarith only [h6233, hlam, p6230_0]
                                · have p6230_0 := h6230c.1
                                  have p6230_1 := h6230c.2.1
                                  have p6230_2 := h6230c.2.2.1
                                  have p6230_3 := h6230c.2.2.2
                                  rcases p6230_3 (m.d 0 2) (by simp) with h6242 | h6242
                                  · rcases p6230_3 (m.d 1 2) (by simp) with h6243 | h6243
                                    · linarith only [h0, h6243, hlam]
                                    · rcases p6230_3 (m.d 2 3) (by simp) with h6245 | h6245
                                      · linarith only [h4, h6245, hlam]
                                      · rcases p6230_3 (m.d 2 4) (by simp) with h6247 | h6247
                                        · linarith only [h6247, hlam, p6230_0]
                                        · rcases p6230_3 (m.d 2 5) (by simp) with h6249 | h6249
                                          · linarith only [h6, h6249, hlam]
                                          · rcases h3bigk with h6251c | h6251c | h6251c | h6251c | h6251c | h6251c | h6251c | h6251c | h6251c | h6251c | h6251c | h6251c | h6251c | h6251c | h6251c | h6251c | h6251c | h6251c | h6251c | h6251c | h6251c | h6251c | h6251c | h6251c | h6251c
                                            · have p6251_0 := h6251c.1
                                              have p6251_1 := h6251c.2.1
                                              have p6251_2 := h6251c.2.2.1
                                              have p6251_3 := h6251c.2.2.2
                                              linarith only [hlam, p6251_0]
                                            · have p6251_0 := h6251c.1
                                              have p6251_1 := h6251c.2.1
                                              have p6251_2 := h6251c.2.2.1
                                              have p6251_3 := h6251c.2.2.2
                                              linarith only [h4553, h5072, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p6193_1, p6251_1]
                                            · have p6251_0 := h6251c.1
                                              have p6251_1 := h6251c.2.1
                                              have p6251_2 := h6251c.2.2.1
                                              have p6251_3 := h6251c.2.2.2
                                              linarith only [h0, h4553, h5072, h5073, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6193_1, p6251_1]
                                            · have p6251_0 := h6251c.1
                                              have p6251_1 := h6251c.2.1
                                              have p6251_2 := h6251c.2.2.1
                                              have p6251_3 := h6251c.2.2.2
                                              linarith only [h7, hlam, p6251_0]
                                            · have p6251_0 := h6251c.1
                                              have p6251_1 := h6251c.2.1
                                              have p6251_2 := h6251c.2.2.1
                                              have p6251_3 := h6251c.2.2.2
                                              linarith only [h4553, hlam, p6251_0]
                                            · have p6251_0 := h6251c.1
                                              have p6251_1 := h6251c.2.1
                                              have p6251_2 := h6251c.2.2.1
                                              have p6251_3 := h6251c.2.2.2
                                              linarith only [h1, hlam, p6251_0]
                                            · have p6251_0 := h6251c.1
                                              have p6251_1 := h6251c.2.1
                                              have p6251_2 := h6251c.2.2.1
                                              have p6251_3 := h6251c.2.2.2
                                              linarith only [hlam, p6251_0]
                                            · have p6251_0 := h6251c.1
                                              have p6251_1 := h6251c.2.1
                                              have p6251_2 := h6251c.2.2.1
                                              have p6251_3 := h6251c.2.2.2
                                              linarith only [h5073, hlam, p6251_1]
                                            · have p6251_0 := h6251c.1
                                              have p6251_1 := h6251c.2.1
                                              have p6251_2 := h6251c.2.2.1
                                              have p6251_3 := h6251c.2.2.2
                                              linarith only [h6182, hlam, p6251_0]
                                            · have p6251_0 := h6251c.1
                                              have p6251_1 := h6251c.2.1
                                              have p6251_2 := h6251c.2.2.1
                                              have p6251_3 := h6251c.2.2.2
                                              linarith only [h6184, hlam, p6251_0]
                                            · have p6251_0 := h6251c.1
                                              have p6251_1 := h6251c.2.1
                                              have p6251_2 := h6251c.2.2.1
                                              have p6251_3 := h6251c.2.2.2
                                              linarith only [h4, hlam, p6251_0]
                                            · have p6251_0 := h6251c.1
                                              have p6251_1 := h6251c.2.1
                                              have p6251_2 := h6251c.2.2.1
                                              have p6251_3 := h6251c.2.2.2
                                              linarith only [h0, h4, h4553, h5072, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p6193_1, p6251_1]
                                            · have p6251_0 := h6251c.1
                                              have p6251_1 := h6251c.2.1
                                              have p6251_2 := h6251c.2.2.1
                                              have p6251_3 := h6251c.2.2.2
                                              linarith only [hlam, p6251_0]
                                            · have p6251_0 := h6251c.1
                                              have p6251_1 := h6251c.2.1
                                              have p6251_2 := h6251c.2.2.1
                                              have p6251_3 := h6251c.2.2.2
                                              linarith only [h6187, hlam, p6251_0]
                                            · have p6251_0 := h6251c.1
                                              have p6251_1 := h6251c.2.1
                                              have p6251_2 := h6251c.2.2.1
                                              have p6251_3 := h6251c.2.2.2
                                              linarith only [h6189, hlam, p6251_0]
                                            · have p6251_0 := h6251c.1
                                              have p6251_1 := h6251c.2.1
                                              have p6251_2 := h6251c.2.2.1
                                              have p6251_3 := h6251c.2.2.2
                                              linarith only [h4, h5073, hc12, hc34, hlam, hphi, ht23, p6251_1]
                                            · have p6251_0 := h6251c.1
                                              have p6251_1 := h6251c.2.1
                                              have p6251_2 := h6251c.2.2.1
                                              have p6251_3 := h6251c.2.2.2
                                              rcases p6251_3 (m.d 0 3) (by simp) with h6268 | h6268
                                              · linarith only [h6268, h7, hlam]
                                              · linarith only [h1, h6268, hlam]
                                            · have p6251_0 := h6251c.1
                                              have p6251_1 := h6251c.2.1
                                              have p6251_2 := h6251c.2.2.1
                                              have p6251_3 := h6251c.2.2.2
                                              linarith only [h5073, hc12, hc34, hlam, hphi, ht23, p6251_1]
                                            · have p6251_0 := h6251c.1
                                              have p6251_1 := h6251c.2.1
                                              have p6251_2 := h6251c.2.2.1
                                              have p6251_3 := h6251c.2.2.2
                                              linarith only [hlam, p6251_0]
                                            · have p6251_0 := h6251c.1
                                              have p6251_1 := h6251c.2.1
                                              have p6251_2 := h6251c.2.2.1
                                              have p6251_3 := h6251c.2.2.2
                                              linarith only [h4, h4553, h5073, hc12, hc34, hlam, hphi, ht23, p6251_1]
                                            · have p6251_0 := h6251c.1
                                              have p6251_1 := h6251c.2.1
                                              have p6251_2 := h6251c.2.2.1
                                              have p6251_3 := h6251c.2.2.2
                                              linarith only [h4, h5073, hc12, hc35, hlam, hphi, ht23, p6251_1]
                                            · have p6251_0 := h6251c.1
                                              have p6251_1 := h6251c.2.1
                                              have p6251_2 := h6251c.2.2.1
                                              have p6251_3 := h6251c.2.2.2
                                              rcases p6251_3 (m.d 0 3) (by simp) with h6275 | h6275
                                              · linarith only [h4553, h6275, hlam]
                                              · linarith only [h1, h6275, hlam]
                                            · have p6251_0 := h6251c.1
                                              have p6251_1 := h6251c.2.1
                                              have p6251_2 := h6251c.2.2.1
                                              have p6251_3 := h6251c.2.2.2
                                              linarith only [h5073, h6192, hc12, hc34, hlam, hphi, ht23, p6251_1]
                                            · have p6251_0 := h6251c.1
                                              have p6251_1 := h6251c.2.1
                                              have p6251_2 := h6251c.2.2.1
                                              have p6251_3 := h6251c.2.2.2
                                              linarith only [h6192, hlam, p6251_0]
                                            · have p6251_0 := h6251c.1
                                              have p6251_1 := h6251c.2.1
                                              have p6251_2 := h6251c.2.2.1
                                              have p6251_3 := h6251c.2.2.2
                                              linarith only [hlam, p6251_0]
                                  · linarith only [h6242, hlam, p6230_0]
                                · have p6230_0 := h6230c.1
                                  have p6230_1 := h6230c.2.1
                                  have p6230_2 := h6230c.2.2.1
                                  have p6230_3 := h6230c.2.2.2
                                  rcases p6230_3 (m.d 0 2) (by simp) with h6282 | h6282
                                  · rcases p6230_3 (m.d 1 2) (by simp) with h6283 | h6283
                                    · linarith only [h0, h6283, hlam]
                                    · rcases p6230_3 (m.d 2 3) (by simp) with h6285 | h6285
                                      · linarith only [h4, h6285, hlam]
                                      · rcases p6230_3 (m.d 2 4) (by simp) with h6287 | h6287
                                        · linarith only [h5, h6287, hlam]
                                        · linarith only [h6191, h6287, hlam]
                                  · linarith only [h6282, hlam, p6230_0]
                                · have p6230_0 := h6230c.1
                                  have p6230_1 := h6230c.2.1
                                  have p6230_2 := h6230c.2.2.1
                                  have p6230_3 := h6230c.2.2.2
                                  linarith only [h0, hlam, p6230_0]
                                · have p6230_0 := h6230c.1
                                  have p6230_1 := h6230c.2.1
                                  have p6230_2 := h6230c.2.2.1
                                  have p6230_3 := h6230c.2.2.2
                                  linarith only [hlam, p6230_0]
                                · have p6230_0 := h6230c.1
                                  have p6230_1 := h6230c.2.1
                                  have p6230_2 := h6230c.2.2.1
                                  have p6230_3 := h6230c.2.2.2
                                  linarith only [h5073, hlam, p6230_0]
                                · have p6230_0 := h6230c.1
                                  have p6230_1 := h6230c.2.1
                                  have p6230_2 := h6230c.2.2.1
                                  have p6230_3 := h6230c.2.2.2
                                  linarith only [h6168, hlam, p6230_0]
                                · have p6230_0 := h6230c.1
                                  have p6230_1 := h6230c.2.1
                                  have p6230_2 := h6230c.2.2.1
                                  have p6230_3 := h6230c.2.2.2
                                  linarith only [h6176, hlam, p6230_0]
                                · have p6230_0 := h6230c.1
                                  have p6230_1 := h6230c.2.1
                                  have p6230_2 := h6230c.2.2.1
                                  have p6230_3 := h6230c.2.2.2
                                  linarith only [h4, hlam, p6230_0]
                                · have p6230_0 := h6230c.1
                                  have p6230_1 := h6230c.2.1
                                  have p6230_2 := h6230c.2.2.1
                                  have p6230_3 := h6230c.2.2.2
                                  linarith only [h0, h5, h6189, h6191, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6193_1, p6230_1]
                                · have p6230_0 := h6230c.1
                                  have p6230_1 := h6230c.2.1
                                  have p6230_2 := h6230c.2.2.1
                                  have p6230_3 := h6230c.2.2.2
                                  linarith only [hlam, p6230_0]
                                · have p6230_0 := h6230c.1
                                  have p6230_1 := h6230c.2.1
                                  have p6230_2 := h6230c.2.2.1
                                  have p6230_3 := h6230c.2.2.2
                                  linarith only [h6187, hlam, p6230_0]
                                · have p6230_0 := h6230c.1
                                  have p6230_1 := h6230c.2.1
                                  have p6230_2 := h6230c.2.2.1
                                  have p6230_3 := h6230c.2.2.2
                                  linarith only [h6189, hlam, p6230_0]
                                · have p6230_0 := h6230c.1
                                  have p6230_1 := h6230c.2.1
                                  have p6230_2 := h6230c.2.2.1
                                  have p6230_3 := h6230c.2.2.2
                                  linarith only [h5, hlam, p6230_0]
                                · have p6230_0 := h6230c.1
                                  have p6230_1 := h6230c.2.1
                                  have p6230_2 := h6230c.2.2.1
                                  have p6230_3 := h6230c.2.2.2
                                  linarith only [h0, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6193_1, p6230_1]
                                · have p6230_0 := h6230c.1
                                  have p6230_1 := h6230c.2.1
                                  have p6230_2 := h6230c.2.2.1
                                  have p6230_3 := h6230c.2.2.2
                                  linarith only [h0, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6193_1, p6230_1]
                                · have p6230_0 := h6230c.1
                                  have p6230_1 := h6230c.2.1
                                  have p6230_2 := h6230c.2.2.1
                                  have p6230_3 := h6230c.2.2.2
                                  linarith only [hlam, p6230_0]
                                · have p6230_0 := h6230c.1
                                  have p6230_1 := h6230c.2.1
                                  have p6230_2 := h6230c.2.2.1
                                  have p6230_3 := h6230c.2.2.2
                                  linarith only [h0, h5, hc01, hc25, hlam, hphi, ht0b, ht5b, p6193_1, p6230_1]
                                · have p6230_0 := h6230c.1
                                  have p6230_1 := h6230c.2.1
                                  have p6230_2 := h6230c.2.2.1
                                  have p6230_3 := h6230c.2.2.2
                                  linarith only [h6, hlam, p6230_0]
                                · have p6230_0 := h6230c.1
                                  have p6230_1 := h6230c.2.1
                                  have p6230_2 := h6230c.2.2.1
                                  have p6230_3 := h6230c.2.2.2
                                  linarith only [h0, h5072, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6193_1, p6230_1]
                                · have p6230_0 := h6230c.1
                                  have p6230_1 := h6230c.2.1
                                  have p6230_2 := h6230c.2.2.1
                                  have p6230_3 := h6230c.2.2.2
                                  linarith only [h0, h5072, h5073, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6193_1, p6230_1]
                                · have p6230_0 := h6230c.1
                                  have p6230_1 := h6230c.2.1
                                  have p6230_2 := h6230c.2.2.1
                                  have p6230_3 := h6230c.2.2.2
                                  linarith only [h6191, hlam, p6230_0]
                                · have p6230_0 := h6230c.1
                                  have p6230_1 := h6230c.2.1
                                  have p6230_2 := h6230c.2.2.1
                                  have p6230_3 := h6230c.2.2.2
                                  linarith only [hlam, p6230_0]
                        · linarith only [h5, h6223, hlam]
                      · linarith only [h2, h6222, hlam]
                    · have p6193_0 := h6193c.1
                      have p6193_1 := h6193c.2.1
                      have p6193_2 := h6193c.2.2.1
                      have p6193_3 := h6193c.2.2.2
                      rcases p6193_3 (m.d 0 1) (by simp) with h6313 | h6313
                      · rcases p6193_3 (m.d 0 2) (by simp) with h6314 | h6314
                        · rcases p6193_3 (m.d 0 3) (by simp) with h6315 | h6315
                          · linarith only [h4, h6315, hlam]
                          · rcases p6193_3 (m.d 0 4) (by simp) with h6317 | h6317
                            · linarith only [h5, h6317, hlam]
                            · linarith only [h5072, h6317, hlam]
                        · linarith only [h6, h6314, hlam]
                      · linarith only [h3, h6313, hlam]
                    · have p6193_0 := h6193c.1
                      have p6193_1 := h6193c.2.1
                      have p6193_2 := h6193c.2.2.1
                      have p6193_3 := h6193c.2.2.2
                      linarith only [h1, hlam, p6193_1]
                    · have p6193_0 := h6193c.1
                      have p6193_1 := h6193c.2.1
                      have p6193_2 := h6193c.2.2.1
                      have p6193_3 := h6193c.2.2.2
                      linarith only [h4, hlam, p6193_1]
                    · have p6193_0 := h6193c.1
                      have p6193_1 := h6193c.2.1
                      have p6193_2 := h6193c.2.2.1
                      have p6193_3 := h6193c.2.2.2
                      linarith only [hlam, p6193_0]
                    · have p6193_0 := h6193c.1
                      have p6193_1 := h6193c.2.1
                      have p6193_2 := h6193c.2.2.1
                      have p6193_3 := h6193c.2.2.2
                      linarith only [h7, hlam, p6193_1]
                    · have p6193_0 := h6193c.1
                      have p6193_1 := h6193c.2.1
                      have p6193_2 := h6193c.2.2.1
                      have p6193_3 := h6193c.2.2.2
                      linarith only [h4553, hlam, p6193_1]
                    · have p6193_0 := h6193c.1
                      have p6193_1 := h6193c.2.1
                      have p6193_2 := h6193c.2.2.1
                      have p6193_3 := h6193c.2.2.2
                      linarith only [h2, hlam, p6193_0]
                    · have p6193_0 := h6193c.1
                      have p6193_1 := h6193c.2.1
                      have p6193_2 := h6193c.2.2.1
                      have p6193_3 := h6193c.2.2.2
                      linarith only [h5, hlam, p6193_0]
                    · have p6193_0 := h6193c.1
                      have p6193_1 := h6193c.2.1
                      have p6193_2 := h6193c.2.2.1
                      have p6193_3 := h6193c.2.2.2
                      linarith only [h4, h5073, h7, hc12, hc34, hlam, hphi, ht23, p6193_1]
                    · have p6193_0 := h6193c.1
                      have p6193_1 := h6193c.2.1
                      have p6193_2 := h6193c.2.2.1
                      have p6193_3 := h6193c.2.2.2
                      linarith only [hlam, p6193_0]
                    · have p6193_0 := h6193c.1
                      have p6193_1 := h6193c.2.1
                      have p6193_2 := h6193c.2.2.1
                      have p6193_3 := h6193c.2.2.2
                      linarith only [h4, h4553, h5073, h7, hc12, hc34, hlam, hphi, ht23, p6193_1]
                    · have p6193_0 := h6193c.1
                      have p6193_1 := h6193c.2.1
                      have p6193_2 := h6193c.2.2.1
                      have p6193_3 := h6193c.2.2.2
                      linarith only [h3, hlam, p6193_0]
                    · have p6193_0 := h6193c.1
                      have p6193_1 := h6193c.2.1
                      have p6193_2 := h6193c.2.2.1
                      have p6193_3 := h6193c.2.2.2
                      linarith only [h6, hlam, p6193_1]
                    · have p6193_0 := h6193c.1
                      have p6193_1 := h6193c.2.1
                      have p6193_2 := h6193c.2.2.1
                      have p6193_3 := h6193c.2.2.2
                      linarith only [h4, h4553, h5073, h6192, hc12, hc34, hlam, hphi, ht23, p6193_1]
                    · have p6193_0 := h6193c.1
                      have p6193_1 := h6193c.2.1
                      have p6193_2 := h6193c.2.2.1
                      have p6193_3 := h6193c.2.2.2
                      linarith only [h5072, hlam, p6193_1]
                    · have p6193_0 := h6193c.1
                      have p6193_1 := h6193c.2.1
                      have p6193_2 := h6193c.2.2.1
                      have p6193_3 := h6193c.2.2.2
                      linarith only [hlam, p6193_0]
                  · linarith only [h2, h6186, h6192, h7, hlam]
                · linarith only [h2, h6168, h6186, h6191, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h6339 | h6339
            · linarith only [h4, h6339, h7, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h6341 | h6341
              · linarith only [h4, h4553, h6341, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h6343 | h6343
                · rcases m.htr 3 4 5 (by decide) (by decide) with h6344 | h6344
                  · rcases h0bigk with h6345c | h6345c | h6345c | h6345c | h6345c | h6345c | h6345c | h6345c | h6345c | h6345c | h6345c | h6345c | h6345c | h6345c | h6345c | h6345c | h6345c | h6345c | h6345c | h6345c | h6345c | h6345c | h6345c | h6345c | h6345c
                    · have p6345_0 := h6345c.1
                      have p6345_1 := h6345c.2.1
                      have p6345_2 := h6345c.2.2.1
                      have p6345_3 := h6345c.2.2.2
                      linarith only [hlam, p6345_0]
                    · have p6345_0 := h6345c.1
                      have p6345_1 := h6345c.2.1
                      have p6345_2 := h6345c.2.2.1
                      have p6345_3 := h6345c.2.2.2
                      linarith only [h5, h5073, h6182, h6186, h6343, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6345_1]
                    · have p6345_0 := h6345c.1
                      have p6345_1 := h6345c.2.1
                      have p6345_2 := h6345c.2.2.1
                      have p6345_3 := h6345c.2.2.2
                      rcases p6345_3 (m.d 0 1) (by simp) with h6348 | h6348
                      · rcases p6345_3 (m.d 0 2) (by simp) with h6349 | h6349
                        · linarith only [h0, h6349, hlam]
                        · linarith only [h4, h6349, hlam]
                      · linarith only [h1, h6348, hlam]
                    · have p6345_0 := h6345c.1
                      have p6345_1 := h6345c.2.1
                      have p6345_2 := h6345c.2.2.1
                      have p6345_3 := h6345c.2.2.2
                      linarith only [h5, h5073, h6182, h6186, h6343, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6345_1]
                    · have p6345_0 := h6345c.1
                      have p6345_1 := h6345c.2.1
                      have p6345_2 := h6345c.2.2.1
                      have p6345_3 := h6345c.2.2.2
                      rcases p6345_3 (m.d 0 1) (by simp) with h6354 | h6354
                      · rcases p6345_3 (m.d 0 2) (by simp) with h6355 | h6355
                        · linarith only [h0, h6355, hlam]
                        · linarith only [h6, h6355, hlam]
                      · linarith only [h3, h6354, hlam]
                    · have p6345_0 := h6345c.1
                      have p6345_1 := h6345c.2.1
                      have p6345_2 := h6345c.2.2.1
                      have p6345_3 := h6345c.2.2.2
                      linarith only [h0, hlam, p6345_0]
                    · have p6345_0 := h6345c.1
                      have p6345_1 := h6345c.2.1
                      have p6345_2 := h6345c.2.2.1
                      have p6345_3 := h6345c.2.2.2
                      linarith only [hlam, p6345_0]
                    · have p6345_0 := h6345c.1
                      have p6345_1 := h6345c.2.1
                      have p6345_2 := h6345c.2.2.1
                      have p6345_3 := h6345c.2.2.2
                      rcases p6345_3 (m.d 0 1) (by simp) with h6361 | h6361
                      · rcases p6345_3 (m.d 0 2) (by simp) with h6362 | h6362
                        · rcases p6345_3 (m.d 0 3) (by simp) with h6363 | h6363
                          · linarith only [h4, h6363, hlam]
                          · rcases p6345_3 (m.d 0 4) (by simp) with h6365 | h6365
                            · linarith only [h5, h6365, hlam]
                            · linarith only [h6365, h7, hlam]
                        · linarith only [h4, h6362, hlam]
                      · linarith only [h1, h6361, hlam]
                    · have p6345_0 := h6345c.1
                      have p6345_1 := h6345c.2.1
                      have p6345_2 := h6345c.2.2.1
                      have p6345_3 := h6345c.2.2.2
                      linarith only [h5, h5073, h6182, h6186, h6343, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6345_1]
                    · have p6345_0 := h6345c.1
                      have p6345_1 := h6345c.2.1
                      have p6345_2 := h6345c.2.2.1
                      have p6345_3 := h6345c.2.2.2
                      rcases p6345_3 (m.d 0 1) (by simp) with h6371 | h6371
                      · rcases p6345_3 (m.d 0 2) (by simp) with h6372 | h6372
                        · rcases p6345_3 (m.d 0 3) (by simp) with h6373 | h6373
                          · linarith only [h4, h6373, hlam]
                          · rcases p6345_3 (m.d 0 4) (by simp) with h6375 | h6375
                            · linarith only [h5, h6375, hlam]
                            · linarith only [h5072, h6375, hlam]
                        · linarith only [h6, h6372, hlam]
                      · linarith only [h3, h6371, hlam]
                    · have p6345_0 := h6345c.1
                      have p6345_1 := h6345c.2.1
                      have p6345_2 := h6345c.2.2.1
                      have p6345_3 := h6345c.2.2.2
                      linarith only [h1, hlam, p6345_1]
                    · have p6345_0 := h6345c.1
                      have p6345_1 := h6345c.2.1
                      have p6345_2 := h6345c.2.2.1
                      have p6345_3 := h6345c.2.2.2
                      linarith only [h4, hlam, p6345_1]
                    · have p6345_0 := h6345c.1
                      have p6345_1 := h6345c.2.1
                      have p6345_2 := h6345c.2.2.1
                      have p6345_3 := h6345c.2.2.2
                      linarith only [hlam, p6345_0]
                    · have p6345_0 := h6345c.1
                      have p6345_1 := h6345c.2.1
                      have p6345_2 := h6345c.2.2.1
                      have p6345_3 := h6345c.2.2.2
                      linarith only [h7, hlam, p6345_1]
                    · have p6345_0 := h6345c.1
                      have p6345_1 := h6345c.2.1
                      have p6345_2 := h6345c.2.2.1
                      have p6345_3 := h6345c.2.2.2
                      linarith only [h4553, hlam, p6345_1]
                    · have p6345_0 := h6345c.1
                      have p6345_1 := h6345c.2.1
                      have p6345_2 := h6345c.2.2.1
                      have p6345_3 := h6345c.2.2.2
                      linarith only [h2, hlam, p6345_0]
                    · have p6345_0 := h6345c.1
                      have p6345_1 := h6345c.2.1
                      have p6345_2 := h6345c.2.2.1
                      have p6345_3 := h6345c.2.2.2
                      linarith only [h5, hlam, p6345_0]
                    · have p6345_0 := h6345c.1
                      have p6345_1 := h6345c.2.1
                      have p6345_2 := h6345c.2.2.1
                      have p6345_3 := h6345c.2.2.2
                      linarith only [h4, h5073, h7, hc12, hc34, hlam, hphi, ht23, p6345_1]
                    · have p6345_0 := h6345c.1
                      have p6345_1 := h6345c.2.1
                      have p6345_2 := h6345c.2.2.1
                      have p6345_3 := h6345c.2.2.2
                      linarith only [hlam, p6345_0]
                    · have p6345_0 := h6345c.1
                      have p6345_1 := h6345c.2.1
                      have p6345_2 := h6345c.2.2.1
                      have p6345_3 := h6345c.2.2.2
                      linarith only [h5072, h5073, h6182, h6186, h7, hc12, hc34, hlam, hphi, ht23, p6345_1]
                    · have p6345_0 := h6345c.1
                      have p6345_1 := h6345c.2.1
                      have p6345_2 := h6345c.2.2.1
                      have p6345_3 := h6345c.2.2.2
                      linarith only [h3, hlam, p6345_0]
                    · have p6345_0 := h6345c.1
                      have p6345_1 := h6345c.2.1
                      have p6345_2 := h6345c.2.2.1
                      have p6345_3 := h6345c.2.2.2
                      linarith only [h6, hlam, p6345_1]
                    · have p6345_0 := h6345c.1
                      have p6345_1 := h6345c.2.1
                      have p6345_2 := h6345c.2.2.1
                      have p6345_3 := h6345c.2.2.2
                      linarith only [h4, h4553, h5073, h6344, hc12, hc34, hlam, hphi, ht23, p6345_1]
                    · have p6345_0 := h6345c.1
                      have p6345_1 := h6345c.2.1
                      have p6345_2 := h6345c.2.2.1
                      have p6345_3 := h6345c.2.2.2
                      linarith only [h5072, hlam, p6345_1]
                    · have p6345_0 := h6345c.1
                      have p6345_1 := h6345c.2.1
                      have p6345_2 := h6345c.2.2.1
                      have p6345_3 := h6345c.2.2.2
                      linarith only [hlam, p6345_0]
                  · linarith only [h5, h6343, h6344, h7, hlam]
                · linarith only [h5072, h6168, h6343, h7, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 5520000 in
set_option maxHeartbeats 5520000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s10_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h4553 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h5072 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 2 3 (by decide) (by decide) with h5073 | h5073
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s10_x1_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h4553 h5072 h5073
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s10_x1_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h4553 h5072 h5073

end R2N4
