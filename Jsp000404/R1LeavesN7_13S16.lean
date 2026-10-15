import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11000000 in
set_option maxHeartbeats 11000000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s6_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5135 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h6923 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6924 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h5135 := hg5135
  rcases m.htr 0 2 3 (by decide) (by decide) with h6925 | h6925
  · rcases m.htr 0 2 4 (by decide) (by decide) with h6926 | h6926
    · rcases m.htr 0 2 5 (by decide) (by decide) with h6927 | h6927
      · rcases m.htr 0 3 4 (by decide) (by decide) with h6928 | h6928
        · rcases m.htr 0 3 5 (by decide) (by decide) with h6929 | h6929
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6930 | h6930
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6931 | h6931
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6932 | h6932
                · rcases m.htr 1 2 5 (by decide) (by decide) with h6933 | h6933
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h6934 | h6934
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h6935 | h6935
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h6936 | h6936
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6937 | h6937
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6938 | h6938
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6939 | h6939
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6940 | h6940
                                · rcases h2bigk with h6941c | h6941c | h6941c | h6941c | h6941c | h6941c | h6941c | h6941c | h6941c | h6941c | h6941c | h6941c | h6941c | h6941c | h6941c | h6941c | h6941c | h6941c | h6941c | h6941c | h6941c | h6941c | h6941c | h6941c | h6941c
                                  · have p6941_0 := h6941c.1
                                    have p6941_1 := h6941c.2.1
                                    have p6941_2 := h6941c.2.2.1
                                    have p6941_3 := h6941c.2.2.2
                                    linarith only [hlam, p6941_0]
                                  · have p6941_0 := h6941c.1
                                    have p6941_1 := h6941c.2.1
                                    have p6941_2 := h6941c.2.2.1
                                    have p6941_3 := h6941c.2.2.2
                                    linarith only [h0, hlam, p6941_0]
                                  · have p6941_0 := h6941c.1
                                    have p6941_1 := h6941c.2.1
                                    have p6941_2 := h6941c.2.2.1
                                    have p6941_3 := h6941c.2.2.2
                                    linarith only [h6937, h6940, hc02, hc45, hlam, hphi, ht0b, ht5b, p6941_1]
                                  · have p6941_0 := h6941c.1
                                    have p6941_1 := h6941c.2.1
                                    have p6941_2 := h6941c.2.2.1
                                    have p6941_3 := h6941c.2.2.2
                                    linarith only [h0, h6937, h6940, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6941_1]
                                  · have p6941_0 := h6941c.1
                                    have p6941_1 := h6941c.2.1
                                    have p6941_2 := h6941c.2.2.1
                                    have p6941_3 := h6941c.2.2.2
                                    rcases p6941_3 (m.d 0 2) (by simp) with h6946 | h6946
                                    · rcases p6941_3 (m.d 1 2) (by simp) with h6947 | h6947
                                      · rcases p6941_3 (m.d 2 3) (by simp) with h6948 | h6948
                                        · linarith only [h6925, h6948, hlam]
                                        · linarith only [h6938, h6948, hlam]
                                      · linarith only [h6933, h6947, hlam]
                                    · linarith only [h6946, hlam, p6941_0]
                                  · have p6941_0 := h6941c.1
                                    have p6941_1 := h6941c.2.1
                                    have p6941_2 := h6941c.2.2.1
                                    have p6941_3 := h6941c.2.2.2
                                    linarith only [h0, h6923, h6932, h6937, h6940, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6941_1]
                                  · have p6941_0 := h6941c.1
                                    have p6941_1 := h6941c.2.1
                                    have p6941_2 := h6941c.2.2.1
                                    have p6941_3 := h6941c.2.2.2
                                    linarith only [hlam, p6941_0]
                                  · have p6941_0 := h6941c.1
                                    have p6941_1 := h6941c.2.1
                                    have p6941_2 := h6941c.2.2.1
                                    have p6941_3 := h6941c.2.2.2
                                    linarith only [h6937, h6940, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6941_1]
                                  · have p6941_0 := h6941c.1
                                    have p6941_1 := h6941c.2.1
                                    have p6941_2 := h6941c.2.2.1
                                    have p6941_3 := h6941c.2.2.2
                                    linarith only [h6937, h6940, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6941_1]
                                  · have p6941_0 := h6941c.1
                                    have p6941_1 := h6941c.2.1
                                    have p6941_2 := h6941c.2.2.1
                                    have p6941_3 := h6941c.2.2.2
                                    rcases p6941_3 (m.d 0 2) (by simp) with h6957 | h6957
                                    · linarith only [h0, h6957, hlam]
                                    · linarith only [h6927, h6957, hlam]
                                  · have p6941_0 := h6941c.1
                                    have p6941_1 := h6941c.2.1
                                    have p6941_2 := h6941c.2.2.1
                                    have p6941_3 := h6941c.2.2.2
                                    linarith only [h6925, hlam, p6941_0]
                                  · have p6941_0 := h6941c.1
                                    have p6941_1 := h6941c.2.1
                                    have p6941_2 := h6941c.2.2.1
                                    have p6941_3 := h6941c.2.2.2
                                    linarith only [h6931, hlam, p6941_0]
                                  · have p6941_0 := h6941c.1
                                    have p6941_1 := h6941c.2.1
                                    have p6941_2 := h6941c.2.2.1
                                    have p6941_3 := h6941c.2.2.2
                                    linarith only [hlam, p6941_0]
                                  · have p6941_0 := h6941c.1
                                    have p6941_1 := h6941c.2.1
                                    have p6941_2 := h6941c.2.2.1
                                    have p6941_3 := h6941c.2.2.2
                                    linarith only [h6925, h6937, h6940, hc02, hc45, hlam, hphi, ht0b, ht5b, p6941_1]
                                  · have p6941_0 := h6941c.1
                                    have p6941_1 := h6941c.2.1
                                    have p6941_2 := h6941c.2.2.1
                                    have p6941_3 := h6941c.2.2.2
                                    linarith only [h0, h6925, h6938, h6940, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6941_1]
                                  · have p6941_0 := h6941c.1
                                    have p6941_1 := h6941c.2.1
                                    have p6941_2 := h6941c.2.2.1
                                    have p6941_3 := h6941c.2.2.2
                                    linarith only [h6926, hlam, p6941_0]
                                  · have p6941_0 := h6941c.1
                                    have p6941_1 := h6941c.2.1
                                    have p6941_2 := h6941c.2.2.1
                                    have p6941_3 := h6941c.2.2.2
                                    linarith only [h6932, hlam, p6941_0]
                                  · have p6941_0 := h6941c.1
                                    have p6941_1 := h6941c.2.1
                                    have p6941_2 := h6941c.2.2.1
                                    have p6941_3 := h6941c.2.2.2
                                    linarith only [h6937, hlam, p6941_0]
                                  · have p6941_0 := h6941c.1
                                    have p6941_1 := h6941c.2.1
                                    have p6941_2 := h6941c.2.2.1
                                    have p6941_3 := h6941c.2.2.2
                                    linarith only [hlam, p6941_0]
                                  · have p6941_0 := h6941c.1
                                    have p6941_1 := h6941c.2.1
                                    have p6941_2 := h6941c.2.2.1
                                    have p6941_3 := h6941c.2.2.2
                                    linarith only [h6923, h6932, h6938, h6940, hc01, hc45, hlam, hphi, ht0b, ht5b, p6941_1]
                                  · have p6941_0 := h6941c.1
                                    have p6941_1 := h6941c.2.1
                                    have p6941_2 := h6941c.2.2.1
                                    have p6941_3 := h6941c.2.2.2
                                    linarith only [h6927, hlam, p6941_0]
                                  · have p6941_0 := h6941c.1
                                    have p6941_1 := h6941c.2.1
                                    have p6941_2 := h6941c.2.2.1
                                    have p6941_3 := h6941c.2.2.2
                                    linarith only [h6933, hlam, p6941_0]
                                  · have p6941_0 := h6941c.1
                                    have p6941_1 := h6941c.2.1
                                    have p6941_2 := h6941c.2.2.1
                                    have p6941_3 := h6941c.2.2.2
                                    linarith only [h6938, hlam, p6941_0]
                                  · have p6941_0 := h6941c.1
                                    have p6941_1 := h6941c.2.1
                                    have p6941_2 := h6941c.2.2.1
                                    have p6941_3 := h6941c.2.2.2
                                    linarith only [h6939, hlam, p6941_1]
                                  · have p6941_0 := h6941c.1
                                    have p6941_1 := h6941c.2.1
                                    have p6941_2 := h6941c.2.2.1
                                    have p6941_3 := h6941c.2.2.2
                                    linarith only [hlam, p6941_0]
                                · linarith only [h5135, h6923, h6931, h6936, h6940, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h5135, h6923, h6931, h6936, h6939, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h5135, h6923, h6931, h6935, h6936, h6937, h6938, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6978 | h6978
                            · linarith only [h5135, h6923, h6931, h6934, h6937, h6978, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6980 | h6980
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6981 | h6981
                                · rcases h2bigk with h6982c | h6982c | h6982c | h6982c | h6982c | h6982c | h6982c | h6982c | h6982c | h6982c | h6982c | h6982c | h6982c | h6982c | h6982c | h6982c | h6982c | h6982c | h6982c | h6982c | h6982c | h6982c | h6982c | h6982c | h6982c
                                  · have p6982_0 := h6982c.1
                                    have p6982_1 := h6982c.2.1
                                    have p6982_2 := h6982c.2.2.1
                                    have p6982_3 := h6982c.2.2.2
                                    linarith only [hlam, p6982_0]
                                  · have p6982_0 := h6982c.1
                                    have p6982_1 := h6982c.2.1
                                    have p6982_2 := h6982c.2.2.1
                                    have p6982_3 := h6982c.2.2.2
                                    linarith only [h0, hlam, p6982_0]
                                  · have p6982_0 := h6982c.1
                                    have p6982_1 := h6982c.2.1
                                    have p6982_2 := h6982c.2.2.1
                                    have p6982_3 := h6982c.2.2.2
                                    rcases p6982_3 (m.d 0 2) (by simp) with h6985 | h6985
                                    · rcases p6982_3 (m.d 1 2) (by simp) with h6986 | h6986
                                      · rcases p6982_3 (m.d 2 3) (by simp) with h6987 | h6987
                                        · linarith only [h6987, hlam, p6982_0]
                                        · rcases p6982_3 (m.d 2 4) (by simp) with h6989 | h6989
                                          · linarith only [h6926, h6989, hlam]
                                          · linarith only [h6937, h6989, hlam]
                                      · linarith only [h6931, h6986, hlam]
                                    · linarith only [h6985, hlam, p6982_0]
                                  · have p6982_0 := h6982c.1
                                    have p6982_1 := h6982c.2.1
                                    have p6982_2 := h6982c.2.2.1
                                    have p6982_3 := h6982c.2.2.2
                                    linarith only [h0, h6980, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6982_1]
                                  · have p6982_0 := h6982c.1
                                    have p6982_1 := h6982c.2.1
                                    have p6982_2 := h6982c.2.2.1
                                    have p6982_3 := h6982c.2.2.2
                                    rcases p6982_3 (m.d 0 2) (by simp) with h6995 | h6995
                                    · rcases p6982_3 (m.d 1 2) (by simp) with h6996 | h6996
                                      · rcases p6982_3 (m.d 2 3) (by simp) with h6997 | h6997
                                        · linarith only [h6925, h6997, hlam]
                                        · rcases p6982_3 (m.d 2 4) (by simp) with h6999 | h6999
                                          · linarith only [h6926, h6999, hlam]
                                          · linarith only [h6980, h6999, hlam]
                                      · linarith only [h6933, h6996, hlam]
                                    · linarith only [h6995, hlam, p6982_0]
                                  · have p6982_0 := h6982c.1
                                    have p6982_1 := h6982c.2.1
                                    have p6982_2 := h6982c.2.2.1
                                    have p6982_3 := h6982c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p6982_1]
                                  · have p6982_0 := h6982c.1
                                    have p6982_1 := h6982c.2.1
                                    have p6982_2 := h6982c.2.2.1
                                    have p6982_3 := h6982c.2.2.2
                                    linarith only [hlam, p6982_0]
                                  · have p6982_0 := h6982c.1
                                    have p6982_1 := h6982c.2.1
                                    have p6982_2 := h6982c.2.2.1
                                    have p6982_3 := h6982c.2.2.2
                                    rcases p6982_3 (m.d 0 2) (by simp) with h7006 | h7006
                                    · linarith only [h0, h7006, hlam]
                                    · linarith only [h6925, h7006, hlam]
                                  · have p6982_0 := h6982c.1
                                    have p6982_1 := h6982c.2.1
                                    have p6982_2 := h6982c.2.2.1
                                    have p6982_3 := h6982c.2.2.2
                                    linarith only [h6980, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6982_1]
                                  · have p6982_0 := h6982c.1
                                    have p6982_1 := h6982c.2.1
                                    have p6982_2 := h6982c.2.2.1
                                    have p6982_3 := h6982c.2.2.2
                                    rcases p6982_3 (m.d 0 2) (by simp) with h7010 | h7010
                                    · linarith only [h0, h7010, hlam]
                                    · linarith only [h6927, h7010, hlam]
                                  · have p6982_0 := h6982c.1
                                    have p6982_1 := h6982c.2.1
                                    have p6982_2 := h6982c.2.2.1
                                    have p6982_3 := h6982c.2.2.2
                                    linarith only [h6925, hlam, p6982_0]
                                  · have p6982_0 := h6982c.1
                                    have p6982_1 := h6982c.2.1
                                    have p6982_2 := h6982c.2.2.1
                                    have p6982_3 := h6982c.2.2.2
                                    linarith only [h6931, hlam, p6982_0]
                                  · have p6982_0 := h6982c.1
                                    have p6982_1 := h6982c.2.1
                                    have p6982_2 := h6982c.2.2.1
                                    have p6982_3 := h6982c.2.2.2
                                    linarith only [hlam, p6982_0]
                                  · have p6982_0 := h6982c.1
                                    have p6982_1 := h6982c.2.1
                                    have p6982_2 := h6982c.2.2.1
                                    have p6982_3 := h6982c.2.2.2
                                    linarith only [h6937, hlam, p6982_1]
                                  · have p6982_0 := h6982c.1
                                    have p6982_1 := h6982c.2.1
                                    have p6982_2 := h6982c.2.2.1
                                    have p6982_3 := h6982c.2.2.2
                                    linarith only [h6978, hlam, p6982_1]
                                  · have p6982_0 := h6982c.1
                                    have p6982_1 := h6982c.2.1
                                    have p6982_2 := h6982c.2.2.1
                                    have p6982_3 := h6982c.2.2.2
                                    linarith only [h6926, hlam, p6982_0]
                                  · have p6982_0 := h6982c.1
                                    have p6982_1 := h6982c.2.1
                                    have p6982_2 := h6982c.2.2.1
                                    have p6982_3 := h6982c.2.2.2
                                    linarith only [h6932, hlam, p6982_0]
                                  · have p6982_0 := h6982c.1
                                    have p6982_1 := h6982c.2.1
                                    have p6982_2 := h6982c.2.2.1
                                    have p6982_3 := h6982c.2.2.2
                                    linarith only [h6926, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6982_1]
                                  · have p6982_0 := h6982c.1
                                    have p6982_1 := h6982c.2.1
                                    have p6982_2 := h6982c.2.2.1
                                    have p6982_3 := h6982c.2.2.2
                                    linarith only [hlam, p6982_0]
                                  · have p6982_0 := h6982c.1
                                    have p6982_1 := h6982c.2.1
                                    have p6982_2 := h6982c.2.2.1
                                    have p6982_3 := h6982c.2.2.2
                                    linarith only [h6923, h6934, h6937, h6978, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6982_1]
                                  · have p6982_0 := h6982c.1
                                    have p6982_1 := h6982c.2.1
                                    have p6982_2 := h6982c.2.2.1
                                    have p6982_3 := h6982c.2.2.2
                                    linarith only [h6927, hlam, p6982_0]
                                  · have p6982_0 := h6982c.1
                                    have p6982_1 := h6982c.2.1
                                    have p6982_2 := h6982c.2.2.1
                                    have p6982_3 := h6982c.2.2.2
                                    linarith only [h6933, hlam, p6982_0]
                                  · have p6982_0 := h6982c.1
                                    have p6982_1 := h6982c.2.1
                                    have p6982_2 := h6982c.2.2.1
                                    have p6982_3 := h6982c.2.2.2
                                    linarith only [h0, h6927, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6982_1]
                                  · have p6982_0 := h6982c.1
                                    have p6982_1 := h6982c.2.1
                                    have p6982_2 := h6982c.2.2.1
                                    have p6982_3 := h6982c.2.2.2
                                    linarith only [h6980, hlam, p6982_1]
                                  · have p6982_0 := h6982c.1
                                    have p6982_1 := h6982c.2.1
                                    have p6982_2 := h6982c.2.2.1
                                    have p6982_3 := h6982c.2.2.2
                                    linarith only [hlam, p6982_0]
                                · linarith only [h5135, h6923, h6931, h6936, h6937, h6981, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h5135, h6923, h6931, h6936, h6937, h6980, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h7030 | h7030
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h7031 | h7031
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h7032 | h7032
                              · linarith only [h6932, h6936, h7032, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h7034 | h7034
                                · linarith only [h0, h6925, h6932, h6936, h7030, h7034, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases h2bigk with h7036c | h7036c | h7036c | h7036c | h7036c | h7036c | h7036c | h7036c | h7036c | h7036c | h7036c | h7036c | h7036c | h7036c | h7036c | h7036c | h7036c | h7036c | h7036c | h7036c | h7036c | h7036c | h7036c | h7036c | h7036c
                                  · have p7036_0 := h7036c.1
                                    have p7036_1 := h7036c.2.1
                                    have p7036_2 := h7036c.2.2.1
                                    have p7036_3 := h7036c.2.2.2
                                    linarith only [hlam, p7036_0]
                                  · have p7036_0 := h7036c.1
                                    have p7036_1 := h7036c.2.1
                                    have p7036_2 := h7036c.2.2.1
                                    have p7036_3 := h7036c.2.2.2
                                    linarith only [h0, hlam, p7036_0]
                                  · have p7036_0 := h7036c.1
                                    have p7036_1 := h7036c.2.1
                                    have p7036_2 := h7036c.2.2.1
                                    have p7036_3 := h7036c.2.2.2
                                    linarith only [h0, h7030, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7036_1]
                                  · have p7036_0 := h7036c.1
                                    have p7036_1 := h7036c.2.1
                                    have p7036_2 := h7036c.2.2.1
                                    have p7036_3 := h7036c.2.2.2
                                    rcases p7036_3 (m.d 0 2) (by simp) with h7040 | h7040
                                    · rcases p7036_3 (m.d 1 2) (by simp) with h7041 | h7041
                                      · rcases p7036_3 (m.d 2 3) (by simp) with h7042 | h7042
                                        · linarith only [h6925, h7042, hlam]
                                        · linarith only [h7030, h7042, hlam]
                                      · linarith only [h6932, h7041, hlam]
                                    · linarith only [h7040, hlam, p7036_0]
                                  · have p7036_0 := h7036c.1
                                    have p7036_1 := h7036c.2.1
                                    have p7036_2 := h7036c.2.2.1
                                    have p7036_3 := h7036c.2.2.2
                                    rcases p7036_3 (m.d 0 2) (by simp) with h7047 | h7047
                                    · rcases p7036_3 (m.d 1 2) (by simp) with h7048 | h7048
                                      · rcases p7036_3 (m.d 2 3) (by simp) with h7049 | h7049
                                        · linarith only [h6925, h7049, hlam]
                                        · linarith only [h7031, h7049, hlam]
                                      · linarith only [h6933, h7048, hlam]
                                    · linarith only [h7047, hlam, p7036_0]
                                  · have p7036_0 := h7036c.1
                                    have p7036_1 := h7036c.2.1
                                    have p7036_2 := h7036c.2.2.1
                                    have p7036_3 := h7036c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p7036_1]
                                  · have p7036_0 := h7036c.1
                                    have p7036_1 := h7036c.2.1
                                    have p7036_2 := h7036c.2.2.1
                                    have p7036_3 := h7036c.2.2.2
                                    linarith only [hlam, p7036_0]
                                  · have p7036_0 := h7036c.1
                                    have p7036_1 := h7036c.2.1
                                    have p7036_2 := h7036c.2.2.1
                                    have p7036_3 := h7036c.2.2.2
                                    linarith only [h7030, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7036_1]
                                  · have p7036_0 := h7036c.1
                                    have p7036_1 := h7036c.2.1
                                    have p7036_2 := h7036c.2.2.1
                                    have p7036_3 := h7036c.2.2.2
                                    rcases p7036_3 (m.d 0 2) (by simp) with h7057 | h7057
                                    · linarith only [h0, h7057, hlam]
                                    · linarith only [h6926, h7057, hlam]
                                  · have p7036_0 := h7036c.1
                                    have p7036_1 := h7036c.2.1
                                    have p7036_2 := h7036c.2.2.1
                                    have p7036_3 := h7036c.2.2.2
                                    rcases p7036_3 (m.d 0 2) (by simp) with h7060 | h7060
                                    · linarith only [h0, h7060, hlam]
                                    · linarith only [h6927, h7060, hlam]
                                  · have p7036_0 := h7036c.1
                                    have p7036_1 := h7036c.2.1
                                    have p7036_2 := h7036c.2.2.1
                                    have p7036_3 := h7036c.2.2.2
                                    linarith only [h6925, hlam, p7036_0]
                                  · have p7036_0 := h7036c.1
                                    have p7036_1 := h7036c.2.1
                                    have p7036_2 := h7036c.2.2.1
                                    have p7036_3 := h7036c.2.2.2
                                    linarith only [h6931, hlam, p7036_0]
                                  · have p7036_0 := h7036c.1
                                    have p7036_1 := h7036c.2.1
                                    have p7036_2 := h7036c.2.2.1
                                    have p7036_3 := h7036c.2.2.2
                                    linarith only [hlam, p7036_0]
                                  · have p7036_0 := h7036c.1
                                    have p7036_1 := h7036c.2.1
                                    have p7036_2 := h7036c.2.2.1
                                    have p7036_3 := h7036c.2.2.2
                                    linarith only [h6925, h7030, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p7036_1]
                                  · have p7036_0 := h7036c.1
                                    have p7036_1 := h7036c.2.1
                                    have p7036_2 := h7036c.2.2.1
                                    have p7036_3 := h7036c.2.2.2
                                    linarith only [h0, h6925, h7030, h7032, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7036_1]
                                  · have p7036_0 := h7036c.1
                                    have p7036_1 := h7036c.2.1
                                    have p7036_2 := h7036c.2.2.1
                                    have p7036_3 := h7036c.2.2.2
                                    linarith only [h6926, hlam, p7036_0]
                                  · have p7036_0 := h7036c.1
                                    have p7036_1 := h7036c.2.1
                                    have p7036_2 := h7036c.2.2.1
                                    have p7036_3 := h7036c.2.2.2
                                    linarith only [h6932, hlam, p7036_0]
                                  · have p7036_0 := h7036c.1
                                    have p7036_1 := h7036c.2.1
                                    have p7036_2 := h7036c.2.2.1
                                    have p7036_3 := h7036c.2.2.2
                                    linarith only [h7030, hlam, p7036_0]
                                  · have p7036_0 := h7036c.1
                                    have p7036_1 := h7036c.2.1
                                    have p7036_2 := h7036c.2.2.1
                                    have p7036_3 := h7036c.2.2.2
                                    linarith only [hlam, p7036_0]
                                  · have p7036_0 := h7036c.1
                                    have p7036_1 := h7036c.2.1
                                    have p7036_2 := h7036c.2.2.1
                                    have p7036_3 := h7036c.2.2.2
                                    linarith only [h7032, hlam, p7036_0]
                                  · have p7036_0 := h7036c.1
                                    have p7036_1 := h7036c.2.1
                                    have p7036_2 := h7036c.2.2.1
                                    have p7036_3 := h7036c.2.2.2
                                    linarith only [h6927, hlam, p7036_0]
                                  · have p7036_0 := h7036c.1
                                    have p7036_1 := h7036c.2.1
                                    have p7036_2 := h7036c.2.2.1
                                    have p7036_3 := h7036c.2.2.2
                                    linarith only [h6933, hlam, p7036_0]
                                  · have p7036_0 := h7036c.1
                                    have p7036_1 := h7036c.2.1
                                    have p7036_2 := h7036c.2.2.1
                                    have p7036_3 := h7036c.2.2.2
                                    linarith only [h7031, hlam, p7036_0]
                                  · have p7036_0 := h7036c.1
                                    have p7036_1 := h7036c.2.1
                                    have p7036_2 := h7036c.2.2.1
                                    have p7036_3 := h7036c.2.2.2
                                    linarith only [h0, h6927, h7030, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7036_1]
                                  · have p7036_0 := h7036c.1
                                    have p7036_1 := h7036c.2.1
                                    have p7036_2 := h7036c.2.2.1
                                    have p7036_3 := h7036c.2.2.2
                                    linarith only [hlam, p7036_0]
                            · linarith only [h0, h6923, h6930, h6935, h6936, h7030, h7031, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h5135, h6923, h6930, h6931, h6934, h6936, h7030, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h5135, h6929, h6935, hlam]
                    · linarith only [h5135, h6928, h6934, hlam]
                  · linarith only [h0, h6927, h6933, hlam]
                · linarith only [h0, h6926, h6932, hlam]
              · linarith only [h0, h6925, h6931, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h7085 | h7085
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7086 | h7086
                · rcases m.htr 1 2 5 (by decide) (by decide) with h7087 | h7087
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h7088 | h7088
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h7089 | h7089
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7090 | h7090
                        · linarith only [h6923, h6930, h7090, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h7092 | h7092
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h7093 | h7093
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h7094 | h7094
                              · linarith only [h6923, h6930, h7086, h7094, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h7096 | h7096
                                · linarith only [h6923, h6930, h7086, h7092, h7096, hlam]
                                · rcases h2bigk with h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c | h7098c
                                  · have p7098_0 := h7098c.1
                                    have p7098_1 := h7098c.2.1
                                    have p7098_2 := h7098c.2.2.1
                                    have p7098_3 := h7098c.2.2.2
                                    linarith only [hlam, p7098_0]
                                  · have p7098_0 := h7098c.1
                                    have p7098_1 := h7098c.2.1
                                    have p7098_2 := h7098c.2.2.1
                                    have p7098_3 := h7098c.2.2.2
                                    linarith only [h0, hlam, p7098_0]
                                  · have p7098_0 := h7098c.1
                                    have p7098_1 := h7098c.2.1
                                    have p7098_2 := h7098c.2.2.1
                                    have p7098_3 := h7098c.2.2.2
                                    linarith only [h7092, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p7098_1]
                                  · have p7098_0 := h7098c.1
                                    have p7098_1 := h7098c.2.1
                                    have p7098_2 := h7098c.2.2.1
                                    have p7098_3 := h7098c.2.2.2
                                    rcases p7098_3 (m.d 0 2) (by simp) with h7102 | h7102
                                    · rcases p7098_3 (m.d 1 2) (by simp) with h7103 | h7103
                                      · rcases p7098_3 (m.d 2 3) (by simp) with h7104 | h7104
                                        · linarith only [h6925, h7104, hlam]
                                        · linarith only [h7092, h7104, hlam]
                                      · linarith only [h7086, h7103, hlam]
                                    · linarith only [h7102, hlam, p7098_0]
                                  · have p7098_0 := h7098c.1
                                    have p7098_1 := h7098c.2.1
                                    have p7098_2 := h7098c.2.2.1
                                    have p7098_3 := h7098c.2.2.2
                                    rcases p7098_3 (m.d 0 2) (by simp) with h7109 | h7109
                                    · rcases p7098_3 (m.d 1 2) (by simp) with h7110 | h7110
                                      · rcases p7098_3 (m.d 2 3) (by simp) with h7111 | h7111
                                        · linarith only [h6925, h7111, hlam]
                                        · linarith only [h7093, h7111, hlam]
                                      · linarith only [h7087, h7110, hlam]
                                    · linarith only [h7109, hlam, p7098_0]
                                  · have p7098_0 := h7098c.1
                                    have p7098_1 := h7098c.2.1
                                    have p7098_2 := h7098c.2.2.1
                                    have p7098_3 := h7098c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p7098_1]
                                  · have p7098_0 := h7098c.1
                                    have p7098_1 := h7098c.2.1
                                    have p7098_2 := h7098c.2.2.1
                                    have p7098_3 := h7098c.2.2.2
                                    linarith only [hlam, p7098_0]
                                  · have p7098_0 := h7098c.1
                                    have p7098_1 := h7098c.2.1
                                    have p7098_2 := h7098c.2.2.1
                                    have p7098_3 := h7098c.2.2.2
                                    linarith only [h7093, h7096, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7098_1]
                                  · have p7098_0 := h7098c.1
                                    have p7098_1 := h7098c.2.1
                                    have p7098_2 := h7098c.2.2.1
                                    have p7098_3 := h7098c.2.2.2
                                    rcases p7098_3 (m.d 0 2) (by simp) with h7119 | h7119
                                    · linarith only [h0, h7119, hlam]
                                    · linarith only [h6926, h7119, hlam]
                                  · have p7098_0 := h7098c.1
                                    have p7098_1 := h7098c.2.1
                                    have p7098_2 := h7098c.2.2.1
                                    have p7098_3 := h7098c.2.2.2
                                    rcases p7098_3 (m.d 0 2) (by simp) with h7122 | h7122
                                    · linarith only [h0, h7122, hlam]
                                    · linarith only [h6927, h7122, hlam]
                                  · have p7098_0 := h7098c.1
                                    have p7098_1 := h7098c.2.1
                                    have p7098_2 := h7098c.2.2.1
                                    have p7098_3 := h7098c.2.2.2
                                    linarith only [h6925, hlam, p7098_0]
                                  · have p7098_0 := h7098c.1
                                    have p7098_1 := h7098c.2.1
                                    have p7098_2 := h7098c.2.2.1
                                    have p7098_3 := h7098c.2.2.2
                                    linarith only [h7085, hlam, p7098_0]
                                  · have p7098_0 := h7098c.1
                                    have p7098_1 := h7098c.2.1
                                    have p7098_2 := h7098c.2.2.1
                                    have p7098_3 := h7098c.2.2.2
                                    linarith only [hlam, p7098_0]
                                  · have p7098_0 := h7098c.1
                                    have p7098_1 := h7098c.2.1
                                    have p7098_2 := h7098c.2.2.1
                                    have p7098_3 := h7098c.2.2.2
                                    linarith only [h6925, h7092, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p7098_1]
                                  · have p7098_0 := h7098c.1
                                    have p7098_1 := h7098c.2.1
                                    have p7098_2 := h7098c.2.2.1
                                    have p7098_3 := h7098c.2.2.2
                                    linarith only [h0, h6925, h7092, h7094, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7098_1]
                                  · have p7098_0 := h7098c.1
                                    have p7098_1 := h7098c.2.1
                                    have p7098_2 := h7098c.2.2.1
                                    have p7098_3 := h7098c.2.2.2
                                    linarith only [h6926, hlam, p7098_0]
                                  · have p7098_0 := h7098c.1
                                    have p7098_1 := h7098c.2.1
                                    have p7098_2 := h7098c.2.2.1
                                    have p7098_3 := h7098c.2.2.2
                                    linarith only [h7086, hlam, p7098_0]
                                  · have p7098_0 := h7098c.1
                                    have p7098_1 := h7098c.2.1
                                    have p7098_2 := h7098c.2.2.1
                                    have p7098_3 := h7098c.2.2.2
                                    linarith only [h7092, hlam, p7098_0]
                                  · have p7098_0 := h7098c.1
                                    have p7098_1 := h7098c.2.1
                                    have p7098_2 := h7098c.2.2.1
                                    have p7098_3 := h7098c.2.2.2
                                    linarith only [hlam, p7098_0]
                                  · have p7098_0 := h7098c.1
                                    have p7098_1 := h7098c.2.1
                                    have p7098_2 := h7098c.2.2.1
                                    have p7098_3 := h7098c.2.2.2
                                    linarith only [h7094, hlam, p7098_0]
                                  · have p7098_0 := h7098c.1
                                    have p7098_1 := h7098c.2.1
                                    have p7098_2 := h7098c.2.2.1
                                    have p7098_3 := h7098c.2.2.2
                                    linarith only [h6927, hlam, p7098_0]
                                  · have p7098_0 := h7098c.1
                                    have p7098_1 := h7098c.2.1
                                    have p7098_2 := h7098c.2.2.1
                                    have p7098_3 := h7098c.2.2.2
                                    linarith only [h7087, hlam, p7098_0]
                                  · have p7098_0 := h7098c.1
                                    have p7098_1 := h7098c.2.1
                                    have p7098_2 := h7098c.2.2.1
                                    have p7098_3 := h7098c.2.2.2
                                    linarith only [h7093, hlam, p7098_0]
                                  · have p7098_0 := h7098c.1
                                    have p7098_1 := h7098c.2.1
                                    have p7098_2 := h7098c.2.2.1
                                    have p7098_3 := h7098c.2.2.2
                                    linarith only [h6924, h7087, h7092, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7098_1]
                                  · have p7098_0 := h7098c.1
                                    have p7098_1 := h7098c.2.1
                                    have p7098_2 := h7098c.2.2.1
                                    have p7098_3 := h7098c.2.2.2
                                    linarith only [hlam, p7098_0]
                            · linarith only [h5135, h6924, h7085, h7089, h7092, h7093, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h7141 | h7141
                            · linarith only [h5135, h6923, h7085, h7088, h7092, h7141, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h7143 | h7143
                              · linarith only [h5135, h6924, h6930, h7085, h7088, h7090, h7092, h7143, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h7145 | h7145
                                · linarith only [h6923, h6930, h7088, h7145, hlam]
                                · rcases h2bigk with h7147c | h7147c | h7147c | h7147c | h7147c | h7147c | h7147c | h7147c | h7147c | h7147c | h7147c | h7147c | h7147c | h7147c | h7147c | h7147c | h7147c | h7147c | h7147c | h7147c | h7147c | h7147c | h7147c | h7147c | h7147c
                                  · have p7147_0 := h7147c.1
                                    have p7147_1 := h7147c.2.1
                                    have p7147_2 := h7147c.2.2.1
                                    have p7147_3 := h7147c.2.2.2
                                    linarith only [hlam, p7147_0]
                                  · have p7147_0 := h7147c.1
                                    have p7147_1 := h7147c.2.1
                                    have p7147_2 := h7147c.2.2.1
                                    have p7147_3 := h7147c.2.2.2
                                    linarith only [h0, hlam, p7147_0]
                                  · have p7147_0 := h7147c.1
                                    have p7147_1 := h7147c.2.1
                                    have p7147_2 := h7147c.2.2.1
                                    have p7147_3 := h7147c.2.2.2
                                    rcases p7147_3 (m.d 0 2) (by simp) with h7150 | h7150
                                    · rcases p7147_3 (m.d 1 2) (by simp) with h7151 | h7151
                                      · rcases p7147_3 (m.d 2 3) (by simp) with h7152 | h7152
                                        · linarith only [h7152, hlam, p7147_0]
                                        · rcases p7147_3 (m.d 2 4) (by simp) with h7154 | h7154
                                          · linarith only [h6926, h7154, hlam]
                                          · linarith only [h7092, h7154, hlam]
                                      · linarith only [h7085, h7151, hlam]
                                    · linarith only [h7150, hlam, p7147_0]
                                  · have p7147_0 := h7147c.1
                                    have p7147_1 := h7147c.2.1
                                    have p7147_2 := h7147c.2.2.1
                                    have p7147_3 := h7147c.2.2.2
                                    rcases p7147_3 (m.d 0 2) (by simp) with h7159 | h7159
                                    · rcases p7147_3 (m.d 1 2) (by simp) with h7160 | h7160
                                      · rcases p7147_3 (m.d 2 3) (by simp) with h7161 | h7161
                                        · linarith only [h6925, h7161, hlam]
                                        · rcases p7147_3 (m.d 2 4) (by simp) with h7163 | h7163
                                          · linarith only [h7163, hlam, p7147_0]
                                          · rcases p7147_3 (m.d 2 5) (by simp) with h7165 | h7165
                                            · linarith only [h6927, h7165, hlam]
                                            · linarith only [h7143, h7165, hlam]
                                      · linarith only [h7086, h7160, hlam]
                                    · linarith only [h7159, hlam, p7147_0]
                                  · have p7147_0 := h7147c.1
                                    have p7147_1 := h7147c.2.1
                                    have p7147_2 := h7147c.2.2.1
                                    have p7147_3 := h7147c.2.2.2
                                    rcases p7147_3 (m.d 0 2) (by simp) with h7170 | h7170
                                    · rcases p7147_3 (m.d 1 2) (by simp) with h7171 | h7171
                                      · rcases p7147_3 (m.d 2 3) (by simp) with h7172 | h7172
                                        · linarith only [h6925, h7172, hlam]
                                        · rcases p7147_3 (m.d 2 4) (by simp) with h7174 | h7174
                                          · linarith only [h6926, h7174, hlam]
                                          · rcases p7147_3 (m.d 2 5) (by simp) with h7176 | h7176
                                            · linarith only [h7176, hlam, p7147_0]
                                            · rcases h3bigk with h7178c | h7178c | h7178c | h7178c | h7178c | h7178c | h7178c | h7178c | h7178c | h7178c | h7178c | h7178c | h7178c | h7178c | h7178c | h7178c | h7178c | h7178c | h7178c | h7178c | h7178c | h7178c | h7178c | h7178c | h7178c
                                              · have p7178_0 := h7178c.1
                                                have p7178_1 := h7178c.2.1
                                                have p7178_2 := h7178c.2.2.1
                                                have p7178_3 := h7178c.2.2.2
                                                linarith only [hlam, p7178_0]
                                              · have p7178_0 := h7178c.1
                                                have p7178_1 := h7178c.2.1
                                                have p7178_2 := h7178c.2.2.1
                                                have p7178_3 := h7178c.2.2.2
                                                linarith only [h5135, hlam, p7178_1]
                                              · have p7178_0 := h7178c.1
                                                have p7178_1 := h7178c.2.1
                                                have p7178_2 := h7178c.2.2.1
                                                have p7178_3 := h7178c.2.2.2
                                                rcases p7178_3 (m.d 0 3) (by simp) with h7181 | h7181
                                                · rcases p7178_3 (m.d 1 3) (by simp) with h7182 | h7182
                                                  · rcases p7178_3 (m.d 2 3) (by simp) with h7183 | h7183
                                                    · linarith only [h6925, h7183, hlam]
                                                    · rcases p7178_3 (m.d 3 4) (by simp) with h7185 | h7185
                                                      · linarith only [h6928, h7185, hlam]
                                                      · linarith only [h7092, h7185, hlam]
                                                  · linarith only [h7085, h7182, hlam]
                                                · linarith only [h6925, h7181, hlam]
                                              · have p7178_0 := h7178c.1
                                                have p7178_1 := h7178c.2.1
                                                have p7178_2 := h7178c.2.2.1
                                                have p7178_3 := h7178c.2.2.2
                                                rcases p7178_3 (m.d 0 3) (by simp) with h7190 | h7190
                                                · rcases p7178_3 (m.d 1 3) (by simp) with h7191 | h7191
                                                  · rcases p7178_3 (m.d 2 3) (by simp) with h7192 | h7192
                                                    · linarith only [h6925, h7192, hlam]
                                                    · rcases p7178_3 (m.d 3 4) (by simp) with h7194 | h7194
                                                      · linarith only [h7194, hlam, p7178_0]
                                                      · rcases p7178_3 (m.d 3 5) (by simp) with h7196 | h7196
                                                        · linarith only [h6929, h7196, hlam]
                                                        · linarith only [h7145, h7196, hlam]
                                                  · linarith only [h7088, h7191, hlam]
                                                · linarith only [h7190, hlam, p7178_0]
                                              · have p7178_0 := h7178c.1
                                                have p7178_1 := h7178c.2.1
                                                have p7178_2 := h7178c.2.2.1
                                                have p7178_3 := h7178c.2.2.2
                                                rcases p7178_3 (m.d 0 3) (by simp) with h7201 | h7201
                                                · rcases p7178_3 (m.d 1 3) (by simp) with h7202 | h7202
                                                  · rcases p7178_3 (m.d 2 3) (by simp) with h7203 | h7203
                                                    · linarith only [h6925, h7203, hlam]
                                                    · rcases p7178_3 (m.d 3 4) (by simp) with h7205 | h7205
                                                      · linarith only [h6928, h7205, hlam]
                                                      · rcases p7178_3 (m.d 3 5) (by simp) with h7207 | h7207
                                                        · linarith only [h7207, hlam, p7178_0]
                                                        · rcases h5bigk with h7209c | h7209c | h7209c | h7209c | h7209c | h7209c | h7209c | h7209c | h7209c | h7209c | h7209c | h7209c | h7209c | h7209c | h7209c | h7209c | h7209c | h7209c | h7209c | h7209c | h7209c | h7209c | h7209c | h7209c | h7209c
                                                          · have p7209_0 := h7209c.1
                                                            have p7209_1 := h7209c.2.1
                                                            have p7209_2 := h7209c.2.2.1
                                                            have p7209_3 := h7209c.2.2.2
                                                            linarith only [hlam, p7209_0]
                                                          · have p7209_0 := h7209c.1
                                                            have p7209_1 := h7209c.2.1
                                                            have p7209_2 := h7209c.2.2.1
                                                            have p7209_3 := h7209c.2.2.2
                                                            linarith only [h5135, h6924, h7085, h7088, h7090, h7092, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7209_1]
                                                          · have p7209_0 := h7209c.1
                                                            have p7209_1 := h7209c.2.1
                                                            have p7209_2 := h7209c.2.2.1
                                                            have p7209_3 := h7209c.2.2.2
                                                            rcases p7209_3 (m.d 0 5) (by simp) with h7212 | h7212
                                                            · rcases p7209_3 (m.d 1 5) (by simp) with h7213 | h7213
                                                              · linarith only [h6924, h7213, hlam]
                                                              · linarith only [h7087, h7213, hlam]
                                                            · linarith only [h6927, h7212, hlam]
                                                          · have p7209_0 := h7209c.1
                                                            have p7209_1 := h7209c.2.1
                                                            have p7209_2 := h7209c.2.2.1
                                                            have p7209_3 := h7209c.2.2.2
                                                            linarith only [h5135, h6924, h7085, h7092, h7145, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7209_1]
                                                          · have p7209_0 := h7209c.1
                                                            have p7209_1 := h7209c.2.1
                                                            have p7209_2 := h7209c.2.2.1
                                                            have p7209_3 := h7209c.2.2.2
                                                            linarith only [h6930, hlam, p7209_0]
                                                          · have p7209_0 := h7209c.1
                                                            have p7209_1 := h7209c.2.1
                                                            have p7209_2 := h7209c.2.2.1
                                                            have p7209_3 := h7209c.2.2.2
                                                            linarith only [h6924, hlam, p7209_0]
                                                          · have p7209_0 := h7209c.1
                                                            have p7209_1 := h7209c.2.1
                                                            have p7209_2 := h7209c.2.2.1
                                                            have p7209_3 := h7209c.2.2.2
                                                            linarith only [hlam, p7209_0]
                                                          · have p7209_0 := h7209c.1
                                                            have p7209_1 := h7209c.2.1
                                                            have p7209_2 := h7209c.2.2.1
                                                            have p7209_3 := h7209c.2.2.2
                                                            linarith only [h5135, h6924, h7085, h7143, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p7209_1]
                                                          · have p7209_0 := h7209c.1
                                                            have p7209_1 := h7209c.2.1
                                                            have p7209_2 := h7209c.2.2.1
                                                            have p7209_3 := h7209c.2.2.2
                                                            linarith only [h5135, h6924, h7085, h7092, h7145, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7209_1]
                                                          · have p7209_0 := h7209c.1
                                                            have p7209_1 := h7209c.2.1
                                                            have p7209_2 := h7209c.2.2.1
                                                            have p7209_3 := h7209c.2.2.2
                                                            linarith only [h7090, hlam, p7209_0]
                                                          · have p7209_0 := h7209c.1
                                                            have p7209_1 := h7209c.2.1
                                                            have p7209_2 := h7209c.2.2.1
                                                            have p7209_3 := h7209c.2.2.2
                                                            linarith only [h6927, hlam, p7209_1]
                                                          · have p7209_0 := h7209c.1
                                                            have p7209_1 := h7209c.2.1
                                                            have p7209_2 := h7209c.2.2.1
                                                            have p7209_3 := h7209c.2.2.2
                                                            linarith only [h7087, hlam, p7209_1]
                                                          · have p7209_0 := h7209c.1
                                                            have p7209_1 := h7209c.2.1
                                                            have p7209_2 := h7209c.2.2.1
                                                            have p7209_3 := h7209c.2.2.2
                                                            linarith only [hlam, p7209_0]
                                                          · have p7209_0 := h7209c.1
                                                            have p7209_1 := h7209c.2.1
                                                            have p7209_2 := h7209c.2.2.1
                                                            have p7209_3 := h7209c.2.2.2
                                                            linarith only [h7141, hlam, p7209_1]
                                                          · have p7209_0 := h7209c.1
                                                            have p7209_1 := h7209c.2.1
                                                            have p7209_2 := h7209c.2.2.1
                                                            have p7209_3 := h7209c.2.2.2
                                                            linarith only [h7143, hlam, p7209_0]
                                                          · have p7209_0 := h7209c.1
                                                            have p7209_1 := h7209c.2.1
                                                            have p7209_2 := h7209c.2.2.1
                                                            have p7209_3 := h7209c.2.2.2
                                                            linarith only [h6929, hlam, p7209_1]
                                                          · have p7209_0 := h7209c.1
                                                            have p7209_1 := h7209c.2.1
                                                            have p7209_2 := h7209c.2.2.1
                                                            have p7209_3 := h7209c.2.2.2
                                                            linarith only [h7089, hlam, p7209_1]
                                                          · have p7209_0 := h7209c.1
                                                            have p7209_1 := h7209c.2.1
                                                            have p7209_2 := h7209c.2.2.1
                                                            have p7209_3 := h7209c.2.2.2
                                                            linarith only [h7092, h7143, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7178_1, p7209_1]
                                                          · have p7209_0 := h7209c.1
                                                            have p7209_1 := h7209c.2.1
                                                            have p7209_2 := h7209c.2.2.1
                                                            have p7209_3 := h7209c.2.2.2
                                                            linarith only [hlam, p7209_0]
                                                          · have p7209_0 := h7209c.1
                                                            have p7209_1 := h7209c.2.1
                                                            have p7209_2 := h7209c.2.2.1
                                                            have p7209_3 := h7209c.2.2.2
                                                            linarith only [h7145, hlam, p7209_0]
                                                          · have p7209_0 := h7209c.1
                                                            have p7209_1 := h7209c.2.1
                                                            have p7209_2 := h7209c.2.2.1
                                                            have p7209_3 := h7209c.2.2.2
                                                            linarith only [h6923, h6930, h7088, h7092, hc23, hc45, hlam, hphi, ht34, p7209_1]
                                                          · have p7209_0 := h7209c.1
                                                            have p7209_1 := h7209c.2.1
                                                            have p7209_2 := h7209c.2.2.1
                                                            have p7209_3 := h7209c.2.2.2
                                                            linarith only [h7088, h7090, h7092, hc23, hc45, hlam, hphi, ht34, p7209_1]
                                                          · have p7209_0 := h7209c.1
                                                            have p7209_1 := h7209c.2.1
                                                            have p7209_2 := h7209c.2.2.1
                                                            have p7209_3 := h7209c.2.2.2
                                                            rcases p7209_3 (m.d 0 5) (by simp) with h7236 | h7236
                                                            · linarith only [h6930, h7236, hlam]
                                                            · linarith only [h6927, h7236, hlam]
                                                          · have p7209_0 := h7209c.1
                                                            have p7209_1 := h7209c.2.1
                                                            have p7209_2 := h7209c.2.2.1
                                                            have p7209_3 := h7209c.2.2.2
                                                            linarith only [h7141, hc23, hc45, hlam, hphi, ht34, p7209_1]
                                                          · have p7209_0 := h7209c.1
                                                            have p7209_1 := h7209c.2.1
                                                            have p7209_2 := h7209c.2.2.1
                                                            have p7209_3 := h7209c.2.2.2
                                                            linarith only [hlam, p7209_0]
                                                  · linarith only [h7089, h7202, hlam]
                                                · linarith only [h7201, hlam, p7178_0]
                                              · have p7178_0 := h7178c.1
                                                have p7178_1 := h7178c.2.1
                                                have p7178_2 := h7178c.2.2.1
                                                have p7178_3 := h7178c.2.2.2
                                                linarith only [h5135, h6923, h7085, h7088, h7092, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7178_1]
                                              · have p7178_0 := h7178c.1
                                                have p7178_1 := h7178c.2.1
                                                have p7178_2 := h7178c.2.2.1
                                                have p7178_3 := h7178c.2.2.2
                                                linarith only [hlam, p7178_0]
                                              · have p7178_0 := h7178c.1
                                                have p7178_1 := h7178c.2.1
                                                have p7178_2 := h7178c.2.2.1
                                                have p7178_3 := h7178c.2.2.2
                                                linarith only [h5135, h6924, h7088, h7090, h7092, hlam, p7178_2]
                                              · have p7178_0 := h7178c.1
                                                have p7178_1 := h7178c.2.1
                                                have p7178_2 := h7178c.2.2.1
                                                have p7178_3 := h7178c.2.2.2
                                                rcases p7178_3 (m.d 0 3) (by simp) with h7246 | h7246
                                                · linarith only [h5135, h7246, hlam]
                                                · linarith only [h6928, h7246, hlam]
                                              · have p7178_0 := h7178c.1
                                                have p7178_1 := h7178c.2.1
                                                have p7178_2 := h7178c.2.2.1
                                                have p7178_3 := h7178c.2.2.2
                                                rcases p7178_3 (m.d 0 3) (by simp) with h7249 | h7249
                                                · linarith only [h5135, h7249, hlam]
                                                · linarith only [h6929, h7249, hlam]
                                              · have p7178_0 := h7178c.1
                                                have p7178_1 := h7178c.2.1
                                                have p7178_2 := h7178c.2.2.1
                                                have p7178_3 := h7178c.2.2.2
                                                linarith only [h6925, hlam, p7178_1]
                                              · have p7178_0 := h7178c.1
                                                have p7178_1 := h7178c.2.1
                                                have p7178_2 := h7178c.2.2.1
                                                have p7178_3 := h7178c.2.2.2
                                                linarith only [h7085, hlam, p7178_1]
                                              · have p7178_0 := h7178c.1
                                                have p7178_1 := h7178c.2.1
                                                have p7178_2 := h7178c.2.2.1
                                                have p7178_3 := h7178c.2.2.2
                                                linarith only [hlam, p7178_0]
                                              · have p7178_0 := h7178c.1
                                                have p7178_1 := h7178c.2.1
                                                have p7178_2 := h7178c.2.2.1
                                                have p7178_3 := h7178c.2.2.2
                                                linarith only [h7092, hlam, p7178_0]
                                              · have p7178_0 := h7178c.1
                                                have p7178_1 := h7178c.2.1
                                                have p7178_2 := h7178c.2.2.1
                                                have p7178_3 := h7178c.2.2.2
                                                linarith only [h7141, hlam, p7178_0]
                                              · have p7178_0 := h7178c.1
                                                have p7178_1 := h7178c.2.1
                                                have p7178_2 := h7178c.2.2.1
                                                have p7178_3 := h7178c.2.2.2
                                                linarith only [h6928, hlam, p7178_0]
                                              · have p7178_0 := h7178c.1
                                                have p7178_1 := h7178c.2.1
                                                have p7178_2 := h7178c.2.2.1
                                                have p7178_3 := h7178c.2.2.2
                                                linarith only [h7088, hlam, p7178_0]
                                              · have p7178_0 := h7178c.1
                                                have p7178_1 := h7178c.2.1
                                                have p7178_2 := h7178c.2.2.1
                                                have p7178_3 := h7178c.2.2.2
                                                linarith only [h5135, h6924, h7088, h7090, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7178_1]
                                              · have p7178_0 := h7178c.1
                                                have p7178_1 := h7178c.2.1
                                                have p7178_2 := h7178c.2.2.1
                                                have p7178_3 := h7178c.2.2.2
                                                linarith only [hlam, p7178_0]
                                              · have p7178_0 := h7178c.1
                                                have p7178_1 := h7178c.2.1
                                                have p7178_2 := h7178c.2.2.1
                                                have p7178_3 := h7178c.2.2.2
                                                linarith only [h7145, hlam, p7178_0]
                                              · have p7178_0 := h7178c.1
                                                have p7178_1 := h7178c.2.1
                                                have p7178_2 := h7178c.2.2.1
                                                have p7178_3 := h7178c.2.2.2
                                                linarith only [h6929, hlam, p7178_0]
                                              · have p7178_0 := h7178c.1
                                                have p7178_1 := h7178c.2.1
                                                have p7178_2 := h7178c.2.2.1
                                                have p7178_3 := h7178c.2.2.2
                                                linarith only [h7089, hlam, p7178_0]
                                              · have p7178_0 := h7178c.1
                                                have p7178_1 := h7178c.2.1
                                                have p7178_2 := h7178c.2.2.1
                                                have p7178_3 := h7178c.2.2.2
                                                linarith only [h5135, h6924, h7085, h7089, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7178_1]
                                              · have p7178_0 := h7178c.1
                                                have p7178_1 := h7178c.2.1
                                                have p7178_2 := h7178c.2.2.1
                                                have p7178_3 := h7178c.2.2.2
                                                linarith only [h5135, h6924, h7085, h7089, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7178_1]
                                              · have p7178_0 := h7178c.1
                                                have p7178_1 := h7178c.2.1
                                                have p7178_2 := h7178c.2.2.1
                                                have p7178_3 := h7178c.2.2.2
                                                linarith only [hlam, p7178_0]
                                      · linarith only [h7087, h7171, hlam]
                                    · linarith only [h7170, hlam, p7147_0]
                                  · have p7147_0 := h7147c.1
                                    have p7147_1 := h7147c.2.1
                                    have p7147_2 := h7147c.2.2.1
                                    have p7147_3 := h7147c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p7147_1]
                                  · have p7147_0 := h7147c.1
                                    have p7147_1 := h7147c.2.1
                                    have p7147_2 := h7147c.2.2.1
                                    have p7147_3 := h7147c.2.2.2
                                    linarith only [hlam, p7147_0]
                                  · have p7147_0 := h7147c.1
                                    have p7147_1 := h7147c.2.1
                                    have p7147_2 := h7147c.2.2.1
                                    have p7147_3 := h7147c.2.2.2
                                    rcases p7147_3 (m.d 0 2) (by simp) with h7271 | h7271
                                    · linarith only [h0, h7271, hlam]
                                    · linarith only [h6925, h7271, hlam]
                                  · have p7147_0 := h7147c.1
                                    have p7147_1 := h7147c.2.1
                                    have p7147_2 := h7147c.2.2.1
                                    have p7147_3 := h7147c.2.2.2
                                    rcases p7147_3 (m.d 0 2) (by simp) with h7274 | h7274
                                    · linarith only [h0, h7274, hlam]
                                    · linarith only [h6926, h7274, hlam]
                                  · have p7147_0 := h7147c.1
                                    have p7147_1 := h7147c.2.1
                                    have p7147_2 := h7147c.2.2.1
                                    have p7147_3 := h7147c.2.2.2
                                    rcases p7147_3 (m.d 0 2) (by simp) with h7277 | h7277
                                    · linarith only [h0, h7277, hlam]
                                    · linarith only [h6927, h7277, hlam]
                                  · have p7147_0 := h7147c.1
                                    have p7147_1 := h7147c.2.1
                                    have p7147_2 := h7147c.2.2.1
                                    have p7147_3 := h7147c.2.2.2
                                    linarith only [h6925, hlam, p7147_0]
                                  · have p7147_0 := h7147c.1
                                    have p7147_1 := h7147c.2.1
                                    have p7147_2 := h7147c.2.2.1
                                    have p7147_3 := h7147c.2.2.2
                                    linarith only [h7085, hlam, p7147_0]
                                  · have p7147_0 := h7147c.1
                                    have p7147_1 := h7147c.2.1
                                    have p7147_2 := h7147c.2.2.1
                                    have p7147_3 := h7147c.2.2.2
                                    linarith only [hlam, p7147_0]
                                  · have p7147_0 := h7147c.1
                                    have p7147_1 := h7147c.2.1
                                    have p7147_2 := h7147c.2.2.1
                                    have p7147_3 := h7147c.2.2.2
                                    linarith only [h7092, hlam, p7147_1]
                                  · have p7147_0 := h7147c.1
                                    have p7147_1 := h7147c.2.1
                                    have p7147_2 := h7147c.2.2.1
                                    have p7147_3 := h7147c.2.2.2
                                    linarith only [h7141, hlam, p7147_1]
                                  · have p7147_0 := h7147c.1
                                    have p7147_1 := h7147c.2.1
                                    have p7147_2 := h7147c.2.2.1
                                    have p7147_3 := h7147c.2.2.2
                                    linarith only [h6926, hlam, p7147_0]
                                  · have p7147_0 := h7147c.1
                                    have p7147_1 := h7147c.2.1
                                    have p7147_2 := h7147c.2.2.1
                                    have p7147_3 := h7147c.2.2.2
                                    linarith only [h7086, hlam, p7147_0]
                                  · have p7147_0 := h7147c.1
                                    have p7147_1 := h7147c.2.1
                                    have p7147_2 := h7147c.2.2.1
                                    have p7147_3 := h7147c.2.2.2
                                    linarith only [h6926, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7147_1]
                                  · have p7147_0 := h7147c.1
                                    have p7147_1 := h7147c.2.1
                                    have p7147_2 := h7147c.2.2.1
                                    have p7147_3 := h7147c.2.2.2
                                    linarith only [hlam, p7147_0]
                                  · have p7147_0 := h7147c.1
                                    have p7147_1 := h7147c.2.1
                                    have p7147_2 := h7147c.2.2.1
                                    have p7147_3 := h7147c.2.2.2
                                    linarith only [h7143, hlam, p7147_0]
                                  · have p7147_0 := h7147c.1
                                    have p7147_1 := h7147c.2.1
                                    have p7147_2 := h7147c.2.2.1
                                    have p7147_3 := h7147c.2.2.2
                                    linarith only [h6927, hlam, p7147_0]
                                  · have p7147_0 := h7147c.1
                                    have p7147_1 := h7147c.2.1
                                    have p7147_2 := h7147c.2.2.1
                                    have p7147_3 := h7147c.2.2.2
                                    linarith only [h7087, hlam, p7147_0]
                                  · have p7147_0 := h7147c.1
                                    have p7147_1 := h7147c.2.1
                                    have p7147_2 := h7147c.2.2.1
                                    have p7147_3 := h7147c.2.2.2
                                    linarith only [h0, h6927, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7147_1]
                                  · have p7147_0 := h7147c.1
                                    have p7147_1 := h7147c.2.1
                                    have p7147_2 := h7147c.2.2.1
                                    have p7147_3 := h7147c.2.2.2
                                    linarith only [h6924, h7089, h7141, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p7147_1]
                                  · have p7147_0 := h7147c.1
                                    have p7147_1 := h7147c.2.1
                                    have p7147_2 := h7147c.2.2.1
                                    have p7147_3 := h7147c.2.2.2
                                    linarith only [hlam, p7147_0]
                      · linarith only [h5135, h6924, h6929, h7089, hlam]
                    · linarith only [h5135, h6928, h7088, hlam]
                  · linarith only [h0, h6927, h7087, hlam]
                · linarith only [h0, h6926, h7086, hlam]
              · linarith only [h0, h6925, h7085, hlam]
          · linarith only [h5135, h6924, h6929, hlam]
        · linarith only [h5135, h6923, h6928, hlam]
      · linarith only [h5135, h6924, h6925, h6927, hlam]
    · linarith only [h5135, h6923, h6925, h6926, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h7304 | h7304
    · rcases m.htr 0 2 5 (by decide) (by decide) with h7305 | h7305
      · rcases m.htr 0 3 4 (by decide) (by decide) with h7306 | h7306
        · rcases m.htr 0 3 5 (by decide) (by decide) with h7307 | h7307
          · rcases m.htr 0 4 5 (by decide) (by decide) with h7308 | h7308
            · rcases m.htr 1 2 3 (by decide) (by decide) with h7309 | h7309
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7310 | h7310
                · rcases m.htr 1 2 5 (by decide) (by decide) with h7311 | h7311
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h7312 | h7312
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h7313 | h7313
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7314 | h7314
                        · linarith only [h0, h6923, h6925, h7309, h7314, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h0, h6923, h6925, h7308, h7309, h7314, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h6924, h6925, h7307, h7309, h7313, hc03, hc15, hlam, hphi, ht0b, ht5b]
                    · linarith only [h5135, h6923, h7306, h7310, h7312, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h6923, h6925, h7309, h7310, h7311, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h6923, h6925, h7309, h7310, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7321 | h7321
                · rcases m.htr 1 2 5 (by decide) (by decide) with h7322 | h7322
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h7323 | h7323
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h7324 | h7324
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7325 | h7325
                        · linarith only [h0, h6923, h7309, h7325, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h0, h6923, h7308, h7309, h7325, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h5135, h6924, h7307, h7324, hc03, hc15, hlam, hphi, ht0b, ht5b]
                    · linarith only [h5135, h7306, h7323, hlam]
                  · linarith only [h0, h6923, h7305, h7321, h7322, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h7304, h7321, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h7332 | h7332
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7333 | h7333
                · rcases m.htr 1 2 5 (by decide) (by decide) with h7334 | h7334
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h7335 | h7335
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h7336 | h7336
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7337 | h7337
                        · linarith only [h0, h6923, h7308, h7337, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h7339 | h7339
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h7340 | h7340
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h7341 | h7341
                              · linarith only [h6923, h7308, h7333, h7341, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h7343 | h7343
                                · linarith only [h6923, h7308, h7333, h7339, h7343, hlam]
                                · rcases h2bigk with h7345c | h7345c | h7345c | h7345c | h7345c | h7345c | h7345c | h7345c | h7345c | h7345c | h7345c | h7345c | h7345c | h7345c | h7345c | h7345c | h7345c | h7345c | h7345c | h7345c | h7345c | h7345c | h7345c | h7345c | h7345c
                                  · have p7345_0 := h7345c.1
                                    have p7345_1 := h7345c.2.1
                                    have p7345_2 := h7345c.2.2.1
                                    have p7345_3 := h7345c.2.2.2
                                    linarith only [hlam, p7345_0]
                                  · have p7345_0 := h7345c.1
                                    have p7345_1 := h7345c.2.1
                                    have p7345_2 := h7345c.2.2.1
                                    have p7345_3 := h7345c.2.2.2
                                    linarith only [h0, hlam, p7345_0]
                                  · have p7345_0 := h7345c.1
                                    have p7345_1 := h7345c.2.1
                                    have p7345_2 := h7345c.2.2.1
                                    have p7345_3 := h7345c.2.2.2
                                    linarith only [h6925, hlam, p7345_0]
                                  · have p7345_0 := h7345c.1
                                    have p7345_1 := h7345c.2.1
                                    have p7345_2 := h7345c.2.2.1
                                    have p7345_3 := h7345c.2.2.2
                                    linarith only [h6925, h7332, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p7345_1]
                                  · have p7345_0 := h7345c.1
                                    have p7345_1 := h7345c.2.1
                                    have p7345_2 := h7345c.2.2.1
                                    have p7345_3 := h7345c.2.2.2
                                    linarith only [h6925, h7332, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p7345_1]
                                  · have p7345_0 := h7345c.1
                                    have p7345_1 := h7345c.2.1
                                    have p7345_2 := h7345c.2.2.1
                                    have p7345_3 := h7345c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p7345_1]
                                  · have p7345_0 := h7345c.1
                                    have p7345_1 := h7345c.2.1
                                    have p7345_2 := h7345c.2.2.1
                                    have p7345_3 := h7345c.2.2.2
                                    linarith only [hlam, p7345_0]
                                  · have p7345_0 := h7345c.1
                                    have p7345_1 := h7345c.2.1
                                    have p7345_2 := h7345c.2.2.1
                                    have p7345_3 := h7345c.2.2.2
                                    linarith only [h5135, h6924, h6925, h7337, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p7345_1]
                                  · have p7345_0 := h7345c.1
                                    have p7345_1 := h7345c.2.1
                                    have p7345_2 := h7345c.2.2.1
                                    have p7345_3 := h7345c.2.2.2
                                    rcases p7345_3 (m.d 0 2) (by simp) with h7354 | h7354
                                    · linarith only [h0, h7354, hlam]
                                    · linarith only [h7304, h7354, hlam]
                                  · have p7345_0 := h7345c.1
                                    have p7345_1 := h7345c.2.1
                                    have p7345_2 := h7345c.2.2.1
                                    have p7345_3 := h7345c.2.2.2
                                    rcases p7345_3 (m.d 0 2) (by simp) with h7357 | h7357
                                    · linarith only [h0, h7357, hlam]
                                    · linarith only [h7305, h7357, hlam]
                                  · have p7345_0 := h7345c.1
                                    have p7345_1 := h7345c.2.1
                                    have p7345_2 := h7345c.2.2.1
                                    have p7345_3 := h7345c.2.2.2
                                    linarith only [h0, h6924, h7332, h7333, h7337, h7339, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7345_1]
                                  · have p7345_0 := h7345c.1
                                    have p7345_1 := h7345c.2.1
                                    have p7345_2 := h7345c.2.2.1
                                    have p7345_3 := h7345c.2.2.2
                                    linarith only [h7332, hlam, p7345_0]
                                  · have p7345_0 := h7345c.1
                                    have p7345_1 := h7345c.2.1
                                    have p7345_2 := h7345c.2.2.1
                                    have p7345_3 := h7345c.2.2.2
                                    linarith only [hlam, p7345_0]
                                  · have p7345_0 := h7345c.1
                                    have p7345_1 := h7345c.2.1
                                    have p7345_2 := h7345c.2.2.1
                                    have p7345_3 := h7345c.2.2.2
                                    linarith only [h7332, h7339, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7345_1]
                                  · have p7345_0 := h7345c.1
                                    have p7345_1 := h7345c.2.1
                                    have p7345_2 := h7345c.2.2.1
                                    have p7345_3 := h7345c.2.2.2
                                    linarith only [h7332, h7339, h7341, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7345_1]
                                  · have p7345_0 := h7345c.1
                                    have p7345_1 := h7345c.2.1
                                    have p7345_2 := h7345c.2.2.1
                                    have p7345_3 := h7345c.2.2.2
                                    linarith only [h7304, hlam, p7345_0]
                                  · have p7345_0 := h7345c.1
                                    have p7345_1 := h7345c.2.1
                                    have p7345_2 := h7345c.2.2.1
                                    have p7345_3 := h7345c.2.2.2
                                    linarith only [h7333, hlam, p7345_0]
                                  · have p7345_0 := h7345c.1
                                    have p7345_1 := h7345c.2.1
                                    have p7345_2 := h7345c.2.2.1
                                    have p7345_3 := h7345c.2.2.2
                                    linarith only [h7339, hlam, p7345_0]
                                  · have p7345_0 := h7345c.1
                                    have p7345_1 := h7345c.2.1
                                    have p7345_2 := h7345c.2.2.1
                                    have p7345_3 := h7345c.2.2.2
                                    linarith only [hlam, p7345_0]
                                  · have p7345_0 := h7345c.1
                                    have p7345_1 := h7345c.2.1
                                    have p7345_2 := h7345c.2.2.1
                                    have p7345_3 := h7345c.2.2.2
                                    linarith only [h7341, hlam, p7345_0]
                                  · have p7345_0 := h7345c.1
                                    have p7345_1 := h7345c.2.1
                                    have p7345_2 := h7345c.2.2.1
                                    have p7345_3 := h7345c.2.2.2
                                    linarith only [h7305, hlam, p7345_0]
                                  · have p7345_0 := h7345c.1
                                    have p7345_1 := h7345c.2.1
                                    have p7345_2 := h7345c.2.2.1
                                    have p7345_3 := h7345c.2.2.2
                                    linarith only [h7334, hlam, p7345_0]
                                  · have p7345_0 := h7345c.1
                                    have p7345_1 := h7345c.2.1
                                    have p7345_2 := h7345c.2.2.1
                                    have p7345_3 := h7345c.2.2.2
                                    linarith only [h7340, hlam, p7345_0]
                                  · have p7345_0 := h7345c.1
                                    have p7345_1 := h7345c.2.1
                                    have p7345_2 := h7345c.2.2.1
                                    have p7345_3 := h7345c.2.2.2
                                    linarith only [h7305, h7339, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p7345_1]
                                  · have p7345_0 := h7345c.1
                                    have p7345_1 := h7345c.2.1
                                    have p7345_2 := h7345c.2.2.1
                                    have p7345_3 := h7345c.2.2.2
                                    linarith only [hlam, p7345_0]
                            · linarith only [h0, h6924, h6925, h7307, h7333, h7337, h7339, h7340, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h0, h5135, h6925, h7306, h7332, h7339, hc01, hc12, hlam, hphi]
                      · linarith only [h5135, h7307, h7336, hlam]
                    · linarith only [h6925, h7306, h7332, h7335, hlam]
                  · linarith only [h0, h6923, h6925, h7332, h7333, h7334, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h6925, h7332, h7333, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7381 | h7381
                · rcases m.htr 1 2 5 (by decide) (by decide) with h7382 | h7382
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h7383 | h7383
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h7384 | h7384
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7385 | h7385
                        · linarith only [h0, h6923, h7332, h7385, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h7387 | h7387
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h7388 | h7388
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h7389 | h7389
                              · linarith only [h0, h6924, h7308, h7332, h7381, h7385, h7389, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h7391 | h7391
                                · linarith only [h6923, h7308, h7381, h7387, h7391, hlam]
                                · rcases h2bigk with h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c | h7393c
                                  · have p7393_0 := h7393c.1
                                    have p7393_1 := h7393c.2.1
                                    have p7393_2 := h7393c.2.2.1
                                    have p7393_3 := h7393c.2.2.2
                                    linarith only [hlam, p7393_0]
                                  · have p7393_0 := h7393c.1
                                    have p7393_1 := h7393c.2.1
                                    have p7393_2 := h7393c.2.2.1
                                    have p7393_3 := h7393c.2.2.2
                                    linarith only [h0, hlam, p7393_0]
                                  · have p7393_0 := h7393c.1
                                    have p7393_1 := h7393c.2.1
                                    have p7393_2 := h7393c.2.2.1
                                    have p7393_3 := h7393c.2.2.2
                                    linarith only [h6925, hlam, p7393_0]
                                  · have p7393_0 := h7393c.1
                                    have p7393_1 := h7393c.2.1
                                    have p7393_2 := h7393c.2.2.1
                                    have p7393_3 := h7393c.2.2.2
                                    linarith only [h0, h7332, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7393_1]
                                  · have p7393_0 := h7393c.1
                                    have p7393_1 := h7393c.2.1
                                    have p7393_2 := h7393c.2.2.1
                                    have p7393_3 := h7393c.2.2.2
                                    linarith only [h0, h7332, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p7393_1]
                                  · have p7393_0 := h7393c.1
                                    have p7393_1 := h7393c.2.1
                                    have p7393_2 := h7393c.2.2.1
                                    have p7393_3 := h7393c.2.2.2
                                    linarith only [h7332, hc02, hc23, hlam, hphi, p7393_1]
                                  · have p7393_0 := h7393c.1
                                    have p7393_1 := h7393c.2.1
                                    have p7393_2 := h7393c.2.2.1
                                    have p7393_3 := h7393c.2.2.2
                                    linarith only [hlam, p7393_0]
                                  · have p7393_0 := h7393c.1
                                    have p7393_1 := h7393c.2.1
                                    have p7393_2 := h7393c.2.2.1
                                    have p7393_3 := h7393c.2.2.2
                                    linarith only [h7332, hlam, p7393_0]
                                  · have p7393_0 := h7393c.1
                                    have p7393_1 := h7393c.2.1
                                    have p7393_2 := h7393c.2.2.1
                                    have p7393_3 := h7393c.2.2.2
                                    linarith only [h7332, h7387, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7393_1]
                                  · have p7393_0 := h7393c.1
                                    have p7393_1 := h7393c.2.1
                                    have p7393_2 := h7393c.2.2.1
                                    have p7393_3 := h7393c.2.2.2
                                    linarith only [h7332, h7388, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p7393_1]
                                  · have p7393_0 := h7393c.1
                                    have p7393_1 := h7393c.2.1
                                    have p7393_2 := h7393c.2.2.1
                                    have p7393_3 := h7393c.2.2.2
                                    linarith only [h0, hc01, hc23, hlam, hphi, ht12, p7393_1]
                                  · have p7393_0 := h7393c.1
                                    have p7393_1 := h7393c.2.1
                                    have p7393_2 := h7393c.2.2.1
                                    have p7393_3 := h7393c.2.2.2
                                    linarith only [hc12, hc23, hlam, hphi, p7393_1]
                                  · have p7393_0 := h7393c.1
                                    have p7393_1 := h7393c.2.1
                                    have p7393_2 := h7393c.2.2.1
                                    have p7393_3 := h7393c.2.2.2
                                    linarith only [hlam, p7393_0]
                                  · have p7393_0 := h7393c.1
                                    have p7393_1 := h7393c.2.1
                                    have p7393_2 := h7393c.2.2.1
                                    have p7393_3 := h7393c.2.2.2
                                    rcases p7393_3 (m.d 0 2) (by simp) with h7407 | h7407
                                    · linarith only [h6925, h7407, hlam]
                                    · linarith only [h7304, h7407, hlam]
                                  · have p7393_0 := h7393c.1
                                    have p7393_1 := h7393c.2.1
                                    have p7393_2 := h7393c.2.2.1
                                    have p7393_3 := h7393c.2.2.2
                                    rcases p7393_3 (m.d 0 2) (by simp) with h7410 | h7410
                                    · linarith only [h6925, h7410, hlam]
                                    · linarith only [h7305, h7410, hlam]
                                  · have p7393_0 := h7393c.1
                                    have p7393_1 := h7393c.2.1
                                    have p7393_2 := h7393c.2.2.1
                                    have p7393_3 := h7393c.2.2.2
                                    linarith only [h7304, hlam, p7393_0]
                                  · have p7393_0 := h7393c.1
                                    have p7393_1 := h7393c.2.1
                                    have p7393_2 := h7393c.2.2.1
                                    have p7393_3 := h7393c.2.2.2
                                    linarith only [h7381, hlam, p7393_0]
                                  · have p7393_0 := h7393c.1
                                    have p7393_1 := h7393c.2.1
                                    have p7393_2 := h7393c.2.2.1
                                    have p7393_3 := h7393c.2.2.2
                                    linarith only [h7387, hlam, p7393_0]
                                  · have p7393_0 := h7393c.1
                                    have p7393_1 := h7393c.2.1
                                    have p7393_2 := h7393c.2.2.1
                                    have p7393_3 := h7393c.2.2.2
                                    linarith only [hlam, p7393_0]
                                  · have p7393_0 := h7393c.1
                                    have p7393_1 := h7393c.2.1
                                    have p7393_2 := h7393c.2.2.1
                                    have p7393_3 := h7393c.2.2.2
                                    linarith only [h7389, hlam, p7393_0]
                                  · have p7393_0 := h7393c.1
                                    have p7393_1 := h7393c.2.1
                                    have p7393_2 := h7393c.2.2.1
                                    have p7393_3 := h7393c.2.2.2
                                    linarith only [h7305, hlam, p7393_0]
                                  · have p7393_0 := h7393c.1
                                    have p7393_1 := h7393c.2.1
                                    have p7393_2 := h7393c.2.2.1
                                    have p7393_3 := h7393c.2.2.2
                                    linarith only [h7382, hlam, p7393_0]
                                  · have p7393_0 := h7393c.1
                                    have p7393_1 := h7393c.2.1
                                    have p7393_2 := h7393c.2.2.1
                                    have p7393_3 := h7393c.2.2.2
                                    linarith only [h7388, hlam, p7393_0]
                                  · have p7393_0 := h7393c.1
                                    have p7393_1 := h7393c.2.1
                                    have p7393_2 := h7393c.2.2.1
                                    have p7393_3 := h7393c.2.2.2
                                    linarith only [h7305, h7387, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p7393_1]
                                  · have p7393_0 := h7393c.1
                                    have p7393_1 := h7393c.2.1
                                    have p7393_2 := h7393c.2.2.1
                                    have p7393_3 := h7393c.2.2.2
                                    linarith only [hlam, p7393_0]
                            · linarith only [h0, h6924, h7332, h7381, h7385, h7387, h7388, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h6924, h7332, h7381, h7385, h7387, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h5135, h7307, h7384, hlam]
                    · linarith only [h5135, h7306, h7383, hlam]
                  · linarith only [h0, h6924, h7305, h7382, hc02, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h7304, h7381, hlam]
          · linarith only [h0, h6924, h6925, h7307, hlam]
        · linarith only [h0, h6923, h6925, h7306, hlam]
      · linarith only [h0, h6924, h7305, hlam]
    · linarith only [h0, h6923, h7304, hlam]

end R2N4
