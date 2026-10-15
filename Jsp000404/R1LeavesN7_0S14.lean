import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S13

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10278000 in
set_option maxHeartbeats 10278000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s15_x1_x1_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h4129 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h6948 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h7434 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h7435 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  rcases m.htr 2 3 5 (by decide) (by decide) with h7931 | h7931
  · linarith only [h10, h6948, h7435, h7931, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 2 4 5 (by decide) (by decide) with h7933 | h7933
    · rcases m.htr 3 4 5 (by decide) (by decide) with h7934 | h7934
      · rcases h1bigk with h7935c | h7935c | h7935c | h7935c | h7935c | h7935c | h7935c | h7935c | h7935c | h7935c | h7935c | h7935c | h7935c | h7935c | h7935c | h7935c | h7935c | h7935c | h7935c | h7935c | h7935c | h7935c | h7935c | h7935c | h7935c
        · have p7935_0 := h7935c.1
          have p7935_1 := h7935c.2.1
          have p7935_2 := h7935c.2.2.1
          have p7935_3 := h7935c.2.2.2
          linarith only [hlam, p7935_0]
        · have p7935_0 := h7935c.1
          have p7935_1 := h7935c.2.1
          have p7935_2 := h7935c.2.2.1
          have p7935_3 := h7935c.2.2.2
          linarith only [h0, h10, h4, h7, h7931, h7934, hlam, p7935_2]
        · have p7935_0 := h7935c.1
          have p7935_1 := h7935c.2.1
          have p7935_2 := h7935c.2.2.1
          have p7935_3 := h7935c.2.2.2
          rcases p7935_3 (m.d 0 1) (by simp) with h7938 | h7938
          · rcases p7935_3 (m.d 1 2) (by simp) with h7939 | h7939
            · linarith only [h0, h7939, hlam]
            · rcases p7935_3 (m.d 1 3) (by simp) with h7941 | h7941
              · linarith only [h7941, hlam, p7935_0]
              · rcases p7935_3 (m.d 1 4) (by simp) with h7943 | h7943
                · linarith only [h2, h7943, hlam]
                · linarith only [h4129, h7943, hlam]
          · linarith only [h7938, hlam, p7935_0]
        · have p7935_0 := h7935c.1
          have p7935_1 := h7935c.2.1
          have p7935_2 := h7935c.2.2.1
          have p7935_3 := h7935c.2.2.2
          rcases p7935_3 (m.d 0 1) (by simp) with h7947 | h7947
          · rcases p7935_3 (m.d 1 2) (by simp) with h7948 | h7948
            · linarith only [h0, h7948, hlam]
            · rcases p7935_3 (m.d 1 3) (by simp) with h7950 | h7950
              · linarith only [h1, h7950, hlam]
              · rcases p7935_3 (m.d 1 4) (by simp) with h7952 | h7952
                · linarith only [h7952, hlam, p7935_0]
                · rcases p7935_3 (m.d 1 5) (by simp) with h7954 | h7954
                  · linarith only [h3, h7954, hlam]
                  · rcases h1emax with h7956 | h7956 | h7956 | h7956 | h7956
                    · linarith only [h0, h10, h4, h7, h7931, h7934, h7956, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases h2bigk with h7958c | h7958c | h7958c | h7958c | h7958c | h7958c | h7958c | h7958c | h7958c | h7958c | h7958c | h7958c | h7958c | h7958c | h7958c | h7958c | h7958c | h7958c | h7958c | h7958c | h7958c | h7958c | h7958c | h7958c | h7958c
                      · have p7958_0 := h7958c.1
                        have p7958_1 := h7958c.2.1
                        have p7958_2 := h7958c.2.2.1
                        have p7958_3 := h7958c.2.2.2
                        linarith only [hlam, p7958_0]
                      · have p7958_0 := h7958c.1
                        have p7958_1 := h7958c.2.1
                        have p7958_2 := h7958c.2.2.1
                        have p7958_3 := h7958c.2.2.2
                        linarith only [h10, h4, h7, h7931, h7934, hlam, p7958_2]
                      · have p7958_0 := h7958c.1
                        have p7958_1 := h7958c.2.1
                        have p7958_2 := h7958c.2.2.1
                        have p7958_3 := h7958c.2.2.2
                        rcases p7958_3 (m.d 0 2) (by simp) with h7961 | h7961
                        · rcases p7958_3 (m.d 1 2) (by simp) with h7962 | h7962
                          · linarith only [h0, h7962, hlam]
                          · rcases p7958_3 (m.d 2 3) (by simp) with h7964 | h7964
                            · linarith only [h7964, hlam, p7958_0]
                            · rcases p7958_3 (m.d 2 4) (by simp) with h7966 | h7966
                              · linarith only [h5, h7966, hlam]
                              · linarith only [h7435, h7966, hlam]
                        · linarith only [h7961, hlam, p7958_0]
                      · have p7958_0 := h7958c.1
                        have p7958_1 := h7958c.2.1
                        have p7958_2 := h7958c.2.2.1
                        have p7958_3 := h7958c.2.2.2
                        rcases p7958_3 (m.d 0 2) (by simp) with h7970 | h7970
                        · rcases p7958_3 (m.d 1 2) (by simp) with h7971 | h7971
                          · linarith only [h0, h7971, hlam]
                          · rcases p7958_3 (m.d 2 3) (by simp) with h7973 | h7973
                            · linarith only [h4, h7973, hlam]
                            · rcases p7958_3 (m.d 2 4) (by simp) with h7975 | h7975
                              · linarith only [h7975, hlam, p7958_0]
                              · rcases p7958_3 (m.d 2 5) (by simp) with h7977 | h7977
                                · linarith only [h6, h7977, hlam]
                                · rcases h4bigk with h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c | h7979c
                                  · have p7979_0 := h7979c.1
                                    have p7979_1 := h7979c.2.1
                                    have p7979_2 := h7979c.2.2.1
                                    have p7979_3 := h7979c.2.2.2
                                    linarith only [hlam, p7979_0]
                                  · have p7979_0 := h7979c.1
                                    have p7979_1 := h7979c.2.1
                                    have p7979_2 := h7979c.2.2.1
                                    have p7979_3 := h7979c.2.2.2
                                    rcases p7979_3 (m.d 0 4) (by simp) with h7981 | h7981
                                    · rcases p7979_3 (m.d 1 4) (by simp) with h7982 | h7982
                                      · linarith only [h2, h7982, hlam]
                                      · rcases p7979_3 (m.d 2 4) (by simp) with h7984 | h7984
                                        · linarith only [h5, h7984, hlam]
                                        · linarith only [h3576, h7984, hlam]
                                    · linarith only [h2, h7981, hlam]
                                  · have p7979_0 := h7979c.1
                                    have p7979_1 := h7979c.2.1
                                    have p7979_2 := h7979c.2.2.1
                                    have p7979_3 := h7979c.2.2.2
                                    rcases p7979_3 (m.d 0 4) (by simp) with h7988 | h7988
                                    · rcases p7979_3 (m.d 1 4) (by simp) with h7989 | h7989
                                      · linarith only [h2, h7989, hlam]
                                      · rcases p7979_3 (m.d 2 4) (by simp) with h7991 | h7991
                                        · linarith only [h5, h7991, hlam]
                                        · rcases p7979_3 (m.d 3 4) (by simp) with h7993 | h7993
                                          · linarith only [h7, h7993, hlam]
                                          · linarith only [h7435, h7993, hlam]
                                    · linarith only [h5, h7988, hlam]
                                  · have p7979_0 := h7979c.1
                                    have p7979_1 := h7979c.2.1
                                    have p7979_2 := h7979c.2.2.1
                                    have p7979_3 := h7979c.2.2.2
                                    linarith only [h0, h10, h4, h7, h7435, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7979_1]
                                  · have p7979_0 := h7979c.1
                                    have p7979_1 := h7979c.2.1
                                    have p7979_2 := h7979c.2.2.1
                                    have p7979_3 := h7979c.2.2.2
                                    rcases p7979_3 (m.d 0 4) (by simp) with h7998 | h7998
                                    · rcases p7979_3 (m.d 1 4) (by simp) with h7999 | h7999
                                      · linarith only [h2, h7999, hlam]
                                      · linarith only [h7434, h7999, hlam]
                                    · linarith only [h7998, hlam, p7979_0]
                                  · have p7979_0 := h7979c.1
                                    have p7979_1 := h7979c.2.1
                                    have p7979_2 := h7979c.2.2.1
                                    have p7979_3 := h7979c.2.2.2
                                    linarith only [h2, hlam, p7979_0]
                                  · have p7979_0 := h7979c.1
                                    have p7979_1 := h7979c.2.1
                                    have p7979_2 := h7979c.2.2.1
                                    have p7979_3 := h7979c.2.2.2
                                    linarith only [hlam, p7979_0]
                                  · have p7979_0 := h7979c.1
                                    have p7979_1 := h7979c.2.1
                                    have p7979_2 := h7979c.2.2.1
                                    have p7979_3 := h7979c.2.2.2
                                    linarith only [h3576, hlam, p7979_1]
                                  · have p7979_0 := h7979c.1
                                    have p7979_1 := h7979c.2.1
                                    have p7979_2 := h7979c.2.2.1
                                    have p7979_3 := h7979c.2.2.2
                                    linarith only [h4129, hlam, p7979_1]
                                  · have p7979_0 := h7979c.1
                                    have p7979_1 := h7979c.2.1
                                    have p7979_2 := h7979c.2.2.1
                                    have p7979_3 := h7979c.2.2.2
                                    linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p7935_1, p7979_1]
                                  · have p7979_0 := h7979c.1
                                    have p7979_1 := h7979c.2.1
                                    have p7979_2 := h7979c.2.2.1
                                    have p7979_3 := h7979c.2.2.2
                                    linarith only [h5, hlam, p7979_0]
                                  · have p7979_0 := h7979c.1
                                    have p7979_1 := h7979c.2.1
                                    have p7979_2 := h7979c.2.2.1
                                    have p7979_3 := h7979c.2.2.2
                                    linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p7958_1, p7979_1]
                                  · have p7979_0 := h7979c.1
                                    have p7979_1 := h7979c.2.1
                                    have p7979_2 := h7979c.2.2.1
                                    have p7979_3 := h7979c.2.2.2
                                    linarith only [hlam, p7979_0]
                                  · have p7979_0 := h7979c.1
                                    have p7979_1 := h7979c.2.1
                                    have p7979_2 := h7979c.2.2.1
                                    have p7979_3 := h7979c.2.2.2
                                    linarith only [h7435, hlam, p7979_1]
                                  · have p7979_0 := h7979c.1
                                    have p7979_1 := h7979c.2.1
                                    have p7979_2 := h7979c.2.2.1
                                    have p7979_3 := h7979c.2.2.2
                                    linarith only [h0, hc01, hc45, hlam, hphi, ht0b, ht5b, p7958_1, p7979_1]
                                  · have p7979_0 := h7979c.1
                                    have p7979_1 := h7979c.2.1
                                    have p7979_2 := h7979c.2.2.1
                                    have p7979_3 := h7979c.2.2.2
                                    linarith only [h7, hlam, p7979_0]
                                  · have p7979_0 := h7979c.1
                                    have p7979_1 := h7979c.2.1
                                    have p7979_2 := h7979c.2.2.1
                                    have p7979_3 := h7979c.2.2.2
                                    linarith only [h0, h4, h7, h7434, hc01, hc45, hlam, hphi, ht0b, ht5b, p7979_1]
                                  · have p7979_0 := h7979c.1
                                    have p7979_1 := h7979c.2.1
                                    have p7979_2 := h7979c.2.2.1
                                    have p7979_3 := h7979c.2.2.2
                                    linarith only [h4, h7, hlam, p7958_2, p7979_1]
                                  · have p7979_0 := h7979c.1
                                    have p7979_1 := h7979c.2.1
                                    have p7979_2 := h7979c.2.2.1
                                    have p7979_3 := h7979c.2.2.2
                                    linarith only [hlam, p7979_0]
                                  · have p7979_0 := h7979c.1
                                    have p7979_1 := h7979c.2.1
                                    have p7979_2 := h7979c.2.2.1
                                    have p7979_3 := h7979c.2.2.2
                                    rcases p7979_3 (m.d 0 4) (by simp) with h8017 | h8017
                                    · rcases p7979_3 (m.d 1 4) (by simp) with h8018 | h8018
                                      · linarith only [h4129, h8018, hlam]
                                      · linarith only [h7434, h8018, hlam]
                                    · linarith only [h8017, h9, hlam]
                                  · have p7979_0 := h7979c.1
                                    have p7979_1 := h7979c.2.1
                                    have p7979_2 := h7979c.2.2.1
                                    have p7979_3 := h7979c.2.2.2
                                    linarith only [h9, hlam, p7979_0]
                                  · have p7979_0 := h7979c.1
                                    have p7979_1 := h7979c.2.1
                                    have p7979_2 := h7979c.2.2.1
                                    have p7979_3 := h7979c.2.2.2
                                    linarith only [h7434, hlam, p7979_0]
                                  · have p7979_0 := h7979c.1
                                    have p7979_1 := h7979c.2.1
                                    have p7979_2 := h7979c.2.2.1
                                    have p7979_3 := h7979c.2.2.2
                                    linarith only [h7933, hlam, p7979_0]
                                  · have p7979_0 := h7979c.1
                                    have p7979_1 := h7979c.2.1
                                    have p7979_2 := h7979c.2.2.1
                                    have p7979_3 := h7979c.2.2.2
                                    linarith only [h7934, hlam, p7979_0]
                                  · have p7979_0 := h7979c.1
                                    have p7979_1 := h7979c.2.1
                                    have p7979_2 := h7979c.2.2.1
                                    have p7979_3 := h7979c.2.2.2
                                    linarith only [hlam, p7979_0]
                        · linarith only [h7970, hlam, p7958_0]
                      · have p7958_0 := h7958c.1
                        have p7958_1 := h7958c.2.1
                        have p7958_2 := h7958c.2.2.1
                        have p7958_3 := h7958c.2.2.2
                        rcases p7958_3 (m.d 0 2) (by simp) with h8028 | h8028
                        · rcases p7958_3 (m.d 1 2) (by simp) with h8029 | h8029
                          · linarith only [h0, h8029, hlam]
                          · rcases p7958_3 (m.d 2 3) (by simp) with h8031 | h8031
                            · linarith only [h4, h8031, hlam]
                            · rcases p7958_3 (m.d 2 4) (by simp) with h8033 | h8033
                              · linarith only [h5, h8033, hlam]
                              · linarith only [h7933, h8033, hlam]
                        · linarith only [h8028, hlam, p7958_0]
                      · have p7958_0 := h7958c.1
                        have p7958_1 := h7958c.2.1
                        have p7958_2 := h7958c.2.2.1
                        have p7958_3 := h7958c.2.2.2
                        linarith only [h0, hlam, p7958_1]
                      · have p7958_0 := h7958c.1
                        have p7958_1 := h7958c.2.1
                        have p7958_2 := h7958c.2.2.1
                        have p7958_3 := h7958c.2.2.2
                        linarith only [hlam, p7958_0]
                      · have p7958_0 := h7958c.1
                        have p7958_1 := h7958c.2.1
                        have p7958_2 := h7958c.2.2.1
                        have p7958_3 := h7958c.2.2.2
                        linarith only [h10, hlam, p7958_0]
                      · have p7958_0 := h7958c.1
                        have p7958_1 := h7958c.2.1
                        have p7958_2 := h7958c.2.2.1
                        have p7958_3 := h7958c.2.2.2
                        linarith only [h3576, hlam, p7958_0]
                      · have p7958_0 := h7958c.1
                        have p7958_1 := h7958c.2.1
                        have p7958_2 := h7958c.2.2.1
                        have p7958_3 := h7958c.2.2.2
                        linarith only [h4058, hlam, p7958_0]
                      · have p7958_0 := h7958c.1
                        have p7958_1 := h7958c.2.1
                        have p7958_2 := h7958c.2.2.1
                        have p7958_3 := h7958c.2.2.2
                        linarith only [h4, hlam, p7958_0]
                      · have p7958_0 := h7958c.1
                        have p7958_1 := h7958c.2.1
                        have p7958_2 := h7958c.2.2.1
                        have p7958_3 := h7958c.2.2.2
                        linarith only [h7931, hc12, hc35, hlam, hphi, ht23, p7958_1]
                      · have p7958_0 := h7958c.1
                        have p7958_1 := h7958c.2.1
                        have p7958_2 := h7958c.2.2.1
                        have p7958_3 := h7958c.2.2.2
                        linarith only [hlam, p7958_0]
                      · have p7958_0 := h7958c.1
                        have p7958_1 := h7958c.2.1
                        have p7958_2 := h7958c.2.2.1
                        have p7958_3 := h7958c.2.2.2
                        linarith only [h7435, hlam, p7958_1]
                      · have p7958_0 := h7958c.1
                        have p7958_1 := h7958c.2.1
                        have p7958_2 := h7958c.2.2.1
                        have p7958_3 := h7958c.2.2.2
                        linarith only [h7931, hlam, p7958_1]
                      · have p7958_0 := h7958c.1
                        have p7958_1 := h7958c.2.1
                        have p7958_2 := h7958c.2.2.1
                        have p7958_3 := h7958c.2.2.2
                        linarith only [h5, hlam, p7958_0]
                      · have p7958_0 := h7958c.1
                        have p7958_1 := h7958c.2.1
                        have p7958_2 := h7958c.2.2.1
                        have p7958_3 := h7958c.2.2.2
                        rcases p7958_3 (m.d 0 2) (by simp) with h8048 | h8048
                        · rcases p7958_3 (m.d 1 2) (by simp) with h8049 | h8049
                          · linarith only [h8049, hlam, p7958_0]
                          · rcases p7958_3 (m.d 2 3) (by simp) with h8051 | h8051
                            · linarith only [h7435, h8051, hlam]
                            · linarith only [h10, h8051, hlam]
                        · linarith only [h0, h8048, hlam]
                      · have p7958_0 := h7958c.1
                        have p7958_1 := h7958c.2.1
                        have p7958_2 := h7958c.2.2.1
                        have p7958_3 := h7958c.2.2.2
                        linarith only [h0, h10, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7958_1]
                      · have p7958_0 := h7958c.1
                        have p7958_1 := h7958c.2.1
                        have p7958_2 := h7958c.2.2.1
                        have p7958_3 := h7958c.2.2.2
                        linarith only [hlam, p7958_0]
                      · have p7958_0 := h7958c.1
                        have p7958_1 := h7958c.2.1
                        have p7958_2 := h7958c.2.2.1
                        have p7958_3 := h7958c.2.2.2
                        linarith only [h0, h10, h4, h7, h7435, h7931, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7958_1]
                      · have p7958_0 := h7958c.1
                        have p7958_1 := h7958c.2.1
                        have p7958_2 := h7958c.2.2.1
                        have p7958_3 := h7958c.2.2.2
                        linarith only [h6, hlam, p7958_0]
                      · have p7958_0 := h7958c.1
                        have p7958_1 := h7958c.2.1
                        have p7958_2 := h7958c.2.2.1
                        have p7958_3 := h7958c.2.2.2
                        rcases p7958_3 (m.d 0 2) (by simp) with h8059 | h8059
                        · rcases p7958_3 (m.d 1 2) (by simp) with h8060 | h8060
                          · linarith only [h8060, hlam, p7958_0]
                          · rcases p7958_3 (m.d 2 3) (by simp) with h8062 | h8062
                            · linarith only [h7931, h8062, hlam]
                            · linarith only [h10, h8062, hlam]
                        · linarith only [h0, h8059, hlam]
                      · have p7958_0 := h7958c.1
                        have p7958_1 := h7958c.2.1
                        have p7958_2 := h7958c.2.2.1
                        have p7958_3 := h7958c.2.2.2
                        linarith only [h10, hc12, hc25, hlam, hphi, p7958_1]
                      · have p7958_0 := h7958c.1
                        have p7958_1 := h7958c.2.1
                        have p7958_2 := h7958c.2.2.1
                        have p7958_3 := h7958c.2.2.2
                        linarith only [h7933, hlam, p7958_1]
                      · have p7958_0 := h7958c.1
                        have p7958_1 := h7958c.2.1
                        have p7958_2 := h7958c.2.2.1
                        have p7958_3 := h7958c.2.2.2
                        linarith only [hlam, p7958_0]
                    · rcases h2bigk with h8069c | h8069c | h8069c | h8069c | h8069c | h8069c | h8069c | h8069c | h8069c | h8069c | h8069c | h8069c | h8069c | h8069c | h8069c | h8069c | h8069c | h8069c | h8069c | h8069c | h8069c | h8069c | h8069c | h8069c | h8069c
                      · have p8069_0 := h8069c.1
                        have p8069_1 := h8069c.2.1
                        have p8069_2 := h8069c.2.2.1
                        have p8069_3 := h8069c.2.2.2
                        linarith only [hlam, p8069_0]
                      · have p8069_0 := h8069c.1
                        have p8069_1 := h8069c.2.1
                        have p8069_2 := h8069c.2.2.1
                        have p8069_3 := h8069c.2.2.2
                        linarith only [h10, h4, h7, h7435, hlam, p8069_2]
                      · have p8069_0 := h8069c.1
                        have p8069_1 := h8069c.2.1
                        have p8069_2 := h8069c.2.2.1
                        have p8069_3 := h8069c.2.2.2
                        rcases p8069_3 (m.d 0 2) (by simp) with h8072 | h8072
                        · rcases p8069_3 (m.d 1 2) (by simp) with h8073 | h8073
                          · linarith only [h0, h8073, hlam]
                          · rcases p8069_3 (m.d 2 3) (by simp) with h8075 | h8075
                            · linarith only [h8075, hlam, p8069_0]
                            · rcases p8069_3 (m.d 2 4) (by simp) with h8077 | h8077
                              · linarith only [h5, h8077, hlam]
                              · linarith only [h7435, h8077, hlam]
                        · linarith only [h8072, hlam, p8069_0]
                      · have p8069_0 := h8069c.1
                        have p8069_1 := h8069c.2.1
                        have p8069_2 := h8069c.2.2.1
                        have p8069_3 := h8069c.2.2.2
                        rcases p8069_3 (m.d 0 2) (by simp) with h8081 | h8081
                        · rcases p8069_3 (m.d 1 2) (by simp) with h8082 | h8082
                          · linarith only [h0, h8082, hlam]
                          · rcases p8069_3 (m.d 2 3) (by simp) with h8084 | h8084
                            · linarith only [h4, h8084, hlam]
                            · rcases p8069_3 (m.d 2 4) (by simp) with h8086 | h8086
                              · linarith only [h8086, hlam, p8069_0]
                              · rcases p8069_3 (m.d 2 5) (by simp) with h8088 | h8088
                                · linarith only [h6, h8088, hlam]
                                · rcases h4bigk with h8090c | h8090c | h8090c | h8090c | h8090c | h8090c | h8090c | h8090c | h8090c | h8090c | h8090c | h8090c | h8090c | h8090c | h8090c | h8090c | h8090c | h8090c | h8090c | h8090c | h8090c | h8090c | h8090c | h8090c | h8090c
                                  · have p8090_0 := h8090c.1
                                    have p8090_1 := h8090c.2.1
                                    have p8090_2 := h8090c.2.2.1
                                    have p8090_3 := h8090c.2.2.2
                                    linarith only [hlam, p8090_0]
                                  · have p8090_0 := h8090c.1
                                    have p8090_1 := h8090c.2.1
                                    have p8090_2 := h8090c.2.2.1
                                    have p8090_3 := h8090c.2.2.2
                                    rcases p8090_3 (m.d 0 4) (by simp) with h8092 | h8092
                                    · rcases p8090_3 (m.d 1 4) (by simp) with h8093 | h8093
                                      · linarith only [h2, h8093, hlam]
                                      · rcases p8090_3 (m.d 2 4) (by simp) with h8095 | h8095
                                        · linarith only [h5, h8095, hlam]
                                        · linarith only [h3576, h8095, hlam]
                                    · linarith only [h2, h8092, hlam]
                                  · have p8090_0 := h8090c.1
                                    have p8090_1 := h8090c.2.1
                                    have p8090_2 := h8090c.2.2.1
                                    have p8090_3 := h8090c.2.2.2
                                    rcases p8090_3 (m.d 0 4) (by simp) with h8099 | h8099
                                    · rcases p8090_3 (m.d 1 4) (by simp) with h8100 | h8100
                                      · linarith only [h2, h8100, hlam]
                                      · rcases p8090_3 (m.d 2 4) (by simp) with h8102 | h8102
                                        · linarith only [h5, h8102, hlam]
                                        · rcases p8090_3 (m.d 3 4) (by simp) with h8104 | h8104
                                          · linarith only [h7, h8104, hlam]
                                          · linarith only [h7435, h8104, hlam]
                                    · linarith only [h5, h8099, hlam]
                                  · have p8090_0 := h8090c.1
                                    have p8090_1 := h8090c.2.1
                                    have p8090_2 := h8090c.2.2.1
                                    have p8090_3 := h8090c.2.2.2
                                    linarith only [h0, h10, h4, h7, h7435, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8090_1]
                                  · have p8090_0 := h8090c.1
                                    have p8090_1 := h8090c.2.1
                                    have p8090_2 := h8090c.2.2.1
                                    have p8090_3 := h8090c.2.2.2
                                    rcases p8090_3 (m.d 0 4) (by simp) with h8109 | h8109
                                    · rcases p8090_3 (m.d 1 4) (by simp) with h8110 | h8110
                                      · linarith only [h2, h8110, hlam]
                                      · linarith only [h7434, h8110, hlam]
                                    · linarith only [h8109, hlam, p8090_0]
                                  · have p8090_0 := h8090c.1
                                    have p8090_1 := h8090c.2.1
                                    have p8090_2 := h8090c.2.2.1
                                    have p8090_3 := h8090c.2.2.2
                                    linarith only [h2, hlam, p8090_0]
                                  · have p8090_0 := h8090c.1
                                    have p8090_1 := h8090c.2.1
                                    have p8090_2 := h8090c.2.2.1
                                    have p8090_3 := h8090c.2.2.2
                                    linarith only [hlam, p8090_0]
                                  · have p8090_0 := h8090c.1
                                    have p8090_1 := h8090c.2.1
                                    have p8090_2 := h8090c.2.2.1
                                    have p8090_3 := h8090c.2.2.2
                                    linarith only [h3576, hlam, p8090_1]
                                  · have p8090_0 := h8090c.1
                                    have p8090_1 := h8090c.2.1
                                    have p8090_2 := h8090c.2.2.1
                                    have p8090_3 := h8090c.2.2.2
                                    linarith only [h4129, hlam, p8090_1]
                                  · have p8090_0 := h8090c.1
                                    have p8090_1 := h8090c.2.1
                                    have p8090_2 := h8090c.2.2.1
                                    have p8090_3 := h8090c.2.2.2
                                    linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p7935_1, p8090_1]
                                  · have p8090_0 := h8090c.1
                                    have p8090_1 := h8090c.2.1
                                    have p8090_2 := h8090c.2.2.1
                                    have p8090_3 := h8090c.2.2.2
                                    linarith only [h5, hlam, p8090_0]
                                  · have p8090_0 := h8090c.1
                                    have p8090_1 := h8090c.2.1
                                    have p8090_2 := h8090c.2.2.1
                                    have p8090_3 := h8090c.2.2.2
                                    linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p8069_1, p8090_1]
                                  · have p8090_0 := h8090c.1
                                    have p8090_1 := h8090c.2.1
                                    have p8090_2 := h8090c.2.2.1
                                    have p8090_3 := h8090c.2.2.2
                                    linarith only [hlam, p8090_0]
                                  · have p8090_0 := h8090c.1
                                    have p8090_1 := h8090c.2.1
                                    have p8090_2 := h8090c.2.2.1
                                    have p8090_3 := h8090c.2.2.2
                                    linarith only [h7435, hlam, p8090_1]
                                  · have p8090_0 := h8090c.1
                                    have p8090_1 := h8090c.2.1
                                    have p8090_2 := h8090c.2.2.1
                                    have p8090_3 := h8090c.2.2.2
                                    linarith only [h0, hc01, hc45, hlam, hphi, ht0b, ht5b, p8069_1, p8090_1]
                                  · have p8090_0 := h8090c.1
                                    have p8090_1 := h8090c.2.1
                                    have p8090_2 := h8090c.2.2.1
                                    have p8090_3 := h8090c.2.2.2
                                    linarith only [h7, hlam, p8090_0]
                                  · have p8090_0 := h8090c.1
                                    have p8090_1 := h8090c.2.1
                                    have p8090_2 := h8090c.2.2.1
                                    have p8090_3 := h8090c.2.2.2
                                    linarith only [h0, h4, h7, h7434, hc01, hc45, hlam, hphi, ht0b, ht5b, p8090_1]
                                  · have p8090_0 := h8090c.1
                                    have p8090_1 := h8090c.2.1
                                    have p8090_2 := h8090c.2.2.1
                                    have p8090_3 := h8090c.2.2.2
                                    linarith only [h4, h7, hlam, p8069_2, p8090_1]
                                  · have p8090_0 := h8090c.1
                                    have p8090_1 := h8090c.2.1
                                    have p8090_2 := h8090c.2.2.1
                                    have p8090_3 := h8090c.2.2.2
                                    linarith only [hlam, p8090_0]
                                  · have p8090_0 := h8090c.1
                                    have p8090_1 := h8090c.2.1
                                    have p8090_2 := h8090c.2.2.1
                                    have p8090_3 := h8090c.2.2.2
                                    rcases p8090_3 (m.d 0 4) (by simp) with h8128 | h8128
                                    · rcases p8090_3 (m.d 1 4) (by simp) with h8129 | h8129
                                      · linarith only [h4129, h8129, hlam]
                                      · linarith only [h7434, h8129, hlam]
                                    · linarith only [h8128, h9, hlam]
                                  · have p8090_0 := h8090c.1
                                    have p8090_1 := h8090c.2.1
                                    have p8090_2 := h8090c.2.2.1
                                    have p8090_3 := h8090c.2.2.2
                                    linarith only [h9, hlam, p8090_0]
                                  · have p8090_0 := h8090c.1
                                    have p8090_1 := h8090c.2.1
                                    have p8090_2 := h8090c.2.2.1
                                    have p8090_3 := h8090c.2.2.2
                                    linarith only [h7434, hlam, p8090_0]
                                  · have p8090_0 := h8090c.1
                                    have p8090_1 := h8090c.2.1
                                    have p8090_2 := h8090c.2.2.1
                                    have p8090_3 := h8090c.2.2.2
                                    linarith only [h7933, hlam, p8090_0]
                                  · have p8090_0 := h8090c.1
                                    have p8090_1 := h8090c.2.1
                                    have p8090_2 := h8090c.2.2.1
                                    have p8090_3 := h8090c.2.2.2
                                    linarith only [h7934, hlam, p8090_0]
                                  · have p8090_0 := h8090c.1
                                    have p8090_1 := h8090c.2.1
                                    have p8090_2 := h8090c.2.2.1
                                    have p8090_3 := h8090c.2.2.2
                                    linarith only [hlam, p8090_0]
                        · linarith only [h8081, hlam, p8069_0]
                      · have p8069_0 := h8069c.1
                        have p8069_1 := h8069c.2.1
                        have p8069_2 := h8069c.2.2.1
                        have p8069_3 := h8069c.2.2.2
                        rcases p8069_3 (m.d 0 2) (by simp) with h8139 | h8139
                        · rcases p8069_3 (m.d 1 2) (by simp) with h8140 | h8140
                          · linarith only [h0, h8140, hlam]
                          · rcases p8069_3 (m.d 2 3) (by simp) with h8142 | h8142
                            · linarith only [h4, h8142, hlam]
                            · rcases p8069_3 (m.d 2 4) (by simp) with h8144 | h8144
                              · linarith only [h5, h8144, hlam]
                              · linarith only [h7933, h8144, hlam]
                        · linarith only [h8139, hlam, p8069_0]
                      · have p8069_0 := h8069c.1
                        have p8069_1 := h8069c.2.1
                        have p8069_2 := h8069c.2.2.1
                        have p8069_3 := h8069c.2.2.2
                        linarith only [h0, hlam, p8069_1]
                      · have p8069_0 := h8069c.1
                        have p8069_1 := h8069c.2.1
                        have p8069_2 := h8069c.2.2.1
                        have p8069_3 := h8069c.2.2.2
                        linarith only [hlam, p8069_0]
                      · have p8069_0 := h8069c.1
                        have p8069_1 := h8069c.2.1
                        have p8069_2 := h8069c.2.2.1
                        have p8069_3 := h8069c.2.2.2
                        linarith only [h10, hlam, p8069_0]
                      · have p8069_0 := h8069c.1
                        have p8069_1 := h8069c.2.1
                        have p8069_2 := h8069c.2.2.1
                        have p8069_3 := h8069c.2.2.2
                        linarith only [h3576, hlam, p8069_0]
                      · have p8069_0 := h8069c.1
                        have p8069_1 := h8069c.2.1
                        have p8069_2 := h8069c.2.2.1
                        have p8069_3 := h8069c.2.2.2
                        linarith only [h4058, hlam, p8069_0]
                      · have p8069_0 := h8069c.1
                        have p8069_1 := h8069c.2.1
                        have p8069_2 := h8069c.2.2.1
                        have p8069_3 := h8069c.2.2.2
                        linarith only [h4, hlam, p8069_0]
                      · have p8069_0 := h8069c.1
                        have p8069_1 := h8069c.2.1
                        have p8069_2 := h8069c.2.2.1
                        have p8069_3 := h8069c.2.2.2
                        linarith only [h7931, hc12, hc35, hlam, hphi, ht23, p8069_1]
                      · have p8069_0 := h8069c.1
                        have p8069_1 := h8069c.2.1
                        have p8069_2 := h8069c.2.2.1
                        have p8069_3 := h8069c.2.2.2
                        linarith only [hlam, p8069_0]
                      · have p8069_0 := h8069c.1
                        have p8069_1 := h8069c.2.1
                        have p8069_2 := h8069c.2.2.1
                        have p8069_3 := h8069c.2.2.2
                        linarith only [h7435, hlam, p8069_1]
                      · have p8069_0 := h8069c.1
                        have p8069_1 := h8069c.2.1
                        have p8069_2 := h8069c.2.2.1
                        have p8069_3 := h8069c.2.2.2
                        linarith only [h7931, hlam, p8069_1]
                      · have p8069_0 := h8069c.1
                        have p8069_1 := h8069c.2.1
                        have p8069_2 := h8069c.2.2.1
                        have p8069_3 := h8069c.2.2.2
                        linarith only [h5, hlam, p8069_0]
                      · have p8069_0 := h8069c.1
                        have p8069_1 := h8069c.2.1
                        have p8069_2 := h8069c.2.2.1
                        have p8069_3 := h8069c.2.2.2
                        rcases p8069_3 (m.d 0 2) (by simp) with h8159 | h8159
                        · rcases p8069_3 (m.d 1 2) (by simp) with h8160 | h8160
                          · linarith only [h8160, hlam, p8069_0]
                          · rcases p8069_3 (m.d 2 3) (by simp) with h8162 | h8162
                            · linarith only [h7435, h8162, hlam]
                            · linarith only [h10, h8162, hlam]
                        · linarith only [h0, h8159, hlam]
                      · have p8069_0 := h8069c.1
                        have p8069_1 := h8069c.2.1
                        have p8069_2 := h8069c.2.2.1
                        have p8069_3 := h8069c.2.2.2
                        linarith only [h0, h10, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8069_1]
                      · have p8069_0 := h8069c.1
                        have p8069_1 := h8069c.2.1
                        have p8069_2 := h8069c.2.2.1
                        have p8069_3 := h8069c.2.2.2
                        linarith only [hlam, p8069_0]
                      · have p8069_0 := h8069c.1
                        have p8069_1 := h8069c.2.1
                        have p8069_2 := h8069c.2.2.1
                        have p8069_3 := h8069c.2.2.2
                        linarith only [h0, h10, h4, h7, h7435, h7931, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8069_1]
                      · have p8069_0 := h8069c.1
                        have p8069_1 := h8069c.2.1
                        have p8069_2 := h8069c.2.2.1
                        have p8069_3 := h8069c.2.2.2
                        linarith only [h6, hlam, p8069_0]
                      · have p8069_0 := h8069c.1
                        have p8069_1 := h8069c.2.1
                        have p8069_2 := h8069c.2.2.1
                        have p8069_3 := h8069c.2.2.2
                        rcases p8069_3 (m.d 0 2) (by simp) with h8170 | h8170
                        · rcases p8069_3 (m.d 1 2) (by simp) with h8171 | h8171
                          · linarith only [h8171, hlam, p8069_0]
                          · rcases p8069_3 (m.d 2 3) (by simp) with h8173 | h8173
                            · linarith only [h7931, h8173, hlam]
                            · linarith only [h10, h8173, hlam]
                        · linarith only [h0, h8170, hlam]
                      · have p8069_0 := h8069c.1
                        have p8069_1 := h8069c.2.1
                        have p8069_2 := h8069c.2.2.1
                        have p8069_3 := h8069c.2.2.2
                        linarith only [h10, hc12, hc25, hlam, hphi, p8069_1]
                      · have p8069_0 := h8069c.1
                        have p8069_1 := h8069c.2.1
                        have p8069_2 := h8069c.2.2.1
                        have p8069_3 := h8069c.2.2.2
                        linarith only [h7933, hlam, p8069_1]
                      · have p8069_0 := h8069c.1
                        have p8069_1 := h8069c.2.1
                        have p8069_2 := h8069c.2.2.1
                        have p8069_3 := h8069c.2.2.2
                        linarith only [hlam, p8069_0]
                    · rcases h2bigk with h8180c | h8180c | h8180c | h8180c | h8180c | h8180c | h8180c | h8180c | h8180c | h8180c | h8180c | h8180c | h8180c | h8180c | h8180c | h8180c | h8180c | h8180c | h8180c | h8180c | h8180c | h8180c | h8180c | h8180c | h8180c
                      · have p8180_0 := h8180c.1
                        have p8180_1 := h8180c.2.1
                        have p8180_2 := h8180c.2.2.1
                        have p8180_3 := h8180c.2.2.2
                        linarith only [hlam, p8180_0]
                      · have p8180_0 := h8180c.1
                        have p8180_1 := h8180c.2.1
                        have p8180_2 := h8180c.2.2.1
                        have p8180_3 := h8180c.2.2.2
                        linarith only [h10, h4, h7, h7435, hlam, p8180_2]
                      · have p8180_0 := h8180c.1
                        have p8180_1 := h8180c.2.1
                        have p8180_2 := h8180c.2.2.1
                        have p8180_3 := h8180c.2.2.2
                        rcases p8180_3 (m.d 0 2) (by simp) with h8183 | h8183
                        · rcases p8180_3 (m.d 1 2) (by simp) with h8184 | h8184
                          · linarith only [h0, h8184, hlam]
                          · rcases p8180_3 (m.d 2 3) (by simp) with h8186 | h8186
                            · linarith only [h8186, hlam, p8180_0]
                            · rcases p8180_3 (m.d 2 4) (by simp) with h8188 | h8188
                              · linarith only [h5, h8188, hlam]
                              · linarith only [h7435, h8188, hlam]
                        · linarith only [h8183, hlam, p8180_0]
                      · have p8180_0 := h8180c.1
                        have p8180_1 := h8180c.2.1
                        have p8180_2 := h8180c.2.2.1
                        have p8180_3 := h8180c.2.2.2
                        rcases p8180_3 (m.d 0 2) (by simp) with h8192 | h8192
                        · rcases p8180_3 (m.d 1 2) (by simp) with h8193 | h8193
                          · linarith only [h0, h8193, hlam]
                          · rcases p8180_3 (m.d 2 3) (by simp) with h8195 | h8195
                            · linarith only [h4, h8195, hlam]
                            · rcases p8180_3 (m.d 2 4) (by simp) with h8197 | h8197
                              · linarith only [h8197, hlam, p8180_0]
                              · rcases p8180_3 (m.d 2 5) (by simp) with h8199 | h8199
                                · linarith only [h6, h8199, hlam]
                                · rcases h4bigk with h8201c | h8201c | h8201c | h8201c | h8201c | h8201c | h8201c | h8201c | h8201c | h8201c | h8201c | h8201c | h8201c | h8201c | h8201c | h8201c | h8201c | h8201c | h8201c | h8201c | h8201c | h8201c | h8201c | h8201c | h8201c
                                  · have p8201_0 := h8201c.1
                                    have p8201_1 := h8201c.2.1
                                    have p8201_2 := h8201c.2.2.1
                                    have p8201_3 := h8201c.2.2.2
                                    linarith only [hlam, p8201_0]
                                  · have p8201_0 := h8201c.1
                                    have p8201_1 := h8201c.2.1
                                    have p8201_2 := h8201c.2.2.1
                                    have p8201_3 := h8201c.2.2.2
                                    rcases p8201_3 (m.d 0 4) (by simp) with h8203 | h8203
                                    · rcases p8201_3 (m.d 1 4) (by simp) with h8204 | h8204
                                      · linarith only [h2, h8204, hlam]
                                      · rcases p8201_3 (m.d 2 4) (by simp) with h8206 | h8206
                                        · linarith only [h5, h8206, hlam]
                                        · linarith only [h3576, h8206, hlam]
                                    · linarith only [h2, h8203, hlam]
                                  · have p8201_0 := h8201c.1
                                    have p8201_1 := h8201c.2.1
                                    have p8201_2 := h8201c.2.2.1
                                    have p8201_3 := h8201c.2.2.2
                                    rcases p8201_3 (m.d 0 4) (by simp) with h8210 | h8210
                                    · rcases p8201_3 (m.d 1 4) (by simp) with h8211 | h8211
                                      · linarith only [h2, h8211, hlam]
                                      · rcases p8201_3 (m.d 2 4) (by simp) with h8213 | h8213
                                        · linarith only [h5, h8213, hlam]
                                        · rcases p8201_3 (m.d 3 4) (by simp) with h8215 | h8215
                                          · linarith only [h7, h8215, hlam]
                                          · linarith only [h7435, h8215, hlam]
                                    · linarith only [h5, h8210, hlam]
                                  · have p8201_0 := h8201c.1
                                    have p8201_1 := h8201c.2.1
                                    have p8201_2 := h8201c.2.2.1
                                    have p8201_3 := h8201c.2.2.2
                                    linarith only [h0, h10, h4, h7, h7435, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8201_1]
                                  · have p8201_0 := h8201c.1
                                    have p8201_1 := h8201c.2.1
                                    have p8201_2 := h8201c.2.2.1
                                    have p8201_3 := h8201c.2.2.2
                                    rcases p8201_3 (m.d 0 4) (by simp) with h8220 | h8220
                                    · rcases p8201_3 (m.d 1 4) (by simp) with h8221 | h8221
                                      · linarith only [h2, h8221, hlam]
                                      · linarith only [h7434, h8221, hlam]
                                    · linarith only [h8220, hlam, p8201_0]
                                  · have p8201_0 := h8201c.1
                                    have p8201_1 := h8201c.2.1
                                    have p8201_2 := h8201c.2.2.1
                                    have p8201_3 := h8201c.2.2.2
                                    linarith only [h2, hlam, p8201_0]
                                  · have p8201_0 := h8201c.1
                                    have p8201_1 := h8201c.2.1
                                    have p8201_2 := h8201c.2.2.1
                                    have p8201_3 := h8201c.2.2.2
                                    linarith only [hlam, p8201_0]
                                  · have p8201_0 := h8201c.1
                                    have p8201_1 := h8201c.2.1
                                    have p8201_2 := h8201c.2.2.1
                                    have p8201_3 := h8201c.2.2.2
                                    linarith only [h3576, hlam, p8201_1]
                                  · have p8201_0 := h8201c.1
                                    have p8201_1 := h8201c.2.1
                                    have p8201_2 := h8201c.2.2.1
                                    have p8201_3 := h8201c.2.2.2
                                    linarith only [h4129, hlam, p8201_1]
                                  · have p8201_0 := h8201c.1
                                    have p8201_1 := h8201c.2.1
                                    have p8201_2 := h8201c.2.2.1
                                    have p8201_3 := h8201c.2.2.2
                                    linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p7935_1, p8201_1]
                                  · have p8201_0 := h8201c.1
                                    have p8201_1 := h8201c.2.1
                                    have p8201_2 := h8201c.2.2.1
                                    have p8201_3 := h8201c.2.2.2
                                    linarith only [h5, hlam, p8201_0]
                                  · have p8201_0 := h8201c.1
                                    have p8201_1 := h8201c.2.1
                                    have p8201_2 := h8201c.2.2.1
                                    have p8201_3 := h8201c.2.2.2
                                    linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p8180_1, p8201_1]
                                  · have p8201_0 := h8201c.1
                                    have p8201_1 := h8201c.2.1
                                    have p8201_2 := h8201c.2.2.1
                                    have p8201_3 := h8201c.2.2.2
                                    linarith only [hlam, p8201_0]
                                  · have p8201_0 := h8201c.1
                                    have p8201_1 := h8201c.2.1
                                    have p8201_2 := h8201c.2.2.1
                                    have p8201_3 := h8201c.2.2.2
                                    linarith only [h7435, hlam, p8201_1]
                                  · have p8201_0 := h8201c.1
                                    have p8201_1 := h8201c.2.1
                                    have p8201_2 := h8201c.2.2.1
                                    have p8201_3 := h8201c.2.2.2
                                    linarith only [h0, hc01, hc45, hlam, hphi, ht0b, ht5b, p8180_1, p8201_1]
                                  · have p8201_0 := h8201c.1
                                    have p8201_1 := h8201c.2.1
                                    have p8201_2 := h8201c.2.2.1
                                    have p8201_3 := h8201c.2.2.2
                                    linarith only [h7, hlam, p8201_0]
                                  · have p8201_0 := h8201c.1
                                    have p8201_1 := h8201c.2.1
                                    have p8201_2 := h8201c.2.2.1
                                    have p8201_3 := h8201c.2.2.2
                                    linarith only [h0, h4, h7, h7434, hc01, hc45, hlam, hphi, ht0b, ht5b, p8201_1]
                                  · have p8201_0 := h8201c.1
                                    have p8201_1 := h8201c.2.1
                                    have p8201_2 := h8201c.2.2.1
                                    have p8201_3 := h8201c.2.2.2
                                    linarith only [h4, h7, hlam, p8180_2, p8201_1]
                                  · have p8201_0 := h8201c.1
                                    have p8201_1 := h8201c.2.1
                                    have p8201_2 := h8201c.2.2.1
                                    have p8201_3 := h8201c.2.2.2
                                    linarith only [hlam, p8201_0]
                                  · have p8201_0 := h8201c.1
                                    have p8201_1 := h8201c.2.1
                                    have p8201_2 := h8201c.2.2.1
                                    have p8201_3 := h8201c.2.2.2
                                    rcases p8201_3 (m.d 0 4) (by simp) with h8239 | h8239
                                    · rcases p8201_3 (m.d 1 4) (by simp) with h8240 | h8240
                                      · linarith only [h4129, h8240, hlam]
                                      · linarith only [h7434, h8240, hlam]
                                    · linarith only [h8239, h9, hlam]
                                  · have p8201_0 := h8201c.1
                                    have p8201_1 := h8201c.2.1
                                    have p8201_2 := h8201c.2.2.1
                                    have p8201_3 := h8201c.2.2.2
                                    linarith only [h9, hlam, p8201_0]
                                  · have p8201_0 := h8201c.1
                                    have p8201_1 := h8201c.2.1
                                    have p8201_2 := h8201c.2.2.1
                                    have p8201_3 := h8201c.2.2.2
                                    linarith only [h7434, hlam, p8201_0]
                                  · have p8201_0 := h8201c.1
                                    have p8201_1 := h8201c.2.1
                                    have p8201_2 := h8201c.2.2.1
                                    have p8201_3 := h8201c.2.2.2
                                    linarith only [h7933, hlam, p8201_0]
                                  · have p8201_0 := h8201c.1
                                    have p8201_1 := h8201c.2.1
                                    have p8201_2 := h8201c.2.2.1
                                    have p8201_3 := h8201c.2.2.2
                                    linarith only [h7934, hlam, p8201_0]
                                  · have p8201_0 := h8201c.1
                                    have p8201_1 := h8201c.2.1
                                    have p8201_2 := h8201c.2.2.1
                                    have p8201_3 := h8201c.2.2.2
                                    linarith only [hlam, p8201_0]
                        · linarith only [h8192, hlam, p8180_0]
                      · have p8180_0 := h8180c.1
                        have p8180_1 := h8180c.2.1
                        have p8180_2 := h8180c.2.2.1
                        have p8180_3 := h8180c.2.2.2
                        rcases p8180_3 (m.d 0 2) (by simp) with h8250 | h8250
                        · rcases p8180_3 (m.d 1 2) (by simp) with h8251 | h8251
                          · linarith only [h0, h8251, hlam]
                          · rcases p8180_3 (m.d 2 3) (by simp) with h8253 | h8253
                            · linarith only [h4, h8253, hlam]
                            · rcases p8180_3 (m.d 2 4) (by simp) with h8255 | h8255
                              · linarith only [h5, h8255, hlam]
                              · linarith only [h7933, h8255, hlam]
                        · linarith only [h8250, hlam, p8180_0]
                      · have p8180_0 := h8180c.1
                        have p8180_1 := h8180c.2.1
                        have p8180_2 := h8180c.2.2.1
                        have p8180_3 := h8180c.2.2.2
                        linarith only [h0, hlam, p8180_1]
                      · have p8180_0 := h8180c.1
                        have p8180_1 := h8180c.2.1
                        have p8180_2 := h8180c.2.2.1
                        have p8180_3 := h8180c.2.2.2
                        linarith only [hlam, p8180_0]
                      · have p8180_0 := h8180c.1
                        have p8180_1 := h8180c.2.1
                        have p8180_2 := h8180c.2.2.1
                        have p8180_3 := h8180c.2.2.2
                        linarith only [h10, hlam, p8180_0]
                      · have p8180_0 := h8180c.1
                        have p8180_1 := h8180c.2.1
                        have p8180_2 := h8180c.2.2.1
                        have p8180_3 := h8180c.2.2.2
                        linarith only [h3576, hlam, p8180_0]
                      · have p8180_0 := h8180c.1
                        have p8180_1 := h8180c.2.1
                        have p8180_2 := h8180c.2.2.1
                        have p8180_3 := h8180c.2.2.2
                        linarith only [h4058, hlam, p8180_0]
                      · have p8180_0 := h8180c.1
                        have p8180_1 := h8180c.2.1
                        have p8180_2 := h8180c.2.2.1
                        have p8180_3 := h8180c.2.2.2
                        linarith only [h4, hlam, p8180_0]
                      · have p8180_0 := h8180c.1
                        have p8180_1 := h8180c.2.1
                        have p8180_2 := h8180c.2.2.1
                        have p8180_3 := h8180c.2.2.2
                        linarith only [h7931, hc12, hc35, hlam, hphi, ht23, p8180_1]
                      · have p8180_0 := h8180c.1
                        have p8180_1 := h8180c.2.1
                        have p8180_2 := h8180c.2.2.1
                        have p8180_3 := h8180c.2.2.2
                        linarith only [hlam, p8180_0]
                      · have p8180_0 := h8180c.1
                        have p8180_1 := h8180c.2.1
                        have p8180_2 := h8180c.2.2.1
                        have p8180_3 := h8180c.2.2.2
                        linarith only [h7435, hlam, p8180_1]
                      · have p8180_0 := h8180c.1
                        have p8180_1 := h8180c.2.1
                        have p8180_2 := h8180c.2.2.1
                        have p8180_3 := h8180c.2.2.2
                        linarith only [h7931, hlam, p8180_1]
                      · have p8180_0 := h8180c.1
                        have p8180_1 := h8180c.2.1
                        have p8180_2 := h8180c.2.2.1
                        have p8180_3 := h8180c.2.2.2
                        linarith only [h5, hlam, p8180_0]
                      · have p8180_0 := h8180c.1
                        have p8180_1 := h8180c.2.1
                        have p8180_2 := h8180c.2.2.1
                        have p8180_3 := h8180c.2.2.2
                        rcases p8180_3 (m.d 0 2) (by simp) with h8270 | h8270
                        · rcases p8180_3 (m.d 1 2) (by simp) with h8271 | h8271
                          · linarith only [h8271, hlam, p8180_0]
                          · rcases p8180_3 (m.d 2 3) (by simp) with h8273 | h8273
                            · linarith only [h7435, h8273, hlam]
                            · linarith only [h10, h8273, hlam]
                        · linarith only [h0, h8270, hlam]
                      · have p8180_0 := h8180c.1
                        have p8180_1 := h8180c.2.1
                        have p8180_2 := h8180c.2.2.1
                        have p8180_3 := h8180c.2.2.2
                        linarith only [h0, h10, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8180_1]
                      · have p8180_0 := h8180c.1
                        have p8180_1 := h8180c.2.1
                        have p8180_2 := h8180c.2.2.1
                        have p8180_3 := h8180c.2.2.2
                        linarith only [hlam, p8180_0]
                      · have p8180_0 := h8180c.1
                        have p8180_1 := h8180c.2.1
                        have p8180_2 := h8180c.2.2.1
                        have p8180_3 := h8180c.2.2.2
                        linarith only [h0, h10, h4, h7, h7435, h7931, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8180_1]
                      · have p8180_0 := h8180c.1
                        have p8180_1 := h8180c.2.1
                        have p8180_2 := h8180c.2.2.1
                        have p8180_3 := h8180c.2.2.2
                        linarith only [h6, hlam, p8180_0]
                      · have p8180_0 := h8180c.1
                        have p8180_1 := h8180c.2.1
                        have p8180_2 := h8180c.2.2.1
                        have p8180_3 := h8180c.2.2.2
                        rcases p8180_3 (m.d 0 2) (by simp) with h8281 | h8281
                        · rcases p8180_3 (m.d 1 2) (by simp) with h8282 | h8282
                          · linarith only [h8282, hlam, p8180_0]
                          · rcases p8180_3 (m.d 2 3) (by simp) with h8284 | h8284
                            · linarith only [h7931, h8284, hlam]
                            · linarith only [h10, h8284, hlam]
                        · linarith only [h0, h8281, hlam]
                      · have p8180_0 := h8180c.1
                        have p8180_1 := h8180c.2.1
                        have p8180_2 := h8180c.2.2.1
                        have p8180_3 := h8180c.2.2.2
                        linarith only [h10, hc12, hc25, hlam, hphi, p8180_1]
                      · have p8180_0 := h8180c.1
                        have p8180_1 := h8180c.2.1
                        have p8180_2 := h8180c.2.2.1
                        have p8180_3 := h8180c.2.2.2
                        linarith only [h7933, hlam, p8180_1]
                      · have p8180_0 := h8180c.1
                        have p8180_1 := h8180c.2.1
                        have p8180_2 := h8180c.2.2.1
                        have p8180_3 := h8180c.2.2.2
                        linarith only [hlam, p8180_0]
                    · rcases h2bigk with h8291c | h8291c | h8291c | h8291c | h8291c | h8291c | h8291c | h8291c | h8291c | h8291c | h8291c | h8291c | h8291c | h8291c | h8291c | h8291c | h8291c | h8291c | h8291c | h8291c | h8291c | h8291c | h8291c | h8291c | h8291c
                      · have p8291_0 := h8291c.1
                        have p8291_1 := h8291c.2.1
                        have p8291_2 := h8291c.2.2.1
                        have p8291_3 := h8291c.2.2.2
                        linarith only [hlam, p8291_0]
                      · have p8291_0 := h8291c.1
                        have p8291_1 := h8291c.2.1
                        have p8291_2 := h8291c.2.2.1
                        have p8291_3 := h8291c.2.2.2
                        linarith only [h10, h4, h7, h7435, hlam, p8291_2]
                      · have p8291_0 := h8291c.1
                        have p8291_1 := h8291c.2.1
                        have p8291_2 := h8291c.2.2.1
                        have p8291_3 := h8291c.2.2.2
                        rcases p8291_3 (m.d 0 2) (by simp) with h8294 | h8294
                        · rcases p8291_3 (m.d 1 2) (by simp) with h8295 | h8295
                          · linarith only [h0, h8295, hlam]
                          · rcases p8291_3 (m.d 2 3) (by simp) with h8297 | h8297
                            · linarith only [h8297, hlam, p8291_0]
                            · rcases p8291_3 (m.d 2 4) (by simp) with h8299 | h8299
                              · linarith only [h5, h8299, hlam]
                              · linarith only [h7435, h8299, hlam]
                        · linarith only [h8294, hlam, p8291_0]
                      · have p8291_0 := h8291c.1
                        have p8291_1 := h8291c.2.1
                        have p8291_2 := h8291c.2.2.1
                        have p8291_3 := h8291c.2.2.2
                        rcases p8291_3 (m.d 0 2) (by simp) with h8303 | h8303
                        · rcases p8291_3 (m.d 1 2) (by simp) with h8304 | h8304
                          · linarith only [h0, h8304, hlam]
                          · rcases p8291_3 (m.d 2 3) (by simp) with h8306 | h8306
                            · linarith only [h4, h8306, hlam]
                            · rcases p8291_3 (m.d 2 4) (by simp) with h8308 | h8308
                              · linarith only [h8308, hlam, p8291_0]
                              · rcases p8291_3 (m.d 2 5) (by simp) with h8310 | h8310
                                · linarith only [h6, h8310, hlam]
                                · rcases h4bigk with h8312c | h8312c | h8312c | h8312c | h8312c | h8312c | h8312c | h8312c | h8312c | h8312c | h8312c | h8312c | h8312c | h8312c | h8312c | h8312c | h8312c | h8312c | h8312c | h8312c | h8312c | h8312c | h8312c | h8312c | h8312c
                                  · have p8312_0 := h8312c.1
                                    have p8312_1 := h8312c.2.1
                                    have p8312_2 := h8312c.2.2.1
                                    have p8312_3 := h8312c.2.2.2
                                    linarith only [hlam, p8312_0]
                                  · have p8312_0 := h8312c.1
                                    have p8312_1 := h8312c.2.1
                                    have p8312_2 := h8312c.2.2.1
                                    have p8312_3 := h8312c.2.2.2
                                    rcases p8312_3 (m.d 0 4) (by simp) with h8314 | h8314
                                    · rcases p8312_3 (m.d 1 4) (by simp) with h8315 | h8315
                                      · linarith only [h2, h8315, hlam]
                                      · rcases p8312_3 (m.d 2 4) (by simp) with h8317 | h8317
                                        · linarith only [h5, h8317, hlam]
                                        · linarith only [h3576, h8317, hlam]
                                    · linarith only [h2, h8314, hlam]
                                  · have p8312_0 := h8312c.1
                                    have p8312_1 := h8312c.2.1
                                    have p8312_2 := h8312c.2.2.1
                                    have p8312_3 := h8312c.2.2.2
                                    rcases p8312_3 (m.d 0 4) (by simp) with h8321 | h8321
                                    · rcases p8312_3 (m.d 1 4) (by simp) with h8322 | h8322
                                      · linarith only [h2, h8322, hlam]
                                      · rcases p8312_3 (m.d 2 4) (by simp) with h8324 | h8324
                                        · linarith only [h5, h8324, hlam]
                                        · rcases p8312_3 (m.d 3 4) (by simp) with h8326 | h8326
                                          · linarith only [h7, h8326, hlam]
                                          · linarith only [h7435, h8326, hlam]
                                    · linarith only [h5, h8321, hlam]
                                  · have p8312_0 := h8312c.1
                                    have p8312_1 := h8312c.2.1
                                    have p8312_2 := h8312c.2.2.1
                                    have p8312_3 := h8312c.2.2.2
                                    linarith only [h0, h10, h4, h7, h7435, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8312_1]
                                  · have p8312_0 := h8312c.1
                                    have p8312_1 := h8312c.2.1
                                    have p8312_2 := h8312c.2.2.1
                                    have p8312_3 := h8312c.2.2.2
                                    rcases p8312_3 (m.d 0 4) (by simp) with h8331 | h8331
                                    · rcases p8312_3 (m.d 1 4) (by simp) with h8332 | h8332
                                      · linarith only [h2, h8332, hlam]
                                      · linarith only [h7434, h8332, hlam]
                                    · linarith only [h8331, hlam, p8312_0]
                                  · have p8312_0 := h8312c.1
                                    have p8312_1 := h8312c.2.1
                                    have p8312_2 := h8312c.2.2.1
                                    have p8312_3 := h8312c.2.2.2
                                    linarith only [h2, hlam, p8312_0]
                                  · have p8312_0 := h8312c.1
                                    have p8312_1 := h8312c.2.1
                                    have p8312_2 := h8312c.2.2.1
                                    have p8312_3 := h8312c.2.2.2
                                    linarith only [hlam, p8312_0]
                                  · have p8312_0 := h8312c.1
                                    have p8312_1 := h8312c.2.1
                                    have p8312_2 := h8312c.2.2.1
                                    have p8312_3 := h8312c.2.2.2
                                    linarith only [h3576, hlam, p8312_1]
                                  · have p8312_0 := h8312c.1
                                    have p8312_1 := h8312c.2.1
                                    have p8312_2 := h8312c.2.2.1
                                    have p8312_3 := h8312c.2.2.2
                                    linarith only [h4129, hlam, p8312_1]
                                  · have p8312_0 := h8312c.1
                                    have p8312_1 := h8312c.2.1
                                    have p8312_2 := h8312c.2.2.1
                                    have p8312_3 := h8312c.2.2.2
                                    linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p7935_1, p8312_1]
                                  · have p8312_0 := h8312c.1
                                    have p8312_1 := h8312c.2.1
                                    have p8312_2 := h8312c.2.2.1
                                    have p8312_3 := h8312c.2.2.2
                                    linarith only [h5, hlam, p8312_0]
                                  · have p8312_0 := h8312c.1
                                    have p8312_1 := h8312c.2.1
                                    have p8312_2 := h8312c.2.2.1
                                    have p8312_3 := h8312c.2.2.2
                                    linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p8291_1, p8312_1]
                                  · have p8312_0 := h8312c.1
                                    have p8312_1 := h8312c.2.1
                                    have p8312_2 := h8312c.2.2.1
                                    have p8312_3 := h8312c.2.2.2
                                    linarith only [hlam, p8312_0]
                                  · have p8312_0 := h8312c.1
                                    have p8312_1 := h8312c.2.1
                                    have p8312_2 := h8312c.2.2.1
                                    have p8312_3 := h8312c.2.2.2
                                    linarith only [h7435, hlam, p8312_1]
                                  · have p8312_0 := h8312c.1
                                    have p8312_1 := h8312c.2.1
                                    have p8312_2 := h8312c.2.2.1
                                    have p8312_3 := h8312c.2.2.2
                                    linarith only [h0, hc01, hc45, hlam, hphi, ht0b, ht5b, p8291_1, p8312_1]
                                  · have p8312_0 := h8312c.1
                                    have p8312_1 := h8312c.2.1
                                    have p8312_2 := h8312c.2.2.1
                                    have p8312_3 := h8312c.2.2.2
                                    linarith only [h7, hlam, p8312_0]
                                  · have p8312_0 := h8312c.1
                                    have p8312_1 := h8312c.2.1
                                    have p8312_2 := h8312c.2.2.1
                                    have p8312_3 := h8312c.2.2.2
                                    linarith only [h0, h4, h7, h7434, hc01, hc45, hlam, hphi, ht0b, ht5b, p8312_1]
                                  · have p8312_0 := h8312c.1
                                    have p8312_1 := h8312c.2.1
                                    have p8312_2 := h8312c.2.2.1
                                    have p8312_3 := h8312c.2.2.2
                                    linarith only [h4, h7, hlam, p8291_2, p8312_1]
                                  · have p8312_0 := h8312c.1
                                    have p8312_1 := h8312c.2.1
                                    have p8312_2 := h8312c.2.2.1
                                    have p8312_3 := h8312c.2.2.2
                                    linarith only [hlam, p8312_0]
                                  · have p8312_0 := h8312c.1
                                    have p8312_1 := h8312c.2.1
                                    have p8312_2 := h8312c.2.2.1
                                    have p8312_3 := h8312c.2.2.2
                                    rcases p8312_3 (m.d 0 4) (by simp) with h8350 | h8350
                                    · rcases p8312_3 (m.d 1 4) (by simp) with h8351 | h8351
                                      · linarith only [h4129, h8351, hlam]
                                      · linarith only [h7434, h8351, hlam]
                                    · linarith only [h8350, h9, hlam]
                                  · have p8312_0 := h8312c.1
                                    have p8312_1 := h8312c.2.1
                                    have p8312_2 := h8312c.2.2.1
                                    have p8312_3 := h8312c.2.2.2
                                    linarith only [h9, hlam, p8312_0]
                                  · have p8312_0 := h8312c.1
                                    have p8312_1 := h8312c.2.1
                                    have p8312_2 := h8312c.2.2.1
                                    have p8312_3 := h8312c.2.2.2
                                    linarith only [h7434, hlam, p8312_0]
                                  · have p8312_0 := h8312c.1
                                    have p8312_1 := h8312c.2.1
                                    have p8312_2 := h8312c.2.2.1
                                    have p8312_3 := h8312c.2.2.2
                                    linarith only [h7933, hlam, p8312_0]
                                  · have p8312_0 := h8312c.1
                                    have p8312_1 := h8312c.2.1
                                    have p8312_2 := h8312c.2.2.1
                                    have p8312_3 := h8312c.2.2.2
                                    linarith only [h7934, hlam, p8312_0]
                                  · have p8312_0 := h8312c.1
                                    have p8312_1 := h8312c.2.1
                                    have p8312_2 := h8312c.2.2.1
                                    have p8312_3 := h8312c.2.2.2
                                    linarith only [hlam, p8312_0]
                        · linarith only [h8303, hlam, p8291_0]
                      · have p8291_0 := h8291c.1
                        have p8291_1 := h8291c.2.1
                        have p8291_2 := h8291c.2.2.1
                        have p8291_3 := h8291c.2.2.2
                        rcases p8291_3 (m.d 0 2) (by simp) with h8361 | h8361
                        · rcases p8291_3 (m.d 1 2) (by simp) with h8362 | h8362
                          · linarith only [h0, h8362, hlam]
                          · rcases p8291_3 (m.d 2 3) (by simp) with h8364 | h8364
                            · linarith only [h4, h8364, hlam]
                            · rcases p8291_3 (m.d 2 4) (by simp) with h8366 | h8366
                              · linarith only [h5, h8366, hlam]
                              · linarith only [h7933, h8366, hlam]
                        · linarith only [h8361, hlam, p8291_0]
                      · have p8291_0 := h8291c.1
                        have p8291_1 := h8291c.2.1
                        have p8291_2 := h8291c.2.2.1
                        have p8291_3 := h8291c.2.2.2
                        linarith only [h0, hlam, p8291_1]
                      · have p8291_0 := h8291c.1
                        have p8291_1 := h8291c.2.1
                        have p8291_2 := h8291c.2.2.1
                        have p8291_3 := h8291c.2.2.2
                        linarith only [hlam, p8291_0]
                      · have p8291_0 := h8291c.1
                        have p8291_1 := h8291c.2.1
                        have p8291_2 := h8291c.2.2.1
                        have p8291_3 := h8291c.2.2.2
                        linarith only [h10, hlam, p8291_0]
                      · have p8291_0 := h8291c.1
                        have p8291_1 := h8291c.2.1
                        have p8291_2 := h8291c.2.2.1
                        have p8291_3 := h8291c.2.2.2
                        linarith only [h3576, hlam, p8291_0]
                      · have p8291_0 := h8291c.1
                        have p8291_1 := h8291c.2.1
                        have p8291_2 := h8291c.2.2.1
                        have p8291_3 := h8291c.2.2.2
                        linarith only [h4058, hlam, p8291_0]
                      · have p8291_0 := h8291c.1
                        have p8291_1 := h8291c.2.1
                        have p8291_2 := h8291c.2.2.1
                        have p8291_3 := h8291c.2.2.2
                        linarith only [h4, hlam, p8291_0]
                      · have p8291_0 := h8291c.1
                        have p8291_1 := h8291c.2.1
                        have p8291_2 := h8291c.2.2.1
                        have p8291_3 := h8291c.2.2.2
                        linarith only [h7931, hc12, hc35, hlam, hphi, ht23, p8291_1]
                      · have p8291_0 := h8291c.1
                        have p8291_1 := h8291c.2.1
                        have p8291_2 := h8291c.2.2.1
                        have p8291_3 := h8291c.2.2.2
                        linarith only [hlam, p8291_0]
                      · have p8291_0 := h8291c.1
                        have p8291_1 := h8291c.2.1
                        have p8291_2 := h8291c.2.2.1
                        have p8291_3 := h8291c.2.2.2
                        linarith only [h7435, hlam, p8291_1]
                      · have p8291_0 := h8291c.1
                        have p8291_1 := h8291c.2.1
                        have p8291_2 := h8291c.2.2.1
                        have p8291_3 := h8291c.2.2.2
                        linarith only [h7931, hlam, p8291_1]
                      · have p8291_0 := h8291c.1
                        have p8291_1 := h8291c.2.1
                        have p8291_2 := h8291c.2.2.1
                        have p8291_3 := h8291c.2.2.2
                        linarith only [h5, hlam, p8291_0]
                      · have p8291_0 := h8291c.1
                        have p8291_1 := h8291c.2.1
                        have p8291_2 := h8291c.2.2.1
                        have p8291_3 := h8291c.2.2.2
                        rcases p8291_3 (m.d 0 2) (by simp) with h8381 | h8381
                        · rcases p8291_3 (m.d 1 2) (by simp) with h8382 | h8382
                          · linarith only [h8382, hlam, p8291_0]
                          · rcases p8291_3 (m.d 2 3) (by simp) with h8384 | h8384
                            · linarith only [h7435, h8384, hlam]
                            · linarith only [h10, h8384, hlam]
                        · linarith only [h0, h8381, hlam]
                      · have p8291_0 := h8291c.1
                        have p8291_1 := h8291c.2.1
                        have p8291_2 := h8291c.2.2.1
                        have p8291_3 := h8291c.2.2.2
                        linarith only [h0, h10, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8291_1]
                      · have p8291_0 := h8291c.1
                        have p8291_1 := h8291c.2.1
                        have p8291_2 := h8291c.2.2.1
                        have p8291_3 := h8291c.2.2.2
                        linarith only [hlam, p8291_0]
                      · have p8291_0 := h8291c.1
                        have p8291_1 := h8291c.2.1
                        have p8291_2 := h8291c.2.2.1
                        have p8291_3 := h8291c.2.2.2
                        linarith only [h0, h10, h4, h7, h7435, h7931, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8291_1]
                      · have p8291_0 := h8291c.1
                        have p8291_1 := h8291c.2.1
                        have p8291_2 := h8291c.2.2.1
                        have p8291_3 := h8291c.2.2.2
                        linarith only [h6, hlam, p8291_0]
                      · have p8291_0 := h8291c.1
                        have p8291_1 := h8291c.2.1
                        have p8291_2 := h8291c.2.2.1
                        have p8291_3 := h8291c.2.2.2
                        rcases p8291_3 (m.d 0 2) (by simp) with h8392 | h8392
                        · rcases p8291_3 (m.d 1 2) (by simp) with h8393 | h8393
                          · linarith only [h8393, hlam, p8291_0]
                          · rcases p8291_3 (m.d 2 3) (by simp) with h8395 | h8395
                            · linarith only [h7931, h8395, hlam]
                            · linarith only [h10, h8395, hlam]
                        · linarith only [h0, h8392, hlam]
                      · have p8291_0 := h8291c.1
                        have p8291_1 := h8291c.2.1
                        have p8291_2 := h8291c.2.2.1
                        have p8291_3 := h8291c.2.2.2
                        linarith only [h10, hc12, hc25, hlam, hphi, p8291_1]
                      · have p8291_0 := h8291c.1
                        have p8291_1 := h8291c.2.1
                        have p8291_2 := h8291c.2.2.1
                        have p8291_3 := h8291c.2.2.2
                        linarith only [h7933, hlam, p8291_1]
                      · have p8291_0 := h8291c.1
                        have p8291_1 := h8291c.2.1
                        have p8291_2 := h8291c.2.2.1
                        have p8291_3 := h8291c.2.2.2
                        linarith only [hlam, p8291_0]
          · linarith only [h7947, hlam, p7935_0]
        · have p7935_0 := h7935c.1
          have p7935_1 := h7935c.2.1
          have p7935_2 := h7935c.2.2.1
          have p7935_3 := h7935c.2.2.2
          rcases p7935_3 (m.d 0 1) (by simp) with h8403 | h8403
          · rcases p7935_3 (m.d 1 2) (by simp) with h8404 | h8404
            · linarith only [h0, h8404, hlam]
            · rcases p7935_3 (m.d 1 3) (by simp) with h8406 | h8406
              · linarith only [h1, h8406, hlam]
              · rcases p7935_3 (m.d 1 4) (by simp) with h8408 | h8408
                · linarith only [h2, h8408, hlam]
                · linarith only [h7434, h8408, hlam]
          · linarith only [h8403, hlam, p7935_0]
        · have p7935_0 := h7935c.1
          have p7935_1 := h7935c.2.1
          have p7935_2 := h7935c.2.2.1
          have p7935_3 := h7935c.2.2.2
          linarith only [h0, hlam, p7935_0]
        · have p7935_0 := h7935c.1
          have p7935_1 := h7935c.2.1
          have p7935_2 := h7935c.2.2.1
          have p7935_3 := h7935c.2.2.2
          linarith only [hlam, p7935_0]
        · have p7935_0 := h7935c.1
          have p7935_1 := h7935c.2.1
          have p7935_2 := h7935c.2.2.1
          have p7935_3 := h7935c.2.2.2
          linarith only [h10, hlam, p7935_1]
        · have p7935_0 := h7935c.1
          have p7935_1 := h7935c.2.1
          have p7935_2 := h7935c.2.2.1
          have p7935_3 := h7935c.2.2.2
          linarith only [h3576, hlam, p7935_1]
        · have p7935_0 := h7935c.1
          have p7935_1 := h7935c.2.1
          have p7935_2 := h7935c.2.2.1
          have p7935_3 := h7935c.2.2.2
          linarith only [h4058, hlam, p7935_1]
        · have p7935_0 := h7935c.1
          have p7935_1 := h7935c.2.1
          have p7935_2 := h7935c.2.2.1
          have p7935_3 := h7935c.2.2.2
          linarith only [h1, hlam, p7935_0]
        · have p7935_0 := h7935c.1
          have p7935_1 := h7935c.2.1
          have p7935_2 := h7935c.2.2.1
          have p7935_3 := h7935c.2.2.2
          linarith only [h0, h4, h4129, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7935_1]
        · have p7935_0 := h7935c.1
          have p7935_1 := h7935c.2.1
          have p7935_2 := h7935c.2.2.1
          have p7935_3 := h7935c.2.2.2
          linarith only [hlam, p7935_0]
        · have p7935_0 := h7935c.1
          have p7935_1 := h7935c.2.1
          have p7935_2 := h7935c.2.2.1
          have p7935_3 := h7935c.2.2.2
          linarith only [h4129, hlam, p7935_0]
        · have p7935_0 := h7935c.1
          have p7935_1 := h7935c.2.1
          have p7935_2 := h7935c.2.2.1
          have p7935_3 := h7935c.2.2.2
          linarith only [h6948, hlam, p7935_1]
        · have p7935_0 := h7935c.1
          have p7935_1 := h7935c.2.1
          have p7935_2 := h7935c.2.2.1
          have p7935_3 := h7935c.2.2.2
          linarith only [h2, hlam, p7935_0]
        · have p7935_0 := h7935c.1
          have p7935_1 := h7935c.2.1
          have p7935_2 := h7935c.2.2.1
          have p7935_3 := h7935c.2.2.2
          rcases p7935_3 (m.d 0 1) (by simp) with h8423 | h8423
          · rcases p7935_3 (m.d 1 2) (by simp) with h8424 | h8424
            · linarith only [h3576, h8424, hlam]
            · rcases p7935_3 (m.d 1 3) (by simp) with h8426 | h8426
              · linarith only [h4129, h8426, hlam]
              · linarith only [h10, h8426, hlam]
          · linarith only [h0, h8423, hlam]
        · have p7935_0 := h7935c.1
          have p7935_1 := h7935c.2.1
          have p7935_2 := h7935c.2.2.1
          have p7935_3 := h7935c.2.2.2
          rcases p7935_3 (m.d 0 1) (by simp) with h8430 | h8430
          · rcases p7935_3 (m.d 1 2) (by simp) with h8431 | h8431
            · linarith only [h3576, h8431, hlam]
            · rcases p7935_3 (m.d 1 3) (by simp) with h8433 | h8433
              · linarith only [h4129, h8433, hlam]
              · rcases p7935_3 (m.d 1 4) (by simp) with h8435 | h8435
                · rcases p7935_3 (m.d 1 5) (by simp) with h8436 | h8436
                  · linarith only [h7434, h8436, hlam]
                  · linarith only [h6948, h8436, hlam]
                · linarith only [h4129, h8435, hlam]
          · linarith only [h1, h8430, hlam]
        · have p7935_0 := h7935c.1
          have p7935_1 := h7935c.2.1
          have p7935_2 := h7935c.2.2.1
          have p7935_3 := h7935c.2.2.2
          linarith only [hlam, p7935_0]
        · have p7935_0 := h7935c.1
          have p7935_1 := h7935c.2.1
          have p7935_2 := h7935c.2.2.1
          have p7935_3 := h7935c.2.2.2
          rcases p7935_3 (m.d 0 1) (by simp) with h8442 | h8442
          · rcases p7935_3 (m.d 1 2) (by simp) with h8443 | h8443
            · linarith only [h3576, h8443, hlam]
            · rcases p7935_3 (m.d 1 3) (by simp) with h8445 | h8445
              · linarith only [h4129, h8445, hlam]
              · rcases p7935_3 (m.d 1 4) (by simp) with h8447 | h8447
                · rcases p7935_3 (m.d 1 5) (by simp) with h8448 | h8448
                  · linarith only [h7434, h8448, hlam]
                  · rcases h1emax with h8450 | h8450 | h8450 | h8450 | h8450
                    · linarith only [h0, h3576, h4, h6948, h7, h7435, h8450, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7935_1]
                    · rcases h2bigk with h8452c | h8452c | h8452c | h8452c | h8452c | h8452c | h8452c | h8452c | h8452c | h8452c | h8452c | h8452c | h8452c | h8452c | h8452c | h8452c | h8452c | h8452c | h8452c | h8452c | h8452c | h8452c | h8452c | h8452c | h8452c
                      · have p8452_0 := h8452c.1
                        have p8452_1 := h8452c.2.1
                        have p8452_2 := h8452c.2.2.1
                        have p8452_3 := h8452c.2.2.2
                        linarith only [hlam, p8452_0]
                      · have p8452_0 := h8452c.1
                        have p8452_1 := h8452c.2.1
                        have p8452_2 := h8452c.2.2.1
                        have p8452_3 := h8452c.2.2.2
                        linarith only [h10, h3576, h4, h6948, h7, h7435, hlam, p7935_1, p8452_2]
                      · have p8452_0 := h8452c.1
                        have p8452_1 := h8452c.2.1
                        have p8452_2 := h8452c.2.2.1
                        have p8452_3 := h8452c.2.2.2
                        rcases p8452_3 (m.d 0 2) (by simp) with h8455 | h8455
                        · rcases p8452_3 (m.d 1 2) (by simp) with h8456 | h8456
                          · linarith only [h0, h8456, hlam]
                          · rcases p8452_3 (m.d 2 3) (by simp) with h8458 | h8458
                            · linarith only [h8458, hlam, p8452_0]
                            · rcases p8452_3 (m.d 2 4) (by simp) with h8460 | h8460
                              · linarith only [h5, h8460, hlam]
                              · linarith only [h7435, h8460, hlam]
                        · linarith only [h8455, hlam, p8452_0]
                      · have p8452_0 := h8452c.1
                        have p8452_1 := h8452c.2.1
                        have p8452_2 := h8452c.2.2.1
                        have p8452_3 := h8452c.2.2.2
                        linarith only [h0, h10, h3576, h6948, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7935_1, p8452_1]
                      · have p8452_0 := h8452c.1
                        have p8452_1 := h8452c.2.1
                        have p8452_2 := h8452c.2.2.1
                        have p8452_3 := h8452c.2.2.2
                        rcases p8452_3 (m.d 0 2) (by simp) with h8465 | h8465
                        · rcases p8452_3 (m.d 1 2) (by simp) with h8466 | h8466
                          · linarith only [h0, h8466, hlam]
                          · rcases p8452_3 (m.d 2 3) (by simp) with h8468 | h8468
                            · linarith only [h4, h8468, hlam]
                            · rcases p8452_3 (m.d 2 4) (by simp) with h8470 | h8470
                              · linarith only [h5, h8470, hlam]
                              · linarith only [h7933, h8470, hlam]
                        · linarith only [h8465, hlam, p8452_0]
                      · have p8452_0 := h8452c.1
                        have p8452_1 := h8452c.2.1
                        have p8452_2 := h8452c.2.2.1
                        have p8452_3 := h8452c.2.2.2
                        linarith only [h0, hlam, p8452_1]
                      · have p8452_0 := h8452c.1
                        have p8452_1 := h8452c.2.1
                        have p8452_2 := h8452c.2.2.1
                        have p8452_3 := h8452c.2.2.2
                        linarith only [hlam, p8452_0]
                      · have p8452_0 := h8452c.1
                        have p8452_1 := h8452c.2.1
                        have p8452_2 := h8452c.2.2.1
                        have p8452_3 := h8452c.2.2.2
                        linarith only [h10, hlam, p8452_0]
                      · have p8452_0 := h8452c.1
                        have p8452_1 := h8452c.2.1
                        have p8452_2 := h8452c.2.2.1
                        have p8452_3 := h8452c.2.2.2
                        linarith only [h3576, hlam, p8452_0]
                      · have p8452_0 := h8452c.1
                        have p8452_1 := h8452c.2.1
                        have p8452_2 := h8452c.2.2.1
                        have p8452_3 := h8452c.2.2.2
                        linarith only [h4058, hlam, p8452_0]
                      · have p8452_0 := h8452c.1
                        have p8452_1 := h8452c.2.1
                        have p8452_2 := h8452c.2.2.1
                        have p8452_3 := h8452c.2.2.2
                        linarith only [h4, hlam, p8452_0]
                      · have p8452_0 := h8452c.1
                        have p8452_1 := h8452c.2.1
                        have p8452_2 := h8452c.2.2.1
                        have p8452_3 := h8452c.2.2.2
                        linarith only [h7, h7931, h7934, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8452_1]
                      · have p8452_0 := h8452c.1
                        have p8452_1 := h8452c.2.1
                        have p8452_2 := h8452c.2.2.1
                        have p8452_3 := h8452c.2.2.2
                        linarith only [hlam, p8452_0]
                      · have p8452_0 := h8452c.1
                        have p8452_1 := h8452c.2.1
                        have p8452_2 := h8452c.2.2.1
                        have p8452_3 := h8452c.2.2.2
                        linarith only [h7435, hlam, p8452_1]
                      · have p8452_0 := h8452c.1
                        have p8452_1 := h8452c.2.1
                        have p8452_2 := h8452c.2.2.1
                        have p8452_3 := h8452c.2.2.2
                        linarith only [h7931, hlam, p8452_1]
                      · have p8452_0 := h8452c.1
                        have p8452_1 := h8452c.2.1
                        have p8452_2 := h8452c.2.2.1
                        have p8452_3 := h8452c.2.2.2
                        linarith only [h5, hlam, p8452_0]
                      · have p8452_0 := h8452c.1
                        have p8452_1 := h8452c.2.1
                        have p8452_2 := h8452c.2.2.1
                        have p8452_3 := h8452c.2.2.2
                        rcases p8452_3 (m.d 0 2) (by simp) with h8485 | h8485
                        · rcases p8452_3 (m.d 1 2) (by simp) with h8486 | h8486
                          · linarith only [h8486, hlam, p8452_0]
                          · rcases p8452_3 (m.d 2 3) (by simp) with h8488 | h8488
                            · linarith only [h7435, h8488, hlam]
                            · linarith only [h10, h8488, hlam]
                        · linarith only [h0, h8485, hlam]
                      · have p8452_0 := h8452c.1
                        have p8452_1 := h8452c.2.1
                        have p8452_2 := h8452c.2.2.1
                        have p8452_3 := h8452c.2.2.2
                        linarith only [h0, h10, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8452_1]
                      · have p8452_0 := h8452c.1
                        have p8452_1 := h8452c.2.1
                        have p8452_2 := h8452c.2.2.1
                        have p8452_3 := h8452c.2.2.2
                        linarith only [hlam, p8452_0]
                      · have p8452_0 := h8452c.1
                        have p8452_1 := h8452c.2.1
                        have p8452_2 := h8452c.2.2.1
                        have p8452_3 := h8452c.2.2.2
                        linarith only [h0, h4, h4058, h7, h7435, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8452_1]
                      · have p8452_0 := h8452c.1
                        have p8452_1 := h8452c.2.1
                        have p8452_2 := h8452c.2.2.1
                        have p8452_3 := h8452c.2.2.2
                        linarith only [h6, hlam, p8452_0]
                      · have p8452_0 := h8452c.1
                        have p8452_1 := h8452c.2.1
                        have p8452_2 := h8452c.2.2.1
                        have p8452_3 := h8452c.2.2.2
                        rcases p8452_3 (m.d 0 2) (by simp) with h8496 | h8496
                        · rcases p8452_3 (m.d 1 2) (by simp) with h8497 | h8497
                          · linarith only [h8497, hlam, p8452_0]
                          · rcases p8452_3 (m.d 2 3) (by simp) with h8499 | h8499
                            · linarith only [h7931, h8499, hlam]
                            · linarith only [h10, h8499, hlam]
                        · linarith only [h0, h8496, hlam]
                      · have p8452_0 := h8452c.1
                        have p8452_1 := h8452c.2.1
                        have p8452_2 := h8452c.2.2.1
                        have p8452_3 := h8452c.2.2.2
                        linarith only [h10, hc12, hc25, hlam, hphi, p8452_1]
                      · have p8452_0 := h8452c.1
                        have p8452_1 := h8452c.2.1
                        have p8452_2 := h8452c.2.2.1
                        have p8452_3 := h8452c.2.2.2
                        linarith only [h7933, hlam, p8452_1]
                      · have p8452_0 := h8452c.1
                        have p8452_1 := h8452c.2.1
                        have p8452_2 := h8452c.2.2.1
                        have p8452_3 := h8452c.2.2.2
                        linarith only [hlam, p8452_0]
                    · rcases h2bigk with h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c
                      · have p8506_0 := h8506c.1
                        have p8506_1 := h8506c.2.1
                        have p8506_2 := h8506c.2.2.1
                        have p8506_3 := h8506c.2.2.2
                        linarith only [hlam, p8506_0]
                      · have p8506_0 := h8506c.1
                        have p8506_1 := h8506c.2.1
                        have p8506_2 := h8506c.2.2.1
                        have p8506_3 := h8506c.2.2.2
                        linarith only [h10, h3576, h4, h6948, h7, h7435, hlam, p7935_1, p8506_2]
                      · have p8506_0 := h8506c.1
                        have p8506_1 := h8506c.2.1
                        have p8506_2 := h8506c.2.2.1
                        have p8506_3 := h8506c.2.2.2
                        rcases p8506_3 (m.d 0 2) (by simp) with h8509 | h8509
                        · rcases p8506_3 (m.d 1 2) (by simp) with h8510 | h8510
                          · linarith only [h0, h8510, hlam]
                          · rcases p8506_3 (m.d 2 3) (by simp) with h8512 | h8512
                            · linarith only [h8512, hlam, p8506_0]
                            · rcases p8506_3 (m.d 2 4) (by simp) with h8514 | h8514
                              · linarith only [h5, h8514, hlam]
                              · linarith only [h7435, h8514, hlam]
                        · linarith only [h8509, hlam, p8506_0]
                      · have p8506_0 := h8506c.1
                        have p8506_1 := h8506c.2.1
                        have p8506_2 := h8506c.2.2.1
                        have p8506_3 := h8506c.2.2.2
                        linarith only [h0, h10, h3576, h6948, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7935_1, p8506_1]
                      · have p8506_0 := h8506c.1
                        have p8506_1 := h8506c.2.1
                        have p8506_2 := h8506c.2.2.1
                        have p8506_3 := h8506c.2.2.2
                        rcases p8506_3 (m.d 0 2) (by simp) with h8519 | h8519
                        · rcases p8506_3 (m.d 1 2) (by simp) with h8520 | h8520
                          · linarith only [h0, h8520, hlam]
                          · rcases p8506_3 (m.d 2 3) (by simp) with h8522 | h8522
                            · linarith only [h4, h8522, hlam]
                            · rcases p8506_3 (m.d 2 4) (by simp) with h8524 | h8524
                              · linarith only [h5, h8524, hlam]
                              · linarith only [h7933, h8524, hlam]
                        · linarith only [h8519, hlam, p8506_0]
                      · have p8506_0 := h8506c.1
                        have p8506_1 := h8506c.2.1
                        have p8506_2 := h8506c.2.2.1
                        have p8506_3 := h8506c.2.2.2
                        linarith only [h0, hlam, p8506_1]
                      · have p8506_0 := h8506c.1
                        have p8506_1 := h8506c.2.1
                        have p8506_2 := h8506c.2.2.1
                        have p8506_3 := h8506c.2.2.2
                        linarith only [hlam, p8506_0]
                      · have p8506_0 := h8506c.1
                        have p8506_1 := h8506c.2.1
                        have p8506_2 := h8506c.2.2.1
                        have p8506_3 := h8506c.2.2.2
                        linarith only [h10, hlam, p8506_0]
                      · have p8506_0 := h8506c.1
                        have p8506_1 := h8506c.2.1
                        have p8506_2 := h8506c.2.2.1
                        have p8506_3 := h8506c.2.2.2
                        linarith only [h3576, hlam, p8506_0]
                      · have p8506_0 := h8506c.1
                        have p8506_1 := h8506c.2.1
                        have p8506_2 := h8506c.2.2.1
                        have p8506_3 := h8506c.2.2.2
                        linarith only [h4058, hlam, p8506_0]
                      · have p8506_0 := h8506c.1
                        have p8506_1 := h8506c.2.1
                        have p8506_2 := h8506c.2.2.1
                        have p8506_3 := h8506c.2.2.2
                        linarith only [h4, hlam, p8506_0]
                      · have p8506_0 := h8506c.1
                        have p8506_1 := h8506c.2.1
                        have p8506_2 := h8506c.2.2.1
                        have p8506_3 := h8506c.2.2.2
                        linarith only [h0, h4, h7, h7931, h7934, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8506_1]
                      · have p8506_0 := h8506c.1
                        have p8506_1 := h8506c.2.1
                        have p8506_2 := h8506c.2.2.1
                        have p8506_3 := h8506c.2.2.2
                        linarith only [hlam, p8506_0]
                      · have p8506_0 := h8506c.1
                        have p8506_1 := h8506c.2.1
                        have p8506_2 := h8506c.2.2.1
                        have p8506_3 := h8506c.2.2.2
                        linarith only [h7435, hlam, p8506_1]
                      · have p8506_0 := h8506c.1
                        have p8506_1 := h8506c.2.1
                        have p8506_2 := h8506c.2.2.1
                        have p8506_3 := h8506c.2.2.2
                        linarith only [h7931, hlam, p8506_1]
                      · have p8506_0 := h8506c.1
                        have p8506_1 := h8506c.2.1
                        have p8506_2 := h8506c.2.2.1
                        have p8506_3 := h8506c.2.2.2
                        linarith only [h5, hlam, p8506_0]
                      · have p8506_0 := h8506c.1
                        have p8506_1 := h8506c.2.1
                        have p8506_2 := h8506c.2.2.1
                        have p8506_3 := h8506c.2.2.2
                        rcases p8506_3 (m.d 0 2) (by simp) with h8539 | h8539
                        · rcases p8506_3 (m.d 1 2) (by simp) with h8540 | h8540
                          · linarith only [h8540, hlam, p8506_0]
                          · rcases p8506_3 (m.d 2 3) (by simp) with h8542 | h8542
                            · linarith only [h7435, h8542, hlam]
                            · linarith only [h10, h8542, hlam]
                        · linarith only [h0, h8539, hlam]
                      · have p8506_0 := h8506c.1
                        have p8506_1 := h8506c.2.1
                        have p8506_2 := h8506c.2.2.1
                        have p8506_3 := h8506c.2.2.2
                        linarith only [h10, hc12, hc24, hlam, hphi, p8506_1]
                      · have p8506_0 := h8506c.1
                        have p8506_1 := h8506c.2.1
                        have p8506_2 := h8506c.2.2.1
                        have p8506_3 := h8506c.2.2.2
                        linarith only [hlam, p8506_0]
                      · have p8506_0 := h8506c.1
                        have p8506_1 := h8506c.2.1
                        have p8506_2 := h8506c.2.2.1
                        have p8506_3 := h8506c.2.2.2
                        linarith only [h0, h4, h4058, h7, h7435, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8506_1]
                      · have p8506_0 := h8506c.1
                        have p8506_1 := h8506c.2.1
                        have p8506_2 := h8506c.2.2.1
                        have p8506_3 := h8506c.2.2.2
                        linarith only [h6, hlam, p8506_0]
                      · have p8506_0 := h8506c.1
                        have p8506_1 := h8506c.2.1
                        have p8506_2 := h8506c.2.2.1
                        have p8506_3 := h8506c.2.2.2
                        rcases p8506_3 (m.d 0 2) (by simp) with h8550 | h8550
                        · rcases p8506_3 (m.d 1 2) (by simp) with h8551 | h8551
                          · linarith only [h8551, hlam, p8506_0]
                          · rcases p8506_3 (m.d 2 3) (by simp) with h8553 | h8553
                            · linarith only [h7931, h8553, hlam]
                            · linarith only [h10, h8553, hlam]
                        · linarith only [h0, h8550, hlam]
                      · have p8506_0 := h8506c.1
                        have p8506_1 := h8506c.2.1
                        have p8506_2 := h8506c.2.2.1
                        have p8506_3 := h8506c.2.2.2
                        linarith only [h10, hc12, hc25, hlam, hphi, p8506_1]
                      · have p8506_0 := h8506c.1
                        have p8506_1 := h8506c.2.1
                        have p8506_2 := h8506c.2.2.1
                        have p8506_3 := h8506c.2.2.2
                        linarith only [h7933, hlam, p8506_1]
                      · have p8506_0 := h8506c.1
                        have p8506_1 := h8506c.2.1
                        have p8506_2 := h8506c.2.2.1
                        have p8506_3 := h8506c.2.2.2
                        linarith only [hlam, p8506_0]
                    · linarith only [h10, h6948, h8450, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p7935_1]
                    · rcases h2bigk with h8561c | h8561c | h8561c | h8561c | h8561c | h8561c | h8561c | h8561c | h8561c | h8561c | h8561c | h8561c | h8561c | h8561c | h8561c | h8561c | h8561c | h8561c | h8561c | h8561c | h8561c | h8561c | h8561c | h8561c | h8561c
                      · have p8561_0 := h8561c.1
                        have p8561_1 := h8561c.2.1
                        have p8561_2 := h8561c.2.2.1
                        have p8561_3 := h8561c.2.2.2
                        linarith only [hlam, p8561_0]
                      · have p8561_0 := h8561c.1
                        have p8561_1 := h8561c.2.1
                        have p8561_2 := h8561c.2.2.1
                        have p8561_3 := h8561c.2.2.2
                        linarith only [h10, h3576, h4, h6948, h7, h7435, hlam, p7935_1, p8561_2]
                      · have p8561_0 := h8561c.1
                        have p8561_1 := h8561c.2.1
                        have p8561_2 := h8561c.2.2.1
                        have p8561_3 := h8561c.2.2.2
                        rcases p8561_3 (m.d 0 2) (by simp) with h8564 | h8564
                        · rcases p8561_3 (m.d 1 2) (by simp) with h8565 | h8565
                          · linarith only [h0, h8565, hlam]
                          · rcases p8561_3 (m.d 2 3) (by simp) with h8567 | h8567
                            · linarith only [h8567, hlam, p8561_0]
                            · rcases p8561_3 (m.d 2 4) (by simp) with h8569 | h8569
                              · linarith only [h5, h8569, hlam]
                              · linarith only [h7435, h8569, hlam]
                        · linarith only [h8564, hlam, p8561_0]
                      · have p8561_0 := h8561c.1
                        have p8561_1 := h8561c.2.1
                        have p8561_2 := h8561c.2.2.1
                        have p8561_3 := h8561c.2.2.2
                        linarith only [h0, h10, h3576, h6948, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7935_1, p8561_1]
                      · have p8561_0 := h8561c.1
                        have p8561_1 := h8561c.2.1
                        have p8561_2 := h8561c.2.2.1
                        have p8561_3 := h8561c.2.2.2
                        rcases p8561_3 (m.d 0 2) (by simp) with h8574 | h8574
                        · rcases p8561_3 (m.d 1 2) (by simp) with h8575 | h8575
                          · linarith only [h0, h8575, hlam]
                          · rcases p8561_3 (m.d 2 3) (by simp) with h8577 | h8577
                            · linarith only [h4, h8577, hlam]
                            · rcases p8561_3 (m.d 2 4) (by simp) with h8579 | h8579
                              · linarith only [h5, h8579, hlam]
                              · linarith only [h7933, h8579, hlam]
                        · linarith only [h8574, hlam, p8561_0]
                      · have p8561_0 := h8561c.1
                        have p8561_1 := h8561c.2.1
                        have p8561_2 := h8561c.2.2.1
                        have p8561_3 := h8561c.2.2.2
                        linarith only [h0, hlam, p8561_1]
                      · have p8561_0 := h8561c.1
                        have p8561_1 := h8561c.2.1
                        have p8561_2 := h8561c.2.2.1
                        have p8561_3 := h8561c.2.2.2
                        linarith only [hlam, p8561_0]
                      · have p8561_0 := h8561c.1
                        have p8561_1 := h8561c.2.1
                        have p8561_2 := h8561c.2.2.1
                        have p8561_3 := h8561c.2.2.2
                        linarith only [h10, hlam, p8561_0]
                      · have p8561_0 := h8561c.1
                        have p8561_1 := h8561c.2.1
                        have p8561_2 := h8561c.2.2.1
                        have p8561_3 := h8561c.2.2.2
                        linarith only [h3576, hlam, p8561_0]
                      · have p8561_0 := h8561c.1
                        have p8561_1 := h8561c.2.1
                        have p8561_2 := h8561c.2.2.1
                        have p8561_3 := h8561c.2.2.2
                        linarith only [h4058, hlam, p8561_0]
                      · have p8561_0 := h8561c.1
                        have p8561_1 := h8561c.2.1
                        have p8561_2 := h8561c.2.2.1
                        have p8561_3 := h8561c.2.2.2
                        linarith only [h4, hlam, p8561_0]
                      · have p8561_0 := h8561c.1
                        have p8561_1 := h8561c.2.1
                        have p8561_2 := h8561c.2.2.1
                        have p8561_3 := h8561c.2.2.2
                        linarith only [h0, h4, h7, h7931, h7934, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8561_1]
                      · have p8561_0 := h8561c.1
                        have p8561_1 := h8561c.2.1
                        have p8561_2 := h8561c.2.2.1
                        have p8561_3 := h8561c.2.2.2
                        linarith only [hlam, p8561_0]
                      · have p8561_0 := h8561c.1
                        have p8561_1 := h8561c.2.1
                        have p8561_2 := h8561c.2.2.1
                        have p8561_3 := h8561c.2.2.2
                        linarith only [h7435, hlam, p8561_1]
                      · have p8561_0 := h8561c.1
                        have p8561_1 := h8561c.2.1
                        have p8561_2 := h8561c.2.2.1
                        have p8561_3 := h8561c.2.2.2
                        linarith only [h7931, hlam, p8561_1]
                      · have p8561_0 := h8561c.1
                        have p8561_1 := h8561c.2.1
                        have p8561_2 := h8561c.2.2.1
                        have p8561_3 := h8561c.2.2.2
                        linarith only [h5, hlam, p8561_0]
                      · have p8561_0 := h8561c.1
                        have p8561_1 := h8561c.2.1
                        have p8561_2 := h8561c.2.2.1
                        have p8561_3 := h8561c.2.2.2
                        rcases p8561_3 (m.d 0 2) (by simp) with h8594 | h8594
                        · rcases p8561_3 (m.d 1 2) (by simp) with h8595 | h8595
                          · linarith only [h8595, hlam, p8561_0]
                          · rcases p8561_3 (m.d 2 3) (by simp) with h8597 | h8597
                            · linarith only [h7435, h8597, hlam]
                            · linarith only [h10, h8597, hlam]
                        · linarith only [h0, h8594, hlam]
                      · have p8561_0 := h8561c.1
                        have p8561_1 := h8561c.2.1
                        have p8561_2 := h8561c.2.2.1
                        have p8561_3 := h8561c.2.2.2
                        linarith only [h0, h10, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8561_1]
                      · have p8561_0 := h8561c.1
                        have p8561_1 := h8561c.2.1
                        have p8561_2 := h8561c.2.2.1
                        have p8561_3 := h8561c.2.2.2
                        linarith only [hlam, p8561_0]
                      · have p8561_0 := h8561c.1
                        have p8561_1 := h8561c.2.1
                        have p8561_2 := h8561c.2.2.1
                        have p8561_3 := h8561c.2.2.2
                        linarith only [h0, h4, h4058, h7, h7435, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8561_1]
                      · have p8561_0 := h8561c.1
                        have p8561_1 := h8561c.2.1
                        have p8561_2 := h8561c.2.2.1
                        have p8561_3 := h8561c.2.2.2
                        linarith only [h6, hlam, p8561_0]
                      · have p8561_0 := h8561c.1
                        have p8561_1 := h8561c.2.1
                        have p8561_2 := h8561c.2.2.1
                        have p8561_3 := h8561c.2.2.2
                        rcases p8561_3 (m.d 0 2) (by simp) with h8605 | h8605
                        · rcases p8561_3 (m.d 1 2) (by simp) with h8606 | h8606
                          · linarith only [h8606, hlam, p8561_0]
                          · rcases p8561_3 (m.d 2 3) (by simp) with h8608 | h8608
                            · linarith only [h7931, h8608, hlam]
                            · linarith only [h10, h8608, hlam]
                        · linarith only [h0, h8605, hlam]
                      · have p8561_0 := h8561c.1
                        have p8561_1 := h8561c.2.1
                        have p8561_2 := h8561c.2.2.1
                        have p8561_3 := h8561c.2.2.2
                        linarith only [h10, hc12, hc25, hlam, hphi, p8561_1]
                      · have p8561_0 := h8561c.1
                        have p8561_1 := h8561c.2.1
                        have p8561_2 := h8561c.2.2.1
                        have p8561_3 := h8561c.2.2.2
                        linarith only [h7933, hlam, p8561_1]
                      · have p8561_0 := h8561c.1
                        have p8561_1 := h8561c.2.1
                        have p8561_2 := h8561c.2.2.1
                        have p8561_3 := h8561c.2.2.2
                        linarith only [hlam, p8561_0]
                · linarith only [h7434, h8447, hlam]
          · linarith only [h3, h8442, hlam]
        · have p7935_0 := h7935c.1
          have p7935_1 := h7935c.2.1
          have p7935_2 := h7935c.2.2.1
          have p7935_3 := h7935c.2.2.2
          linarith only [h3, hlam, p7935_0]
        · have p7935_0 := h7935c.1
          have p7935_1 := h7935c.2.1
          have p7935_2 := h7935c.2.2.1
          have p7935_3 := h7935c.2.2.2
          rcases p7935_3 (m.d 0 1) (by simp) with h8618 | h8618
          · rcases p7935_3 (m.d 1 2) (by simp) with h8619 | h8619
            · linarith only [h4058, h8619, hlam]
            · rcases p7935_3 (m.d 1 3) (by simp) with h8621 | h8621
              · linarith only [h6948, h8621, hlam]
              · linarith only [h10, h8621, hlam]
          · linarith only [h0, h8618, hlam]
        · have p7935_0 := h7935c.1
          have p7935_1 := h7935c.2.1
          have p7935_2 := h7935c.2.2.1
          have p7935_3 := h7935c.2.2.2
          rcases p7935_3 (m.d 0 1) (by simp) with h8625 | h8625
          · rcases p7935_3 (m.d 1 2) (by simp) with h8626 | h8626
            · linarith only [h4058, h8626, hlam]
            · rcases p7935_3 (m.d 1 3) (by simp) with h8628 | h8628
              · linarith only [h6948, h8628, hlam]
              · rcases p7935_3 (m.d 1 4) (by simp) with h8630 | h8630
                · rcases p7935_3 (m.d 1 5) (by simp) with h8631 | h8631
                  · rcases h1emax with h8632 | h8632 | h8632 | h8632 | h8632
                    · linarith only [h10, h3, h8632, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p7935_1]
                    · rcases h2bigk with h8634c | h8634c | h8634c | h8634c | h8634c | h8634c | h8634c | h8634c | h8634c | h8634c | h8634c | h8634c | h8634c | h8634c | h8634c | h8634c | h8634c | h8634c | h8634c | h8634c | h8634c | h8634c | h8634c | h8634c | h8634c
                      · have p8634_0 := h8634c.1
                        have p8634_1 := h8634c.2.1
                        have p8634_2 := h8634c.2.2.1
                        have p8634_3 := h8634c.2.2.2
                        linarith only [hlam, p8634_0]
                      · have p8634_0 := h8634c.1
                        have p8634_1 := h8634c.2.1
                        have p8634_2 := h8634c.2.2.1
                        have p8634_3 := h8634c.2.2.2
                        linarith only [h10, h4, h4058, h7, h7931, h7934, hlam, p7935_1, p8634_2]
                      · have p8634_0 := h8634c.1
                        have p8634_1 := h8634c.2.1
                        have p8634_2 := h8634c.2.2.1
                        have p8634_3 := h8634c.2.2.2
                        rcases p8634_3 (m.d 0 2) (by simp) with h8637 | h8637
                        · rcases p8634_3 (m.d 1 2) (by simp) with h8638 | h8638
                          · linarith only [h0, h8638, hlam]
                          · rcases p8634_3 (m.d 2 3) (by simp) with h8640 | h8640
                            · linarith only [h8640, hlam, p8634_0]
                            · rcases p8634_3 (m.d 2 4) (by simp) with h8642 | h8642
                              · linarith only [h5, h8642, hlam]
                              · linarith only [h7435, h8642, hlam]
                        · linarith only [h8637, hlam, p8634_0]
                      · have p8634_0 := h8634c.1
                        have p8634_1 := h8634c.2.1
                        have p8634_2 := h8634c.2.2.1
                        have p8634_3 := h8634c.2.2.2
                        linarith only [h0, h10, h3576, h7434, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7935_1, p8634_1]
                      · have p8634_0 := h8634c.1
                        have p8634_1 := h8634c.2.1
                        have p8634_2 := h8634c.2.2.1
                        have p8634_3 := h8634c.2.2.2
                        linarith only [h0, h10, h4058, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7935_1, p8634_1]
                      · have p8634_0 := h8634c.1
                        have p8634_1 := h8634c.2.1
                        have p8634_2 := h8634c.2.2.1
                        have p8634_3 := h8634c.2.2.2
                        linarith only [h0, hlam, p8634_1]
                      · have p8634_0 := h8634c.1
                        have p8634_1 := h8634c.2.1
                        have p8634_2 := h8634c.2.2.1
                        have p8634_3 := h8634c.2.2.2
                        linarith only [hlam, p8634_0]
                      · have p8634_0 := h8634c.1
                        have p8634_1 := h8634c.2.1
                        have p8634_2 := h8634c.2.2.1
                        have p8634_3 := h8634c.2.2.2
                        linarith only [h10, hlam, p8634_0]
                      · have p8634_0 := h8634c.1
                        have p8634_1 := h8634c.2.1
                        have p8634_2 := h8634c.2.2.1
                        have p8634_3 := h8634c.2.2.2
                        linarith only [h3576, hlam, p8634_0]
                      · have p8634_0 := h8634c.1
                        have p8634_1 := h8634c.2.1
                        have p8634_2 := h8634c.2.2.1
                        have p8634_3 := h8634c.2.2.2
                        linarith only [h4058, hlam, p8634_0]
                      · have p8634_0 := h8634c.1
                        have p8634_1 := h8634c.2.1
                        have p8634_2 := h8634c.2.2.1
                        have p8634_3 := h8634c.2.2.2
                        linarith only [h4, hlam, p8634_0]
                      · have p8634_0 := h8634c.1
                        have p8634_1 := h8634c.2.1
                        have p8634_2 := h8634c.2.2.1
                        have p8634_3 := h8634c.2.2.2
                        linarith only [h7, h7435, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8634_1]
                      · have p8634_0 := h8634c.1
                        have p8634_1 := h8634c.2.1
                        have p8634_2 := h8634c.2.2.1
                        have p8634_3 := h8634c.2.2.2
                        linarith only [hlam, p8634_0]
                      · have p8634_0 := h8634c.1
                        have p8634_1 := h8634c.2.1
                        have p8634_2 := h8634c.2.2.1
                        have p8634_3 := h8634c.2.2.2
                        linarith only [h7435, hlam, p8634_1]
                      · have p8634_0 := h8634c.1
                        have p8634_1 := h8634c.2.1
                        have p8634_2 := h8634c.2.2.1
                        have p8634_3 := h8634c.2.2.2
                        linarith only [h7931, hlam, p8634_1]
                      · have p8634_0 := h8634c.1
                        have p8634_1 := h8634c.2.1
                        have p8634_2 := h8634c.2.2.1
                        have p8634_3 := h8634c.2.2.2
                        linarith only [h5, hlam, p8634_0]
                      · have p8634_0 := h8634c.1
                        have p8634_1 := h8634c.2.1
                        have p8634_2 := h8634c.2.2.1
                        have p8634_3 := h8634c.2.2.2
                        rcases p8634_3 (m.d 0 2) (by simp) with h8659 | h8659
                        · rcases p8634_3 (m.d 1 2) (by simp) with h8660 | h8660
                          · linarith only [h8660, hlam, p8634_0]
                          · rcases p8634_3 (m.d 2 3) (by simp) with h8662 | h8662
                            · linarith only [h7435, h8662, hlam]
                            · linarith only [h10, h8662, hlam]
                        · linarith only [h0, h8659, hlam]
                      · have p8634_0 := h8634c.1
                        have p8634_1 := h8634c.2.1
                        have p8634_2 := h8634c.2.2.1
                        have p8634_3 := h8634c.2.2.2
                        linarith only [h0, h10, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8634_1]
                      · have p8634_0 := h8634c.1
                        have p8634_1 := h8634c.2.1
                        have p8634_2 := h8634c.2.2.1
                        have p8634_3 := h8634c.2.2.2
                        linarith only [hlam, p8634_0]
                      · have p8634_0 := h8634c.1
                        have p8634_1 := h8634c.2.1
                        have p8634_2 := h8634c.2.2.1
                        have p8634_3 := h8634c.2.2.2
                        linarith only [h0, h10, h4, h4058, h7, h7435, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7935_1, p8634_1]
                      · have p8634_0 := h8634c.1
                        have p8634_1 := h8634c.2.1
                        have p8634_2 := h8634c.2.2.1
                        have p8634_3 := h8634c.2.2.2
                        linarith only [h6, hlam, p8634_0]
                      · have p8634_0 := h8634c.1
                        have p8634_1 := h8634c.2.1
                        have p8634_2 := h8634c.2.2.1
                        have p8634_3 := h8634c.2.2.2
                        rcases p8634_3 (m.d 0 2) (by simp) with h8670 | h8670
                        · rcases p8634_3 (m.d 1 2) (by simp) with h8671 | h8671
                          · linarith only [h8671, hlam, p8634_0]
                          · rcases p8634_3 (m.d 2 3) (by simp) with h8673 | h8673
                            · linarith only [h7931, h8673, hlam]
                            · linarith only [h10, h8673, hlam]
                        · linarith only [h0, h8670, hlam]
                      · have p8634_0 := h8634c.1
                        have p8634_1 := h8634c.2.1
                        have p8634_2 := h8634c.2.2.1
                        have p8634_3 := h8634c.2.2.2
                        linarith only [h10, hc12, hc25, hlam, hphi, p8634_1]
                      · have p8634_0 := h8634c.1
                        have p8634_1 := h8634c.2.1
                        have p8634_2 := h8634c.2.2.1
                        have p8634_3 := h8634c.2.2.2
                        linarith only [h7933, hlam, p8634_1]
                      · have p8634_0 := h8634c.1
                        have p8634_1 := h8634c.2.1
                        have p8634_2 := h8634c.2.2.1
                        have p8634_3 := h8634c.2.2.2
                        linarith only [hlam, p8634_0]
                    · rcases h2bigk with h8680c | h8680c | h8680c | h8680c | h8680c | h8680c | h8680c | h8680c | h8680c | h8680c | h8680c | h8680c | h8680c | h8680c | h8680c | h8680c | h8680c | h8680c | h8680c | h8680c | h8680c | h8680c | h8680c | h8680c | h8680c
                      · have p8680_0 := h8680c.1
                        have p8680_1 := h8680c.2.1
                        have p8680_2 := h8680c.2.2.1
                        have p8680_3 := h8680c.2.2.2
                        linarith only [hlam, p8680_0]
                      · have p8680_0 := h8680c.1
                        have p8680_1 := h8680c.2.1
                        have p8680_2 := h8680c.2.2.1
                        have p8680_3 := h8680c.2.2.2
                        linarith only [h10, h3576, h4, h7, h7434, h7435, hlam, p7935_1, p8680_2]
                      · have p8680_0 := h8680c.1
                        have p8680_1 := h8680c.2.1
                        have p8680_2 := h8680c.2.2.1
                        have p8680_3 := h8680c.2.2.2
                        rcases p8680_3 (m.d 0 2) (by simp) with h8683 | h8683
                        · rcases p8680_3 (m.d 1 2) (by simp) with h8684 | h8684
                          · linarith only [h0, h8684, hlam]
                          · rcases p8680_3 (m.d 2 3) (by simp) with h8686 | h8686
                            · linarith only [h8686, hlam, p8680_0]
                            · rcases p8680_3 (m.d 2 4) (by simp) with h8688 | h8688
                              · linarith only [h5, h8688, hlam]
                              · linarith only [h7435, h8688, hlam]
                        · linarith only [h8683, hlam, p8680_0]
                      · have p8680_0 := h8680c.1
                        have p8680_1 := h8680c.2.1
                        have p8680_2 := h8680c.2.2.1
                        have p8680_3 := h8680c.2.2.2
                        linarith only [h0, h10, h3576, h7434, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7935_1, p8680_1]
                      · have p8680_0 := h8680c.1
                        have p8680_1 := h8680c.2.1
                        have p8680_2 := h8680c.2.2.1
                        have p8680_3 := h8680c.2.2.2
                        linarith only [h0, h10, h4058, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7935_1, p8680_1]
                      · have p8680_0 := h8680c.1
                        have p8680_1 := h8680c.2.1
                        have p8680_2 := h8680c.2.2.1
                        have p8680_3 := h8680c.2.2.2
                        linarith only [h0, hlam, p8680_1]
                      · have p8680_0 := h8680c.1
                        have p8680_1 := h8680c.2.1
                        have p8680_2 := h8680c.2.2.1
                        have p8680_3 := h8680c.2.2.2
                        linarith only [hlam, p8680_0]
                      · have p8680_0 := h8680c.1
                        have p8680_1 := h8680c.2.1
                        have p8680_2 := h8680c.2.2.1
                        have p8680_3 := h8680c.2.2.2
                        linarith only [h10, hlam, p8680_0]
                      · have p8680_0 := h8680c.1
                        have p8680_1 := h8680c.2.1
                        have p8680_2 := h8680c.2.2.1
                        have p8680_3 := h8680c.2.2.2
                        linarith only [h3576, hlam, p8680_0]
                      · have p8680_0 := h8680c.1
                        have p8680_1 := h8680c.2.1
                        have p8680_2 := h8680c.2.2.1
                        have p8680_3 := h8680c.2.2.2
                        linarith only [h4058, hlam, p8680_0]
                      · have p8680_0 := h8680c.1
                        have p8680_1 := h8680c.2.1
                        have p8680_2 := h8680c.2.2.1
                        have p8680_3 := h8680c.2.2.2
                        linarith only [h4, hlam, p8680_0]
                      · have p8680_0 := h8680c.1
                        have p8680_1 := h8680c.2.1
                        have p8680_2 := h8680c.2.2.1
                        have p8680_3 := h8680c.2.2.2
                        linarith only [h0, h4, h7, h7931, h7934, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8680_1]
                      · have p8680_0 := h8680c.1
                        have p8680_1 := h8680c.2.1
                        have p8680_2 := h8680c.2.2.1
                        have p8680_3 := h8680c.2.2.2
                        linarith only [hlam, p8680_0]
                      · have p8680_0 := h8680c.1
                        have p8680_1 := h8680c.2.1
                        have p8680_2 := h8680c.2.2.1
                        have p8680_3 := h8680c.2.2.2
                        linarith only [h7435, hlam, p8680_1]
                      · have p8680_0 := h8680c.1
                        have p8680_1 := h8680c.2.1
                        have p8680_2 := h8680c.2.2.1
                        have p8680_3 := h8680c.2.2.2
                        linarith only [h7931, hlam, p8680_1]
                      · have p8680_0 := h8680c.1
                        have p8680_1 := h8680c.2.1
                        have p8680_2 := h8680c.2.2.1
                        have p8680_3 := h8680c.2.2.2
                        linarith only [h5, hlam, p8680_0]
                      · have p8680_0 := h8680c.1
                        have p8680_1 := h8680c.2.1
                        have p8680_2 := h8680c.2.2.1
                        have p8680_3 := h8680c.2.2.2
                        rcases p8680_3 (m.d 0 2) (by simp) with h8705 | h8705
                        · rcases p8680_3 (m.d 1 2) (by simp) with h8706 | h8706
                          · linarith only [h8706, hlam, p8680_0]
                          · rcases p8680_3 (m.d 2 3) (by simp) with h8708 | h8708
                            · linarith only [h7435, h8708, hlam]
                            · linarith only [h10, h8708, hlam]
                        · linarith only [h0, h8705, hlam]
                      · have p8680_0 := h8680c.1
                        have p8680_1 := h8680c.2.1
                        have p8680_2 := h8680c.2.2.1
                        have p8680_3 := h8680c.2.2.2
                        linarith only [h10, hc12, hc24, hlam, hphi, p8680_1]
                      · have p8680_0 := h8680c.1
                        have p8680_1 := h8680c.2.1
                        have p8680_2 := h8680c.2.2.1
                        have p8680_3 := h8680c.2.2.2
                        linarith only [hlam, p8680_0]
                      · have p8680_0 := h8680c.1
                        have p8680_1 := h8680c.2.1
                        have p8680_2 := h8680c.2.2.1
                        have p8680_3 := h8680c.2.2.2
                        linarith only [h0, h10, h4, h4058, h7, h7435, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7935_1, p8680_1]
                      · have p8680_0 := h8680c.1
                        have p8680_1 := h8680c.2.1
                        have p8680_2 := h8680c.2.2.1
                        have p8680_3 := h8680c.2.2.2
                        linarith only [h6, hlam, p8680_0]
                      · have p8680_0 := h8680c.1
                        have p8680_1 := h8680c.2.1
                        have p8680_2 := h8680c.2.2.1
                        have p8680_3 := h8680c.2.2.2
                        rcases p8680_3 (m.d 0 2) (by simp) with h8716 | h8716
                        · rcases p8680_3 (m.d 1 2) (by simp) with h8717 | h8717
                          · linarith only [h8717, hlam, p8680_0]
                          · rcases p8680_3 (m.d 2 3) (by simp) with h8719 | h8719
                            · linarith only [h7931, h8719, hlam]
                            · linarith only [h10, h8719, hlam]
                        · linarith only [h0, h8716, hlam]
                      · have p8680_0 := h8680c.1
                        have p8680_1 := h8680c.2.1
                        have p8680_2 := h8680c.2.2.1
                        have p8680_3 := h8680c.2.2.2
                        linarith only [h10, hc12, hc25, hlam, hphi, p8680_1]
                      · have p8680_0 := h8680c.1
                        have p8680_1 := h8680c.2.1
                        have p8680_2 := h8680c.2.2.1
                        have p8680_3 := h8680c.2.2.2
                        linarith only [h7933, hlam, p8680_1]
                      · have p8680_0 := h8680c.1
                        have p8680_1 := h8680c.2.1
                        have p8680_2 := h8680c.2.2.1
                        have p8680_3 := h8680c.2.2.2
                        linarith only [hlam, p8680_0]
                    · linarith only [h10, h7434, h8632, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p7935_1]
                    · linarith only [h10, h8632, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p7935_1]
                  · linarith only [h6948, h8631, hlam]
                · linarith only [h4129, h8630, hlam]
          · linarith only [h1, h8625, hlam]
        · have p7935_0 := h7935c.1
          have p7935_1 := h7935c.2.1
          have p7935_2 := h7935c.2.2.1
          have p7935_3 := h7935c.2.2.2
          linarith only [h7434, hlam, p7935_0]
        · have p7935_0 := h7935c.1
          have p7935_1 := h7935c.2.1
          have p7935_2 := h7935c.2.2.1
          have p7935_3 := h7935c.2.2.2
          linarith only [hlam, p7935_0]
      · linarith only [h3576, h7434, h7435, h7934, hlam]
    · linarith only [h3576, h7434, h7933, hlam]

set_option maxHeartbeats 10278000 in
set_option maxHeartbeats 10278000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s15_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h4129 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h6948 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h7434 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  rcases m.htr 2 3 4 (by decide) (by decide) with h7435 | h7435
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s15_x1_x1_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 h4129 h6948 h7434 h7435
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s15_x1_x1_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 h4129 h6948 h7434 h7435

end R2N4
