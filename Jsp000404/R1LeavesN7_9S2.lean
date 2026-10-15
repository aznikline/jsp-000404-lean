import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5068000 in
theorem r1l7_13_24_L_I_H_I_s7_x0_x1_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h969 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 3 4 (by decide) (by decide) with h970 | h970
  · rcases m.htr 1 3 5 (by decide) (by decide) with h971 | h971
    · rcases m.htr 1 4 5 (by decide) (by decide) with h972 | h972
      · rcases m.htr 2 3 4 (by decide) (by decide) with h973 | h973
        · rcases m.htr 2 3 5 (by decide) (by decide) with h974 | h974
          · rcases m.htr 2 4 5 (by decide) (by decide) with h975 | h975
            · linarith only [h0, h4, h9, h969, h975, hc01, hc45, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h4, h9, h969, h972, h975, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h9, h969, h971, h972, h974, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b]
        · linarith only [h0, h4, h6, h9, h969, h973, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h980 | h980
        · rcases m.htr 2 3 5 (by decide) (by decide) with h981 | h981
          · rcases m.htr 2 4 5 (by decide) (by decide) with h982 | h982
            · linarith only [h9, h969, h972, h982, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h984 | h984
              · linarith only [h0, h4, h9, h969, h972, h980, h984, hc01, hc15, hlam, hphi, ht0b, ht5b]
              · rcases h3bigk with h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [hlam, p986_0]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  rcases p986_3 (m.d 0 3) (by simp) with h988 | h988
                  · rcases p986_3 (m.d 1 3) (by simp) with h989 | h989
                    · linarith only [h1, h989, hlam]
                    · rcases p986_3 (m.d 2 3) (by simp) with h991 | h991
                      · linarith only [h4, h991, hlam]
                      · linarith only [h9, h991, hlam]
                  · linarith only [h1, h988, hlam]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [h0, h4, h9, h969, h980, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p986_1]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  rcases p986_3 (m.d 0 3) (by simp) with h996 | h996
                  · rcases p986_3 (m.d 1 3) (by simp) with h997 | h997
                    · linarith only [h1, h997, hlam]
                    · linarith only [h970, h997, hlam]
                  · linarith only [h996, hlam, p986_0]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  rcases p986_3 (m.d 0 3) (by simp) with h1001 | h1001
                  · rcases p986_3 (m.d 1 3) (by simp) with h1002 | h1002
                    · linarith only [h1, h1002, hlam]
                    · linarith only [h1002, h971, hlam]
                  · linarith only [h1001, hlam, p986_0]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [h1, hlam, p986_0]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [hlam, p986_0]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [h9, hlam, p986_1]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  rcases p986_3 (m.d 0 3) (by simp) with h1009 | h1009
                  · rcases p986_3 (m.d 1 3) (by simp) with h1010 | h1010
                    · rcases p986_3 (m.d 2 3) (by simp) with h1011 | h1011
                      · rcases p986_3 (m.d 3 4) (by simp) with h1012 | h1012
                        · linarith only [h1012, hlam, p986_0]
                        · rcases p986_3 (m.d 3 5) (by simp) with h1014 | h1014
                          · linarith only [h1014, h971, hlam]
                          · linarith only [h1014, h984, hlam]
                      · linarith only [h1011, h980, hlam]
                    · linarith only [h1010, hlam, p986_0]
                  · linarith only [h1009, h6, hlam]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  rcases p986_3 (m.d 0 3) (by simp) with h1020 | h1020
                  · rcases p986_3 (m.d 1 3) (by simp) with h1021 | h1021
                    · rcases p986_3 (m.d 2 3) (by simp) with h1022 | h1022
                      · rcases p986_3 (m.d 3 4) (by simp) with h1023 | h1023
                        · linarith only [h1023, h970, hlam]
                        · rcases p986_3 (m.d 3 5) (by simp) with h1025 | h1025
                          · linarith only [h1025, hlam, p986_0]
                          · rcases h4bigk with h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c
                            · have p1027_0 := h1027c.1
                              have p1027_1 := h1027c.2.1
                              have p1027_2 := h1027c.2.2.1
                              have p1027_3 := h1027c.2.2.2
                              linarith only [hlam, p1027_0]
                            · have p1027_0 := h1027c.1
                              have p1027_1 := h1027c.2.1
                              have p1027_2 := h1027c.2.2.1
                              have p1027_3 := h1027c.2.2.2
                              rcases p1027_3 (m.d 0 4) (by simp) with h1029 | h1029
                              · rcases p1027_3 (m.d 1 4) (by simp) with h1030 | h1030
                                · linarith only [h1030, h2, hlam]
                                · rcases p1027_3 (m.d 2 4) (by simp) with h1032 | h1032
                                  · linarith only [h1032, h5, hlam]
                                  · rcases p1027_3 (m.d 3 4) (by simp) with h1034 | h1034
                                    · linarith only [h1034, h6, hlam]
                                    · rcases p1027_3 (m.d 4 5) (by simp) with h1036 | h1036
                                      · linarith only [h1036, h8, hlam]
                                      · linarith only [h1036, h972, hlam]
                              · linarith only [h1029, h2, hlam]
                            · have p1027_0 := h1027c.1
                              have p1027_1 := h1027c.2.1
                              have p1027_2 := h1027c.2.2.1
                              have p1027_3 := h1027c.2.2.2
                              rcases p1027_3 (m.d 0 4) (by simp) with h1040 | h1040
                              · rcases p1027_3 (m.d 1 4) (by simp) with h1041 | h1041
                                · linarith only [h1041, h2, hlam]
                                · linarith only [h1041, h969, hlam]
                              · linarith only [h1040, h5, hlam]
                            · have p1027_0 := h1027c.1
                              have p1027_1 := h1027c.2.1
                              have p1027_2 := h1027c.2.2.1
                              have p1027_3 := h1027c.2.2.2
                              rcases p1027_3 (m.d 0 4) (by simp) with h1045 | h1045
                              · rcases p1027_3 (m.d 1 4) (by simp) with h1046 | h1046
                                · linarith only [h1046, h2, hlam]
                                · linarith only [h1046, h970, hlam]
                              · linarith only [h1045, h6, hlam]
                            · have p1027_0 := h1027c.1
                              have p1027_1 := h1027c.2.1
                              have p1027_2 := h1027c.2.2.1
                              have p1027_3 := h1027c.2.2.2
                              linarith only [h6, h969, h972, h980, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1027_1]
                            · have p1027_0 := h1027c.1
                              have p1027_1 := h1027c.2.1
                              have p1027_2 := h1027c.2.2.1
                              have p1027_3 := h1027c.2.2.2
                              linarith only [h2, hlam, p1027_1]
                            · have p1027_0 := h1027c.1
                              have p1027_1 := h1027c.2.1
                              have p1027_2 := h1027c.2.2.1
                              have p1027_3 := h1027c.2.2.2
                              linarith only [hlam, p1027_0]
                            · have p1027_0 := h1027c.1
                              have p1027_1 := h1027c.2.1
                              have p1027_2 := h1027c.2.2.1
                              have p1027_3 := h1027c.2.2.2
                              linarith only [h972, h980, hc34, hc45, hlam, hphi, p1027_1]
                            · have p1027_0 := h1027c.1
                              have p1027_1 := h1027c.2.1
                              have p1027_2 := h1027c.2.2.1
                              have p1027_3 := h1027c.2.2.2
                              linarith only [h0, h4, h6, h8, h972, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1027_1]
                            · have p1027_0 := h1027c.1
                              have p1027_1 := h1027c.2.1
                              have p1027_2 := h1027c.2.2.1
                              have p1027_3 := h1027c.2.2.2
                              linarith only [h972, hlam, p1027_0]
                            · have p1027_0 := h1027c.1
                              have p1027_1 := h1027c.2.1
                              have p1027_2 := h1027c.2.2.1
                              have p1027_3 := h1027c.2.2.2
                              linarith only [h5, hlam, p1027_1]
                            · have p1027_0 := h1027c.1
                              have p1027_1 := h1027c.2.1
                              have p1027_2 := h1027c.2.2.1
                              have p1027_3 := h1027c.2.2.2
                              linarith only [h969, hlam, p1027_1]
                            · have p1027_0 := h1027c.1
                              have p1027_1 := h1027c.2.1
                              have p1027_2 := h1027c.2.2.1
                              have p1027_3 := h1027c.2.2.2
                              linarith only [hlam, p1027_0]
                            · have p1027_0 := h1027c.1
                              have p1027_1 := h1027c.2.1
                              have p1027_2 := h1027c.2.2.1
                              have p1027_3 := h1027c.2.2.2
                              linarith only [h0, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1027_1]
                            · have p1027_0 := h1027c.1
                              have p1027_1 := h1027c.2.1
                              have p1027_2 := h1027c.2.2.1
                              have p1027_3 := h1027c.2.2.2
                              linarith only [h982, hlam, p1027_0]
                            · have p1027_0 := h1027c.1
                              have p1027_1 := h1027c.2.1
                              have p1027_2 := h1027c.2.2.1
                              have p1027_3 := h1027c.2.2.2
                              linarith only [h6, hlam, p1027_1]
                            · have p1027_0 := h1027c.1
                              have p1027_1 := h1027c.2.1
                              have p1027_2 := h1027c.2.2.1
                              have p1027_3 := h1027c.2.2.2
                              linarith only [h970, hlam, p1027_0]
                            · have p1027_0 := h1027c.1
                              have p1027_1 := h1027c.2.1
                              have p1027_2 := h1027c.2.2.1
                              have p1027_3 := h1027c.2.2.2
                              linarith only [h980, hlam, p1027_0]
                            · have p1027_0 := h1027c.1
                              have p1027_1 := h1027c.2.1
                              have p1027_2 := h1027c.2.2.1
                              have p1027_3 := h1027c.2.2.2
                              linarith only [hlam, p1027_0]
                            · have p1027_0 := h1027c.1
                              have p1027_1 := h1027c.2.1
                              have p1027_2 := h1027c.2.2.1
                              have p1027_3 := h1027c.2.2.2
                              linarith only [h984, hlam, p1027_0]
                            · have p1027_0 := h1027c.1
                              have p1027_1 := h1027c.2.1
                              have p1027_2 := h1027c.2.2.1
                              have p1027_3 := h1027c.2.2.2
                              linarith only [h8, hlam, p1027_0]
                            · have p1027_0 := h1027c.1
                              have p1027_1 := h1027c.2.1
                              have p1027_2 := h1027c.2.2.1
                              have p1027_3 := h1027c.2.2.2
                              linarith only [h0, h4, h6, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1027_1]
                            · have p1027_0 := h1027c.1
                              have p1027_1 := h1027c.2.1
                              have p1027_2 := h1027c.2.2.1
                              have p1027_3 := h1027c.2.2.2
                              linarith only [h0, h4, h6, h8, h980, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1027_1]
                            · have p1027_0 := h1027c.1
                              have p1027_1 := h1027c.2.1
                              have p1027_2 := h1027c.2.2.1
                              have p1027_3 := h1027c.2.2.2
                              linarith only [h0, h4, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1027_1]
                            · have p1027_0 := h1027c.1
                              have p1027_1 := h1027c.2.1
                              have p1027_2 := h1027c.2.2.1
                              have p1027_3 := h1027c.2.2.2
                              linarith only [hlam, p1027_0]
                      · linarith only [h1022, h981, hlam]
                    · linarith only [h1021, hlam, p986_0]
                  · linarith only [h1020, h7, hlam]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [h4, hlam, p986_0]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [h0, h4, h9, h969, h980, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p986_1]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [hlam, p986_0]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  rcases p986_3 (m.d 0 3) (by simp) with h1077 | h1077
                  · rcases p986_3 (m.d 1 3) (by simp) with h1078 | h1078
                    · linarith only [h1078, h9, hlam]
                    · linarith only [h1078, h970, hlam]
                  · linarith only [h1077, h6, hlam]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  rcases p986_3 (m.d 0 3) (by simp) with h1082 | h1082
                  · rcases p986_3 (m.d 1 3) (by simp) with h1083 | h1083
                    · linarith only [h1083, h9, hlam]
                    · linarith only [h1083, h971, hlam]
                  · linarith only [h1082, h7, hlam]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [h6, hlam, p986_0]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [h970, hlam, p986_0]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [h980, hlam, p986_0]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [hlam, p986_0]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [h984, hlam, p986_1]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [h7, hlam, p986_0]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [h971, hlam, p986_0]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [h981, hlam, p986_0]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [h1, h971, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p986_1]
                · have p986_0 := h986c.1
                  have p986_1 := h986c.2.1
                  have p986_2 := h986c.2.2.1
                  have p986_3 := h986c.2.2.2
                  linarith only [hlam, p986_0]
          · linarith only [h9, h971, h981, hlam]
        · linarith only [h0, h4, h6, h9, h969, h980, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h1099 | h1099
      · linarith only [h1099, h9, h969, h971, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1101 | h1101
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1102 | h1102
          · linarith only [h0, h1101, h1102, h4, h9, h969, h971, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h1101, h1102, h4, h7, h9, h969, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h0, h1101, h4, h6, h9, h969, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
  · linarith only [h9, h969, h970, hlam]

end R2N4
