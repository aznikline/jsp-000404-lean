import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_24S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6172000 in
set_option maxHeartbeats 6172000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_s3_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h999 | h999
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1000 | h1000
    · linarith only [h1000, h4, h5, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1002 | h1002
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1003 | h1003
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1004 | h1004
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1005 | h1005
            · linarith only [h0, h1005, h5, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1007 | h1007
              · linarith only [h1, h1000, h1007, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1009 | h1009
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1010 | h1010
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1011 | h1011
                    · linarith only [h1000, h1004, h1005, h1011, h2, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1013 | h1013
                      · linarith only [h1004, h1005, h1013, h2, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · linarith only [h1, h1009, h1013, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h1000, h1002, h1003, h1004, h1005, h1010, hc23, hc34, hlam, hphi]
                · linarith only [h1000, h1002, h1009, hc13, hc34, hlam, hphi]
          · linarith only [h1004, h4, h5, hc12, hc24, hlam, hphi]
        · linarith only [h1002, h1003, h4, h5, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1020 | h1020
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1021 | h1021
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1022 | h1022
            · linarith only [h0, h1022, h5, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1024 | h1024
              · linarith only [h1, h1000, h1024, h4, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1026 | h1026
                · linarith only [h1, h1002, h1026, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1028 | h1028
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1029 | h1029
                    · linarith only [h0, h1000, h1021, h1029, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1031 | h1031
                      · linarith only [h1002, h1021, h1022, h1031, h2, hc05, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1033 | h1033
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1034 | h1034
                          · rcases h0bigk with h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c | h1035c
                            · have p1035_0 := h1035c.1
                              have p1035_1 := h1035c.2.1
                              have p1035_2 := h1035c.2.2.1
                              have p1035_3 := h1035c.2.2.2
                              linarith only [hlam, p1035_0]
                            · have p1035_0 := h1035c.1
                              have p1035_1 := h1035c.2.1
                              have p1035_2 := h1035c.2.2.1
                              have p1035_3 := h1035c.2.2.2
                              linarith only [h0, h1021, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1035_1, u1elo0]
                            · have p1035_0 := h1035c.1
                              have p1035_1 := h1035c.2.1
                              have p1035_2 := h1035c.2.2.1
                              have p1035_3 := h1035c.2.2.2
                              rcases p1035_3 (m.d 0 1) (by simp) with h1038 | h1038
                              · rcases p1035_3 (m.d 0 2) (by simp) with h1039 | h1039
                                · linarith only [h0, h1039, hlam]
                                · linarith only [h1039, h4, hlam]
                              · linarith only [h1, h1038, hlam]
                            · have p1035_0 := h1035c.1
                              have p1035_1 := h1035c.2.1
                              have p1035_2 := h1035c.2.2.1
                              have p1035_3 := h1035c.2.2.2
                              linarith only [h0, h1021, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1035_1, u1elo0]
                            · have p1035_0 := h1035c.1
                              have p1035_1 := h1035c.2.1
                              have p1035_2 := h1035c.2.2.1
                              have p1035_3 := h1035c.2.2.2
                              rcases p1035_3 (m.d 0 1) (by simp) with h1044 | h1044
                              · rcases p1035_3 (m.d 0 2) (by simp) with h1045 | h1045
                                · linarith only [h0, h1045, hlam]
                                · linarith only [h1045, h999, hlam]
                              · linarith only [h1044, h3, hlam]
                            · have p1035_0 := h1035c.1
                              have p1035_1 := h1035c.2.1
                              have p1035_2 := h1035c.2.2.1
                              have p1035_3 := h1035c.2.2.2
                              linarith only [h0, hlam, p1035_0]
                            · have p1035_0 := h1035c.1
                              have p1035_1 := h1035c.2.1
                              have p1035_2 := h1035c.2.2.1
                              have p1035_3 := h1035c.2.2.2
                              linarith only [hlam, p1035_0]
                            · have p1035_0 := h1035c.1
                              have p1035_1 := h1035c.2.1
                              have p1035_2 := h1035c.2.2.1
                              have p1035_3 := h1035c.2.2.2
                              linarith only [h1, h1021, h1029, h5, hc23, hc34, hlam, hphi, p1035_1]
                            · have p1035_0 := h1035c.1
                              have p1035_1 := h1035c.2.1
                              have p1035_2 := h1035c.2.2.1
                              have p1035_3 := h1035c.2.2.2
                              linarith only [h5, hlam, p1035_1]
                            · have p1035_0 := h1035c.1
                              have p1035_1 := h1035c.2.1
                              have p1035_2 := h1035c.2.2.1
                              have p1035_3 := h1035c.2.2.2
                              linarith only [h1, h1002, h1021, h1029, h5, hc23, hc34, hlam, hphi, p1035_1]
                            · have p1035_0 := h1035c.1
                              have p1035_1 := h1035c.2.1
                              have p1035_2 := h1035c.2.2.1
                              have p1035_3 := h1035c.2.2.2
                              linarith only [h1, hlam, p1035_1]
                            · have p1035_0 := h1035c.1
                              have p1035_1 := h1035c.2.1
                              have p1035_2 := h1035c.2.2.1
                              have p1035_3 := h1035c.2.2.2
                              linarith only [h4, hlam, p1035_1]
                            · have p1035_0 := h1035c.1
                              have p1035_1 := h1035c.2.1
                              have p1035_2 := h1035c.2.2.1
                              have p1035_3 := h1035c.2.2.2
                              linarith only [hlam, p1035_0]
                            · have p1035_0 := h1035c.1
                              have p1035_1 := h1035c.2.1
                              have p1035_2 := h1035c.2.2.1
                              have p1035_3 := h1035c.2.2.2
                              linarith only [h1000, hlam, p1035_1]
                            · have p1035_0 := h1035c.1
                              have p1035_1 := h1035c.2.1
                              have p1035_2 := h1035c.2.2.1
                              have p1035_3 := h1035c.2.2.2
                              linarith only [h1002, hlam, p1035_1]
                            · have p1035_0 := h1035c.1
                              have p1035_1 := h1035c.2.1
                              have p1035_2 := h1035c.2.2.1
                              have p1035_3 := h1035c.2.2.2
                              linarith only [h2, hlam, p1035_0]
                            · have p1035_0 := h1035c.1
                              have p1035_1 := h1035c.2.1
                              have p1035_2 := h1035c.2.2.1
                              have p1035_3 := h1035c.2.2.2
                              linarith only [h0, h1021, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1035_1, u0elo3]
                            · have p1035_0 := h1035c.1
                              have p1035_1 := h1035c.2.1
                              have p1035_2 := h1035c.2.2.1
                              have p1035_3 := h1035c.2.2.2
                              rcases p1035_3 (m.d 0 1) (by simp) with h1061 | h1061
                              · rcases p1035_3 (m.d 0 2) (by simp) with h1062 | h1062
                                · linarith only [h1062, h5, hlam]
                                · linarith only [h1062, h4, hlam]
                              · linarith only [h1, h1061, hlam]
                            · have p1035_0 := h1035c.1
                              have p1035_1 := h1035c.2.1
                              have p1035_2 := h1035c.2.2.1
                              have p1035_3 := h1035c.2.2.2
                              linarith only [hlam, p1035_0]
                            · have p1035_0 := h1035c.1
                              have p1035_1 := h1035c.2.1
                              have p1035_2 := h1035c.2.2.1
                              have p1035_3 := h1035c.2.2.2
                              rcases p1035_3 (m.d 0 1) (by simp) with h1067 | h1067
                              · rcases p1035_3 (m.d 0 2) (by simp) with h1068 | h1068
                                · linarith only [h1068, h5, hlam]
                                · linarith only [h1068, h999, hlam]
                              · linarith only [h1067, h3, hlam]
                            · have p1035_0 := h1035c.1
                              have p1035_1 := h1035c.2.1
                              have p1035_2 := h1035c.2.2.1
                              have p1035_3 := h1035c.2.2.2
                              linarith only [h3, hlam, p1035_0]
                            · have p1035_0 := h1035c.1
                              have p1035_1 := h1035c.2.1
                              have p1035_2 := h1035c.2.2.1
                              have p1035_3 := h1035c.2.2.2
                              linarith only [h999, hlam, p1035_1]
                            · have p1035_0 := h1035c.1
                              have p1035_1 := h1035c.2.1
                              have p1035_2 := h1035c.2.2.1
                              have p1035_3 := h1035c.2.2.2
                              linarith only [h1, h1021, h1029, h5, h999, hc23, hc34, hlam, hphi, p1035_1]
                            · have p1035_0 := h1035c.1
                              have p1035_1 := h1035c.2.1
                              have p1035_2 := h1035c.2.2.1
                              have p1035_3 := h1035c.2.2.2
                              linarith only [h1020, hlam, p1035_1]
                            · have p1035_0 := h1035c.1
                              have p1035_1 := h1035c.2.1
                              have p1035_2 := h1035c.2.2.1
                              have p1035_3 := h1035c.2.2.2
                              linarith only [hlam, p1035_0]
                          · linarith only [h0, h1021, h1029, h1034, h5, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h0, h1021, h1028, h1033, h2, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h1020, h1021, h1022, h1028, h2, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
          · linarith only [h1021, h4, h5, hc12, hc24, hlam, hphi]
        · linarith only [h1020, h5, h999, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1082 | h1082
    · linarith only [h1082, h4, h5, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1084 | h1084
      · linarith only [h1084, h4, h999, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1086 | h1086
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1087 | h1087
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1088 | h1088
            · linarith only [h0, h1088, h5, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1090 | h1090
              · linarith only [h1, h1082, h1086, h1090, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1092 | h1092
                · linarith only [h1, h1084, h1092, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1094 | h1094
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1095 | h1095
                    · linarith only [h0, h1082, h1087, h1095, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1097 | h1097
                      · linarith only [h1084, h1087, h1092, h1097, h3, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1099 | h1099
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1100 | h1100
                          · rcases h0bigk with h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [hlam, p1101_0]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [h0, h1087, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1101_1, u1elo0]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              rcases p1101_3 (m.d 0 1) (by simp) with h1104 | h1104
                              · rcases p1101_3 (m.d 0 2) (by simp) with h1105 | h1105
                                · linarith only [h0, h1105, hlam]
                                · linarith only [h1105, h4, hlam]
                              · linarith only [h1, h1104, hlam]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [h0, h1087, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1101_1, u1elo0]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [h0, h1087, h999, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1101_1, u1elo0]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [h0, hlam, p1101_0]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [hlam, p1101_0]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [h1, h1095, h5, hc13, hc34, hlam, hphi, p1101_1]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [h5, hlam, p1101_1]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [h999, hlam, p1101_0]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [h1, hlam, p1101_1]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [h4, hlam, p1101_1]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [hlam, p1101_0]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [h1082, hlam, p1101_1]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [h1084, hlam, p1101_1]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [h2, hlam, p1101_0]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [h0, h1087, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1101_1, u0elo3]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              rcases p1101_3 (m.d 0 1) (by simp) with h1123 | h1123
                              · rcases p1101_3 (m.d 0 2) (by simp) with h1124 | h1124
                                · linarith only [h1124, h5, hlam]
                                · linarith only [h1124, h4, hlam]
                              · linarith only [h1, h1123, hlam]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [hlam, p1101_0]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [h0, h1087, h2, h999, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1101_1, u1elo0]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [h3, hlam, p1101_0]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [h0, h1087, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1101_1, u0elo4]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              rcases p1101_3 (m.d 0 1) (by simp) with h1132 | h1132
                              · rcases p1101_3 (m.d 0 2) (by simp) with h1133 | h1133
                                · linarith only [h1133, h999, hlam]
                                · linarith only [h1133, h4, hlam]
                              · linarith only [h1, h1132, hlam]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [h1086, hlam, p1101_1]
                            · have p1101_0 := h1101c.1
                              have p1101_1 := h1101c.2.1
                              have p1101_2 := h1101c.2.2.1
                              have p1101_3 := h1101c.2.2.2
                              linarith only [hlam, p1101_0]
                          · linarith only [h0, h1087, h1095, h1100, h5, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h1094, h1099, h2, h5, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h1086, h1087, h1088, h1094, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
          · linarith only [h1087, h4, h999, hc12, hc25, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1143 | h1143
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1144 | h1144
            · linarith only [h0, h1144, h5, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1146 | h1146
              · linarith only [h1, h1082, h1146, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1148 | h1148
                · linarith only [h1, h1084, h1148, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1150 | h1150
                  · linarith only [h1086, h1150, h2, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1152 | h1152
                    · linarith only [h1082, h1143, h1144, h1150, h1152, h3, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1154 | h1154
                      · linarith only [h1084, h1086, h1144, h1154, h2, h4, h5, hc12, hc24, hlam, hphi]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1156 | h1156
                        · linarith only [h1086, h1143, h1144, h1152, h1156, h2, hc23, hc34, hlam, hphi]
                        · linarith only [h0, h1143, h1156, h5, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h1143, h4, h5, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 6172000 in
set_option maxHeartbeats 6172000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_s3_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_s3_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 h4 h5
  · exact r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_s3_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 h4 h5

set_option maxHeartbeats 6172000 in
set_option maxHeartbeats 6172000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_s3_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1160 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h1161 | h1161
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1162 | h1162
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1163 | h1163
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1164 | h1164
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1165 | h1165
          · linarith only [h0, h1165, h4, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1167 | h1167
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1168 | h1168
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1169 | h1169
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1170 | h1170
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1171 | h1171
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1172 | h1172
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1173 | h1173
                        · linarith only [h0, h1167, h1173, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · linarith only [h1, h1165, h1167, h1170, h1173, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · linarith only [h1, h1169, h1172, h4, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h0, h1162, h1167, h1170, h1171, h4, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1178 | h1178
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1179 | h1179
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1180 | h1180
                        · linarith only [h1167, h1170, h1180, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1182 | h1182
                          · linarith only [h1167, h1170, h1178, h1182, hlam]
                          · rcases h0bigk with h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c | h1184c
                            · have p1184_0 := h1184c.1
                              have p1184_1 := h1184c.2.1
                              have p1184_2 := h1184c.2.2.1
                              have p1184_3 := h1184c.2.2.2
                              linarith only [hlam, p1184_0]
                            · have p1184_0 := h1184c.1
                              have p1184_1 := h1184c.2.1
                              have p1184_2 := h1184c.2.2.1
                              have p1184_3 := h1184c.2.2.2
                              linarith only [h1160, h1178, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1184_1, u1elo0]
                            · have p1184_0 := h1184c.1
                              have p1184_1 := h1184c.2.1
                              have p1184_2 := h1184c.2.2.1
                              have p1184_3 := h1184c.2.2.2
                              linarith only [h1160, h1178, h4, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1184_1, u1elo0]
                            · have p1184_0 := h1184c.1
                              have p1184_1 := h1184c.2.1
                              have p1184_2 := h1184c.2.2.1
                              have p1184_3 := h1184c.2.2.2
                              linarith only [h1164, h1167, h1170, h1178, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1184_1, u1elo0]
                            · have p1184_0 := h1184c.1
                              have p1184_1 := h1184c.2.1
                              have p1184_2 := h1184c.2.2.1
                              have p1184_3 := h1184c.2.2.2
                              linarith only [h1164, h1167, h1170, h1178, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1184_1, u1elo0]
                            · have p1184_0 := h1184c.1
                              have p1184_1 := h1184c.2.1
                              have p1184_2 := h1184c.2.2.1
                              have p1184_3 := h1184c.2.2.2
                              linarith only [h0, hlam, p1184_0]
                            · have p1184_0 := h1184c.1
                              have p1184_1 := h1184c.2.1
                              have p1184_2 := h1184c.2.2.1
                              have p1184_3 := h1184c.2.2.2
                              linarith only [hlam, p1184_0]
                            · have p1184_0 := h1184c.1
                              have p1184_1 := h1184c.2.1
                              have p1184_2 := h1184c.2.2.1
                              have p1184_3 := h1184c.2.2.2
                              linarith only [h4, hlam, p1184_0]
                            · have p1184_0 := h1184c.1
                              have p1184_1 := h1184c.2.1
                              have p1184_2 := h1184c.2.2.1
                              have p1184_3 := h1184c.2.2.2
                              linarith only [h1164, h1167, h1170, h1178, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1184_1]
                            · have p1184_0 := h1184c.1
                              have p1184_1 := h1184c.2.1
                              have p1184_2 := h1184c.2.2.1
                              have p1184_3 := h1184c.2.2.2
                              linarith only [h1, h1164, h1167, h1170, h1178, h4, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1184_1, u1elo0]
                            · have p1184_0 := h1184c.1
                              have p1184_1 := h1184c.2.1
                              have p1184_2 := h1184c.2.2.1
                              have p1184_3 := h1184c.2.2.2
                              linarith only [h1, hlam, p1184_1]
                            · have p1184_0 := h1184c.1
                              have p1184_1 := h1184c.2.1
                              have p1184_2 := h1184c.2.2.1
                              have p1184_3 := h1184c.2.2.2
                              linarith only [h1, h1160, h1178, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1184_1, u1elo0]
                            · have p1184_0 := h1184c.1
                              have p1184_1 := h1184c.2.1
                              have p1184_2 := h1184c.2.2.1
                              have p1184_3 := h1184c.2.2.2
                              linarith only [hlam, p1184_0]
                            · have p1184_0 := h1184c.1
                              have p1184_1 := h1184c.2.1
                              have p1184_2 := h1184c.2.2.1
                              have p1184_3 := h1184c.2.2.2
                              linarith only [h1, h1164, h1167, h1170, h1178, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1184_1, u1elo0]
                            · have p1184_0 := h1184c.1
                              have p1184_1 := h1184c.2.1
                              have p1184_2 := h1184c.2.2.1
                              have p1184_3 := h1184c.2.2.2
                              linarith only [h1, h1164, h1167, h1170, h1178, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1184_1, u1elo0]
                            · have p1184_0 := h1184c.1
                              have p1184_1 := h1184c.2.1
                              have p1184_2 := h1184c.2.2.1
                              have p1184_3 := h1184c.2.2.2
                              linarith only [h2, hlam, p1184_0]
                            · have p1184_0 := h1184c.1
                              have p1184_1 := h1184c.2.1
                              have p1184_2 := h1184c.2.2.1
                              have p1184_3 := h1184c.2.2.2
                              linarith only [h1160, hlam, p1184_0]
                            · have p1184_0 := h1184c.1
                              have p1184_1 := h1184c.2.1
                              have p1184_2 := h1184c.2.2.1
                              have p1184_3 := h1184c.2.2.2
                              linarith only [h1162, hlam, p1184_0]
                            · have p1184_0 := h1184c.1
                              have p1184_1 := h1184c.2.1
                              have p1184_2 := h1184c.2.2.1
                              have p1184_3 := h1184c.2.2.2
                              linarith only [hlam, p1184_0]
                            · have p1184_0 := h1184c.1
                              have p1184_1 := h1184c.2.1
                              have p1184_2 := h1184c.2.2.1
                              have p1184_3 := h1184c.2.2.2
                              linarith only [h1160, h1164, h1167, h1170, h1178, hc34, hlam, hphi, ht0b, ht45, ht5b, p1184_1, u0elo1]
                            · have p1184_0 := h1184c.1
                              have p1184_1 := h1184c.2.1
                              have p1184_2 := h1184c.2.2.1
                              have p1184_3 := h1184c.2.2.2
                              linarith only [h3, hlam, p1184_0]
                            · have p1184_0 := h1184c.1
                              have p1184_1 := h1184c.2.1
                              have p1184_2 := h1184c.2.2.1
                              have p1184_3 := h1184c.2.2.2
                              linarith only [h1161, hlam, p1184_1]
                            · have p1184_0 := h1184c.1
                              have p1184_1 := h1184c.2.1
                              have p1184_2 := h1184c.2.2.1
                              have p1184_3 := h1184c.2.2.2
                              linarith only [h1163, hlam, p1184_0]
                            · have p1184_0 := h1184c.1
                              have p1184_1 := h1184c.2.1
                              have p1184_2 := h1184c.2.2.1
                              have p1184_3 := h1184c.2.2.2
                              linarith only [h1164, hlam, p1184_1]
                            · have p1184_0 := h1184c.1
                              have p1184_1 := h1184c.2.1
                              have p1184_2 := h1184c.2.2.1
                              have p1184_3 := h1184c.2.2.2
                              linarith only [hlam, p1184_0]
                      · linarith only [h1163, h1179, h4, hlam]
                    · linarith only [h1160, h1164, h1167, h1170, h1178, h4, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h1, h1163, h1165, h1167, h1169, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h1, h1162, h1165, h1167, h1168, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · linarith only [h1160, h1167, h4, hc12, hc23, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1215 | h1215
          · linarith only [h1160, h1215, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1217 | h1217
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1218 | h1218
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1219 | h1219
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1220 | h1220
                  · linarith only [h1164, h1220, h2, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1222 | h1222
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1223 | h1223
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1224 | h1224
                        · linarith only [h1164, h1217, h1224, h2, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1226 | h1226
                          · linarith only [h1164, h1217, h1222, h1226, h2, hlam]
                          · rcases h0bigk with h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c | h1228c
                            · have p1228_0 := h1228c.1
                              have p1228_1 := h1228c.2.1
                              have p1228_2 := h1228c.2.2.1
                              have p1228_3 := h1228c.2.2.2
                              linarith only [hlam, p1228_0]
                            · have p1228_0 := h1228c.1
                              have p1228_1 := h1228c.2.1
                              have p1228_2 := h1228c.2.2.1
                              have p1228_3 := h1228c.2.2.2
                              linarith only [h0, h1217, h1222, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1228_1, u1elo0]
                            · have p1228_0 := h1228c.1
                              have p1228_1 := h1228c.2.1
                              have p1228_2 := h1228c.2.2.1
                              have p1228_3 := h1228c.2.2.2
                              linarith only [h1, h1215, h1217, h1222, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1228_1, u1elo0]
                            · have p1228_0 := h1228c.1
                              have p1228_1 := h1228c.2.1
                              have p1228_2 := h1228c.2.2.1
                              have p1228_3 := h1228c.2.2.2
                              rcases p1228_3 (m.d 0 1) (by simp) with h1232 | h1232
                              · rcases p1228_3 (m.d 0 2) (by simp) with h1233 | h1233
                                · linarith only [h0, h1233, hlam]
                                · linarith only [h1160, h1233, hlam]
                              · linarith only [h1232, h2, hlam]
                            · have p1228_0 := h1228c.1
                              have p1228_1 := h1228c.2.1
                              have p1228_2 := h1228c.2.2.1
                              have p1228_3 := h1228c.2.2.2
                              rcases p1228_3 (m.d 0 1) (by simp) with h1237 | h1237
                              · rcases p1228_3 (m.d 0 2) (by simp) with h1238 | h1238
                                · linarith only [h0, h1238, hlam]
                                · linarith only [h1161, h1238, hlam]
                              · linarith only [h1237, h3, hlam]
                            · have p1228_0 := h1228c.1
                              have p1228_1 := h1228c.2.1
                              have p1228_2 := h1228c.2.2.1
                              have p1228_3 := h1228c.2.2.2
                              linarith only [h0, hlam, p1228_0]
                            · have p1228_0 := h1228c.1
                              have p1228_1 := h1228c.2.1
                              have p1228_2 := h1228c.2.2.1
                              have p1228_3 := h1228c.2.2.2
                              linarith only [hlam, p1228_0]
                            · have p1228_0 := h1228c.1
                              have p1228_1 := h1228c.2.1
                              have p1228_2 := h1228c.2.2.1
                              have p1228_3 := h1228c.2.2.2
                              linarith only [h4, hlam, p1228_0]
                            · have p1228_0 := h1228c.1
                              have p1228_1 := h1228c.2.1
                              have p1228_2 := h1228c.2.2.1
                              have p1228_3 := h1228c.2.2.2
                              rcases p1228_3 (m.d 0 1) (by simp) with h1245 | h1245
                              · rcases p1228_3 (m.d 0 2) (by simp) with h1246 | h1246
                                · rcases p1228_3 (m.d 0 3) (by simp) with h1247 | h1247
                                  · rcases p1228_3 (m.d 0 4) (by simp) with h1248 | h1248
                                    · linarith only [h1160, h1248, hlam]
                                    · rcases p1228_3 (m.d 0 5) (by simp) with h1250 | h1250
                                      · linarith only [h1161, h1250, hlam]
                                      · linarith only [h1164, h1250, hlam]
                                  · linarith only [h1162, h1247, hlam]
                                · linarith only [h1160, h1246, hlam]
                              · linarith only [h1245, h2, hlam]
                            · have p1228_0 := h1228c.1
                              have p1228_1 := h1228c.2.1
                              have p1228_2 := h1228c.2.2.1
                              have p1228_3 := h1228c.2.2.2
                              rcases p1228_3 (m.d 0 1) (by simp) with h1256 | h1256
                              · rcases p1228_3 (m.d 0 2) (by simp) with h1257 | h1257
                                · rcases p1228_3 (m.d 0 3) (by simp) with h1258 | h1258
                                  · rcases p1228_3 (m.d 0 4) (by simp) with h1259 | h1259
                                    · linarith only [h1160, h1259, hlam]
                                    · rcases p1228_3 (m.d 0 5) (by simp) with h1261 | h1261
                                      · linarith only [h1161, h1261, hlam]
                                      · rcases h3bigk with h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c
                                        · have p1263_0 := h1263c.1
                                          have p1263_1 := h1263c.2.1
                                          have p1263_2 := h1263c.2.2.1
                                          have p1263_3 := h1263c.2.2.2
                                          linarith only [hlam, p1263_0]
                                        · have p1263_0 := h1263c.1
                                          have p1263_1 := h1263c.2.1
                                          have p1263_2 := h1263c.2.2.1
                                          have p1263_3 := h1263c.2.2.2
                                          linarith only [h1215, h1217, h1222, hc34, hlam, hphi, ht0b, ht45, ht5b, p1263_1, u0elo2]
                                        · have p1263_0 := h1263c.1
                                          have p1263_1 := h1263c.2.1
                                          have p1263_2 := h1263c.2.2.1
                                          have p1263_3 := h1263c.2.2.2
                                          linarith only [h4, hlam, p1263_1]
                                        · have p1263_0 := h1263c.1
                                          have p1263_1 := h1263c.2.1
                                          have p1263_2 := h1263c.2.2.1
                                          have p1263_3 := h1263c.2.2.2
                                          rcases p1263_3 (m.d 0 3) (by simp) with h1267 | h1267
                                          · rcases p1263_3 (m.d 1 3) (by simp) with h1268 | h1268
                                            · linarith only [h1, h1268, hlam]
                                            · linarith only [h1218, h1268, hlam]
                                          · linarith only [h1267, hlam, p1263_0]
                                        · have p1263_0 := h1263c.1
                                          have p1263_1 := h1263c.2.1
                                          have p1263_2 := h1263c.2.2.1
                                          have p1263_3 := h1263c.2.2.2
                                          rcases p1263_3 (m.d 0 3) (by simp) with h1272 | h1272
                                          · rcases p1263_3 (m.d 1 3) (by simp) with h1273 | h1273
                                            · linarith only [h1, h1273, hlam]
                                            · linarith only [h1219, h1273, hlam]
                                          · linarith only [h1272, hlam, p1263_0]
                                        · have p1263_0 := h1263c.1
                                          have p1263_1 := h1263c.2.1
                                          have p1263_2 := h1263c.2.2.1
                                          have p1263_3 := h1263c.2.2.2
                                          linarith only [h1, hlam, p1263_0]
                                        · have p1263_0 := h1263c.1
                                          have p1263_1 := h1263c.2.1
                                          have p1263_2 := h1263c.2.2.1
                                          have p1263_3 := h1263c.2.2.2
                                          linarith only [hlam, p1263_0]
                                        · have p1263_0 := h1263c.1
                                          have p1263_1 := h1263c.2.1
                                          have p1263_2 := h1263c.2.2.1
                                          have p1263_3 := h1263c.2.2.2
                                          linarith only [h1215, hlam, p1263_1]
                                        · have p1263_0 := h1263c.1
                                          have p1263_1 := h1263c.2.1
                                          have p1263_2 := h1263c.2.2.1
                                          have p1263_3 := h1263c.2.2.2
                                          linarith only [h1, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1263_1, u1elo0]
                                        · have p1263_0 := h1263c.1
                                          have p1263_1 := h1263c.2.1
                                          have p1263_2 := h1263c.2.2.1
                                          have p1263_3 := h1263c.2.2.2
                                          linarith only [h1, hc35, hlam, hphi, ht01, ht0b, ht5b, p1263_1, u1elo0]
                                        · have p1263_0 := h1263c.1
                                          have p1263_1 := h1263c.2.1
                                          have p1263_2 := h1263c.2.2.1
                                          have p1263_3 := h1263c.2.2.2
                                          linarith only [h1164, h1217, h1222, h2, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1228_1, p1263_1]
                                        · have p1263_0 := h1263c.1
                                          have p1263_1 := h1263c.2.1
                                          have p1263_2 := h1263c.2.2.1
                                          have p1263_3 := h1263c.2.2.2
                                          rcases p1263_3 (m.d 0 3) (by simp) with h1283 | h1283
                                          · linarith only [h1283, h4, hlam]
                                          · linarith only [h1, h1283, hlam]
                                        · have p1263_0 := h1263c.1
                                          have p1263_1 := h1263c.2.1
                                          have p1263_2 := h1263c.2.2.1
                                          have p1263_3 := h1263c.2.2.2
                                          linarith only [hlam, p1263_0]
                                        · have p1263_0 := h1263c.1
                                          have p1263_1 := h1263c.2.1
                                          have p1263_2 := h1263c.2.2.1
                                          have p1263_3 := h1263c.2.2.2
                                          linarith only [h1164, h1217, h1222, h2, h4, hlam, p1228_1, p1263_2]
                                        · have p1263_0 := h1263c.1
                                          have p1263_1 := h1263c.2.1
                                          have p1263_2 := h1263c.2.2.1
                                          have p1263_3 := h1263c.2.2.2
                                          linarith only [h1163, h4, hlam, p1228_1, p1263_2]
                                        · have p1263_0 := h1263c.1
                                          have p1263_1 := h1263c.2.1
                                          have p1263_2 := h1263c.2.2.1
                                          have p1263_3 := h1263c.2.2.2
                                          linarith only [h1162, hlam, p1263_0]
                                        · have p1263_0 := h1263c.1
                                          have p1263_1 := h1263c.2.1
                                          have p1263_2 := h1263c.2.2.1
                                          have p1263_3 := h1263c.2.2.2
                                          linarith only [h1218, hlam, p1263_0]
                                        · have p1263_0 := h1263c.1
                                          have p1263_1 := h1263c.2.1
                                          have p1263_2 := h1263c.2.2.1
                                          have p1263_3 := h1263c.2.2.2
                                          linarith only [h1222, hlam, p1263_0]
                                        · have p1263_0 := h1263c.1
                                          have p1263_1 := h1263c.2.1
                                          have p1263_2 := h1263c.2.2.1
                                          have p1263_3 := h1263c.2.2.2
                                          linarith only [hlam, p1263_0]
                                        · have p1263_0 := h1263c.1
                                          have p1263_1 := h1263c.2.1
                                          have p1263_2 := h1263c.2.2.1
                                          have p1263_3 := h1263c.2.2.2
                                          linarith only [h1226, hlam, p1263_1]
                                        · have p1263_0 := h1263c.1
                                          have p1263_1 := h1263c.2.1
                                          have p1263_2 := h1263c.2.2.1
                                          have p1263_3 := h1263c.2.2.2
                                          linarith only [h1163, hlam, p1263_0]
                                        · have p1263_0 := h1263c.1
                                          have p1263_1 := h1263c.2.1
                                          have p1263_2 := h1263c.2.2.1
                                          have p1263_3 := h1263c.2.2.2
                                          linarith only [h1219, hlam, p1263_0]
                                        · have p1263_0 := h1263c.1
                                          have p1263_1 := h1263c.2.1
                                          have p1263_2 := h1263c.2.2.1
                                          have p1263_3 := h1263c.2.2.2
                                          linarith only [h1223, hlam, p1263_0]
                                        · have p1263_0 := h1263c.1
                                          have p1263_1 := h1263c.2.1
                                          have p1263_2 := h1263c.2.2.1
                                          have p1263_3 := h1263c.2.2.2
                                          linarith only [h1219, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, p1228_1, p1263_1, u0elo1]
                                        · have p1263_0 := h1263c.1
                                          have p1263_1 := h1263c.2.1
                                          have p1263_2 := h1263c.2.2.1
                                          have p1263_3 := h1263c.2.2.2
                                          linarith only [hlam, p1263_0]
                                  · linarith only [h1163, h1258, hlam]
                                · linarith only [h1161, h1257, hlam]
                              · linarith only [h1256, h3, hlam]
                            · have p1228_0 := h1228c.1
                              have p1228_1 := h1228c.2.1
                              have p1228_2 := h1228c.2.2.1
                              have p1228_3 := h1228c.2.2.2
                              linarith only [h1, hlam, p1228_1]
                            · have p1228_0 := h1228c.1
                              have p1228_1 := h1228c.2.1
                              have p1228_2 := h1228c.2.2.1
                              have p1228_3 := h1228c.2.2.2
                              linarith only [h0, h1217, h1222, hc34, hlam, hphi, ht0b, ht45, ht5b, p1228_1, u0elo2]
                            · have p1228_0 := h1228c.1
                              have p1228_1 := h1228c.2.1
                              have p1228_2 := h1228c.2.2.1
                              have p1228_3 := h1228c.2.2.2
                              linarith only [hlam, p1228_0]
                            · have p1228_0 := h1228c.1
                              have p1228_1 := h1228c.2.1
                              have p1228_2 := h1228c.2.2.1
                              have p1228_3 := h1228c.2.2.2
                              rcases p1228_3 (m.d 0 1) (by simp) with h1305 | h1305
                              · rcases p1228_3 (m.d 0 2) (by simp) with h1306 | h1306
                                · linarith only [h1306, h4, hlam]
                                · linarith only [h1160, h1306, hlam]
                              · linarith only [h1305, h2, hlam]
                            · have p1228_0 := h1228c.1
                              have p1228_1 := h1228c.2.1
                              have p1228_2 := h1228c.2.2.1
                              have p1228_3 := h1228c.2.2.2
                              rcases p1228_3 (m.d 0 1) (by simp) with h1310 | h1310
                              · rcases p1228_3 (m.d 0 2) (by simp) with h1311 | h1311
                                · linarith only [h1311, h4, hlam]
                                · linarith only [h1161, h1311, hlam]
                              · linarith only [h1310, h3, hlam]
                            · have p1228_0 := h1228c.1
                              have p1228_1 := h1228c.2.1
                              have p1228_2 := h1228c.2.2.1
                              have p1228_3 := h1228c.2.2.2
                              linarith only [h2, hlam, p1228_0]
                            · have p1228_0 := h1228c.1
                              have p1228_1 := h1228c.2.1
                              have p1228_2 := h1228c.2.2.1
                              have p1228_3 := h1228c.2.2.2
                              linarith only [h1160, hlam, p1228_0]
                            · have p1228_0 := h1228c.1
                              have p1228_1 := h1228c.2.1
                              have p1228_2 := h1228c.2.2.1
                              have p1228_3 := h1228c.2.2.2
                              linarith only [h1162, hlam, p1228_0]
                            · have p1228_0 := h1228c.1
                              have p1228_1 := h1228c.2.1
                              have p1228_2 := h1228c.2.2.1
                              have p1228_3 := h1228c.2.2.2
                              linarith only [hlam, p1228_0]
                            · have p1228_0 := h1228c.1
                              have p1228_1 := h1228c.2.1
                              have p1228_2 := h1228c.2.2.1
                              have p1228_3 := h1228c.2.2.2
                              linarith only [h1164, hlam, p1228_0]
                            · have p1228_0 := h1228c.1
                              have p1228_1 := h1228c.2.1
                              have p1228_2 := h1228c.2.2.1
                              have p1228_3 := h1228c.2.2.2
                              linarith only [h3, hlam, p1228_0]
                            · have p1228_0 := h1228c.1
                              have p1228_1 := h1228c.2.1
                              have p1228_2 := h1228c.2.2.1
                              have p1228_3 := h1228c.2.2.2
                              linarith only [h1161, hlam, p1228_1]
                            · have p1228_0 := h1228c.1
                              have p1228_1 := h1228c.2.1
                              have p1228_2 := h1228c.2.2.1
                              have p1228_3 := h1228c.2.2.2
                              linarith only [h1163, hlam, p1228_0]
                            · have p1228_0 := h1228c.1
                              have p1228_1 := h1228c.2.1
                              have p1228_2 := h1228c.2.2.1
                              have p1228_3 := h1228c.2.2.2
                              rcases p1228_3 (m.d 0 1) (by simp) with h1323 | h1323
                              · rcases p1228_3 (m.d 0 2) (by simp) with h1324 | h1324
                                · rcases p1228_3 (m.d 0 3) (by simp) with h1325 | h1325
                                  · rcases p1228_3 (m.d 0 4) (by simp) with h1326 | h1326
                                    · linarith only [h1164, h1326, hlam]
                                    · rcases p1228_3 (m.d 0 5) (by simp) with h1328 | h1328
                                      · rcases h3bigk with h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c
                                        · have p1329_0 := h1329c.1
                                          have p1329_1 := h1329c.2.1
                                          have p1329_2 := h1329c.2.2.1
                                          have p1329_3 := h1329c.2.2.2
                                          linarith only [hlam, p1329_0]
                                        · have p1329_0 := h1329c.1
                                          have p1329_1 := h1329c.2.1
                                          have p1329_2 := h1329c.2.2.1
                                          have p1329_3 := h1329c.2.2.2
                                          linarith only [h1, h1219, hc35, hlam, hphi, ht01, ht0b, ht5b, p1329_1, u1elo0]
                                        · have p1329_0 := h1329c.1
                                          have p1329_1 := h1329c.2.1
                                          have p1329_2 := h1329c.2.2.1
                                          have p1329_3 := h1329c.2.2.2
                                          linarith only [h4, hlam, p1329_1]
                                        · have p1329_0 := h1329c.1
                                          have p1329_1 := h1329c.2.1
                                          have p1329_2 := h1329c.2.2.1
                                          have p1329_3 := h1329c.2.2.2
                                          rcases p1329_3 (m.d 0 3) (by simp) with h1333 | h1333
                                          · rcases p1329_3 (m.d 1 3) (by simp) with h1334 | h1334
                                            · linarith only [h1, h1334, hlam]
                                            · linarith only [h1218, h1334, hlam]
                                          · linarith only [h1333, hlam, p1329_0]
                                        · have p1329_0 := h1329c.1
                                          have p1329_1 := h1329c.2.1
                                          have p1329_2 := h1329c.2.2.1
                                          have p1329_3 := h1329c.2.2.2
                                          rcases p1329_3 (m.d 0 3) (by simp) with h1338 | h1338
                                          · rcases p1329_3 (m.d 1 3) (by simp) with h1339 | h1339
                                            · linarith only [h1, h1339, hlam]
                                            · linarith only [h1219, h1339, hlam]
                                          · linarith only [h1338, hlam, p1329_0]
                                        · have p1329_0 := h1329c.1
                                          have p1329_1 := h1329c.2.1
                                          have p1329_2 := h1329c.2.2.1
                                          have p1329_3 := h1329c.2.2.2
                                          linarith only [h1, hlam, p1329_0]
                                        · have p1329_0 := h1329c.1
                                          have p1329_1 := h1329c.2.1
                                          have p1329_2 := h1329c.2.2.1
                                          have p1329_3 := h1329c.2.2.2
                                          linarith only [hlam, p1329_0]
                                        · have p1329_0 := h1329c.1
                                          have p1329_1 := h1329c.2.1
                                          have p1329_2 := h1329c.2.2.1
                                          have p1329_3 := h1329c.2.2.2
                                          linarith only [h1215, hlam, p1329_1]
                                        · have p1329_0 := h1329c.1
                                          have p1329_1 := h1329c.2.1
                                          have p1329_2 := h1329c.2.2.1
                                          have p1329_3 := h1329c.2.2.2
                                          linarith only [h1, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1329_1, u1elo0]
                                        · have p1329_0 := h1329c.1
                                          have p1329_1 := h1329c.2.1
                                          have p1329_2 := h1329c.2.2.1
                                          have p1329_3 := h1329c.2.2.2
                                          linarith only [h1, h1226, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1329_1, u1elo0]
                                        · have p1329_0 := h1329c.1
                                          have p1329_1 := h1329c.2.1
                                          have p1329_2 := h1329c.2.2.1
                                          have p1329_3 := h1329c.2.2.2
                                          linarith only [h1161, h1217, h1222, h2, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1228_1, p1329_1]
                                        · have p1329_0 := h1329c.1
                                          have p1329_1 := h1329c.2.1
                                          have p1329_2 := h1329c.2.2.1
                                          have p1329_3 := h1329c.2.2.2
                                          rcases p1329_3 (m.d 0 3) (by simp) with h1349 | h1349
                                          · linarith only [h1349, h4, hlam]
                                          · linarith only [h1, h1349, hlam]
                                        · have p1329_0 := h1329c.1
                                          have p1329_1 := h1329c.2.1
                                          have p1329_2 := h1329c.2.2.1
                                          have p1329_3 := h1329c.2.2.2
                                          linarith only [hlam, p1329_0]
                                        · have p1329_0 := h1329c.1
                                          have p1329_1 := h1329c.2.1
                                          have p1329_2 := h1329c.2.2.1
                                          have p1329_3 := h1329c.2.2.2
                                          linarith only [h1161, h1217, h1222, h2, h4, hlam, p1228_1, p1329_2]
                                        · have p1329_0 := h1329c.1
                                          have p1329_1 := h1329c.2.1
                                          have p1329_2 := h1329c.2.2.1
                                          have p1329_3 := h1329c.2.2.2
                                          rcases p1329_3 (m.d 0 3) (by simp) with h1354 | h1354
                                          · linarith only [h1354, h4, hlam]
                                          · linarith only [h1163, h1354, hlam]
                                        · have p1329_0 := h1329c.1
                                          have p1329_1 := h1329c.2.1
                                          have p1329_2 := h1329c.2.2.1
                                          have p1329_3 := h1329c.2.2.2
                                          linarith only [h1162, hlam, p1329_0]
                                        · have p1329_0 := h1329c.1
                                          have p1329_1 := h1329c.2.1
                                          have p1329_2 := h1329c.2.2.1
                                          have p1329_3 := h1329c.2.2.2
                                          linarith only [h1218, hlam, p1329_0]
                                        · have p1329_0 := h1329c.1
                                          have p1329_1 := h1329c.2.1
                                          have p1329_2 := h1329c.2.2.1
                                          have p1329_3 := h1329c.2.2.2
                                          linarith only [h1222, hlam, p1329_0]
                                        · have p1329_0 := h1329c.1
                                          have p1329_1 := h1329c.2.1
                                          have p1329_2 := h1329c.2.2.1
                                          have p1329_3 := h1329c.2.2.2
                                          linarith only [hlam, p1329_0]
                                        · have p1329_0 := h1329c.1
                                          have p1329_1 := h1329c.2.1
                                          have p1329_2 := h1329c.2.2.1
                                          have p1329_3 := h1329c.2.2.2
                                          linarith only [h1226, hlam, p1329_1]
                                        · have p1329_0 := h1329c.1
                                          have p1329_1 := h1329c.2.1
                                          have p1329_2 := h1329c.2.2.1
                                          have p1329_3 := h1329c.2.2.2
                                          linarith only [h1163, hlam, p1329_0]
                                        · have p1329_0 := h1329c.1
                                          have p1329_1 := h1329c.2.1
                                          have p1329_2 := h1329c.2.2.1
                                          have p1329_3 := h1329c.2.2.2
                                          linarith only [h1219, hlam, p1329_0]
                                        · have p1329_0 := h1329c.1
                                          have p1329_1 := h1329c.2.1
                                          have p1329_2 := h1329c.2.2.1
                                          have p1329_3 := h1329c.2.2.2
                                          linarith only [h1223, hlam, p1329_0]
                                        · have p1329_0 := h1329c.1
                                          have p1329_1 := h1329c.2.1
                                          have p1329_2 := h1329c.2.2.1
                                          have p1329_3 := h1329c.2.2.2
                                          linarith only [h1219, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1329_1, u1elo2]
                                        · have p1329_0 := h1329c.1
                                          have p1329_1 := h1329c.2.1
                                          have p1329_2 := h1329c.2.2.1
                                          have p1329_3 := h1329c.2.2.2
                                          linarith only [hlam, p1329_0]
                                      · linarith only [h1164, h1328, hlam]
                                  · linarith only [h1162, h1325, hlam]
                                · linarith only [h1160, h1324, hlam]
                              · linarith only [h1323, h2, hlam]
                            · have p1228_0 := h1228c.1
                              have p1228_1 := h1228c.2.1
                              have p1228_2 := h1228c.2.2.1
                              have p1228_3 := h1228c.2.2.2
                              linarith only [hlam, p1228_0]
                      · linarith only [h1, h1219, h1223, h4, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h1162, h1222, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h1, h1163, h1215, h1217, h1219, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h1, h1162, h1215, h1217, h1218, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · linarith only [h1160, h1217, h4, hc12, hc23, hlam, hphi]
      · linarith only [h1161, h1163, h4, hlam]
    · linarith only [h1160, h1162, h4, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1379 | h1379
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1380 | h1380
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1381 | h1381
        · linarith only [h1160, h1161, h1381, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1383 | h1383
          · linarith only [h0, h1383, h4, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1385 | h1385
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1386 | h1386
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1387 | h1387
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1388 | h1388
                  · linarith only [h1160, h1161, h1381, h1388, h2, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1390 | h1390
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1391 | h1391
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1392 | h1392
                        · linarith only [h1381, h1385, h1392, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1394 | h1394
                          · linarith only [h1, h1161, h1379, h1392, h1394, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · rcases h0bigk with h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c
                            · have p1396_0 := h1396c.1
                              have p1396_1 := h1396c.2.1
                              have p1396_2 := h1396c.2.2.1
                              have p1396_3 := h1396c.2.2.2
                              linarith only [hlam, p1396_0]
                            · have p1396_0 := h1396c.1
                              have p1396_1 := h1396c.2.1
                              have p1396_2 := h1396c.2.2.1
                              have p1396_3 := h1396c.2.2.2
                              linarith only [h0, h1385, h1390, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1396_1, u1elo0]
                            · have p1396_0 := h1396c.1
                              have p1396_1 := h1396c.2.1
                              have p1396_2 := h1396c.2.2.1
                              have p1396_3 := h1396c.2.2.2
                              linarith only [h1, h1383, h1385, h1390, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1396_1, u1elo0]
                            · have p1396_0 := h1396c.1
                              have p1396_1 := h1396c.2.1
                              have p1396_2 := h1396c.2.2.1
                              have p1396_3 := h1396c.2.2.2
                              rcases p1396_3 (m.d 0 1) (by simp) with h1400 | h1400
                              · rcases p1396_3 (m.d 0 2) (by simp) with h1401 | h1401
                                · linarith only [h0, h1401, hlam]
                                · linarith only [h1160, h1401, hlam]
                              · linarith only [h1400, h2, hlam]
                            · have p1396_0 := h1396c.1
                              have p1396_1 := h1396c.2.1
                              have p1396_2 := h1396c.2.2.1
                              have p1396_3 := h1396c.2.2.2
                              linarith only [h0, h1161, h1385, h1390, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1396_1, u1elo0]
                            · have p1396_0 := h1396c.1
                              have p1396_1 := h1396c.2.1
                              have p1396_2 := h1396c.2.2.1
                              have p1396_3 := h1396c.2.2.2
                              linarith only [h0, hlam, p1396_0]
                            · have p1396_0 := h1396c.1
                              have p1396_1 := h1396c.2.1
                              have p1396_2 := h1396c.2.2.1
                              have p1396_3 := h1396c.2.2.2
                              linarith only [hlam, p1396_0]
                            · have p1396_0 := h1396c.1
                              have p1396_1 := h1396c.2.1
                              have p1396_2 := h1396c.2.2.1
                              have p1396_3 := h1396c.2.2.2
                              linarith only [h4, hlam, p1396_0]
                            · have p1396_0 := h1396c.1
                              have p1396_1 := h1396c.2.1
                              have p1396_2 := h1396c.2.2.1
                              have p1396_3 := h1396c.2.2.2
                              linarith only [h1161, h1392, hc04, hc45, hlam, hphi, p1396_1]
                            · have p1396_0 := h1396c.1
                              have p1396_1 := h1396c.2.1
                              have p1396_2 := h1396c.2.2.1
                              have p1396_3 := h1396c.2.2.2
                              linarith only [h1161, hlam, p1396_0]
                            · have p1396_0 := h1396c.1
                              have p1396_1 := h1396c.2.1
                              have p1396_2 := h1396c.2.2.1
                              have p1396_3 := h1396c.2.2.2
                              linarith only [h1, hlam, p1396_1]
                            · have p1396_0 := h1396c.1
                              have p1396_1 := h1396c.2.1
                              have p1396_2 := h1396c.2.2.1
                              have p1396_3 := h1396c.2.2.2
                              linarith only [h0, h1385, hc24, hlam, hphi, ht0b, ht45, ht5b, p1396_1, u0elo2]
                            · have p1396_0 := h1396c.1
                              have p1396_1 := h1396c.2.1
                              have p1396_2 := h1396c.2.2.1
                              have p1396_3 := h1396c.2.2.2
                              linarith only [hlam, p1396_0]
                            · have p1396_0 := h1396c.1
                              have p1396_1 := h1396c.2.1
                              have p1396_2 := h1396c.2.2.1
                              have p1396_3 := h1396c.2.2.2
                              rcases p1396_3 (m.d 0 1) (by simp) with h1414 | h1414
                              · rcases p1396_3 (m.d 0 2) (by simp) with h1415 | h1415
                                · linarith only [h1415, h4, hlam]
                                · linarith only [h1160, h1415, hlam]
                              · linarith only [h1414, h2, hlam]
                            · have p1396_0 := h1396c.1
                              have p1396_1 := h1396c.2.1
                              have p1396_2 := h1396c.2.2.1
                              have p1396_3 := h1396c.2.2.2
                              linarith only [h0, h1, h1161, h1385, h1390, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1396_1, u1elo0]
                            · have p1396_0 := h1396c.1
                              have p1396_1 := h1396c.2.1
                              have p1396_2 := h1396c.2.2.1
                              have p1396_3 := h1396c.2.2.2
                              linarith only [h2, hlam, p1396_0]
                            · have p1396_0 := h1396c.1
                              have p1396_1 := h1396c.2.1
                              have p1396_2 := h1396c.2.2.1
                              have p1396_3 := h1396c.2.2.2
                              linarith only [h1160, hlam, p1396_0]
                            · have p1396_0 := h1396c.1
                              have p1396_1 := h1396c.2.1
                              have p1396_2 := h1396c.2.2.1
                              have p1396_3 := h1396c.2.2.2
                              linarith only [h1379, hlam, p1396_0]
                            · have p1396_0 := h1396c.1
                              have p1396_1 := h1396c.2.1
                              have p1396_2 := h1396c.2.2.1
                              have p1396_3 := h1396c.2.2.2
                              linarith only [hlam, p1396_0]
                            · have p1396_0 := h1396c.1
                              have p1396_1 := h1396c.2.1
                              have p1396_2 := h1396c.2.2.1
                              have p1396_3 := h1396c.2.2.2
                              linarith only [h1381, hlam, p1396_0]
                            · have p1396_0 := h1396c.1
                              have p1396_1 := h1396c.2.1
                              have p1396_2 := h1396c.2.2.1
                              have p1396_3 := h1396c.2.2.2
                              linarith only [h3, hlam, p1396_0]
                            · have p1396_0 := h1396c.1
                              have p1396_1 := h1396c.2.1
                              have p1396_2 := h1396c.2.2.1
                              have p1396_3 := h1396c.2.2.2
                              linarith only [h0, h1385, h1390, hc34, hlam, hphi, ht0b, ht45, ht5b, p1396_1, u0elo4]
                            · have p1396_0 := h1396c.1
                              have p1396_1 := h1396c.2.1
                              have p1396_2 := h1396c.2.2.1
                              have p1396_3 := h1396c.2.2.2
                              linarith only [h1380, hlam, p1396_0]
                            · have p1396_0 := h1396c.1
                              have p1396_1 := h1396c.2.1
                              have p1396_2 := h1396c.2.2.1
                              have p1396_3 := h1396c.2.2.2
                              rcases p1396_3 (m.d 0 1) (by simp) with h1428 | h1428
                              · rcases p1396_3 (m.d 0 2) (by simp) with h1429 | h1429
                                · linarith only [h1161, h1429, hlam]
                                · linarith only [h1160, h1429, hlam]
                              · linarith only [h1428, h2, hlam]
                            · have p1396_0 := h1396c.1
                              have p1396_1 := h1396c.2.1
                              have p1396_2 := h1396c.2.2.1
                              have p1396_3 := h1396c.2.2.2
                              linarith only [hlam, p1396_0]
                      · linarith only [h1380, h1391, h4, hlam]
                    · linarith only [h0, h1379, h1385, h1390, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                · linarith only [h1, h1380, h1383, h1385, h1387, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h1, h1379, h1383, h1385, h1386, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · linarith only [h1160, h1385, h4, hc12, hc23, hlam, hphi]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1439 | h1439
        · linarith only [h1160, h1161, h1439, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1441 | h1441
          · linarith only [h1160, h1441, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1443 | h1443
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1444 | h1444
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1445 | h1445
                · linarith only [h1, h1380, h1445, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1447 | h1447
                  · linarith only [h1439, h1447, h2, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1449 | h1449
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1450 | h1450
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1451 | h1451
                        · linarith only [h0, h1439, h1443, h1451, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1453 | h1453
                          · linarith only [h0, h1380, h1443, h1449, h1450, h1451, h1453, h4, hlam]
                          · rcases h0bigk with h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c
                            · have p1455_0 := h1455c.1
                              have p1455_1 := h1455c.2.1
                              have p1455_2 := h1455c.2.2.1
                              have p1455_3 := h1455c.2.2.2
                              linarith only [hlam, p1455_0]
                            · have p1455_0 := h1455c.1
                              have p1455_1 := h1455c.2.1
                              have p1455_2 := h1455c.2.2.1
                              have p1455_3 := h1455c.2.2.2
                              linarith only [h0, h1443, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1455_1, u1elo0]
                            · have p1455_0 := h1455c.1
                              have p1455_1 := h1455c.2.1
                              have p1455_2 := h1455c.2.2.1
                              have p1455_3 := h1455c.2.2.2
                              linarith only [h0, h1443, h1449, h4, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1455_1, u1elo0]
                            · have p1455_0 := h1455c.1
                              have p1455_1 := h1455c.2.1
                              have p1455_2 := h1455c.2.2.1
                              have p1455_3 := h1455c.2.2.2
                              rcases p1455_3 (m.d 0 1) (by simp) with h1459 | h1459
                              · rcases p1455_3 (m.d 0 2) (by simp) with h1460 | h1460
                                · linarith only [h0, h1460, hlam]
                                · linarith only [h1160, h1460, hlam]
                              · linarith only [h1459, h2, hlam]
                            · have p1455_0 := h1455c.1
                              have p1455_1 := h1455c.2.1
                              have p1455_2 := h1455c.2.2.1
                              have p1455_3 := h1455c.2.2.2
                              linarith only [h0, h1161, h1443, h1449, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1455_1, u1elo0]
                            · have p1455_0 := h1455c.1
                              have p1455_1 := h1455c.2.1
                              have p1455_2 := h1455c.2.2.1
                              have p1455_3 := h1455c.2.2.2
                              linarith only [h0, hlam, p1455_0]
                            · have p1455_0 := h1455c.1
                              have p1455_1 := h1455c.2.1
                              have p1455_2 := h1455c.2.2.1
                              have p1455_3 := h1455c.2.2.2
                              linarith only [hlam, p1455_0]
                            · have p1455_0 := h1455c.1
                              have p1455_1 := h1455c.2.1
                              have p1455_2 := h1455c.2.2.1
                              have p1455_3 := h1455c.2.2.2
                              linarith only [h4, hlam, p1455_0]
                            · have p1455_0 := h1455c.1
                              have p1455_1 := h1455c.2.1
                              have p1455_2 := h1455c.2.2.1
                              have p1455_3 := h1455c.2.2.2
                              linarith only [h1380, h1443, h1449, h1450, h2, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1455_1]
                            · have p1455_0 := h1455c.1
                              have p1455_1 := h1455c.2.1
                              have p1455_2 := h1455c.2.2.1
                              have p1455_3 := h1455c.2.2.2
                              linarith only [h1161, hlam, p1455_0]
                            · have p1455_0 := h1455c.1
                              have p1455_1 := h1455c.2.1
                              have p1455_2 := h1455c.2.2.1
                              have p1455_3 := h1455c.2.2.2
                              linarith only [h1, hlam, p1455_1]
                            · have p1455_0 := h1455c.1
                              have p1455_1 := h1455c.2.1
                              have p1455_2 := h1455c.2.2.1
                              have p1455_3 := h1455c.2.2.2
                              linarith only [h1380, h1450, hc02, hc23, hlam, hphi, p1455_1]
                            · have p1455_0 := h1455c.1
                              have p1455_1 := h1455c.2.1
                              have p1455_2 := h1455c.2.2.1
                              have p1455_3 := h1455c.2.2.2
                              linarith only [hlam, p1455_0]
                            · have p1455_0 := h1455c.1
                              have p1455_1 := h1455c.2.1
                              have p1455_2 := h1455c.2.2.1
                              have p1455_3 := h1455c.2.2.2
                              linarith only [h1380, h1443, h1449, h1450, h2, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1455_1]
                            · have p1455_0 := h1455c.1
                              have p1455_1 := h1455c.2.1
                              have p1455_2 := h1455c.2.2.1
                              have p1455_3 := h1455c.2.2.2
                              linarith only [h1380, hlam, p1455_1]
                            · have p1455_0 := h1455c.1
                              have p1455_1 := h1455c.2.1
                              have p1455_2 := h1455c.2.2.1
                              have p1455_3 := h1455c.2.2.2
                              linarith only [h2, hlam, p1455_0]
                            · have p1455_0 := h1455c.1
                              have p1455_1 := h1455c.2.1
                              have p1455_2 := h1455c.2.2.1
                              have p1455_3 := h1455c.2.2.2
                              linarith only [h1160, hlam, p1455_0]
                            · have p1455_0 := h1455c.1
                              have p1455_1 := h1455c.2.1
                              have p1455_2 := h1455c.2.2.1
                              have p1455_3 := h1455c.2.2.2
                              linarith only [h1379, hlam, p1455_0]
                            · have p1455_0 := h1455c.1
                              have p1455_1 := h1455c.2.1
                              have p1455_2 := h1455c.2.2.1
                              have p1455_3 := h1455c.2.2.2
                              linarith only [hlam, p1455_0]
                            · have p1455_0 := h1455c.1
                              have p1455_1 := h1455c.2.1
                              have p1455_2 := h1455c.2.2.1
                              have p1455_3 := h1455c.2.2.2
                              linarith only [h1439, hlam, p1455_0]
                            · have p1455_0 := h1455c.1
                              have p1455_1 := h1455c.2.1
                              have p1455_2 := h1455c.2.2.1
                              have p1455_3 := h1455c.2.2.2
                              linarith only [h3, hlam, p1455_0]
                            · have p1455_0 := h1455c.1
                              have p1455_1 := h1455c.2.1
                              have p1455_2 := h1455c.2.2.1
                              have p1455_3 := h1455c.2.2.2
                              linarith only [h0, h1443, h1449, hc34, hlam, hphi, ht0b, ht45, ht5b, p1455_1, u0elo4]
                            · have p1455_0 := h1455c.1
                              have p1455_1 := h1455c.2.1
                              have p1455_2 := h1455c.2.2.1
                              have p1455_3 := h1455c.2.2.2
                              linarith only [h0, h1380, h1443, h1449, h1450, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1455_1]
                            · have p1455_0 := h1455c.1
                              have p1455_1 := h1455c.2.1
                              have p1455_2 := h1455c.2.2.1
                              have p1455_3 := h1455c.2.2.2
                              rcases p1455_3 (m.d 0 1) (by simp) with h1483 | h1483
                              · rcases p1455_3 (m.d 0 2) (by simp) with h1484 | h1484
                                · linarith only [h1161, h1484, hlam]
                                · linarith only [h1160, h1484, hlam]
                              · linarith only [h1483, h2, hlam]
                            · have p1455_0 := h1455c.1
                              have p1455_1 := h1455c.2.1
                              have p1455_2 := h1455c.2.2.1
                              have p1455_3 := h1455c.2.2.2
                              linarith only [hlam, p1455_0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1489 | h1489
                        · linarith only [h0, h1443, h1489, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1491 | h1491
                          · linarith only [h0, h1443, h1449, h1450, h1489, h1491, h4, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h0, h1443, h1449, h1450, h1491, h4, hc34, hc45, hlam, hphi]
                    · linarith only [h0, h1379, h1443, h1449, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
              · linarith only [h1379, h1441, h1443, h1444, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
            · linarith only [h1160, h1443, h4, hc12, hc23, hlam, hphi]
    · linarith only [h1160, h1379, h4, hlam]

set_option maxHeartbeats 6172000 in
set_option maxHeartbeats 6172000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_s3_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1160 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1498 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 4 (by decide) (by decide) with h1499 | h1499
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1500 | h1500
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1501 | h1501
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1502 | h1502
        · linarith only [h1498, h1502, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1504 | h1504
          · linarith only [h0, h1160, h1504, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1506 | h1506
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1507 | h1507
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1508 | h1508
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1509 | h1509
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1510 | h1510
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1511 | h1511
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1512 | h1512
                        · linarith only [h1, h1506, h1512, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · linarith only [h1508, h1512, h2, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · linarith only [h1, h1160, h1506, h1508, h1511, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h1500, h1510, h4, hlam]
                  · linarith only [h1499, h1509, h4, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1518 | h1518
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1519 | h1519
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1520 | h1520
                      · linarith only [h1160, h1498, h1504, h1508, h1518, h1520, hc12, hc23, hlam, hphi]
                      · linarith only [h1160, h1498, h1501, h1520, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                    · linarith only [h1, h1160, h1507, h1518, h1519, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h1, h1498, h1501, h1506, h1507, h1508, h1518, h4, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
              · linarith only [h1500, h1506, h1507, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1526 | h1526
              · linarith only [h1, h1499, h1506, h1526, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1528 | h1528
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1529 | h1529
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1530 | h1530
                    · linarith only [h1160, h1498, h1502, h1526, h1529, h1530, hc12, hc23, hlam, hphi]
                    · linarith only [h1160, h1498, h1500, h1529, h1530, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                  · linarith only [h1, h1498, h1499, h1500, h1502, h1526, h1529, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1534 | h1534
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1535 | h1535
                    · linarith only [h1160, h1498, h1502, h1526, h1535, hc12, hc24, hlam, hphi]
                    · linarith only [h1160, h1501, h1502, h1506, h1528, h1534, h1535, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h1498, h1499, h1501, h1502, h1506, h1528, h1534, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
      · linarith only [h1160, h1498, h1501, hlam]
    · linarith only [h1498, h1500, h4, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1541 | h1541
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1542 | h1542
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1543 | h1543
        · linarith only [h1498, h1543, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1545 | h1545
          · linarith only [h0, h1160, h1545, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1547 | h1547
            · linarith only [h1498, h1499, h1547, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1549 | h1549
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1550 | h1550
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1551 | h1551
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1552 | h1552
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1553 | h1553
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1554 | h1554
                        · rcases h0bigk with h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c
                          · have p1555_0 := h1555c.1
                            have p1555_1 := h1555c.2.1
                            have p1555_2 := h1555c.2.2.1
                            have p1555_3 := h1555c.2.2.2
                            linarith only [hlam, p1555_0]
                          · have p1555_0 := h1555c.1
                            have p1555_1 := h1555c.2.1
                            have p1555_2 := h1555c.2.2.1
                            have p1555_3 := h1555c.2.2.2
                            linarith only [h1498, h1552, h1554, hc45, hlam, hphi, ht01, ht0b, ht5b, p1555_1, u1elo0]
                          · have p1555_0 := h1555c.1
                            have p1555_1 := h1555c.2.1
                            have p1555_2 := h1555c.2.2.1
                            have p1555_3 := h1555c.2.2.2
                            linarith only [h1498, h1552, h1554, h4, hc45, hlam, hphi, ht01, ht0b, ht5b, p1555_1, u1elo0]
                          · have p1555_0 := h1555c.1
                            have p1555_1 := h1555c.2.1
                            have p1555_2 := h1555c.2.2.1
                            have p1555_3 := h1555c.2.2.2
                            linarith only [h1498, h1499, h1552, h1554, h4, hc45, hlam, hphi, ht01, ht0b, ht5b, p1555_1, u1elo0]
                          · have p1555_0 := h1555c.1
                            have p1555_1 := h1555c.2.1
                            have p1555_2 := h1555c.2.2.1
                            have p1555_3 := h1555c.2.2.2
                            rcases p1555_3 (m.d 0 1) (by simp) with h1560 | h1560
                            · rcases p1555_3 (m.d 0 2) (by simp) with h1561 | h1561
                              · linarith only [h0, h1561, hlam]
                              · linarith only [h1498, h1561, hlam]
                            · linarith only [h1560, h3, hlam]
                          · have p1555_0 := h1555c.1
                            have p1555_1 := h1555c.2.1
                            have p1555_2 := h1555c.2.2.1
                            have p1555_3 := h1555c.2.2.2
                            linarith only [h0, hlam, p1555_0]
                          · have p1555_0 := h1555c.1
                            have p1555_1 := h1555c.2.1
                            have p1555_2 := h1555c.2.2.1
                            have p1555_3 := h1555c.2.2.2
                            linarith only [hlam, p1555_0]
                          · have p1555_0 := h1555c.1
                            have p1555_1 := h1555c.2.1
                            have p1555_2 := h1555c.2.2.1
                            have p1555_3 := h1555c.2.2.2
                            linarith only [h4, hlam, p1555_0]
                          · have p1555_0 := h1555c.1
                            have p1555_1 := h1555c.2.1
                            have p1555_2 := h1555c.2.2.1
                            have p1555_3 := h1555c.2.2.2
                            linarith only [h1160, hlam, p1555_1]
                          · have p1555_0 := h1555c.1
                            have p1555_1 := h1555c.2.1
                            have p1555_2 := h1555c.2.2.1
                            have p1555_3 := h1555c.2.2.2
                            linarith only [h1499, h1551, h3, h4, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1555_1]
                          · have p1555_0 := h1555c.1
                            have p1555_1 := h1555c.2.1
                            have p1555_2 := h1555c.2.2.1
                            have p1555_3 := h1555c.2.2.2
                            linarith only [h1, hlam, p1555_1]
                          · have p1555_0 := h1555c.1
                            have p1555_1 := h1555c.2.1
                            have p1555_2 := h1555c.2.2.1
                            have p1555_3 := h1555c.2.2.2
                            linarith only [h0, h1499, h1551, hc12, hc23, hlam, hphi, p1555_1]
                          · have p1555_0 := h1555c.1
                            have p1555_1 := h1555c.2.1
                            have p1555_2 := h1555c.2.2.1
                            have p1555_3 := h1555c.2.2.2
                            linarith only [hlam, p1555_0]
                          · have p1555_0 := h1555c.1
                            have p1555_1 := h1555c.2.1
                            have p1555_2 := h1555c.2.2.1
                            have p1555_3 := h1555c.2.2.2
                            linarith only [h1499, hlam, p1555_1]
                          · have p1555_0 := h1555c.1
                            have p1555_1 := h1555c.2.1
                            have p1555_2 := h1555c.2.2.1
                            have p1555_3 := h1555c.2.2.2
                            linarith only [h1498, h1499, h1551, h1552, h1554, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1555_1]
                          · have p1555_0 := h1555c.1
                            have p1555_1 := h1555c.2.1
                            have p1555_2 := h1555c.2.2.1
                            have p1555_3 := h1555c.2.2.2
                            linarith only [h2, hlam, p1555_0]
                          · have p1555_0 := h1555c.1
                            have p1555_1 := h1555c.2.1
                            have p1555_2 := h1555c.2.2.1
                            have p1555_3 := h1555c.2.2.2
                            linarith only [h1498, h1552, h1554, hc45, hlam, hphi, ht0b, ht5b, p1555_1, u0elo3]
                          · have p1555_0 := h1555c.1
                            have p1555_1 := h1555c.2.1
                            have p1555_2 := h1555c.2.2.1
                            have p1555_3 := h1555c.2.2.2
                            linarith only [h1, h1499, h1543, h1551, hc12, hc23, hlam, hphi, p1555_1]
                          · have p1555_0 := h1555c.1
                            have p1555_1 := h1555c.2.1
                            have p1555_2 := h1555c.2.2.1
                            have p1555_3 := h1555c.2.2.2
                            linarith only [hlam, p1555_0]
                          · have p1555_0 := h1555c.1
                            have p1555_1 := h1555c.2.1
                            have p1555_2 := h1555c.2.2.1
                            have p1555_3 := h1555c.2.2.2
                            rcases p1555_3 (m.d 0 1) (by simp) with h1579 | h1579
                            · rcases p1555_3 (m.d 0 2) (by simp) with h1580 | h1580
                              · linarith only [h1160, h1580, hlam]
                              · linarith only [h1498, h1580, hlam]
                            · linarith only [h1579, h3, hlam]
                          · have p1555_0 := h1555c.1
                            have p1555_1 := h1555c.2.1
                            have p1555_2 := h1555c.2.2.1
                            have p1555_3 := h1555c.2.2.2
                            linarith only [h3, hlam, p1555_0]
                          · have p1555_0 := h1555c.1
                            have p1555_1 := h1555c.2.1
                            have p1555_2 := h1555c.2.2.1
                            have p1555_3 := h1555c.2.2.2
                            linarith only [h1498, hlam, p1555_1]
                          · have p1555_0 := h1555c.1
                            have p1555_1 := h1555c.2.1
                            have p1555_2 := h1555c.2.2.1
                            have p1555_3 := h1555c.2.2.2
                            linarith only [h1541, hlam, p1555_0]
                          · have p1555_0 := h1555c.1
                            have p1555_1 := h1555c.2.1
                            have p1555_2 := h1555c.2.2.1
                            have p1555_3 := h1555c.2.2.2
                            linarith only [h1542, hlam, p1555_1]
                          · have p1555_0 := h1555c.1
                            have p1555_1 := h1555c.2.1
                            have p1555_2 := h1555c.2.2.1
                            have p1555_3 := h1555c.2.2.2
                            linarith only [hlam, p1555_0]
                        · linarith only [h1499, h1542, h1554, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h1499, h1547, h1549, h1550, h1551, h1553, h2, h3, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · linarith only [h1, h1549, h1552, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1592 | h1592
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1593 | h1593
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1594 | h1594
                        · rcases h0bigk with h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c
                          · have p1595_0 := h1595c.1
                            have p1595_1 := h1595c.2.1
                            have p1595_2 := h1595c.2.2.1
                            have p1595_3 := h1595c.2.2.2
                            linarith only [hlam, p1595_0]
                          · have p1595_0 := h1595c.1
                            have p1595_1 := h1595c.2.1
                            have p1595_2 := h1595c.2.2.1
                            have p1595_3 := h1595c.2.2.2
                            linarith only [h1498, h1592, h1594, hc45, hlam, hphi, ht01, ht0b, ht5b, p1595_1, u1elo0]
                          · have p1595_0 := h1595c.1
                            have p1595_1 := h1595c.2.1
                            have p1595_2 := h1595c.2.2.1
                            have p1595_3 := h1595c.2.2.2
                            linarith only [h1498, h1592, h1594, h4, hc45, hlam, hphi, ht01, ht0b, ht5b, p1595_1, u1elo0]
                          · have p1595_0 := h1595c.1
                            have p1595_1 := h1595c.2.1
                            have p1595_2 := h1595c.2.2.1
                            have p1595_3 := h1595c.2.2.2
                            linarith only [h1498, h1499, h1592, h1594, h4, hc45, hlam, hphi, ht01, ht0b, ht5b, p1595_1, u1elo0]
                          · have p1595_0 := h1595c.1
                            have p1595_1 := h1595c.2.1
                            have p1595_2 := h1595c.2.2.1
                            have p1595_3 := h1595c.2.2.2
                            rcases p1595_3 (m.d 0 1) (by simp) with h1600 | h1600
                            · rcases p1595_3 (m.d 0 2) (by simp) with h1601 | h1601
                              · linarith only [h0, h1601, hlam]
                              · linarith only [h1498, h1601, hlam]
                            · linarith only [h1600, h3, hlam]
                          · have p1595_0 := h1595c.1
                            have p1595_1 := h1595c.2.1
                            have p1595_2 := h1595c.2.2.1
                            have p1595_3 := h1595c.2.2.2
                            linarith only [h0, hlam, p1595_0]
                          · have p1595_0 := h1595c.1
                            have p1595_1 := h1595c.2.1
                            have p1595_2 := h1595c.2.2.1
                            have p1595_3 := h1595c.2.2.2
                            linarith only [hlam, p1595_0]
                          · have p1595_0 := h1595c.1
                            have p1595_1 := h1595c.2.1
                            have p1595_2 := h1595c.2.2.1
                            have p1595_3 := h1595c.2.2.2
                            linarith only [h4, hlam, p1595_0]
                          · have p1595_0 := h1595c.1
                            have p1595_1 := h1595c.2.1
                            have p1595_2 := h1595c.2.2.1
                            have p1595_3 := h1595c.2.2.2
                            linarith only [h1160, hlam, p1595_1]
                          · have p1595_0 := h1595c.1
                            have p1595_1 := h1595c.2.1
                            have p1595_2 := h1595c.2.2.1
                            have p1595_3 := h1595c.2.2.2
                            linarith only [h1551, h4, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1595_1]
                          · have p1595_0 := h1595c.1
                            have p1595_1 := h1595c.2.1
                            have p1595_2 := h1595c.2.2.1
                            have p1595_3 := h1595c.2.2.2
                            linarith only [h1, hlam, p1595_1]
                          · have p1595_0 := h1595c.1
                            have p1595_1 := h1595c.2.1
                            have p1595_2 := h1595c.2.2.1
                            have p1595_3 := h1595c.2.2.2
                            linarith only [h1498, h1499, hc25, hlam, hphi, ht0b, ht5b, p1595_1, u0elo3]
                          · have p1595_0 := h1595c.1
                            have p1595_1 := h1595c.2.1
                            have p1595_2 := h1595c.2.2.1
                            have p1595_3 := h1595c.2.2.2
                            linarith only [hlam, p1595_0]
                          · have p1595_0 := h1595c.1
                            have p1595_1 := h1595c.2.1
                            have p1595_2 := h1595c.2.2.1
                            have p1595_3 := h1595c.2.2.2
                            linarith only [h1499, hlam, p1595_1]
                          · have p1595_0 := h1595c.1
                            have p1595_1 := h1595c.2.1
                            have p1595_2 := h1595c.2.2.1
                            have p1595_3 := h1595c.2.2.2
                            rcases p1595_3 (m.d 0 1) (by simp) with h1614 | h1614
                            · rcases p1595_3 (m.d 0 2) (by simp) with h1615 | h1615
                              · linarith only [h1615, h4, hlam]
                              · linarith only [h1498, h1615, hlam]
                            · linarith only [h1614, h3, hlam]
                          · have p1595_0 := h1595c.1
                            have p1595_1 := h1595c.2.1
                            have p1595_2 := h1595c.2.2.1
                            have p1595_3 := h1595c.2.2.2
                            linarith only [h2, hlam, p1595_0]
                          · have p1595_0 := h1595c.1
                            have p1595_1 := h1595c.2.1
                            have p1595_2 := h1595c.2.2.1
                            have p1595_3 := h1595c.2.2.2
                            linarith only [h1498, h1592, h1594, h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p1595_1, u1elo0]
                          · have p1595_0 := h1595c.1
                            have p1595_1 := h1595c.2.1
                            have p1595_2 := h1595c.2.2.1
                            have p1595_3 := h1595c.2.2.2
                            linarith only [h1498, h1592, h1594, h2, h4, hc45, hlam, hphi, ht01, ht0b, ht5b, p1595_1, u1elo0]
                          · have p1595_0 := h1595c.1
                            have p1595_1 := h1595c.2.1
                            have p1595_2 := h1595c.2.2.1
                            have p1595_3 := h1595c.2.2.2
                            linarith only [hlam, p1595_0]
                          · have p1595_0 := h1595c.1
                            have p1595_1 := h1595c.2.1
                            have p1595_2 := h1595c.2.2.1
                            have p1595_3 := h1595c.2.2.2
                            rcases p1595_3 (m.d 0 1) (by simp) with h1623 | h1623
                            · rcases p1595_3 (m.d 0 2) (by simp) with h1624 | h1624
                              · linarith only [h1160, h1624, hlam]
                              · linarith only [h1498, h1624, hlam]
                            · linarith only [h1623, h3, hlam]
                          · have p1595_0 := h1595c.1
                            have p1595_1 := h1595c.2.1
                            have p1595_2 := h1595c.2.2.1
                            have p1595_3 := h1595c.2.2.2
                            linarith only [h3, hlam, p1595_0]
                          · have p1595_0 := h1595c.1
                            have p1595_1 := h1595c.2.1
                            have p1595_2 := h1595c.2.2.1
                            have p1595_3 := h1595c.2.2.2
                            linarith only [h1498, hlam, p1595_1]
                          · have p1595_0 := h1595c.1
                            have p1595_1 := h1595c.2.1
                            have p1595_2 := h1595c.2.2.1
                            have p1595_3 := h1595c.2.2.2
                            linarith only [h1541, hlam, p1595_0]
                          · have p1595_0 := h1595c.1
                            have p1595_1 := h1595c.2.1
                            have p1595_2 := h1595c.2.2.1
                            have p1595_3 := h1595c.2.2.2
                            linarith only [h1542, hlam, p1595_1]
                          · have p1595_0 := h1595c.1
                            have p1595_1 := h1595c.2.1
                            have p1595_2 := h1595c.2.2.1
                            have p1595_3 := h1595c.2.2.2
                            linarith only [hlam, p1595_0]
                        · linarith only [h1551, h1594, h4, hc02, hc45, hlam, hphi, ht23, ht34]
                      · linarith only [h1160, h1498, h1550, h1592, h1593, h3, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h1547, h1549, h1592, h2, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · linarith only [h1542, h1547, h1549, h1550, h2, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · linarith only [h1499, h1541, h1543, h1549, hc12, hc34, hlam, hphi, ht23]
      · linarith only [h1160, h1498, h1542, hlam]
    · linarith only [h1498, h1541, h4, hlam]

end R2N4
