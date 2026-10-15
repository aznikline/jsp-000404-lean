import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_56S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4108000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_R_H_I_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1016 | h1016
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1017 | h1017
    · linarith only [h0, h1, h1017, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1019 | h1019
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1020 | h1020
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1021 | h1021
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1022 | h1022
            · linarith only [h1017, h1022, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1024 | h1024
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1025 | h1025
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1026 | h1026
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1027 | h1027
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1028 | h1028
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1029 | h1029
                        · linarith only [h0, h1, h1024, h1029, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h1, h1022, h1029, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h1, h1019, h1021, h1026, h1028, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h1, h1027, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                  · linarith only [h0, h1, h1019, h1021, h1026, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi4]
                · linarith only [h0, h1, h1020, h1022, h1025, hc12, hc23, hlam, hphi]
              · linarith only [h0, h1, h1019, h1022, h1024, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1037 | h1037
            · linarith only [h0, h1, h1037, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1039 | h1039
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1040 | h1040
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1041 | h1041
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1042 | h1042
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1043 | h1043
                      · linarith only [h1021, h1043, hc14, hlam, hphi, ht01, u0ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1045 | h1045
                        · linarith only [h0, h1, h1037, h1039, h1045, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h1, h1037, h1039, h1041, h1043, h1045, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h1, h1039, h1041, h1042, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h0, h1, h1041, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h0, h1, h1020, h1039, h1040, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · linarith only [h0, h1, h1019, h1037, h1039, hc12, hc23, hlam, hphi]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1052 | h1052
          · linarith only [h1019, h1020, h1052, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1054 | h1054
            · linarith only [h0, h1, h1054, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1056 | h1056
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1057 | h1057
                · linarith only [h0, h1, h1019, h1020, h1054, h1057, hc23, hlam, hphi, ht01, ht12, u0ehi3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1059 | h1059
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1060 | h1060
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1061 | h1061
                      · linarith only [h1052, h1061, hc14, hlam, hphi, ht01, u0ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1063 | h1063
                        · linarith only [h1, h1016, h1054, h1056, h1057, h1063, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h1, h1016, h1054, h1057, h1063, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h1, h1016, h1056, h1057, h1059, h1060, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1, h1016, h1057, h1059, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h1016, h1019, h1020, h1054, h1056, hc12, hc23, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1069 | h1069
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1070 | h1070
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1071 | h1071
            · linarith only [h1017, h1071, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1073 | h1073
              · linarith only [h0, h1, h1019, h1069, h1071, h1073, hc23, hlam, hphi, ht01, ht12, u0ehi4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1075 | h1075
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1076 | h1076
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1077 | h1077
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1078 | h1078
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1079 | h1079
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1080 | h1080
                          · linarith only [h0, h1, h1071, h1075, h1080, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                          · linarith only [h0, h1, h1071, h1080, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h1071, h1075, h1077, h1079, hc34, hlam, hphi, u3ehi4]
                      · linarith only [h1073, h1075, h1078, hlam]
                    · linarith only [h1, h1077, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                  · linarith only [h0, h1, h1069, h1076, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi4]
                · linarith only [h0, h1, h1069, h1071, h1075, hc12, hc23, hlam, hphi]
          · linarith only [h1019, h1069, h1070, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1089 | h1089
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1090 | h1090
            · linarith only [h0, h1017, h1090, hc01, hlam, hphi, u0ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1092 | h1092
              · linarith only [h0, h1, h1019, h1090, h1092, hc23, hlam, hphi, ht01, ht12, u0ehi1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1094 | h1094
                · linarith only [h0, h1, h1069, h1090, h1094, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1096 | h1096
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1097 | h1097
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1098 | h1098
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1099 | h1099
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1100 | h1100
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1101 | h1101
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1102 | h1102
                              · rcases h2bigk with h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c | h1103c
                                · have p1103_0 := h1103c.1
                                  have p1103_1 := h1103c.2.1
                                  have p1103_2 := h1103c.2.2.1
                                  have p1103_3 := h1103c.2.2.2
                                  linarith only [hlam, p1103_0]
                                · have p1103_0 := h1103c.1
                                  have p1103_1 := h1103c.2.1
                                  have p1103_2 := h1103c.2.2.1
                                  have p1103_3 := h1103c.2.2.2
                                  linarith only [h1069, h1101, hc12, hc24, hlam, hphi, p1103_1]
                                · have p1103_0 := h1103c.1
                                  have p1103_1 := h1103c.2.1
                                  have p1103_2 := h1103c.2.2.1
                                  have p1103_3 := h1103c.2.2.2
                                  linarith only [h1017, hlam, p1103_0]
                                · have p1103_0 := h1103c.1
                                  have p1103_1 := h1103c.2.1
                                  have p1103_2 := h1103c.2.2.1
                                  have p1103_3 := h1103c.2.2.2
                                  linarith only [h1019, hlam, p1103_0]
                                · have p1103_0 := h1103c.1
                                  have p1103_1 := h1103c.2.1
                                  have p1103_2 := h1103c.2.2.1
                                  have p1103_3 := h1103c.2.2.2
                                  linarith only [h1069, hlam, p1103_0]
                                · have p1103_0 := h1103c.1
                                  have p1103_1 := h1103c.2.1
                                  have p1103_2 := h1103c.2.2.1
                                  have p1103_3 := h1103c.2.2.2
                                  linarith only [h0, hlam, p1103_0]
                                · have p1103_0 := h1103c.1
                                  have p1103_1 := h1103c.2.1
                                  have p1103_2 := h1103c.2.2.1
                                  have p1103_3 := h1103c.2.2.2
                                  linarith only [hlam, p1103_0]
                                · have p1103_0 := h1103c.1
                                  have p1103_1 := h1103c.2.1
                                  have p1103_2 := h1103c.2.2.1
                                  have p1103_3 := h1103c.2.2.2
                                  linarith only [h1090, hlam, p1103_0]
                                · have p1103_0 := h1103c.1
                                  have p1103_1 := h1103c.2.1
                                  have p1103_2 := h1103c.2.2.1
                                  have p1103_3 := h1103c.2.2.2
                                  linarith only [h1092, hlam, p1103_0]
                                · have p1103_0 := h1103c.1
                                  have p1103_1 := h1103c.2.1
                                  have p1103_2 := h1103c.2.2.1
                                  have p1103_3 := h1103c.2.2.2
                                  linarith only [h1094, hlam, p1103_0]
                                · have p1103_0 := h1103c.1
                                  have p1103_1 := h1103c.2.1
                                  have p1103_2 := h1103c.2.2.1
                                  have p1103_3 := h1103c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht01, ht12, p1103_1, u0ehi1]
                                · have p1103_0 := h1103c.1
                                  have p1103_1 := h1103c.2.1
                                  have p1103_2 := h1103c.2.2.1
                                  have p1103_3 := h1103c.2.2.2
                                  rcases p1103_3 (m.d 0 2) (by simp) with h1115 | h1115
                                  · linarith only [h1017, h1115, hlam]
                                  · linarith only [h0, h1115, hlam]
                                · have p1103_0 := h1103c.1
                                  have p1103_1 := h1103c.2.1
                                  have p1103_2 := h1103c.2.2.1
                                  have p1103_3 := h1103c.2.2.2
                                  linarith only [hlam, p1103_0]
                                · have p1103_0 := h1103c.1
                                  have p1103_1 := h1103c.2.1
                                  have p1103_2 := h1103c.2.2.1
                                  have p1103_3 := h1103c.2.2.2
                                  linarith only [h1019, hc23, hlam, hphi, ht01, ht12, p1103_1, u0ehi1]
                                · have p1103_0 := h1103c.1
                                  have p1103_1 := h1103c.2.1
                                  have p1103_2 := h1103c.2.2.1
                                  have p1103_3 := h1103c.2.2.2
                                  linarith only [h1069, hc23, hlam, hphi, ht01, ht12, p1103_1, u0ehi1]
                                · have p1103_0 := h1103c.1
                                  have p1103_1 := h1103c.2.1
                                  have p1103_2 := h1103c.2.2.1
                                  have p1103_3 := h1103c.2.2.2
                                  linarith only [hc24, hlam, hphi, ht01, ht12, p1103_1, u0ehi1]
                                · have p1103_0 := h1103c.1
                                  have p1103_1 := h1103c.2.1
                                  have p1103_2 := h1103c.2.2.1
                                  have p1103_3 := h1103c.2.2.2
                                  rcases p1103_3 (m.d 0 2) (by simp) with h1122 | h1122
                                  · linarith only [h1019, h1122, hlam]
                                  · linarith only [h0, h1122, hlam]
                                · have p1103_0 := h1103c.1
                                  have p1103_1 := h1103c.2.1
                                  have p1103_2 := h1103c.2.2.1
                                  have p1103_3 := h1103c.2.2.2
                                  linarith only [h1099, hlam, p1103_1]
                                · have p1103_0 := h1103c.1
                                  have p1103_1 := h1103c.2.1
                                  have p1103_2 := h1103c.2.2.1
                                  have p1103_3 := h1103c.2.2.2
                                  linarith only [hlam, p1103_0]
                                · have p1103_0 := h1103c.1
                                  have p1103_1 := h1103c.2.1
                                  have p1103_2 := h1103c.2.2.1
                                  have p1103_3 := h1103c.2.2.2
                                  linarith only [h1069, h1099, hc23, hlam, hphi, ht01, ht12, p1103_1, u0ehi1]
                                · have p1103_0 := h1103c.1
                                  have p1103_1 := h1103c.2.1
                                  have p1103_2 := h1103c.2.2.1
                                  have p1103_3 := h1103c.2.2.2
                                  linarith only [hc25, hlam, hphi, ht01, ht12, p1103_1, u0ehi1]
                                · have p1103_0 := h1103c.1
                                  have p1103_1 := h1103c.2.1
                                  have p1103_2 := h1103c.2.2.1
                                  have p1103_3 := h1103c.2.2.2
                                  rcases p1103_3 (m.d 0 2) (by simp) with h1129 | h1129
                                  · linarith only [h1069, h1129, hlam]
                                  · linarith only [h0, h1129, hlam]
                                · have p1103_0 := h1103c.1
                                  have p1103_1 := h1103c.2.1
                                  have p1103_2 := h1103c.2.2.1
                                  have p1103_3 := h1103c.2.2.2
                                  linarith only [h1100, hlam, p1103_1]
                                · have p1103_0 := h1103c.1
                                  have p1103_1 := h1103c.2.1
                                  have p1103_2 := h1103c.2.2.1
                                  have p1103_3 := h1103c.2.2.2
                                  linarith only [h1101, hlam, p1103_0]
                                · have p1103_0 := h1103c.1
                                  have p1103_1 := h1103c.2.1
                                  have p1103_2 := h1103c.2.2.1
                                  have p1103_3 := h1103c.2.2.2
                                  linarith only [hlam, p1103_0]
                              · linarith only [h1, h1016, h1090, h1098, h1102, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h1, h1016, h1019, h1090, h1098, h1101, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                          · linarith only [h1, h1016, h1090, h1097, h1100, hlam]
                        · linarith only [h1, h1090, h1099, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1139 | h1139
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1140 | h1140
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1141 | h1141
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1142 | h1142
                              · linarith only [h1096, h1098, h1142, hlam]
                              · rcases h2bigk with h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c
                                · have p1144_0 := h1144c.1
                                  have p1144_1 := h1144c.2.1
                                  have p1144_2 := h1144c.2.2.1
                                  have p1144_3 := h1144c.2.2.2
                                  linarith only [hlam, p1144_0]
                                · have p1144_0 := h1144c.1
                                  have p1144_1 := h1144c.2.1
                                  have p1144_2 := h1144c.2.2.1
                                  have p1144_3 := h1144c.2.2.2
                                  linarith only [h0, h1, h1090, hc12, hc23, hlam, hphi, p1144_1]
                                · have p1144_0 := h1144c.1
                                  have p1144_1 := h1144c.2.1
                                  have p1144_2 := h1144c.2.2.1
                                  have p1144_3 := h1144c.2.2.2
                                  linarith only [h1017, hlam, p1144_0]
                                · have p1144_0 := h1144c.1
                                  have p1144_1 := h1144c.2.1
                                  have p1144_2 := h1144c.2.2.1
                                  have p1144_3 := h1144c.2.2.2
                                  linarith only [h1019, hlam, p1144_0]
                                · have p1144_0 := h1144c.1
                                  have p1144_1 := h1144c.2.1
                                  have p1144_2 := h1144c.2.2.1
                                  have p1144_3 := h1144c.2.2.2
                                  linarith only [h1069, hlam, p1144_0]
                                · have p1144_0 := h1144c.1
                                  have p1144_1 := h1144c.2.1
                                  have p1144_2 := h1144c.2.2.1
                                  have p1144_3 := h1144c.2.2.2
                                  linarith only [h0, hlam, p1144_0]
                                · have p1144_0 := h1144c.1
                                  have p1144_1 := h1144c.2.1
                                  have p1144_2 := h1144c.2.2.1
                                  have p1144_3 := h1144c.2.2.2
                                  linarith only [hlam, p1144_0]
                                · have p1144_0 := h1144c.1
                                  have p1144_1 := h1144c.2.1
                                  have p1144_2 := h1144c.2.2.1
                                  have p1144_3 := h1144c.2.2.2
                                  linarith only [h1090, hlam, p1144_0]
                                · have p1144_0 := h1144c.1
                                  have p1144_1 := h1144c.2.1
                                  have p1144_2 := h1144c.2.2.1
                                  have p1144_3 := h1144c.2.2.2
                                  linarith only [h1092, hlam, p1144_0]
                                · have p1144_0 := h1144c.1
                                  have p1144_1 := h1144c.2.1
                                  have p1144_2 := h1144c.2.2.1
                                  have p1144_3 := h1144c.2.2.2
                                  linarith only [h1094, hlam, p1144_0]
                                · have p1144_0 := h1144c.1
                                  have p1144_1 := h1144c.2.1
                                  have p1144_2 := h1144c.2.2.1
                                  have p1144_3 := h1144c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht01, ht12, p1144_1, u0ehi1]
                                · have p1144_0 := h1144c.1
                                  have p1144_1 := h1144c.2.1
                                  have p1144_2 := h1144c.2.2.1
                                  have p1144_3 := h1144c.2.2.2
                                  rcases p1144_3 (m.d 0 2) (by simp) with h1156 | h1156
                                  · linarith only [h1017, h1156, hlam]
                                  · linarith only [h0, h1156, hlam]
                                · have p1144_0 := h1144c.1
                                  have p1144_1 := h1144c.2.1
                                  have p1144_2 := h1144c.2.2.1
                                  have p1144_3 := h1144c.2.2.2
                                  linarith only [hlam, p1144_0]
                                · have p1144_0 := h1144c.1
                                  have p1144_1 := h1144c.2.1
                                  have p1144_2 := h1144c.2.2.1
                                  have p1144_3 := h1144c.2.2.2
                                  linarith only [h1019, hc23, hlam, hphi, ht01, ht12, p1144_1, u0ehi1]
                                · have p1144_0 := h1144c.1
                                  have p1144_1 := h1144c.2.1
                                  have p1144_2 := h1144c.2.2.1
                                  have p1144_3 := h1144c.2.2.2
                                  linarith only [h1069, hc23, hlam, hphi, ht01, ht12, p1144_1, u0ehi1]
                                · have p1144_0 := h1144c.1
                                  have p1144_1 := h1144c.2.1
                                  have p1144_2 := h1144c.2.2.1
                                  have p1144_3 := h1144c.2.2.2
                                  linarith only [hc24, hlam, hphi, ht01, ht12, p1144_1, u0ehi1]
                                · have p1144_0 := h1144c.1
                                  have p1144_1 := h1144c.2.1
                                  have p1144_2 := h1144c.2.2.1
                                  have p1144_3 := h1144c.2.2.2
                                  rcases p1144_3 (m.d 0 2) (by simp) with h1163 | h1163
                                  · linarith only [h1019, h1163, hlam]
                                  · linarith only [h0, h1163, hlam]
                                · have p1144_0 := h1144c.1
                                  have p1144_1 := h1144c.2.1
                                  have p1144_2 := h1144c.2.2.1
                                  have p1144_3 := h1144c.2.2.2
                                  linarith only [h1139, hlam, p1144_1]
                                · have p1144_0 := h1144c.1
                                  have p1144_1 := h1144c.2.1
                                  have p1144_2 := h1144c.2.2.1
                                  have p1144_3 := h1144c.2.2.2
                                  linarith only [hlam, p1144_0]
                                · have p1144_0 := h1144c.1
                                  have p1144_1 := h1144c.2.1
                                  have p1144_2 := h1144c.2.2.1
                                  have p1144_3 := h1144c.2.2.2
                                  linarith only [h1069, h1139, hc23, hlam, hphi, ht01, ht12, p1144_1, u0ehi1]
                                · have p1144_0 := h1144c.1
                                  have p1144_1 := h1144c.2.1
                                  have p1144_2 := h1144c.2.2.1
                                  have p1144_3 := h1144c.2.2.2
                                  linarith only [hc25, hlam, hphi, ht01, ht12, p1144_1, u0ehi1]
                                · have p1144_0 := h1144c.1
                                  have p1144_1 := h1144c.2.1
                                  have p1144_2 := h1144c.2.2.1
                                  have p1144_3 := h1144c.2.2.2
                                  rcases p1144_3 (m.d 0 2) (by simp) with h1170 | h1170
                                  · linarith only [h1069, h1170, hlam]
                                  · linarith only [h0, h1170, hlam]
                                · have p1144_0 := h1144c.1
                                  have p1144_1 := h1144c.2.1
                                  have p1144_2 := h1144c.2.2.1
                                  have p1144_3 := h1144c.2.2.2
                                  linarith only [h1140, hlam, p1144_1]
                                · have p1144_0 := h1144c.1
                                  have p1144_1 := h1144c.2.1
                                  have p1144_2 := h1144c.2.2.1
                                  have p1144_3 := h1144c.2.2.2
                                  linarith only [h1141, hlam, p1144_0]
                                · have p1144_0 := h1144c.1
                                  have p1144_1 := h1144c.2.1
                                  have p1144_2 := h1144c.2.2.1
                                  have p1144_3 := h1144c.2.2.2
                                  linarith only [hlam, p1144_0]
                            · linarith only [h1, h1016, h1019, h1089, h1090, h1141, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                          · linarith only [h1, h1016, h1089, h1090, h1096, h1098, h1140, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1, h1016, h1089, h1090, h1096, h1098, h1139, hlam]
                    · linarith only [h1, h1097, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                  · linarith only [h1, h1016, h1069, h1096, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1181 | h1181
            · linarith only [h0, h1, h1181, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1183 | h1183
              · linarith only [h0, h1, h1019, h1181, h1183, hc02, hc23, hlam, hphi]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1185 | h1185
                · linarith only [h0, h1, h1069, h1181, h1185, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1187 | h1187
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1188 | h1188
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1189 | h1189
                      · linarith only [h1089, h1189, hc14, hlam, hphi, ht01, u0ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1191 | h1191
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1192 | h1192
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1193 | h1193
                            · linarith only [h1019, h1089, h1191, h1193, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                            · linarith only [h1, h1016, h1019, h1181, h1187, h1189, h1193, hc23, hc45, hlam, hphi, ht01, ht12, ht34, u0ehi1, u3ehi3]
                          · linarith only [h1, h1016, h1181, h1188, h1192, hlam]
                        · linarith only [h1, h1016, h1181, h1187, h1189, h1191, hlam]
                    · linarith only [h1, h1188, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                  · linarith only [h1, h1016, h1019, h1089, h1187, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1200 | h1200
    · linarith only [h0, h1, h1200, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1202 | h1202
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1203 | h1203
        · linarith only [h0, h1016, h1203, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1205 | h1205
          · linarith only [h0, h1016, h1202, h1205, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1207 | h1207
            · linarith only [h1200, h1207, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1209 | h1209
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1210 | h1210
                · linarith only [h0, h1, h1202, h1203, h1207, h1210, hc23, hlam, hphi, ht01, ht12, u0ehi3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1212 | h1212
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1213 | h1213
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1214 | h1214
                      · linarith only [h0, h1016, h1205, h1207, h1209, h1213, h1214, hc23, hlam, hphi, ht01, ht12, u0ehi3]
                      · linarith only [h0, h1016, h1209, h1212, h1214, hc45, hlam, hphi, ht34, u3ehi3]
                    · linarith only [h0, h1, h1209, h1212, h1213, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h0, h1, h1212, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h0, h1, h1202, h1207, h1209, hc12, hc23, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1220 | h1220
        · linarith only [h0, h1016, h1220, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1222 | h1222
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1223 | h1223
            · linarith only [h0, h1, h1223, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1225 | h1225
              · linarith only [h0, h1, h1202, h1223, h1225, hc02, hc23, hlam, hphi]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1227 | h1227
                · linarith only [h0, h1, h1220, h1223, h1227, hc23, hlam, hphi, ht01, ht12, u0ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1229 | h1229
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1230 | h1230
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1231 | h1231
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1232 | h1232
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1233 | h1233
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1234 | h1234
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1235 | h1235
                              · rcases h2bigk with h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c
                                · have p1236_0 := h1236c.1
                                  have p1236_1 := h1236c.2.1
                                  have p1236_2 := h1236c.2.2.1
                                  have p1236_3 := h1236c.2.2.2
                                  linarith only [hlam, p1236_0]
                                · have p1236_0 := h1236c.1
                                  have p1236_1 := h1236c.2.1
                                  have p1236_2 := h1236c.2.2.1
                                  have p1236_3 := h1236c.2.2.2
                                  linarith only [h0, h1016, h1223, h1229, h1231, hc12, hc23, hlam, hphi, p1236_1]
                                · have p1236_0 := h1236c.1
                                  have p1236_1 := h1236c.2.1
                                  have p1236_2 := h1236c.2.2.1
                                  have p1236_3 := h1236c.2.2.2
                                  linarith only [h1200, hlam, p1236_0]
                                · have p1236_0 := h1236c.1
                                  have p1236_1 := h1236c.2.1
                                  have p1236_2 := h1236c.2.2.1
                                  have p1236_3 := h1236c.2.2.2
                                  linarith only [h1202, hlam, p1236_0]
                                · have p1236_0 := h1236c.1
                                  have p1236_1 := h1236c.2.1
                                  have p1236_2 := h1236c.2.2.1
                                  have p1236_3 := h1236c.2.2.2
                                  linarith only [h1220, hlam, p1236_0]
                                · have p1236_0 := h1236c.1
                                  have p1236_1 := h1236c.2.1
                                  have p1236_2 := h1236c.2.2.1
                                  have p1236_3 := h1236c.2.2.2
                                  linarith only [h0, hlam, p1236_0]
                                · have p1236_0 := h1236c.1
                                  have p1236_1 := h1236c.2.1
                                  have p1236_2 := h1236c.2.2.1
                                  have p1236_3 := h1236c.2.2.2
                                  linarith only [hlam, p1236_0]
                                · have p1236_0 := h1236c.1
                                  have p1236_1 := h1236c.2.1
                                  have p1236_2 := h1236c.2.2.1
                                  have p1236_3 := h1236c.2.2.2
                                  linarith only [h1223, hlam, p1236_0]
                                · have p1236_0 := h1236c.1
                                  have p1236_1 := h1236c.2.1
                                  have p1236_2 := h1236c.2.2.1
                                  have p1236_3 := h1236c.2.2.2
                                  linarith only [h1225, hlam, p1236_0]
                                · have p1236_0 := h1236c.1
                                  have p1236_1 := h1236c.2.1
                                  have p1236_2 := h1236c.2.2.1
                                  have p1236_3 := h1236c.2.2.2
                                  linarith only [h1227, hlam, p1236_0]
                                · have p1236_0 := h1236c.1
                                  have p1236_1 := h1236c.2.1
                                  have p1236_2 := h1236c.2.2.1
                                  have p1236_3 := h1236c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht01, ht12, p1236_1, u0ehi1]
                                · have p1236_0 := h1236c.1
                                  have p1236_1 := h1236c.2.1
                                  have p1236_2 := h1236c.2.2.1
                                  have p1236_3 := h1236c.2.2.2
                                  rcases p1236_3 (m.d 0 2) (by simp) with h1248 | h1248
                                  · linarith only [h1200, h1248, hlam]
                                  · linarith only [h0, h1248, hlam]
                                · have p1236_0 := h1236c.1
                                  have p1236_1 := h1236c.2.1
                                  have p1236_2 := h1236c.2.2.1
                                  have p1236_3 := h1236c.2.2.2
                                  linarith only [hlam, p1236_0]
                                · have p1236_0 := h1236c.1
                                  have p1236_1 := h1236c.2.1
                                  have p1236_2 := h1236c.2.2.1
                                  have p1236_3 := h1236c.2.2.2
                                  linarith only [h1016, h1225, h1231, hc01, hc23, hlam, hphi, ht12, p1236_1]
                                · have p1236_0 := h1236c.1
                                  have p1236_1 := h1236c.2.1
                                  have p1236_2 := h1236c.2.2.1
                                  have p1236_3 := h1236c.2.2.2
                                  linarith only [h0, h1016, h1227, hc23, hlam, hphi, ht01, ht12, p1236_1, u0ehi1]
                                · have p1236_0 := h1236c.1
                                  have p1236_1 := h1236c.2.1
                                  have p1236_2 := h1236c.2.2.1
                                  have p1236_3 := h1236c.2.2.2
                                  linarith only [hc24, hlam, hphi, ht01, ht12, p1236_1, u0ehi1]
                                · have p1236_0 := h1236c.1
                                  have p1236_1 := h1236c.2.1
                                  have p1236_2 := h1236c.2.2.1
                                  have p1236_3 := h1236c.2.2.2
                                  rcases p1236_3 (m.d 0 2) (by simp) with h1255 | h1255
                                  · linarith only [h1202, h1255, hlam]
                                  · linarith only [h0, h1255, hlam]
                                · have p1236_0 := h1236c.1
                                  have p1236_1 := h1236c.2.1
                                  have p1236_2 := h1236c.2.2.1
                                  have p1236_3 := h1236c.2.2.2
                                  linarith only [h1232, hlam, p1236_1]
                                · have p1236_0 := h1236c.1
                                  have p1236_1 := h1236c.2.1
                                  have p1236_2 := h1236c.2.2.1
                                  have p1236_3 := h1236c.2.2.2
                                  linarith only [hlam, p1236_0]
                                · have p1236_0 := h1236c.1
                                  have p1236_1 := h1236c.2.1
                                  have p1236_2 := h1236c.2.2.1
                                  have p1236_3 := h1236c.2.2.2
                                  linarith only [h0, h1016, h1227, h1232, hc23, hlam, hphi, ht01, ht12, p1236_1, u0ehi1]
                                · have p1236_0 := h1236c.1
                                  have p1236_1 := h1236c.2.1
                                  have p1236_2 := h1236c.2.2.1
                                  have p1236_3 := h1236c.2.2.2
                                  linarith only [hc25, hlam, hphi, ht01, ht12, p1236_1, u0ehi1]
                                · have p1236_0 := h1236c.1
                                  have p1236_1 := h1236c.2.1
                                  have p1236_2 := h1236c.2.2.1
                                  have p1236_3 := h1236c.2.2.2
                                  rcases p1236_3 (m.d 0 2) (by simp) with h1262 | h1262
                                  · linarith only [h1220, h1262, hlam]
                                  · linarith only [h0, h1262, hlam]
                                · have p1236_0 := h1236c.1
                                  have p1236_1 := h1236c.2.1
                                  have p1236_2 := h1236c.2.2.1
                                  have p1236_3 := h1236c.2.2.2
                                  linarith only [h1233, hlam, p1236_1]
                                · have p1236_0 := h1236c.1
                                  have p1236_1 := h1236c.2.1
                                  have p1236_2 := h1236c.2.2.1
                                  have p1236_3 := h1236c.2.2.2
                                  linarith only [h1234, hlam, p1236_0]
                                · have p1236_0 := h1236c.1
                                  have p1236_1 := h1236c.2.1
                                  have p1236_2 := h1236c.2.2.1
                                  have p1236_3 := h1236c.2.2.2
                                  linarith only [hlam, p1236_0]
                              · rcases h2bigk with h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c
                                · have p1268_0 := h1268c.1
                                  have p1268_1 := h1268c.2.1
                                  have p1268_2 := h1268c.2.2.1
                                  have p1268_3 := h1268c.2.2.2
                                  linarith only [hlam, p1268_0]
                                · have p1268_0 := h1268c.1
                                  have p1268_1 := h1268c.2.1
                                  have p1268_2 := h1268c.2.2.1
                                  have p1268_3 := h1268c.2.2.2
                                  linarith only [h0, h1, h1223, hc12, hc23, hlam, hphi, p1268_1]
                                · have p1268_0 := h1268c.1
                                  have p1268_1 := h1268c.2.1
                                  have p1268_2 := h1268c.2.2.1
                                  have p1268_3 := h1268c.2.2.2
                                  linarith only [h1200, hlam, p1268_0]
                                · have p1268_0 := h1268c.1
                                  have p1268_1 := h1268c.2.1
                                  have p1268_2 := h1268c.2.2.1
                                  have p1268_3 := h1268c.2.2.2
                                  linarith only [h1202, hlam, p1268_0]
                                · have p1268_0 := h1268c.1
                                  have p1268_1 := h1268c.2.1
                                  have p1268_2 := h1268c.2.2.1
                                  have p1268_3 := h1268c.2.2.2
                                  linarith only [h1220, hlam, p1268_0]
                                · have p1268_0 := h1268c.1
                                  have p1268_1 := h1268c.2.1
                                  have p1268_2 := h1268c.2.2.1
                                  have p1268_3 := h1268c.2.2.2
                                  linarith only [h0, hlam, p1268_0]
                                · have p1268_0 := h1268c.1
                                  have p1268_1 := h1268c.2.1
                                  have p1268_2 := h1268c.2.2.1
                                  have p1268_3 := h1268c.2.2.2
                                  linarith only [hlam, p1268_0]
                                · have p1268_0 := h1268c.1
                                  have p1268_1 := h1268c.2.1
                                  have p1268_2 := h1268c.2.2.1
                                  have p1268_3 := h1268c.2.2.2
                                  linarith only [h1223, hlam, p1268_0]
                                · have p1268_0 := h1268c.1
                                  have p1268_1 := h1268c.2.1
                                  have p1268_2 := h1268c.2.2.1
                                  have p1268_3 := h1268c.2.2.2
                                  linarith only [h1225, hlam, p1268_0]
                                · have p1268_0 := h1268c.1
                                  have p1268_1 := h1268c.2.1
                                  have p1268_2 := h1268c.2.2.1
                                  have p1268_3 := h1268c.2.2.2
                                  linarith only [h1227, hlam, p1268_0]
                                · have p1268_0 := h1268c.1
                                  have p1268_1 := h1268c.2.1
                                  have p1268_2 := h1268c.2.2.1
                                  have p1268_3 := h1268c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht01, ht12, p1268_1, u0ehi1]
                                · have p1268_0 := h1268c.1
                                  have p1268_1 := h1268c.2.1
                                  have p1268_2 := h1268c.2.2.1
                                  have p1268_3 := h1268c.2.2.2
                                  rcases p1268_3 (m.d 0 2) (by simp) with h1280 | h1280
                                  · linarith only [h1200, h1280, hlam]
                                  · linarith only [h0, h1280, hlam]
                                · have p1268_0 := h1268c.1
                                  have p1268_1 := h1268c.2.1
                                  have p1268_2 := h1268c.2.2.1
                                  have p1268_3 := h1268c.2.2.2
                                  linarith only [hlam, p1268_0]
                                · have p1268_0 := h1268c.1
                                  have p1268_1 := h1268c.2.1
                                  have p1268_2 := h1268c.2.2.1
                                  have p1268_3 := h1268c.2.2.2
                                  linarith only [h1016, h1227, h1234, hc01, hc23, hlam, hphi, ht12, p1268_1]
                                · have p1268_0 := h1268c.1
                                  have p1268_1 := h1268c.2.1
                                  have p1268_2 := h1268c.2.2.1
                                  have p1268_3 := h1268c.2.2.2
                                  linarith only [h0, h1016, h1227, hc23, hlam, hphi, ht01, ht12, p1268_1, u0ehi1]
                                · have p1268_0 := h1268c.1
                                  have p1268_1 := h1268c.2.1
                                  have p1268_2 := h1268c.2.2.1
                                  have p1268_3 := h1268c.2.2.2
                                  linarith only [hc24, hlam, hphi, ht01, ht12, p1268_1, u0ehi1]
                                · have p1268_0 := h1268c.1
                                  have p1268_1 := h1268c.2.1
                                  have p1268_2 := h1268c.2.2.1
                                  have p1268_3 := h1268c.2.2.2
                                  rcases p1268_3 (m.d 0 2) (by simp) with h1287 | h1287
                                  · linarith only [h1202, h1287, hlam]
                                  · linarith only [h0, h1287, hlam]
                                · have p1268_0 := h1268c.1
                                  have p1268_1 := h1268c.2.1
                                  have p1268_2 := h1268c.2.2.1
                                  have p1268_3 := h1268c.2.2.2
                                  linarith only [h1232, hlam, p1268_1]
                                · have p1268_0 := h1268c.1
                                  have p1268_1 := h1268c.2.1
                                  have p1268_2 := h1268c.2.2.1
                                  have p1268_3 := h1268c.2.2.2
                                  linarith only [hlam, p1268_0]
                                · have p1268_0 := h1268c.1
                                  have p1268_1 := h1268c.2.1
                                  have p1268_2 := h1268c.2.2.1
                                  have p1268_3 := h1268c.2.2.2
                                  linarith only [h0, h1016, h1227, h1232, hc23, hlam, hphi, ht01, ht12, p1268_1, u0ehi1]
                                · have p1268_0 := h1268c.1
                                  have p1268_1 := h1268c.2.1
                                  have p1268_2 := h1268c.2.2.1
                                  have p1268_3 := h1268c.2.2.2
                                  linarith only [hc25, hlam, hphi, ht01, ht12, p1268_1, u0ehi1]
                                · have p1268_0 := h1268c.1
                                  have p1268_1 := h1268c.2.1
                                  have p1268_2 := h1268c.2.2.1
                                  have p1268_3 := h1268c.2.2.2
                                  rcases p1268_3 (m.d 0 2) (by simp) with h1294 | h1294
                                  · linarith only [h1220, h1294, hlam]
                                  · linarith only [h0, h1294, hlam]
                                · have p1268_0 := h1268c.1
                                  have p1268_1 := h1268c.2.1
                                  have p1268_2 := h1268c.2.2.1
                                  have p1268_3 := h1268c.2.2.2
                                  linarith only [h1233, hlam, p1268_1]
                                · have p1268_0 := h1268c.1
                                  have p1268_1 := h1268c.2.1
                                  have p1268_2 := h1268c.2.2.1
                                  have p1268_3 := h1268c.2.2.2
                                  linarith only [h1234, hlam, p1268_0]
                                · have p1268_0 := h1268c.1
                                  have p1268_1 := h1268c.2.1
                                  have p1268_2 := h1268c.2.2.1
                                  have p1268_3 := h1268c.2.2.2
                                  linarith only [hlam, p1268_0]
                            · linarith only [h1202, h1222, h1234, hc04, hlam, hphi, u0ehi1]
                          · linarith only [h0, h1, h1223, h1233, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                        · linarith only [h1223, h1230, h1232, hc34, hlam, hphi, u3ehi4]
                      · linarith only [h0, h1016, h1202, h1222, h1231, hc24, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h0, h1, h1230, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                  · linarith only [h0, h1, h1229, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1306 | h1306
            · linarith only [h0, h1, h1306, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1308 | h1308
              · linarith only [h0, h1, h1202, h1306, h1308, hc23, hlam, hphi, ht01, ht12, u0ehi1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1310 | h1310
                · linarith only [h0, h1, h1220, h1306, h1310, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1312 | h1312
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1313 | h1313
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1314 | h1314
                      · linarith only [h1222, h1314, hc14, hlam, hphi, ht01, u0ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1316 | h1316
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1317 | h1317
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1318 | h1318
                            · linarith only [h0, h1016, h1314, h1316, h1318, hc12, hc23, hlam, hphi]
                            · linarith only [h1202, h1318, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                          · linarith only [h1200, h1313, h1317, hc13, hlam, hphi, ht01, u0ehi1]
                        · linarith only [h1306, h1312, h1314, h1316, hc45, hlam, hphi, ht34, u3ehi1]
                    · linarith only [h0, h1, h1313, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                  · linarith only [h0, h1, h1312, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]

set_option maxHeartbeats 4108000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_R_H_I_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_10_12_13_25_L_R_L_I_L_R_H_I_x0_x0 m hb0 hb2 hb3 hb5 h0 h1
  · exact r1l7_10_12_13_25_L_R_L_I_L_R_H_I_x0_x1 m hb0 hb2 hb3 hb5 h0 h1

end R2N4
