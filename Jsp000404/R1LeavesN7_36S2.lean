import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_36S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7634000 in
theorem r1l7_10_12_13_25_L_0_L_I_L_I_M_IR_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1035 | h1035
  · linarith only [h0, h1, h1035, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1037 | h1037
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1038 | h1038
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1039 | h1039
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1040 | h1040
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1041 | h1041
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1042 | h1042
              · linarith only [h1035, h1037, h1041, h1042, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1044 | h1044
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1045 | h1045
                  · linarith only [h0, h1045, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                  · linarith only [h0, h1, h1038, h1042, h1045, hc12, hc23, hlam, hphi]
                · linarith only [h0, h1, h1037, h1042, h1044, hc12, hc23, hlam, hphi]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1049 | h1049
              · linarith only [h0, h1035, h1049, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1051 | h1051
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1052 | h1052
                  · linarith only [h0, h1, h1049, h1052, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · linarith only [h1038, h1051, h1052, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · linarith only [h0, h1, h1037, h1049, h1051, hc12, hc23, hlam, hphi]
          · linarith only [h0, h1, h1038, h1040, hlam]
        · linarith only [h0, h1, h1037, h1039, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1058 | h1058
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1059 | h1059
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1060 | h1060
            · linarith only [h1037, h1038, h1060, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1062 | h1062
              · linarith only [h0, h1035, h1062, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1064 | h1064
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1065 | h1065
                  · linarith only [h0, h1038, h1065, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1067 | h1067
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1068 | h1068
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1069 | h1069
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1070 | h1070
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1071 | h1071
                            · linarith only [h0, h1060, h1064, h1071, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1073 | h1073
                              · linarith only [h1037, h1038, h1069, h1071, h1073, hlam]
                              · rcases h2bigk with h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c
                                · have p1075_0 := h1075c.1
                                  have p1075_1 := h1075c.2.1
                                  have p1075_2 := h1075c.2.2.1
                                  have p1075_3 := h1075c.2.2.2
                                  linarith only [hlam, p1075_0]
                                · have p1075_0 := h1075c.1
                                  have p1075_1 := h1075c.2.1
                                  have p1075_2 := h1075c.2.2.1
                                  have p1075_3 := h1075c.2.2.2
                                  linarith only [h1064, h1069, hc34, hlam, hphi, ht0b, ht45, ht5b, p1075_1, u0elo1]
                                · have p1075_0 := h1075c.1
                                  have p1075_1 := h1075c.2.1
                                  have p1075_2 := h1075c.2.2.1
                                  have p1075_3 := h1075c.2.2.2
                                  linarith only [h1035, hlam, p1075_0]
                                · have p1075_0 := h1075c.1
                                  have p1075_1 := h1075c.2.1
                                  have p1075_2 := h1075c.2.2.1
                                  have p1075_3 := h1075c.2.2.2
                                  linarith only [h1038, h1069, h1071, hc34, hc45, hlam, hphi, p1075_1]
                                · have p1075_0 := h1075c.1
                                  have p1075_1 := h1075c.2.1
                                  have p1075_2 := h1075c.2.2.1
                                  have p1075_3 := h1075c.2.2.2
                                  linarith only [h1038, hlam, p1075_0]
                                · have p1075_0 := h1075c.1
                                  have p1075_1 := h1075c.2.1
                                  have p1075_2 := h1075c.2.2.1
                                  have p1075_3 := h1075c.2.2.2
                                  linarith only [h0, hlam, p1075_0]
                                · have p1075_0 := h1075c.1
                                  have p1075_1 := h1075c.2.1
                                  have p1075_2 := h1075c.2.2.1
                                  have p1075_3 := h1075c.2.2.2
                                  linarith only [hlam, p1075_0]
                                · have p1075_0 := h1075c.1
                                  have p1075_1 := h1075c.2.1
                                  have p1075_2 := h1075c.2.2.1
                                  have p1075_3 := h1075c.2.2.2
                                  linarith only [h1062, hlam, p1075_0]
                                · have p1075_0 := h1075c.1
                                  have p1075_1 := h1075c.2.1
                                  have p1075_2 := h1075c.2.2.1
                                  have p1075_3 := h1075c.2.2.2
                                  linarith only [h0, h1, h1062, h1069, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1075_1]
                                · have p1075_0 := h1075c.1
                                  have p1075_1 := h1075c.2.1
                                  have p1075_2 := h1075c.2.2.1
                                  have p1075_3 := h1075c.2.2.2
                                  linarith only [h1065, hlam, p1075_0]
                                · have p1075_0 := h1075c.1
                                  have p1075_1 := h1075c.2.1
                                  have p1075_2 := h1075c.2.2.1
                                  have p1075_3 := h1075c.2.2.2
                                  rcases p1075_3 (m.d 0 2) (by simp) with h1086 | h1086
                                  · linarith only [h1086, hlam, p1075_0]
                                  · rcases p1075_3 (m.d 1 2) (by simp) with h1088 | h1088
                                    · linarith only [h1062, h1088, hlam]
                                    · rcases p1075_3 (m.d 2 3) (by simp) with h1090 | h1090
                                      · rcases p1075_3 (m.d 2 4) (by simp) with h1091 | h1091
                                        · linarith only [h1069, h1091, hlam]
                                        · rcases p1075_3 (m.d 2 5) (by simp) with h1093 | h1093
                                          · linarith only [h1070, h1093, hlam]
                                          · linarith only [h1038, h1093, hlam]
                                      · linarith only [h1090, hlam, p1075_0]
                                · have p1075_0 := h1075c.1
                                  have p1075_1 := h1075c.2.1
                                  have p1075_2 := h1075c.2.2.1
                                  have p1075_3 := h1075c.2.2.2
                                  rcases p1075_3 (m.d 0 2) (by simp) with h1097 | h1097
                                  · linarith only [h1035, h1097, hlam]
                                  · linarith only [h0, h1097, hlam]
                                · have p1075_0 := h1075c.1
                                  have p1075_1 := h1075c.2.1
                                  have p1075_2 := h1075c.2.2.1
                                  have p1075_3 := h1075c.2.2.2
                                  linarith only [hlam, p1075_0]
                                · have p1075_0 := h1075c.1
                                  have p1075_1 := h1075c.2.1
                                  have p1075_2 := h1075c.2.2.1
                                  have p1075_3 := h1075c.2.2.2
                                  linarith only [h0, h1, h1062, h1064, hlam, p1075_2]
                                · have p1075_0 := h1075c.1
                                  have p1075_1 := h1075c.2.1
                                  have p1075_2 := h1075c.2.2.1
                                  have p1075_3 := h1075c.2.2.2
                                  linarith only [h1038, hc02, hc23, hlam, hphi, p1075_1]
                                · have p1075_0 := h1075c.1
                                  have p1075_1 := h1075c.2.1
                                  have p1075_2 := h1075c.2.2.1
                                  have p1075_3 := h1075c.2.2.2
                                  linarith only [h1037, hlam, p1075_0]
                                · have p1075_0 := h1075c.1
                                  have p1075_1 := h1075c.2.1
                                  have p1075_2 := h1075c.2.2.1
                                  have p1075_3 := h1075c.2.2.2
                                  linarith only [h1064, hlam, p1075_0]
                                · have p1075_0 := h1075c.1
                                  have p1075_1 := h1075c.2.1
                                  have p1075_2 := h1075c.2.2.1
                                  have p1075_3 := h1075c.2.2.2
                                  linarith only [h1069, hlam, p1075_1]
                                · have p1075_0 := h1075c.1
                                  have p1075_1 := h1075c.2.1
                                  have p1075_2 := h1075c.2.2.1
                                  have p1075_3 := h1075c.2.2.2
                                  linarith only [hlam, p1075_0]
                                · have p1075_0 := h1075c.1
                                  have p1075_1 := h1075c.2.1
                                  have p1075_2 := h1075c.2.2.1
                                  have p1075_3 := h1075c.2.2.2
                                  linarith only [h1071, hlam, p1075_1]
                                · have p1075_0 := h1075c.1
                                  have p1075_1 := h1075c.2.1
                                  have p1075_2 := h1075c.2.2.1
                                  have p1075_3 := h1075c.2.2.2
                                  linarith only [h0, h1064, h1069, h1071, hc34, hc45, hlam, hphi, p1075_1]
                                · have p1075_0 := h1075c.1
                                  have p1075_1 := h1075c.2.1
                                  have p1075_2 := h1075c.2.2.1
                                  have p1075_3 := h1075c.2.2.2
                                  linarith only [h1064, h1069, h1071, hc34, hc45, hlam, hphi, p1075_1]
                                · have p1075_0 := h1075c.1
                                  have p1075_1 := h1075c.2.1
                                  have p1075_2 := h1075c.2.2.1
                                  have p1075_3 := h1075c.2.2.2
                                  linarith only [h1070, hlam, p1075_1]
                                · have p1075_0 := h1075c.1
                                  have p1075_1 := h1075c.2.1
                                  have p1075_2 := h1075c.2.2.1
                                  have p1075_3 := h1075c.2.2.2
                                  rcases p1075_3 (m.d 0 2) (by simp) with h1111 | h1111
                                  · linarith only [h1038, h1111, hlam]
                                  · linarith only [h1037, h1111, hlam]
                                · have p1075_0 := h1075c.1
                                  have p1075_1 := h1075c.2.1
                                  have p1075_2 := h1075c.2.2.1
                                  have p1075_3 := h1075c.2.2.2
                                  linarith only [hlam, p1075_0]
                          · linarith only [h0, h1, h1062, h1064, h1069, h1070, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h1, h1062, h1064, h1069, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h1, h1059, h1064, h1068, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · linarith only [h0, h1, h1064, h1067, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h0, h1, h1037, h1062, h1064, hc12, hc23, hlam, hphi]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1120 | h1120
            · linarith only [h1037, h1038, h1120, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1122 | h1122
              · linarith only [h0, h1, h1059, h1122, hc23, hc35, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1124 | h1124
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1125 | h1125
                  · linarith only [h0, h1, h1059, h1125, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1127 | h1127
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1128 | h1128
                      · linarith only [h0, h1, h1059, h1122, h1128, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h1124, h1128, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h1, h1124, h1127, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h1037, h1038, h1124, hc12, hc25, hlam, hphi]
        · linarith only [h0, h1, h1037, h1058, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1134 | h1134
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1135 | h1135
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1136 | h1136
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1137 | h1137
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1138 | h1138
              · linarith only [h0, h1035, h1138, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1140 | h1140
                · linarith only [h0, h1, h1037, h1134, h1138, h1140, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1142 | h1142
                  · linarith only [h0, h1, h1138, h1142, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · linarith only [h1037, h1134, h1142, hc12, hc24, hlam, hphi]
            · linarith only [h1037, h1134, h1137, hlam]
          · linarith only [h0, h1, h1134, h1136, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1147 | h1147
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1148 | h1148
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1149 | h1149
              · linarith only [h0, h1, h1135, h1149, hc23, hc34, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1151 | h1151
                · linarith only [h0, h1, h1037, h1135, h1151, hc02, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1153 | h1153
                  · linarith only [h0, h1, h1135, h1153, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                  · linarith only [h1037, h1134, h1153, hc12, hc24, hlam, hphi]
            · linarith only [h0, h1, h1134, h1135, h1148, hlam]
          · linarith only [h0, h1, h1134, h1147, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1158 | h1158
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1159 | h1159
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1160 | h1160
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1161 | h1161
              · linarith only [h0, h1, h1035, h1161, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1163 | h1163
                · linarith only [h0, h1037, h1160, h1163, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1165 | h1165
                  · linarith only [h0, h1, h1134, h1161, h1165, hc02, hc23, hlam, hphi]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1167 | h1167
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1168 | h1168
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1169 | h1169
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1170 | h1170
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1171 | h1171
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1172 | h1172
                              · linarith only [h1158, h1172, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                              · rcases h2bigk with h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c
                                · have p1174_0 := h1174c.1
                                  have p1174_1 := h1174c.2.1
                                  have p1174_2 := h1174c.2.2.1
                                  have p1174_3 := h1174c.2.2.2
                                  linarith only [hlam, p1174_0]
                                · have p1174_0 := h1174c.1
                                  have p1174_1 := h1174c.2.1
                                  have p1174_2 := h1174c.2.2.1
                                  have p1174_3 := h1174c.2.2.2
                                  linarith only [h1134, hc12, hc25, hlam, hphi, p1174_1]
                                · have p1174_0 := h1174c.1
                                  have p1174_1 := h1174c.2.1
                                  have p1174_2 := h1174c.2.2.1
                                  have p1174_3 := h1174c.2.2.2
                                  linarith only [h1035, hlam, p1174_0]
                                · have p1174_0 := h1174c.1
                                  have p1174_1 := h1174c.2.1
                                  have p1174_2 := h1174c.2.2.1
                                  have p1174_3 := h1174c.2.2.2
                                  linarith only [h1037, hlam, p1174_0]
                                · have p1174_0 := h1174c.1
                                  have p1174_1 := h1174c.2.1
                                  have p1174_2 := h1174c.2.2.1
                                  have p1174_3 := h1174c.2.2.2
                                  linarith only [h1134, hlam, p1174_0]
                                · have p1174_0 := h1174c.1
                                  have p1174_1 := h1174c.2.1
                                  have p1174_2 := h1174c.2.2.1
                                  have p1174_3 := h1174c.2.2.2
                                  linarith only [h0, hlam, p1174_0]
                                · have p1174_0 := h1174c.1
                                  have p1174_1 := h1174c.2.1
                                  have p1174_2 := h1174c.2.2.1
                                  have p1174_3 := h1174c.2.2.2
                                  linarith only [hlam, p1174_0]
                                · have p1174_0 := h1174c.1
                                  have p1174_1 := h1174c.2.1
                                  have p1174_2 := h1174c.2.2.1
                                  have p1174_3 := h1174c.2.2.2
                                  linarith only [h1161, hlam, p1174_0]
                                · have p1174_0 := h1174c.1
                                  have p1174_1 := h1174c.2.1
                                  have p1174_2 := h1174c.2.2.1
                                  have p1174_3 := h1174c.2.2.2
                                  linarith only [h1163, hlam, p1174_0]
                                · have p1174_0 := h1174c.1
                                  have p1174_1 := h1174c.2.1
                                  have p1174_2 := h1174c.2.2.1
                                  have p1174_3 := h1174c.2.2.2
                                  linarith only [h1165, hlam, p1174_0]
                                · have p1174_0 := h1174c.1
                                  have p1174_1 := h1174c.2.1
                                  have p1174_2 := h1174c.2.2.1
                                  have p1174_3 := h1174c.2.2.2
                                  rcases p1174_3 (m.d 0 2) (by simp) with h1185 | h1185
                                  · linarith only [h1185, hlam, p1174_0]
                                  · rcases p1174_3 (m.d 1 2) (by simp) with h1187 | h1187
                                    · linarith only [h1161, h1187, hlam]
                                    · rcases p1174_3 (m.d 2 3) (by simp) with h1189 | h1189
                                      · rcases p1174_3 (m.d 2 4) (by simp) with h1190 | h1190
                                        · linarith only [h1169, h1190, hlam]
                                        · linarith only [h1037, h1190, hlam]
                                      · linarith only [h1189, hlam, p1174_0]
                                · have p1174_0 := h1174c.1
                                  have p1174_1 := h1174c.2.1
                                  have p1174_2 := h1174c.2.2.1
                                  have p1174_3 := h1174c.2.2.2
                                  rcases p1174_3 (m.d 0 2) (by simp) with h1194 | h1194
                                  · linarith only [h1035, h1194, hlam]
                                  · linarith only [h0, h1194, hlam]
                                · have p1174_0 := h1174c.1
                                  have p1174_1 := h1174c.2.1
                                  have p1174_2 := h1174c.2.2.1
                                  have p1174_3 := h1174c.2.2.2
                                  linarith only [hlam, p1174_0]
                                · have p1174_0 := h1174c.1
                                  have p1174_1 := h1174c.2.1
                                  have p1174_2 := h1174c.2.2.1
                                  have p1174_3 := h1174c.2.2.2
                                  linarith only [h1037, h1160, h1172, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1174_1]
                                · have p1174_0 := h1174c.1
                                  have p1174_1 := h1174c.2.1
                                  have p1174_2 := h1174c.2.2.1
                                  have p1174_3 := h1174c.2.2.2
                                  linarith only [h1134, hc02, hc23, hlam, hphi, p1174_1]
                                · have p1174_0 := h1174c.1
                                  have p1174_1 := h1174c.2.1
                                  have p1174_2 := h1174c.2.2.1
                                  have p1174_3 := h1174c.2.2.2
                                  rcases p1174_3 (m.d 0 2) (by simp) with h1200 | h1200
                                  · linarith only [h1200, hlam, p1174_0]
                                  · rcases p1174_3 (m.d 1 2) (by simp) with h1202 | h1202
                                    · linarith only [h1163, h1202, hlam]
                                    · rcases p1174_3 (m.d 2 3) (by simp) with h1204 | h1204
                                      · rcases p1174_3 (m.d 2 4) (by simp) with h1205 | h1205
                                        · rcases p1174_3 (m.d 2 5) (by simp) with h1206 | h1206
                                          · linarith only [h1171, h1206, hlam]
                                          · linarith only [h1134, h1206, hlam]
                                        · linarith only [h1205, hlam, p1174_0]
                                      · linarith only [h1035, h1204, hlam]
                                · have p1174_0 := h1174c.1
                                  have p1174_1 := h1174c.2.1
                                  have p1174_2 := h1174c.2.2.1
                                  have p1174_3 := h1174c.2.2.2
                                  rcases p1174_3 (m.d 0 2) (by simp) with h1211 | h1211
                                  · linarith only [h1037, h1211, hlam]
                                  · linarith only [h0, h1211, hlam]
                                · have p1174_0 := h1174c.1
                                  have p1174_1 := h1174c.2.1
                                  have p1174_2 := h1174c.2.2.1
                                  have p1174_3 := h1174c.2.2.2
                                  linarith only [h1169, hlam, p1174_1]
                                · have p1174_0 := h1174c.1
                                  have p1174_1 := h1174c.2.1
                                  have p1174_2 := h1174c.2.2.1
                                  have p1174_3 := h1174c.2.2.2
                                  linarith only [hlam, p1174_0]
                                · have p1174_0 := h1174c.1
                                  have p1174_1 := h1174c.2.1
                                  have p1174_2 := h1174c.2.2.1
                                  have p1174_3 := h1174c.2.2.2
                                  linarith only [h0, h1134, hc12, hc24, hlam, hphi, p1174_1]
                                · have p1174_0 := h1174c.1
                                  have p1174_1 := h1174c.2.1
                                  have p1174_2 := h1174c.2.2.1
                                  have p1174_3 := h1174c.2.2.2
                                  rcases p1174_3 (m.d 0 2) (by simp) with h1217 | h1217
                                  · linarith only [h1217, hlam, p1174_0]
                                  · rcases p1174_3 (m.d 1 2) (by simp) with h1219 | h1219
                                    · linarith only [h1165, h1219, hlam]
                                    · rcases p1174_3 (m.d 2 3) (by simp) with h1221 | h1221
                                      · rcases p1174_3 (m.d 2 4) (by simp) with h1222 | h1222
                                        · rcases p1174_3 (m.d 2 5) (by simp) with h1223 | h1223
                                          · rcases h3bigk with h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c
                                            · have p1224_0 := h1224c.1
                                              have p1224_1 := h1224c.2.1
                                              have p1224_2 := h1224c.2.2.1
                                              have p1224_3 := h1224c.2.2.2
                                              linarith only [hlam, p1224_0]
                                            · have p1224_0 := h1224c.1
                                              have p1224_1 := h1224c.2.1
                                              have p1224_2 := h1224c.2.2.1
                                              have p1224_3 := h1224c.2.2.2
                                              linarith only [h1, hlam, p1224_1]
                                            · have p1224_0 := h1224c.1
                                              have p1224_1 := h1224c.2.1
                                              have p1224_2 := h1224c.2.2.1
                                              have p1224_3 := h1224c.2.2.2
                                              linarith only [h1035, hlam, p1224_1]
                                            · have p1224_0 := h1224c.1
                                              have p1224_1 := h1224c.2.1
                                              have p1224_2 := h1224c.2.2.1
                                              have p1224_3 := h1224c.2.2.2
                                              rcases p1224_3 (m.d 0 3) (by simp) with h1228 | h1228
                                              · rcases p1224_3 (m.d 1 3) (by simp) with h1229 | h1229
                                                · rcases p1224_3 (m.d 2 3) (by simp) with h1230 | h1230
                                                  · rcases p1224_3 (m.d 3 4) (by simp) with h1231 | h1231
                                                    · linarith only [h1231, hlam, p1224_0]
                                                    · rcases p1224_3 (m.d 3 5) (by simp) with h1233 | h1233
                                                      · linarith only [h1159, h1233, hlam]
                                                      · linarith only [h1172, h1233, hlam]
                                                  · linarith only [h1169, h1230, hlam]
                                                · linarith only [h1167, h1229, hlam]
                                              · linarith only [h1228, hlam, p1224_0]
                                            · have p1224_0 := h1224c.1
                                              have p1224_1 := h1224c.2.1
                                              have p1224_2 := h1224c.2.2.1
                                              have p1224_3 := h1224c.2.2.2
                                              linarith only [hlam, hphi, ht0b, ht5b, p1224_1, u0elo2, u5ehi3]
                                            · have p1224_0 := h1224c.1
                                              have p1224_1 := h1224c.2.1
                                              have p1224_2 := h1224c.2.2.1
                                              have p1224_3 := h1224c.2.2.2
                                              linarith only [h0, h1, h1161, hc12, hc23, hlam, hphi, p1224_1]
                                            · have p1224_0 := h1224c.1
                                              have p1224_1 := h1224c.2.1
                                              have p1224_2 := h1224c.2.2.1
                                              have p1224_3 := h1224c.2.2.2
                                              linarith only [hlam, p1224_0]
                                            · have p1224_0 := h1224c.1
                                              have p1224_1 := h1224c.2.1
                                              have p1224_2 := h1224c.2.2.1
                                              have p1224_3 := h1224c.2.2.2
                                              linarith only [h1161, hlam, p1224_1]
                                            · have p1224_0 := h1224c.1
                                              have p1224_1 := h1224c.2.1
                                              have p1224_2 := h1224c.2.2.1
                                              have p1224_3 := h1224c.2.2.2
                                              rcases p1224_3 (m.d 0 3) (by simp) with h1243 | h1243
                                              · linarith only [h1, h1243, hlam]
                                              · linarith only [h1158, h1243, hlam]
                                            · have p1224_0 := h1224c.1
                                              have p1224_1 := h1224c.2.1
                                              have p1224_2 := h1224c.2.2.1
                                              have p1224_3 := h1224c.2.2.2
                                              rcases p1224_3 (m.d 0 3) (by simp) with h1246 | h1246
                                              · linarith only [h1, h1246, hlam]
                                              · linarith only [h1159, h1246, hlam]
                                            · have p1224_0 := h1224c.1
                                              have p1224_1 := h1224c.2.1
                                              have p1224_2 := h1224c.2.2.1
                                              have p1224_3 := h1224c.2.2.2
                                              linarith only [h1158, h1160, h1172, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1224_1]
                                            · have p1224_0 := h1224c.1
                                              have p1224_1 := h1224c.2.1
                                              have p1224_2 := h1224c.2.2.1
                                              have p1224_3 := h1224c.2.2.2
                                              linarith only [h0, h1, hc12, hc23, hlam, hphi, p1224_1]
                                            · have p1224_0 := h1224c.1
                                              have p1224_1 := h1224c.2.1
                                              have p1224_2 := h1224c.2.2.1
                                              have p1224_3 := h1224c.2.2.2
                                              linarith only [hlam, p1224_0]
                                            · have p1224_0 := h1224c.1
                                              have p1224_1 := h1224c.2.1
                                              have p1224_2 := h1224c.2.2.1
                                              have p1224_3 := h1224c.2.2.2
                                              rcases p1224_3 (m.d 0 3) (by simp) with h1252 | h1252
                                              · linarith only [h1035, h1252, hlam]
                                              · linarith only [h1158, h1252, hlam]
                                            · have p1224_0 := h1224c.1
                                              have p1224_1 := h1224c.2.1
                                              have p1224_2 := h1224c.2.2.1
                                              have p1224_3 := h1224c.2.2.2
                                              rcases p1224_3 (m.d 0 3) (by simp) with h1255 | h1255
                                              · linarith only [h1035, h1255, hlam]
                                              · linarith only [h1159, h1255, hlam]
                                            · have p1224_0 := h1224c.1
                                              have p1224_1 := h1224c.2.1
                                              have p1224_2 := h1224c.2.2.1
                                              have p1224_3 := h1224c.2.2.2
                                              linarith only [h1158, hlam, p1224_0]
                                            · have p1224_0 := h1224c.1
                                              have p1224_1 := h1224c.2.1
                                              have p1224_2 := h1224c.2.2.1
                                              have p1224_3 := h1224c.2.2.2
                                              linarith only [h1167, hlam, p1224_0]
                                            · have p1224_0 := h1224c.1
                                              have p1224_1 := h1224c.2.1
                                              have p1224_2 := h1224c.2.2.1
                                              have p1224_3 := h1224c.2.2.2
                                              linarith only [h1169, hlam, p1224_0]
                                            · have p1224_0 := h1224c.1
                                              have p1224_1 := h1224c.2.1
                                              have p1224_2 := h1224c.2.2.1
                                              have p1224_3 := h1224c.2.2.2
                                              linarith only [hlam, p1224_0]
                                            · have p1224_0 := h1224c.1
                                              have p1224_1 := h1224c.2.1
                                              have p1224_2 := h1224c.2.2.1
                                              have p1224_3 := h1224c.2.2.2
                                              linarith only [h1172, hlam, p1224_1]
                                            · have p1224_0 := h1224c.1
                                              have p1224_1 := h1224c.2.1
                                              have p1224_2 := h1224c.2.2.1
                                              have p1224_3 := h1224c.2.2.2
                                              linarith only [h1159, hlam, p1224_0]
                                            · have p1224_0 := h1224c.1
                                              have p1224_1 := h1224c.2.1
                                              have p1224_2 := h1224c.2.2.1
                                              have p1224_3 := h1224c.2.2.2
                                              linarith only [h1168, hlam, p1224_0]
                                            · have p1224_0 := h1224c.1
                                              have p1224_1 := h1224c.2.1
                                              have p1224_2 := h1224c.2.2.1
                                              have p1224_3 := h1224c.2.2.2
                                              linarith only [h1170, hlam, p1224_0]
                                            · have p1224_0 := h1224c.1
                                              have p1224_1 := h1224c.2.1
                                              have p1224_2 := h1224c.2.2.1
                                              have p1224_3 := h1224c.2.2.2
                                              linarith only [h1159, hc34, hlam, hphi, ht0b, ht45, ht5b, p1224_1, u0elo2]
                                            · have p1224_0 := h1224c.1
                                              have p1224_1 := h1224c.2.1
                                              have p1224_2 := h1224c.2.2.1
                                              have p1224_3 := h1224c.2.2.2
                                              linarith only [hlam, p1224_0]
                                          · linarith only [h1223, hlam, p1174_0]
                                        · linarith only [h1037, h1222, hlam]
                                      · linarith only [h1035, h1221, hlam]
                                · have p1174_0 := h1174c.1
                                  have p1174_1 := h1174c.2.1
                                  have p1174_2 := h1174c.2.2.1
                                  have p1174_3 := h1174c.2.2.2
                                  rcases p1174_3 (m.d 0 2) (by simp) with h1271 | h1271
                                  · linarith only [h1134, h1271, hlam]
                                  · linarith only [h0, h1271, hlam]
                                · have p1174_0 := h1174c.1
                                  have p1174_1 := h1174c.2.1
                                  have p1174_2 := h1174c.2.2.1
                                  have p1174_3 := h1174c.2.2.2
                                  linarith only [h1170, hlam, p1174_1]
                                · have p1174_0 := h1174c.1
                                  have p1174_1 := h1174c.2.1
                                  have p1174_2 := h1174c.2.2.1
                                  have p1174_3 := h1174c.2.2.2
                                  linarith only [h1171, hlam, p1174_0]
                                · have p1174_0 := h1174c.1
                                  have p1174_1 := h1174c.2.1
                                  have p1174_2 := h1174c.2.2.1
                                  have p1174_3 := h1174c.2.2.2
                                  linarith only [hlam, p1174_0]
                            · linarith only [h0, h1037, h1158, h1160, h1171, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h1035, h1159, h1170, hlam]
                        · linarith only [h0, h1, h1161, h1169, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h1, h1159, h1168, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                    · linarith only [h0, h1, h1158, h1167, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1282 | h1282
              · linarith only [h0, h1035, h1158, h1282, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1284 | h1284
                · linarith only [h0, h1037, h1284, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1286 | h1286
                  · linarith only [h0, h1134, h1286, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1288 | h1288
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1289 | h1289
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1290 | h1290
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1291 | h1291
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1292 | h1292
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1293 | h1293
                              · linarith only [h1037, h1158, h1160, h1293, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                              · rcases h2bigk with h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [hlam, p1295_0]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [h1037, h1160, h1290, h1292, hc12, hc23, hlam, hphi, p1295_1]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [h1035, hlam, p1295_0]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [h1037, hlam, p1295_0]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [h1134, hlam, p1295_0]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [h0, hlam, p1295_0]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [hlam, p1295_0]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [h1282, hlam, p1295_0]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [h1284, hlam, p1295_0]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [h1286, hlam, p1295_0]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  rcases p1295_3 (m.d 0 2) (by simp) with h1306 | h1306
                                  · linarith only [h1306, hlam, p1295_0]
                                  · rcases p1295_3 (m.d 1 2) (by simp) with h1308 | h1308
                                    · linarith only [h1282, h1308, hlam]
                                    · rcases p1295_3 (m.d 2 3) (by simp) with h1310 | h1310
                                      · rcases p1295_3 (m.d 2 4) (by simp) with h1311 | h1311
                                        · linarith only [h1290, h1311, hlam]
                                        · linarith only [h1037, h1311, hlam]
                                      · linarith only [h1310, hlam, p1295_0]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  rcases p1295_3 (m.d 0 2) (by simp) with h1315 | h1315
                                  · linarith only [h1035, h1315, hlam]
                                  · linarith only [h0, h1315, hlam]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [hlam, p1295_0]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [h1037, h1160, h1292, hc02, hc23, hlam, hphi, p1295_1]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [h0, h1037, h1160, h1292, hc12, hc23, hlam, hphi, p1295_1]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  rcases p1295_3 (m.d 0 2) (by simp) with h1321 | h1321
                                  · linarith only [h1321, hlam, p1295_0]
                                  · rcases p1295_3 (m.d 1 2) (by simp) with h1323 | h1323
                                    · linarith only [h1284, h1323, hlam]
                                    · rcases p1295_3 (m.d 2 3) (by simp) with h1325 | h1325
                                      · rcases p1295_3 (m.d 2 4) (by simp) with h1326 | h1326
                                        · rcases p1295_3 (m.d 2 5) (by simp) with h1327 | h1327
                                          · linarith only [h1292, h1327, hlam]
                                          · linarith only [h1134, h1327, hlam]
                                        · linarith only [h1326, hlam, p1295_0]
                                      · linarith only [h1035, h1325, hlam]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  rcases p1295_3 (m.d 0 2) (by simp) with h1332 | h1332
                                  · linarith only [h1037, h1332, hlam]
                                  · linarith only [h0, h1332, hlam]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [h1290, hlam, p1295_1]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [hlam, p1295_0]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [h0, h1037, h1160, h1292, hc12, hc24, hlam, hphi, p1295_1]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  rcases p1295_3 (m.d 0 2) (by simp) with h1338 | h1338
                                  · linarith only [h1338, hlam, p1295_0]
                                  · rcases p1295_3 (m.d 1 2) (by simp) with h1340 | h1340
                                    · linarith only [h1286, h1340, hlam]
                                    · rcases p1295_3 (m.d 2 3) (by simp) with h1342 | h1342
                                      · rcases p1295_3 (m.d 2 4) (by simp) with h1343 | h1343
                                        · rcases p1295_3 (m.d 2 5) (by simp) with h1344 | h1344
                                          · rcases h3bigk with h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c
                                            · have p1345_0 := h1345c.1
                                              have p1345_1 := h1345c.2.1
                                              have p1345_2 := h1345c.2.2.1
                                              have p1345_3 := h1345c.2.2.2
                                              linarith only [hlam, p1345_0]
                                            · have p1345_0 := h1345c.1
                                              have p1345_1 := h1345c.2.1
                                              have p1345_2 := h1345c.2.2.1
                                              have p1345_3 := h1345c.2.2.2
                                              linarith only [h1, hlam, p1345_1]
                                            · have p1345_0 := h1345c.1
                                              have p1345_1 := h1345c.2.1
                                              have p1345_2 := h1345c.2.2.1
                                              have p1345_3 := h1345c.2.2.2
                                              linarith only [h1035, hlam, p1345_1]
                                            · have p1345_0 := h1345c.1
                                              have p1345_1 := h1345c.2.1
                                              have p1345_2 := h1345c.2.2.1
                                              have p1345_3 := h1345c.2.2.2
                                              rcases p1345_3 (m.d 0 3) (by simp) with h1349 | h1349
                                              · rcases p1345_3 (m.d 1 3) (by simp) with h1350 | h1350
                                                · rcases p1345_3 (m.d 2 3) (by simp) with h1351 | h1351
                                                  · rcases p1345_3 (m.d 3 4) (by simp) with h1352 | h1352
                                                    · linarith only [h1352, hlam, p1345_0]
                                                    · rcases p1345_3 (m.d 3 5) (by simp) with h1354 | h1354
                                                      · linarith only [h1159, h1354, hlam]
                                                      · linarith only [h1293, h1354, hlam]
                                                  · linarith only [h1290, h1351, hlam]
                                                · linarith only [h1288, h1350, hlam]
                                              · linarith only [h1349, hlam, p1345_0]
                                            · have p1345_0 := h1345c.1
                                              have p1345_1 := h1345c.2.1
                                              have p1345_2 := h1345c.2.2.1
                                              have p1345_3 := h1345c.2.2.2
                                              linarith only [hlam, hphi, ht0b, ht5b, p1345_1, u0elo2, u5ehi3]
                                            · have p1345_0 := h1345c.1
                                              have p1345_1 := h1345c.2.1
                                              have p1345_2 := h1345c.2.2.1
                                              have p1345_3 := h1345c.2.2.2
                                              linarith only [h0, h1, h1282, hc12, hc23, hlam, hphi, p1345_1]
                                            · have p1345_0 := h1345c.1
                                              have p1345_1 := h1345c.2.1
                                              have p1345_2 := h1345c.2.2.1
                                              have p1345_3 := h1345c.2.2.2
                                              linarith only [hlam, p1345_0]
                                            · have p1345_0 := h1345c.1
                                              have p1345_1 := h1345c.2.1
                                              have p1345_2 := h1345c.2.2.1
                                              have p1345_3 := h1345c.2.2.2
                                              linarith only [h1282, hlam, p1345_1]
                                            · have p1345_0 := h1345c.1
                                              have p1345_1 := h1345c.2.1
                                              have p1345_2 := h1345c.2.2.1
                                              have p1345_3 := h1345c.2.2.2
                                              rcases p1345_3 (m.d 0 3) (by simp) with h1364 | h1364
                                              · linarith only [h1, h1364, hlam]
                                              · linarith only [h1158, h1364, hlam]
                                            · have p1345_0 := h1345c.1
                                              have p1345_1 := h1345c.2.1
                                              have p1345_2 := h1345c.2.2.1
                                              have p1345_3 := h1345c.2.2.2
                                              rcases p1345_3 (m.d 0 3) (by simp) with h1367 | h1367
                                              · linarith only [h1, h1367, hlam]
                                              · linarith only [h1159, h1367, hlam]
                                            · have p1345_0 := h1345c.1
                                              have p1345_1 := h1345c.2.1
                                              have p1345_2 := h1345c.2.2.1
                                              have p1345_3 := h1345c.2.2.2
                                              linarith only [h1159, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1345_1, u5ehi3]
                                            · have p1345_0 := h1345c.1
                                              have p1345_1 := h1345c.2.1
                                              have p1345_2 := h1345c.2.2.1
                                              have p1345_3 := h1345c.2.2.2
                                              linarith only [h0, h1, hc12, hc23, hlam, hphi, p1345_1]
                                            · have p1345_0 := h1345c.1
                                              have p1345_1 := h1345c.2.1
                                              have p1345_2 := h1345c.2.2.1
                                              have p1345_3 := h1345c.2.2.2
                                              linarith only [hlam, p1345_0]
                                            · have p1345_0 := h1345c.1
                                              have p1345_1 := h1345c.2.1
                                              have p1345_2 := h1345c.2.2.1
                                              have p1345_3 := h1345c.2.2.2
                                              rcases p1345_3 (m.d 0 3) (by simp) with h1373 | h1373
                                              · linarith only [h1035, h1373, hlam]
                                              · linarith only [h1158, h1373, hlam]
                                            · have p1345_0 := h1345c.1
                                              have p1345_1 := h1345c.2.1
                                              have p1345_2 := h1345c.2.2.1
                                              have p1345_3 := h1345c.2.2.2
                                              rcases p1345_3 (m.d 0 3) (by simp) with h1376 | h1376
                                              · linarith only [h1035, h1376, hlam]
                                              · linarith only [h1159, h1376, hlam]
                                            · have p1345_0 := h1345c.1
                                              have p1345_1 := h1345c.2.1
                                              have p1345_2 := h1345c.2.2.1
                                              have p1345_3 := h1345c.2.2.2
                                              linarith only [h1158, hlam, p1345_0]
                                            · have p1345_0 := h1345c.1
                                              have p1345_1 := h1345c.2.1
                                              have p1345_2 := h1345c.2.2.1
                                              have p1345_3 := h1345c.2.2.2
                                              linarith only [h1288, hlam, p1345_0]
                                            · have p1345_0 := h1345c.1
                                              have p1345_1 := h1345c.2.1
                                              have p1345_2 := h1345c.2.2.1
                                              have p1345_3 := h1345c.2.2.2
                                              linarith only [h1290, hlam, p1345_0]
                                            · have p1345_0 := h1345c.1
                                              have p1345_1 := h1345c.2.1
                                              have p1345_2 := h1345c.2.2.1
                                              have p1345_3 := h1345c.2.2.2
                                              linarith only [hlam, p1345_0]
                                            · have p1345_0 := h1345c.1
                                              have p1345_1 := h1345c.2.1
                                              have p1345_2 := h1345c.2.2.1
                                              have p1345_3 := h1345c.2.2.2
                                              linarith only [h1293, hlam, p1345_1]
                                            · have p1345_0 := h1345c.1
                                              have p1345_1 := h1345c.2.1
                                              have p1345_2 := h1345c.2.2.1
                                              have p1345_3 := h1345c.2.2.2
                                              linarith only [h1159, hlam, p1345_0]
                                            · have p1345_0 := h1345c.1
                                              have p1345_1 := h1345c.2.1
                                              have p1345_2 := h1345c.2.2.1
                                              have p1345_3 := h1345c.2.2.2
                                              linarith only [h1289, hlam, p1345_0]
                                            · have p1345_0 := h1345c.1
                                              have p1345_1 := h1345c.2.1
                                              have p1345_2 := h1345c.2.2.1
                                              have p1345_3 := h1345c.2.2.2
                                              linarith only [h1291, hlam, p1345_0]
                                            · have p1345_0 := h1345c.1
                                              have p1345_1 := h1345c.2.1
                                              have p1345_2 := h1345c.2.2.1
                                              have p1345_3 := h1345c.2.2.2
                                              linarith only [h1159, hc34, hlam, hphi, ht0b, ht45, ht5b, p1345_1, u0elo2]
                                            · have p1345_0 := h1345c.1
                                              have p1345_1 := h1345c.2.1
                                              have p1345_2 := h1345c.2.2.1
                                              have p1345_3 := h1345c.2.2.2
                                              linarith only [hlam, p1345_0]
                                          · linarith only [h1344, hlam, p1295_0]
                                        · linarith only [h1037, h1343, hlam]
                                      · linarith only [h1035, h1342, hlam]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  rcases p1295_3 (m.d 0 2) (by simp) with h1392 | h1392
                                  · linarith only [h1134, h1392, hlam]
                                  · linarith only [h0, h1392, hlam]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [h1291, hlam, p1295_1]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [h1292, hlam, p1295_0]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [hlam, p1295_0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1398 | h1398
                              · linarith only [h0, h1037, h1292, h1398, hc12, hc34, hlam, hphi, ht23]
                              · rcases h2bigk with h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [hlam, p1400_0]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [h1037, hc12, hc24, hlam, hphi, p1400_1]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [h1035, hlam, p1400_0]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [h1037, hlam, p1400_0]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [h1134, hlam, p1400_0]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [h0, hlam, p1400_0]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [hlam, p1400_0]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [h1282, hlam, p1400_0]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [h1284, hlam, p1400_0]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [h1286, hlam, p1400_0]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  rcases p1400_3 (m.d 0 2) (by simp) with h1411 | h1411
                                  · linarith only [h1411, hlam, p1400_0]
                                  · rcases p1400_3 (m.d 1 2) (by simp) with h1413 | h1413
                                    · linarith only [h1282, h1413, hlam]
                                    · rcases p1400_3 (m.d 2 3) (by simp) with h1415 | h1415
                                      · rcases p1400_3 (m.d 2 4) (by simp) with h1416 | h1416
                                        · linarith only [h1290, h1416, hlam]
                                        · linarith only [h1037, h1416, hlam]
                                      · linarith only [h1415, hlam, p1400_0]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  rcases p1400_3 (m.d 0 2) (by simp) with h1420 | h1420
                                  · linarith only [h1035, h1420, hlam]
                                  · linarith only [h0, h1420, hlam]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [hlam, p1400_0]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [h1037, hc02, hc23, hlam, hphi, p1400_1]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [h0, h1134, hc12, hc23, hlam, hphi, p1400_1]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [h0, h1292, hc12, hc45, hlam, hphi, ht23, ht34, p1400_1]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [h1292, hc12, hc45, hlam, hphi, ht23, ht34, p1400_1]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [h1290, hlam, p1400_1]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [hlam, p1400_0]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [h1292, hlam, p1400_1]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  rcases p1400_3 (m.d 0 2) (by simp) with h1431 | h1431
                                  · linarith only [h1431, hlam, p1400_0]
                                  · rcases p1400_3 (m.d 1 2) (by simp) with h1433 | h1433
                                    · linarith only [h1286, h1433, hlam]
                                    · rcases p1400_3 (m.d 2 3) (by simp) with h1435 | h1435
                                      · rcases p1400_3 (m.d 2 4) (by simp) with h1436 | h1436
                                        · linarith only [h1292, h1436, hlam]
                                        · linarith only [h1037, h1436, hlam]
                                      · linarith only [h1035, h1435, hlam]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  rcases p1400_3 (m.d 0 2) (by simp) with h1440 | h1440
                                  · linarith only [h1134, h1440, hlam]
                                  · linarith only [h0, h1440, hlam]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [h1291, hlam, p1400_1]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [h0, h1037, hc12, hc25, hlam, hphi, p1400_1]
                                · have p1400_0 := h1400c.1
                                  have p1400_1 := h1400c.2.1
                                  have p1400_2 := h1400c.2.2.1
                                  have p1400_3 := h1400c.2.2.2
                                  linarith only [hlam, p1400_0]
                          · linarith only [h0, h1035, h1159, h1291, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h1, h1158, h1159, h1160, h1282, h1290, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
                      · linarith only [h1, h1159, h1289, hlam]
                    · linarith only [h1, h1158, h1288, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1450 | h1450
            · linarith only [h1158, h1159, h1450, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1452 | h1452
              · linarith only [h0, h1035, h1452, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1454 | h1454
                · linarith only [h0, h1037, h1454, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1456 | h1456
                  · linarith only [h0, h1, h1134, h1159, h1456, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1458 | h1458
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1459 | h1459
                      · linarith only [h0, h1, h1159, h1452, h1459, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h1459, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h0, h1, h1158, h1458, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1463 | h1463
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1464 | h1464
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1465 | h1465
              · linarith only [h0, h1035, h1465, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1467 | h1467
                · linarith only [h0, h1, h1037, h1158, h1467, hc02, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1469 | h1469
                  · linarith only [h0, h1134, h1469, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1471 | h1471
                    · linarith only [h0, h1, h1158, h1465, h1471, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h1471, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h1158, h1463, h1464, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1475 | h1475
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1476 | h1476
              · linarith only [h0, h1, h1463, h1476, hc23, hc35, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1478 | h1478
                · linarith only [h0, h1, h1037, h1463, h1475, h1478, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1480 | h1480
                  · linarith only [h0, h1, h1134, h1463, h1480, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1482 | h1482
                    · linarith only [h0, h1, h1158, h1476, h1482, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h1482, hc12, hc34, hlam, hphi, ht23]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1485 | h1485
              · linarith only [h0, h1, h1158, h1475, h1485, hc23, hc45, hlam, hphi, ht34]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1487 | h1487
                · linarith only [h0, h1, h1037, h1158, h1475, h1487, hc02, hc45, hlam, hphi, ht23, ht34]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1489 | h1489
                  · linarith only [h0, h1, h1134, h1158, h1475, h1489, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1491 | h1491
                    · linarith only [h0, h1, h1158, h1485, h1491, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h1491, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 7634000 in
theorem r1l7_10_12_13_25_L_0_L_I_L_I_M_IR_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_10_12_13_25_L_0_L_I_L_I_M_IR_x0_x0 m hb0 hb2 hb3 hb5 h0 h1
  · exact r1l7_10_12_13_25_L_0_L_I_L_I_M_IR_x0_x1 m hb0 hb2 hb3 hb5 h0 h1

end R2N4
