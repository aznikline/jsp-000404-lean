import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_28S14
import Jsp000404.R1LeavesN7_28S15

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10642000 in
set_option maxHeartbeats 10642000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_R_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h5ehi := hb5.1
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
  rcases m.htr 0 1 5 (by decide) (by decide) with h1085 | h1085
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1086 | h1086
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1087 | h1087
      · linarith only [h0, h1087, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1089 | h1089
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1090 | h1090
          · linarith only [h1, h1090, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1092 | h1092
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1093 | h1093
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1094 | h1094
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1095 | h1095
                  · linarith only [h0, h1086, h1087, h1092, h1095, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1097 | h1097
                    · linarith only [h0, h1095, h1097, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                    · linarith only [h1089, h1094, h1097, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h1086, h1087, h1094, hc12, hc24, hlam, hphi]
              · linarith only [h0, h1086, h1092, h1093, h2, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1102 | h1102
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1103 | h1103
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1104 | h1104
                  · linarith only [h0, h1087, h1104, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1106 | h1106
                    · linarith only [h0, h1104, h1106, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                    · linarith only [h0, h1089, h1104, h1106, h2, hc12, hc24, hlam, hphi]
                · linarith only [h1086, h1087, h1103, hc12, hc24, hlam, hphi]
              · linarith only [h1085, h1102, h2, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1111 | h1111
          · linarith only [h1, h1111, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1113 | h1113
            · linarith only [h1086, h1089, h1113, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1115 | h1115
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1116 | h1116
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1117 | h1117
                  · linarith only [h0, h1087, h1117, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1119 | h1119
                    · linarith only [h0, h1089, h1117, h1119, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1121 | h1121
                      · linarith only [h1085, h1111, h1116, h1119, h1121, h2, hlam]
                      · linarith only [h1085, h1116, h1119, h1121, h2, hc23, hc34, hlam, hphi]
                · linarith only [h1086, h1089, h1116, hc12, hc25, hlam, hphi]
              · linarith only [h1085, h1115, h2, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1126 | h1126
      · linarith only [h0, h1126, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1128 | h1128
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1129 | h1129
          · linarith only [h1, h1129, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1131 | h1131
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1132 | h1132
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1133 | h1133
                · linarith only [h1086, h1128, h1133, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1135 | h1135
                  · linarith only [h1, h1126, h1128, h1133, h1135, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1137 | h1137
                    · linarith only [h1, h1133, h1135, h1137, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                    · linarith only [h1086, h1128, h1137, hc12, hc23, hlam, hphi]
              · linarith only [h1, h1086, h1128, h1132, h2, hlam]
            · linarith only [h1086, h1128, h1131, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1142 | h1142
          · linarith only [h1, h1142, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1144 | h1144
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1145 | h1145
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1146 | h1146
                · linarith only [h0, h1086, h1146, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1148 | h1148
                  · linarith only [h0, h1126, h1148, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1150 | h1150
                    · linarith only [h0, h1128, h1150, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1152 | h1152
                      · linarith only [h1, h1142, h1148, h1152, h2, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1154 | h1154
                        · linarith only [h1, h1152, h1154, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                        · linarith only [h1, h1144, h1152, h1154, h2, hc13, hc34, hlam, hphi]
              · linarith only [h1085, h1145, h2, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1158 | h1158
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1159 | h1159
                · linarith only [h0, h1086, h1159, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1161 | h1161
                  · linarith only [h0, h1126, h1161, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1163 | h1163
                    · linarith only [h0, h1128, h1163, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1165 | h1165
                      · linarith only [h1, h1086, h1142, h1161, h1165, h2, hc02, hc24, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1167 | h1167
                        · linarith only [h1, h1144, h1167, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1169 | h1169
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1170 | h1170
                            · linarith only [h1085, h1165, h1169, h1170, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1172 | h1172
                              · linarith only [h0, h1086, h1144, h1170, h1172, hc12, hc34, hlam, hphi, ht23]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1174 | h1174
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1175 | h1175
                                  · rcases h0bigk with h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c
                                    · have p1176_0 := h1176c.1
                                      have p1176_1 := h1176c.2.1
                                      have p1176_2 := h1176c.2.2.1
                                      have p1176_3 := h1176c.2.2.2
                                      linarith only [hlam, p1176_0]
                                    · have p1176_0 := h1176c.1
                                      have p1176_1 := h1176c.2.1
                                      have p1176_2 := h1176c.2.2.1
                                      have p1176_3 := h1176c.2.2.2
                                      linarith only [h0, h1161, h2, hc12, hc24, hlam, hphi, p1176_1]
                                    · have p1176_0 := h1176c.1
                                      have p1176_1 := h1176c.2.1
                                      have p1176_2 := h1176c.2.2.1
                                      have p1176_3 := h1176c.2.2.2
                                      linarith only [h0, h1086, h1161, h2, hc12, hc24, hlam, hphi, p1176_1]
                                    · have p1176_0 := h1176c.1
                                      have p1176_1 := h1176c.2.1
                                      have p1176_2 := h1176c.2.2.1
                                      have p1176_3 := h1176c.2.2.2
                                      linarith only [h2, hlam, p1176_1]
                                    · have p1176_0 := h1176c.1
                                      have p1176_1 := h1176c.2.1
                                      have p1176_2 := h1176c.2.2.1
                                      have p1176_3 := h1176c.2.2.2
                                      linarith only [h1085, h1161, h1169, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p1176_1, u5ehi4]
                                    · have p1176_0 := h1176c.1
                                      have p1176_1 := h1176c.2.1
                                      have p1176_2 := h1176c.2.2.1
                                      have p1176_3 := h1176c.2.2.2
                                      linarith only [h0, hlam, p1176_0]
                                    · have p1176_0 := h1176c.1
                                      have p1176_1 := h1176c.2.1
                                      have p1176_2 := h1176c.2.2.1
                                      have p1176_3 := h1176c.2.2.2
                                      linarith only [hlam, p1176_0]
                                    · have p1176_0 := h1176c.1
                                      have p1176_1 := h1176c.2.1
                                      have p1176_2 := h1176c.2.2.1
                                      have p1176_3 := h1176c.2.2.2
                                      linarith only [h1086, hlam, p1176_0]
                                    · have p1176_0 := h1176c.1
                                      have p1176_1 := h1176c.2.1
                                      have p1176_2 := h1176c.2.2.1
                                      have p1176_3 := h1176c.2.2.2
                                      linarith only [h1126, hlam, p1176_1]
                                    · have p1176_0 := h1176c.1
                                      have p1176_1 := h1176c.2.1
                                      have p1176_2 := h1176c.2.2.1
                                      have p1176_3 := h1176c.2.2.2
                                      linarith only [h1128, hlam, p1176_0]
                                    · have p1176_0 := h1176c.1
                                      have p1176_1 := h1176c.2.1
                                      have p1176_2 := h1176c.2.2.1
                                      have p1176_3 := h1176c.2.2.2
                                      linarith only [h1, hlam, p1176_1]
                                    · have p1176_0 := h1176c.1
                                      have p1176_1 := h1176c.2.1
                                      have p1176_2 := h1176c.2.2.1
                                      have p1176_3 := h1176c.2.2.2
                                      linarith only [h0, h1, h1161, h2, hc12, hc24, hlam, hphi, p1176_1]
                                    · have p1176_0 := h1176c.1
                                      have p1176_1 := h1176c.2.1
                                      have p1176_2 := h1176c.2.2.1
                                      have p1176_3 := h1176c.2.2.2
                                      linarith only [hlam, p1176_0]
                                    · have p1176_0 := h1176c.1
                                      have p1176_1 := h1176c.2.1
                                      have p1176_2 := h1176c.2.2.1
                                      have p1176_3 := h1176c.2.2.2
                                      linarith only [h1142, hlam, p1176_1]
                                    · have p1176_0 := h1176c.1
                                      have p1176_1 := h1176c.2.1
                                      have p1176_2 := h1176c.2.2.1
                                      have p1176_3 := h1176c.2.2.2
                                      linarith only [h1144, hlam, p1176_1]
                                    · have p1176_0 := h1176c.1
                                      have p1176_1 := h1176c.2.1
                                      have p1176_2 := h1176c.2.2.1
                                      have p1176_3 := h1176c.2.2.2
                                      linarith only [h1, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1176_1, u0elo3]
                                    · have p1176_0 := h1176c.1
                                      have p1176_1 := h1176c.2.1
                                      have p1176_2 := h1176c.2.2.1
                                      have p1176_3 := h1176c.2.2.2
                                      rcases p1176_3 (m.d 0 1) (by simp) with h1193 | h1193
                                      · linarith only [h1193, h2, hlam]
                                      · linarith only [h0, h1193, hlam]
                                    · have p1176_0 := h1176c.1
                                      have p1176_1 := h1176c.2.1
                                      have p1176_2 := h1176c.2.2.1
                                      have p1176_3 := h1176c.2.2.2
                                      rcases p1176_3 (m.d 0 1) (by simp) with h1196 | h1196
                                      · linarith only [h1196, h2, hlam]
                                      · linarith only [h1, h1196, hlam]
                                    · have p1176_0 := h1176c.1
                                      have p1176_1 := h1176c.2.1
                                      have p1176_2 := h1176c.2.2.1
                                      have p1176_3 := h1176c.2.2.2
                                      linarith only [hlam, p1176_0]
                                    · have p1176_0 := h1176c.1
                                      have p1176_1 := h1176c.2.1
                                      have p1176_2 := h1176c.2.2.1
                                      have p1176_3 := h1176c.2.2.2
                                      linarith only [hlam, hphi, ht0b, ht5b, p1176_1, u0elo3, u5ehi0]
                                    · have p1176_0 := h1176c.1
                                      have p1176_1 := h1176c.2.1
                                      have p1176_2 := h1176c.2.2.1
                                      have p1176_3 := h1176c.2.2.2
                                      linarith only [h1085, hlam, p1176_0]
                                    · have p1176_0 := h1176c.1
                                      have p1176_1 := h1176c.2.1
                                      have p1176_2 := h1176c.2.2.1
                                      have p1176_3 := h1176c.2.2.2
                                      linarith only [h0, h1085, h1161, h1170, h2, hc12, hc34, hlam, hphi, ht23, p1176_1]
                                    · have p1176_0 := h1176c.1
                                      have p1176_1 := h1176c.2.1
                                      have p1176_2 := h1176c.2.2.1
                                      have p1176_3 := h1176c.2.2.2
                                      linarith only [h1085, h1161, h1170, h2, hc03, hc34, hlam, hphi, p1176_1]
                                    · have p1176_0 := h1176c.1
                                      have p1176_1 := h1176c.2.1
                                      have p1176_2 := h1176c.2.2.1
                                      have p1176_3 := h1176c.2.2.2
                                      linarith only [h1158, hlam, p1176_1]
                                    · have p1176_0 := h1176c.1
                                      have p1176_1 := h1176c.2.1
                                      have p1176_2 := h1176c.2.2.1
                                      have p1176_3 := h1176c.2.2.2
                                      linarith only [hlam, p1176_0]
                                  · linarith only [h1085, h1161, h1169, h1170, h1175, h2, hlam]
                                · linarith only [h1085, h1161, h1169, h1174, h2, hlam]
                          · linarith only [h1085, h1169, h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi1]
              · linarith only [h1085, h1158, h2, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1210 | h1210
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1211 | h1211
      · linarith only [h0, h1211, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1213 | h1213
        · linarith only [h0, h1085, h1213, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1215 | h1215
          · linarith only [h1, h1215, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1217 | h1217
            · linarith only [h0, h1085, h1210, h1217, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1219 | h1219
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1220 | h1220
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1221 | h1221
                  · linarith only [h0, h1211, h1221, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1223 | h1223
                    · linarith only [h0, h1213, h1221, h1223, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1225 | h1225
                      · linarith only [h0, h1215, h1220, h1221, h1225, h2, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · linarith only [h0, h1220, h1225, h2, hc23, hc34, hlam, hphi]
                · linarith only [h1210, h1211, h1220, hc12, hc24, hlam, hphi]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1229 | h1229
                · linarith only [h0, h1219, h1229, h2, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h1210, h1219, h1229, h2, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1232 | h1232
      · linarith only [h1, h1210, h1232, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1234 | h1234
        · linarith only [h1, h1085, h1210, h1234, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1236 | h1236
          · linarith only [h1, h1236, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1238 | h1238
            · linarith only [h1, h1085, h1238, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1240 | h1240
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1241 | h1241
                · linarith only [h0, h1210, h1241, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1243 | h1243
                  · linarith only [h0, h1232, h1240, h1243, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1245 | h1245
                    · linarith only [h1, h1234, h1241, h1245, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1247 | h1247
                      · linarith only [h1, h1236, h1243, h1247, h2, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1249 | h1249
                        · linarith only [h1, h1085, h1238, h1249, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1251 | h1251
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1252 | h1252
                            · linarith only [h0, h1085, h1247, h1251, h1252, hc12, hc23, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1254 | h1254
                              · linarith only [h1, h1085, h1241, h1249, h1252, h1254, hc12, hc34, hlam, hphi, ht23]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1256 | h1256
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1257 | h1257
                                  · rcases h0bigk with h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c
                                    · have p1258_0 := h1258c.1
                                      have p1258_1 := h1258c.2.1
                                      have p1258_2 := h1258c.2.2.1
                                      have p1258_3 := h1258c.2.2.2
                                      linarith only [hlam, p1258_0]
                                    · have p1258_0 := h1258c.1
                                      have p1258_1 := h1258c.2.1
                                      have p1258_2 := h1258c.2.2.1
                                      have p1258_3 := h1258c.2.2.2
                                      linarith only [h0, h1085, h1245, hc12, hc25, hlam, hphi, p1258_1]
                                    · have p1258_0 := h1258c.1
                                      have p1258_1 := h1258c.2.1
                                      have p1258_2 := h1258c.2.2.1
                                      have p1258_3 := h1258c.2.2.2
                                      linarith only [h0, h1085, h1210, h1245, hc12, hc25, hlam, hphi, p1258_1]
                                    · have p1258_0 := h1258c.1
                                      have p1258_1 := h1258c.2.1
                                      have p1258_2 := h1258c.2.2.1
                                      have p1258_3 := h1258c.2.2.2
                                      linarith only [h2, hlam, p1258_1]
                                    · have p1258_0 := h1258c.1
                                      have p1258_1 := h1258c.2.1
                                      have p1258_2 := h1258c.2.2.1
                                      have p1258_3 := h1258c.2.2.2
                                      linarith only [h1085, hlam, p1258_1]
                                    · have p1258_0 := h1258c.1
                                      have p1258_1 := h1258c.2.1
                                      have p1258_2 := h1258c.2.2.1
                                      have p1258_3 := h1258c.2.2.2
                                      linarith only [h0, hlam, p1258_0]
                                    · have p1258_0 := h1258c.1
                                      have p1258_1 := h1258c.2.1
                                      have p1258_2 := h1258c.2.2.1
                                      have p1258_3 := h1258c.2.2.2
                                      linarith only [hlam, p1258_0]
                                    · have p1258_0 := h1258c.1
                                      have p1258_1 := h1258c.2.1
                                      have p1258_2 := h1258c.2.2.1
                                      have p1258_3 := h1258c.2.2.2
                                      linarith only [h1210, hlam, p1258_0]
                                    · have p1258_0 := h1258c.1
                                      have p1258_1 := h1258c.2.1
                                      have p1258_2 := h1258c.2.2.1
                                      have p1258_3 := h1258c.2.2.2
                                      linarith only [h1232, hlam, p1258_1]
                                    · have p1258_0 := h1258c.1
                                      have p1258_1 := h1258c.2.1
                                      have p1258_2 := h1258c.2.2.1
                                      have p1258_3 := h1258c.2.2.2
                                      linarith only [h1234, hlam, p1258_0]
                                    · have p1258_0 := h1258c.1
                                      have p1258_1 := h1258c.2.1
                                      have p1258_2 := h1258c.2.2.1
                                      have p1258_3 := h1258c.2.2.2
                                      linarith only [h1, hlam, p1258_1]
                                    · have p1258_0 := h1258c.1
                                      have p1258_1 := h1258c.2.1
                                      have p1258_2 := h1258c.2.2.1
                                      have p1258_3 := h1258c.2.2.2
                                      linarith only [h0, h1, h1085, h1245, hc12, hc25, hlam, hphi, p1258_1]
                                    · have p1258_0 := h1258c.1
                                      have p1258_1 := h1258c.2.1
                                      have p1258_2 := h1258c.2.2.1
                                      have p1258_3 := h1258c.2.2.2
                                      linarith only [hlam, p1258_0]
                                    · have p1258_0 := h1258c.1
                                      have p1258_1 := h1258c.2.1
                                      have p1258_2 := h1258c.2.2.1
                                      have p1258_3 := h1258c.2.2.2
                                      linarith only [h1236, hlam, p1258_1]
                                    · have p1258_0 := h1258c.1
                                      have p1258_1 := h1258c.2.1
                                      have p1258_2 := h1258c.2.2.1
                                      have p1258_3 := h1258c.2.2.2
                                      linarith only [h1238, hlam, p1258_1]
                                    · have p1258_0 := h1258c.1
                                      have p1258_1 := h1258c.2.1
                                      have p1258_2 := h1258c.2.2.1
                                      have p1258_3 := h1258c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1258_1, u0elo3]
                                    · have p1258_0 := h1258c.1
                                      have p1258_1 := h1258c.2.1
                                      have p1258_2 := h1258c.2.2.1
                                      have p1258_3 := h1258c.2.2.2
                                      rcases p1258_3 (m.d 0 1) (by simp) with h1275 | h1275
                                      · linarith only [h1275, h2, hlam]
                                      · linarith only [h0, h1275, hlam]
                                    · have p1258_0 := h1258c.1
                                      have p1258_1 := h1258c.2.1
                                      have p1258_2 := h1258c.2.2.1
                                      have p1258_3 := h1258c.2.2.2
                                      rcases p1258_3 (m.d 0 1) (by simp) with h1278 | h1278
                                      · linarith only [h1278, h2, hlam]
                                      · linarith only [h1, h1278, hlam]
                                    · have p1258_0 := h1258c.1
                                      have p1258_1 := h1258c.2.1
                                      have p1258_2 := h1258c.2.2.1
                                      have p1258_3 := h1258c.2.2.2
                                      linarith only [hlam, p1258_0]
                                    · have p1258_0 := h1258c.1
                                      have p1258_1 := h1258c.2.1
                                      have p1258_2 := h1258c.2.2.1
                                      have p1258_3 := h1258c.2.2.2
                                      linarith only [h1, h1085, h1241, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1258_1, u0elo3]
                                    · have p1258_0 := h1258c.1
                                      have p1258_1 := h1258c.2.1
                                      have p1258_2 := h1258c.2.2.1
                                      have p1258_3 := h1258c.2.2.2
                                      linarith only [h1, h1241, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1258_1, u0elo4]
                                    · have p1258_0 := h1258c.1
                                      have p1258_1 := h1258c.2.1
                                      have p1258_2 := h1258c.2.2.1
                                      have p1258_3 := h1258c.2.2.2
                                      rcases p1258_3 (m.d 0 1) (by simp) with h1284 | h1284
                                      · linarith only [h1085, h1284, hlam]
                                      · linarith only [h0, h1284, hlam]
                                    · have p1258_0 := h1258c.1
                                      have p1258_1 := h1258c.2.1
                                      have p1258_2 := h1258c.2.2.1
                                      have p1258_3 := h1258c.2.2.2
                                      rcases p1258_3 (m.d 0 1) (by simp) with h1287 | h1287
                                      · linarith only [h1085, h1287, hlam]
                                      · linarith only [h1, h1287, hlam]
                                    · have p1258_0 := h1258c.1
                                      have p1258_1 := h1258c.2.1
                                      have p1258_2 := h1258c.2.2.1
                                      have p1258_3 := h1258c.2.2.2
                                      linarith only [h1240, hlam, p1258_1]
                                    · have p1258_0 := h1258c.1
                                      have p1258_1 := h1258c.2.1
                                      have p1258_2 := h1258c.2.2.1
                                      have p1258_3 := h1258c.2.2.2
                                      linarith only [hlam, p1258_0]
                                  · linarith only [h1, h1241, h1243, h1252, h1257, h2, hc12, hc45, hlam, hphi, ht23, ht34]
                                · linarith only [h1240, h1243, h1256, h2, hlam]
                          · linarith only [h1240, h1251, h2, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1295 | h1295
                · linarith only [h0, h1240, h1295, h2, hc23, hc45, hlam, hphi, ht34]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1297 | h1297
                  · linarith only [h1, h1240, h1295, h1297, h2, hc24, hc45, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1299 | h1299
                    · linarith only [h1, h1240, h1295, h1299, h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1301 | h1301
                      · linarith only [h1, h1236, h1301, h2, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1303 | h1303
                        · linarith only [h1, h1240, h1303, h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1305 | h1305
                          · linarith only [h1, h1240, h1295, h1297, h1305, h2, hc12, hc24, hlam, hphi]
                          · linarith only [h1, h1295, h1305, h2, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 10642000 in
set_option maxHeartbeats 10642000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_R_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h5ehi := hb5.1
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
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_R_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h1 h2
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_R_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h1 h2

set_option maxHeartbeats 10642000 in
set_option maxHeartbeats 10642000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_R_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h5ehi := hb5.1
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
  rcases m.htr 0 1 4 (by decide) (by decide) with h1308 | h1308
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1309 | h1309
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1310 | h1310
      · linarith only [h0, h1, h1310, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1312 | h1312
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1313 | h1313
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1314 | h1314
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1315 | h1315
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1316 | h1316
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1317 | h1317
                  · linarith only [h1310, h1312, h1316, h1317, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1319 | h1319
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1320 | h1320
                      · linarith only [h0, h1320, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                      · linarith only [h0, h1, h1313, h1317, h1320, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h1312, h1317, h1319, hc12, hc23, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1324 | h1324
                  · linarith only [h0, h1310, h1313, h1324, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1326 | h1326
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1327 | h1327
                      · linarith only [h0, h1, h1324, h1327, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h1313, h1326, h1327, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1, h1312, h1324, h1326, hc12, hc23, hlam, hphi]
              · linarith only [h0, h1, h1313, h1315, hlam]
            · linarith only [h1, h1308, h1314, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1333 | h1333
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1334 | h1334
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1335 | h1335
                · linarith only [h1312, h1313, h1335, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1337 | h1337
                  · linarith only [h0, h1310, h1337, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1339 | h1339
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1340 | h1340
                      · linarith only [h0, h1313, h1340, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1342 | h1342
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1343 | h1343
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1344 | h1344
                            · linarith only [h1, h1308, h1335, h1337, h1344, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1346 | h1346
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1347 | h1347
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1348 | h1348
                                  · linarith only [h0, h1313, h1335, h1339, h1348, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1350 | h1350
                                    · linarith only [h0, h1313, h1339, h1346, h1348, h1350, hlam]
                                    · rcases h0bigk with h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c | h1352c
                                      · have p1352_0 := h1352c.1
                                        have p1352_1 := h1352c.2.1
                                        have p1352_2 := h1352c.2.2.1
                                        have p1352_3 := h1352c.2.2.2
                                        linarith only [hlam, p1352_0]
                                      · have p1352_0 := h1352c.1
                                        have p1352_1 := h1352c.2.1
                                        have p1352_2 := h1352c.2.2.1
                                        have p1352_3 := h1352c.2.2.2
                                        linarith only [h0, h1, h1337, h1339, h1346, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1352_1]
                                      · have p1352_0 := h1352c.1
                                        have p1352_1 := h1352c.2.1
                                        have p1352_2 := h1352c.2.2.1
                                        have p1352_3 := h1352c.2.2.2
                                        linarith only [h1, hlam, p1352_0]
                                      · have p1352_0 := h1352c.1
                                        have p1352_1 := h1352c.2.1
                                        have p1352_2 := h1352c.2.2.1
                                        have p1352_3 := h1352c.2.2.2
                                        rcases p1352_3 (m.d 0 1) (by simp) with h1356 | h1356
                                        · rcases p1352_3 (m.d 0 2) (by simp) with h1357 | h1357
                                          · linarith only [h0, h1357, hlam]
                                          · linarith only [h1312, h1357, hlam]
                                        · linarith only [h1308, h1356, hlam]
                                      · have p1352_0 := h1352c.1
                                        have p1352_1 := h1352c.2.1
                                        have p1352_2 := h1352c.2.2.1
                                        have p1352_3 := h1352c.2.2.2
                                        linarith only [h0, h1, h1313, h1337, h1339, h1346, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1352_1]
                                      · have p1352_0 := h1352c.1
                                        have p1352_1 := h1352c.2.1
                                        have p1352_2 := h1352c.2.2.1
                                        have p1352_3 := h1352c.2.2.2
                                        linarith only [h0, hlam, p1352_0]
                                      · have p1352_0 := h1352c.1
                                        have p1352_1 := h1352c.2.1
                                        have p1352_2 := h1352c.2.2.1
                                        have p1352_3 := h1352c.2.2.2
                                        linarith only [hlam, p1352_0]
                                      · have p1352_0 := h1352c.1
                                        have p1352_1 := h1352c.2.1
                                        have p1352_2 := h1352c.2.2.1
                                        have p1352_3 := h1352c.2.2.2
                                        linarith only [h1310, hlam, p1352_0]
                                      · have p1352_0 := h1352c.1
                                        have p1352_1 := h1352c.2.1
                                        have p1352_2 := h1352c.2.2.1
                                        have p1352_3 := h1352c.2.2.2
                                        linarith only [h1308, h1313, h1339, h1346, h1348, hc34, hc45, hlam, hphi, p1352_1]
                                      · have p1352_0 := h1352c.1
                                        have p1352_1 := h1352c.2.1
                                        have p1352_2 := h1352c.2.2.1
                                        have p1352_3 := h1352c.2.2.2
                                        linarith only [h1313, hlam, p1352_0]
                                      · have p1352_0 := h1352c.1
                                        have p1352_1 := h1352c.2.1
                                        have p1352_2 := h1352c.2.2.1
                                        have p1352_3 := h1352c.2.2.2
                                        linarith only [h0, h1339, h1346, hc34, hlam, hphi, ht0b, ht45, ht5b, p1352_1, u0elo2]
                                      · have p1352_0 := h1352c.1
                                        have p1352_1 := h1352c.2.1
                                        have p1352_2 := h1352c.2.2.1
                                        have p1352_3 := h1352c.2.2.2
                                        linarith only [h0, h1339, h1346, hc34, hlam, hphi, ht0b, ht45, ht5b, p1352_1, u0elo2]
                                      · have p1352_0 := h1352c.1
                                        have p1352_1 := h1352c.2.1
                                        have p1352_2 := h1352c.2.2.1
                                        have p1352_3 := h1352c.2.2.2
                                        linarith only [hlam, p1352_0]
                                      · have p1352_0 := h1352c.1
                                        have p1352_1 := h1352c.2.1
                                        have p1352_2 := h1352c.2.2.1
                                        have p1352_3 := h1352c.2.2.2
                                        rcases p1352_3 (m.d 0 1) (by simp) with h1370 | h1370
                                        · linarith only [h1, h1370, hlam]
                                        · linarith only [h1308, h1370, hlam]
                                      · have p1352_0 := h1352c.1
                                        have p1352_1 := h1352c.2.1
                                        have p1352_2 := h1352c.2.2.1
                                        have p1352_3 := h1352c.2.2.2
                                        linarith only [h1309, h1339, h1340, h1346, hc34, hlam, hphi, ht0b, ht45, ht5b, p1352_1, u0elo2]
                                      · have p1352_0 := h1352c.1
                                        have p1352_1 := h1352c.2.1
                                        have p1352_2 := h1352c.2.2.1
                                        have p1352_3 := h1352c.2.2.2
                                        linarith only [h1308, hlam, p1352_0]
                                      · have p1352_0 := h1352c.1
                                        have p1352_1 := h1352c.2.1
                                        have p1352_2 := h1352c.2.2.1
                                        have p1352_3 := h1352c.2.2.2
                                        linarith only [h1312, hlam, p1352_0]
                                      · have p1352_0 := h1352c.1
                                        have p1352_1 := h1352c.2.1
                                        have p1352_2 := h1352c.2.2.1
                                        have p1352_3 := h1352c.2.2.2
                                        linarith only [h1333, hlam, p1352_0]
                                      · have p1352_0 := h1352c.1
                                        have p1352_1 := h1352c.2.1
                                        have p1352_2 := h1352c.2.2.1
                                        have p1352_3 := h1352c.2.2.2
                                        linarith only [hlam, p1352_0]
                                      · have p1352_0 := h1352c.1
                                        have p1352_1 := h1352c.2.1
                                        have p1352_2 := h1352c.2.2.1
                                        have p1352_3 := h1352c.2.2.2
                                        linarith only [h1335, hlam, p1352_0]
                                      · have p1352_0 := h1352c.1
                                        have p1352_1 := h1352c.2.1
                                        have p1352_2 := h1352c.2.2.1
                                        have p1352_3 := h1352c.2.2.2
                                        linarith only [h1309, hlam, p1352_0]
                                      · have p1352_0 := h1352c.1
                                        have p1352_1 := h1352c.2.1
                                        have p1352_2 := h1352c.2.2.1
                                        have p1352_3 := h1352c.2.2.2
                                        linarith only [h0, h1339, h1346, hc34, hlam, hphi, ht0b, ht45, ht5b, p1352_1, u0elo4]
                                      · have p1352_0 := h1352c.1
                                        have p1352_1 := h1352c.2.1
                                        have p1352_2 := h1352c.2.2.1
                                        have p1352_3 := h1352c.2.2.2
                                        linarith only [h1334, hlam, p1352_0]
                                      · have p1352_0 := h1352c.1
                                        have p1352_1 := h1352c.2.1
                                        have p1352_2 := h1352c.2.2.1
                                        have p1352_3 := h1352c.2.2.2
                                        rcases p1352_3 (m.d 0 1) (by simp) with h1382 | h1382
                                        · rcases p1352_3 (m.d 0 2) (by simp) with h1383 | h1383
                                          · linarith only [h1313, h1383, hlam]
                                          · linarith only [h1312, h1383, hlam]
                                        · linarith only [h1308, h1382, hlam]
                                      · have p1352_0 := h1352c.1
                                        have p1352_1 := h1352c.2.1
                                        have p1352_2 := h1352c.2.2.1
                                        have p1352_3 := h1352c.2.2.2
                                        linarith only [hlam, p1352_0]
                                · linarith only [h0, h1, h1337, h1339, h1346, h1347, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · linarith only [h1, h1309, h1337, h1346, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                          · linarith only [h1, h1309, h1340, h1343, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h1309, h1339, h1340, h1342, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h1, h1312, h1337, h1339, hc12, hc23, hlam, hphi]
              · linarith only [h1, h1309, h1334, hlam]
            · linarith only [h1, h1308, h1333, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1395 | h1395
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1396 | h1396
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1397 | h1397
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1398 | h1398
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1399 | h1399
                  · linarith only [h1310, h1395, h1399, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1401 | h1401
                    · linarith only [h0, h1312, h1395, h1401, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1403 | h1403
                      · linarith only [h1, h1308, h1399, h1401, h1403, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h1312, h1395, h1403, hc12, hc24, hlam, hphi]
                · linarith only [h1312, h1395, h1398, hlam]
              · linarith only [h1, h1308, h1312, h1395, h1397, hlam]
            · linarith only [h1, h1308, h1396, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1409 | h1409
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1410 | h1410
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1411 | h1411
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1412 | h1412
                  · linarith only [h0, h1310, h1412, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1414 | h1414
                    · linarith only [h0, h1312, h1414, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1416 | h1416
                      · linarith only [h0, h1395, h1416, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1418 | h1418
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1419 | h1419
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1420 | h1420
                            · linarith only [h1, h1308, h1412, h1420, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                            · linarith only [h1, h1308, h1411, h1412, h1414, h1420, hc12, hc23, hlam, hphi]
                          · linarith only [h1, h1308, h1411, h1419, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                        · linarith only [h1, h1308, h1411, h1418, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1425 | h1425
                  · linarith only [h0, h1310, h1425, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1427 | h1427
                    · linarith only [h0, h1312, h1427, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1429 | h1429
                      · linarith only [h0, h1395, h1429, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1431 | h1431
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1432 | h1432
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1433 | h1433
                            · linarith only [h1308, h1411, h1433, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1435 | h1435
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1436 | h1436
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1437 | h1437
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1438 | h1438
                                    · linarith only [h1308, h1411, h1431, h1438, hlam]
                                    · rcases h0bigk with h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c | h1440c
                                      · have p1440_0 := h1440c.1
                                        have p1440_1 := h1440c.2.1
                                        have p1440_2 := h1440c.2.2.1
                                        have p1440_3 := h1440c.2.2.2
                                        linarith only [hlam, p1440_0]
                                      · have p1440_0 := h1440c.1
                                        have p1440_1 := h1440c.2.1
                                        have p1440_2 := h1440c.2.2.1
                                        have p1440_3 := h1440c.2.2.2
                                        linarith only [h1, h1425, hc02, hc23, hlam, hphi, p1440_1]
                                      · have p1440_0 := h1440c.1
                                        have p1440_1 := h1440c.2.1
                                        have p1440_2 := h1440c.2.2.1
                                        have p1440_3 := h1440c.2.2.2
                                        linarith only [h1, hlam, p1440_0]
                                      · have p1440_0 := h1440c.1
                                        have p1440_1 := h1440c.2.1
                                        have p1440_2 := h1440c.2.2.1
                                        have p1440_3 := h1440c.2.2.2
                                        linarith only [h0, h1, h1312, h1425, hc12, hc23, hlam, hphi, p1440_1]
                                      · have p1440_0 := h1440c.1
                                        have p1440_1 := h1440c.2.1
                                        have p1440_2 := h1440c.2.2.1
                                        have p1440_3 := h1440c.2.2.2
                                        linarith only [h1, h1425, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1440_1, u5ehi0]
                                      · have p1440_0 := h1440c.1
                                        have p1440_1 := h1440c.2.1
                                        have p1440_2 := h1440c.2.2.1
                                        have p1440_3 := h1440c.2.2.2
                                        linarith only [h0, hlam, p1440_0]
                                      · have p1440_0 := h1440c.1
                                        have p1440_1 := h1440c.2.1
                                        have p1440_2 := h1440c.2.2.1
                                        have p1440_3 := h1440c.2.2.2
                                        linarith only [hlam, p1440_0]
                                      · have p1440_0 := h1440c.1
                                        have p1440_1 := h1440c.2.1
                                        have p1440_2 := h1440c.2.2.1
                                        have p1440_3 := h1440c.2.2.2
                                        linarith only [h1310, hlam, p1440_0]
                                      · have p1440_0 := h1440c.1
                                        have p1440_1 := h1440c.2.1
                                        have p1440_2 := h1440c.2.2.1
                                        have p1440_3 := h1440c.2.2.2
                                        linarith only [h1312, hlam, p1440_1]
                                      · have p1440_0 := h1440c.1
                                        have p1440_1 := h1440c.2.1
                                        have p1440_2 := h1440c.2.2.1
                                        have p1440_3 := h1440c.2.2.2
                                        linarith only [h1395, hlam, p1440_0]
                                      · have p1440_0 := h1440c.1
                                        have p1440_1 := h1440c.2.1
                                        have p1440_2 := h1440c.2.2.1
                                        have p1440_3 := h1440c.2.2.2
                                        linarith only [h1309, hlam, hphi, ht0b, ht5b, p1440_1, u0elo2, u5ehi1]
                                      · have p1440_0 := h1440c.1
                                        have p1440_1 := h1440c.2.1
                                        have p1440_2 := h1440c.2.2.1
                                        have p1440_3 := h1440c.2.2.2
                                        rcases p1440_3 (m.d 0 1) (by simp) with h1452 | h1452
                                        · linarith only [h1, h1452, hlam]
                                        · linarith only [h0, h1452, hlam]
                                      · have p1440_0 := h1440c.1
                                        have p1440_1 := h1440c.2.1
                                        have p1440_2 := h1440c.2.2.1
                                        have p1440_3 := h1440c.2.2.2
                                        linarith only [hlam, p1440_0]
                                      · have p1440_0 := h1440c.1
                                        have p1440_1 := h1440c.2.1
                                        have p1440_2 := h1440c.2.2.1
                                        have p1440_3 := h1440c.2.2.2
                                        rcases p1440_3 (m.d 0 1) (by simp) with h1456 | h1456
                                        · linarith only [h1, h1456, hlam]
                                        · linarith only [h1308, h1456, hlam]
                                      · have p1440_0 := h1440c.1
                                        have p1440_1 := h1440c.2.1
                                        have p1440_2 := h1440c.2.2.1
                                        have p1440_3 := h1440c.2.2.2
                                        linarith only [h1309, h1432, hlam, hphi, ht0b, ht5b, p1440_1, u0elo2, u5ehi3]
                                      · have p1440_0 := h1440c.1
                                        have p1440_1 := h1440c.2.1
                                        have p1440_2 := h1440c.2.2.1
                                        have p1440_3 := h1440c.2.2.2
                                        linarith only [h1308, hlam, p1440_0]
                                      · have p1440_0 := h1440c.1
                                        have p1440_1 := h1440c.2.1
                                        have p1440_2 := h1440c.2.2.1
                                        have p1440_3 := h1440c.2.2.2
                                        linarith only [h0, h1411, h1437, hc12, hc24, hlam, hphi, p1440_1]
                                      · have p1440_0 := h1440c.1
                                        have p1440_1 := h1440c.2.1
                                        have p1440_2 := h1440c.2.2.1
                                        have p1440_3 := h1440c.2.2.2
                                        linarith only [h1409, hlam, p1440_0]
                                      · have p1440_0 := h1440c.1
                                        have p1440_1 := h1440c.2.1
                                        have p1440_2 := h1440c.2.2.1
                                        have p1440_3 := h1440c.2.2.2
                                        linarith only [hlam, p1440_0]
                                      · have p1440_0 := h1440c.1
                                        have p1440_1 := h1440c.2.1
                                        have p1440_2 := h1440c.2.2.1
                                        have p1440_3 := h1440c.2.2.2
                                        linarith only [h1411, hlam, p1440_0]
                                      · have p1440_0 := h1440c.1
                                        have p1440_1 := h1440c.2.1
                                        have p1440_2 := h1440c.2.2.1
                                        have p1440_3 := h1440c.2.2.2
                                        linarith only [h1309, hlam, p1440_0]
                                      · have p1440_0 := h1440c.1
                                        have p1440_1 := h1440c.2.1
                                        have p1440_2 := h1440c.2.2.1
                                        have p1440_3 := h1440c.2.2.2
                                        linarith only [h0, h1, h1309, h1425, hc12, hc23, hlam, hphi, p1440_1]
                                      · have p1440_0 := h1440c.1
                                        have p1440_1 := h1440c.2.1
                                        have p1440_2 := h1440c.2.2.1
                                        have p1440_3 := h1440c.2.2.2
                                        linarith only [h1410, hlam, p1440_0]
                                      · have p1440_0 := h1440c.1
                                        have p1440_1 := h1440c.2.1
                                        have p1440_2 := h1440c.2.2.1
                                        have p1440_3 := h1440c.2.2.2
                                        linarith only [h1, h1308, h1309, h1425, h1427, hc12, hc23, hlam, hphi, p1440_1]
                                      · have p1440_0 := h1440c.1
                                        have p1440_1 := h1440c.2.1
                                        have p1440_2 := h1440c.2.2.1
                                        have p1440_3 := h1440c.2.2.2
                                        linarith only [hlam, p1440_0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1470 | h1470
                                    · linarith only [h1, h1308, h1425, h1431, h1437, h1470, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · rcases h0bigk with h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c
                                      · have p1472_0 := h1472c.1
                                        have p1472_1 := h1472c.2.1
                                        have p1472_2 := h1472c.2.2.1
                                        have p1472_3 := h1472c.2.2.2
                                        linarith only [hlam, p1472_0]
                                      · have p1472_0 := h1472c.1
                                        have p1472_1 := h1472c.2.1
                                        have p1472_2 := h1472c.2.2.1
                                        have p1472_3 := h1472c.2.2.2
                                        linarith only [h0, h1, h1425, hc12, hc23, hlam, hphi, p1472_1]
                                      · have p1472_0 := h1472c.1
                                        have p1472_1 := h1472c.2.1
                                        have p1472_2 := h1472c.2.2.1
                                        have p1472_3 := h1472c.2.2.2
                                        linarith only [h1, hlam, p1472_0]
                                      · have p1472_0 := h1472c.1
                                        have p1472_1 := h1472c.2.1
                                        have p1472_2 := h1472c.2.2.1
                                        have p1472_3 := h1472c.2.2.2
                                        linarith only [h0, h1, h1312, h1425, hc12, hc23, hlam, hphi, p1472_1]
                                      · have p1472_0 := h1472c.1
                                        have p1472_1 := h1472c.2.1
                                        have p1472_2 := h1472c.2.2.1
                                        have p1472_3 := h1472c.2.2.2
                                        linarith only [h1, h1425, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1472_1, u5ehi0]
                                      · have p1472_0 := h1472c.1
                                        have p1472_1 := h1472c.2.1
                                        have p1472_2 := h1472c.2.2.1
                                        have p1472_3 := h1472c.2.2.2
                                        linarith only [h0, hlam, p1472_0]
                                      · have p1472_0 := h1472c.1
                                        have p1472_1 := h1472c.2.1
                                        have p1472_2 := h1472c.2.2.1
                                        have p1472_3 := h1472c.2.2.2
                                        linarith only [hlam, p1472_0]
                                      · have p1472_0 := h1472c.1
                                        have p1472_1 := h1472c.2.1
                                        have p1472_2 := h1472c.2.2.1
                                        have p1472_3 := h1472c.2.2.2
                                        linarith only [h1310, hlam, p1472_0]
                                      · have p1472_0 := h1472c.1
                                        have p1472_1 := h1472c.2.1
                                        have p1472_2 := h1472c.2.2.1
                                        have p1472_3 := h1472c.2.2.2
                                        linarith only [h1312, hlam, p1472_1]
                                      · have p1472_0 := h1472c.1
                                        have p1472_1 := h1472c.2.1
                                        have p1472_2 := h1472c.2.2.1
                                        have p1472_3 := h1472c.2.2.2
                                        linarith only [h1395, hlam, p1472_0]
                                      · have p1472_0 := h1472c.1
                                        have p1472_1 := h1472c.2.1
                                        have p1472_2 := h1472c.2.2.1
                                        have p1472_3 := h1472c.2.2.2
                                        linarith only [h1309, hlam, hphi, ht0b, ht5b, p1472_1, u0elo2, u5ehi1]
                                      · have p1472_0 := h1472c.1
                                        have p1472_1 := h1472c.2.1
                                        have p1472_2 := h1472c.2.2.1
                                        have p1472_3 := h1472c.2.2.2
                                        rcases p1472_3 (m.d 0 1) (by simp) with h1484 | h1484
                                        · linarith only [h1, h1484, hlam]
                                        · linarith only [h0, h1484, hlam]
                                      · have p1472_0 := h1472c.1
                                        have p1472_1 := h1472c.2.1
                                        have p1472_2 := h1472c.2.2.1
                                        have p1472_3 := h1472c.2.2.2
                                        linarith only [hlam, p1472_0]
                                      · have p1472_0 := h1472c.1
                                        have p1472_1 := h1472c.2.1
                                        have p1472_2 := h1472c.2.2.1
                                        have p1472_3 := h1472c.2.2.2
                                        rcases p1472_3 (m.d 0 1) (by simp) with h1488 | h1488
                                        · linarith only [h1, h1488, hlam]
                                        · linarith only [h1308, h1488, hlam]
                                      · have p1472_0 := h1472c.1
                                        have p1472_1 := h1472c.2.1
                                        have p1472_2 := h1472c.2.2.1
                                        have p1472_3 := h1472c.2.2.2
                                        linarith only [h1309, h1432, hlam, hphi, ht0b, ht5b, p1472_1, u0elo2, u5ehi3]
                                      · have p1472_0 := h1472c.1
                                        have p1472_1 := h1472c.2.1
                                        have p1472_2 := h1472c.2.2.1
                                        have p1472_3 := h1472c.2.2.2
                                        linarith only [h1308, hlam, p1472_0]
                                      · have p1472_0 := h1472c.1
                                        have p1472_1 := h1472c.2.1
                                        have p1472_2 := h1472c.2.2.1
                                        have p1472_3 := h1472c.2.2.2
                                        linarith only [h0, h1, h1308, h1425, hc12, hc23, hlam, hphi, p1472_1]
                                      · have p1472_0 := h1472c.1
                                        have p1472_1 := h1472c.2.1
                                        have p1472_2 := h1472c.2.2.1
                                        have p1472_3 := h1472c.2.2.2
                                        linarith only [h1409, hlam, p1472_0]
                                      · have p1472_0 := h1472c.1
                                        have p1472_1 := h1472c.2.1
                                        have p1472_2 := h1472c.2.2.1
                                        have p1472_3 := h1472c.2.2.2
                                        linarith only [hlam, p1472_0]
                                      · have p1472_0 := h1472c.1
                                        have p1472_1 := h1472c.2.1
                                        have p1472_2 := h1472c.2.2.1
                                        have p1472_3 := h1472c.2.2.2
                                        linarith only [h1411, hlam, p1472_0]
                                      · have p1472_0 := h1472c.1
                                        have p1472_1 := h1472c.2.1
                                        have p1472_2 := h1472c.2.2.1
                                        have p1472_3 := h1472c.2.2.2
                                        linarith only [h1309, hlam, p1472_0]
                                      · have p1472_0 := h1472c.1
                                        have p1472_1 := h1472c.2.1
                                        have p1472_2 := h1472c.2.2.1
                                        have p1472_3 := h1472c.2.2.2
                                        linarith only [h0, h1, h1309, h1425, hc12, hc23, hlam, hphi, p1472_1]
                                      · have p1472_0 := h1472c.1
                                        have p1472_1 := h1472c.2.1
                                        have p1472_2 := h1472c.2.2.1
                                        have p1472_3 := h1472c.2.2.2
                                        linarith only [h1410, hlam, p1472_0]
                                      · have p1472_0 := h1472c.1
                                        have p1472_1 := h1472c.2.1
                                        have p1472_2 := h1472c.2.2.1
                                        have p1472_3 := h1472c.2.2.2
                                        linarith only [h1, h1308, h1309, h1425, h1427, hc12, hc23, hlam, hphi, p1472_1]
                                      · have p1472_0 := h1472c.1
                                        have p1472_1 := h1472c.2.1
                                        have p1472_2 := h1472c.2.2.1
                                        have p1472_3 := h1472c.2.2.2
                                        linarith only [hlam, p1472_0]
                                · linarith only [h0, h1, h1425, h1436, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h1, h1309, h1425, h1432, h1435, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                          · linarith only [h1, h1309, h1432, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                        · linarith only [h1, h1309, h1431, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
              · linarith only [h1, h1309, h1410, hlam]
            · linarith only [h1, h1308, h1409, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1508 | h1508
      · linarith only [h0, h1, h1508, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1510 | h1510
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1511 | h1511
          · linarith only [h0, h1309, h1511, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1513 | h1513
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1514 | h1514
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1515 | h1515
                · linarith only [h0, h1309, h1510, h1515, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1517 | h1517
                  · linarith only [h0, h1508, h1517, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1519 | h1519
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1520 | h1520
                      · linarith only [h0, h1, h1511, h1517, h1520, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1522 | h1522
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1523 | h1523
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1524 | h1524
                            · linarith only [h0, h1309, h1515, h1519, h1524, hlam]
                            · linarith only [h0, h1309, h1519, h1524, hc24, hc45, hlam, hphi]
                          · linarith only [h0, h1, h1514, h1519, h1523, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h0, h1, h1519, h1522, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h1508, h1510, h1519, hc12, hc23, hlam, hphi]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1530 | h1530
                · linarith only [h0, h1, h1510, h1514, h1530, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1532 | h1532
                  · linarith only [h0, h1, h1514, h1532, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1534 | h1534
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1535 | h1535
                      · linarith only [h0, h1, h1514, h1535, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1537 | h1537
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1538 | h1538
                          · linarith only [h0, h1, h1514, h1532, h1538, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h1534, h1538, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h1, h1534, h1537, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h1508, h1510, h1534, hc12, hc23, hlam, hphi]
            · linarith only [h1, h1308, h1513, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1544 | h1544
          · linarith only [h1308, h1309, h1510, h1544, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1546 | h1546
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1547 | h1547
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1548 | h1548
                · linarith only [h1308, h1309, h1548, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1550 | h1550
                  · linarith only [h0, h1508, h1550, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1552 | h1552
                    · linarith only [h0, h1510, h1552, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1554 | h1554
                      · linarith only [h0, h1, h1544, h1550, h1554, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1556 | h1556
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1557 | h1557
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1558 | h1558
                            · linarith only [h1308, h1309, h1550, h1557, h1558, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1560 | h1560
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1561 | h1561
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1562 | h1562
                                  · linarith only [h1308, h1309, h1552, h1558, h1562, hc12, hc24, hlam, hphi]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1564 | h1564
                                    · linarith only [h0, h1510, h1562, h1564, hc12, hc34, hlam, hphi, ht23]
                                    · rcases h0bigk with h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c
                                      · have p1566_0 := h1566c.1
                                        have p1566_1 := h1566c.2.1
                                        have p1566_2 := h1566c.2.2.1
                                        have p1566_3 := h1566c.2.2.2
                                        linarith only [hlam, p1566_0]
                                      · have p1566_0 := h1566c.1
                                        have p1566_1 := h1566c.2.1
                                        have p1566_2 := h1566c.2.2.1
                                        have p1566_3 := h1566c.2.2.2
                                        linarith only [h0, h1309, h1554, hc12, hc25, hlam, hphi, p1566_1]
                                      · have p1566_0 := h1566c.1
                                        have p1566_1 := h1566c.2.1
                                        have p1566_2 := h1566c.2.2.1
                                        have p1566_3 := h1566c.2.2.2
                                        linarith only [h1, hlam, p1566_0]
                                      · have p1566_0 := h1566c.1
                                        have p1566_1 := h1566c.2.1
                                        have p1566_2 := h1566c.2.2.1
                                        have p1566_3 := h1566c.2.2.2
                                        linarith only [h0, h1309, h1510, h1554, h1562, hc12, hc45, hlam, hphi, ht23, ht34, p1566_1]
                                      · have p1566_0 := h1566c.1
                                        have p1566_1 := h1566c.2.1
                                        have p1566_2 := h1566c.2.2.1
                                        have p1566_3 := h1566c.2.2.2
                                        linarith only [h1309, hlam, p1566_1]
                                      · have p1566_0 := h1566c.1
                                        have p1566_1 := h1566c.2.1
                                        have p1566_2 := h1566c.2.2.1
                                        have p1566_3 := h1566c.2.2.2
                                        linarith only [h0, hlam, p1566_0]
                                      · have p1566_0 := h1566c.1
                                        have p1566_1 := h1566c.2.1
                                        have p1566_2 := h1566c.2.2.1
                                        have p1566_3 := h1566c.2.2.2
                                        linarith only [hlam, p1566_0]
                                      · have p1566_0 := h1566c.1
                                        have p1566_1 := h1566c.2.1
                                        have p1566_2 := h1566c.2.2.1
                                        have p1566_3 := h1566c.2.2.2
                                        linarith only [h1508, hlam, p1566_0]
                                      · have p1566_0 := h1566c.1
                                        have p1566_1 := h1566c.2.1
                                        have p1566_2 := h1566c.2.2.1
                                        have p1566_3 := h1566c.2.2.2
                                        linarith only [h1510, hlam, p1566_1]
                                      · have p1566_0 := h1566c.1
                                        have p1566_1 := h1566c.2.1
                                        have p1566_2 := h1566c.2.2.1
                                        have p1566_3 := h1566c.2.2.2
                                        linarith only [h1544, hlam, p1566_0]
                                      · have p1566_0 := h1566c.1
                                        have p1566_1 := h1566c.2.1
                                        have p1566_2 := h1566c.2.2.1
                                        have p1566_3 := h1566c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1566_1, u0elo2]
                                      · have p1566_0 := h1566c.1
                                        have p1566_1 := h1566c.2.1
                                        have p1566_2 := h1566c.2.2.1
                                        have p1566_3 := h1566c.2.2.2
                                        rcases p1566_3 (m.d 0 1) (by simp) with h1578 | h1578
                                        · linarith only [h1, h1578, hlam]
                                        · linarith only [h0, h1578, hlam]
                                      · have p1566_0 := h1566c.1
                                        have p1566_1 := h1566c.2.1
                                        have p1566_2 := h1566c.2.2.1
                                        have p1566_3 := h1566c.2.2.2
                                        linarith only [hlam, p1566_0]
                                      · have p1566_0 := h1566c.1
                                        have p1566_1 := h1566c.2.1
                                        have p1566_2 := h1566c.2.2.1
                                        have p1566_3 := h1566c.2.2.2
                                        rcases p1566_3 (m.d 0 1) (by simp) with h1582 | h1582
                                        · linarith only [h1, h1582, hlam]
                                        · linarith only [h1308, h1582, hlam]
                                      · have p1566_0 := h1566c.1
                                        have p1566_1 := h1566c.2.1
                                        have p1566_2 := h1566c.2.2.1
                                        have p1566_3 := h1566c.2.2.2
                                        linarith only [hlam, hphi, ht0b, ht5b, p1566_1, u0elo2, u5ehi0]
                                      · have p1566_0 := h1566c.1
                                        have p1566_1 := h1566c.2.1
                                        have p1566_2 := h1566c.2.2.1
                                        have p1566_3 := h1566c.2.2.2
                                        linarith only [h1308, hlam, p1566_0]
                                      · have p1566_0 := h1566c.1
                                        have p1566_1 := h1566c.2.1
                                        have p1566_2 := h1566c.2.2.1
                                        have p1566_3 := h1566c.2.2.2
                                        linarith only [h0, h1308, h1309, h1554, h1562, hc12, hc45, hlam, hphi, ht23, ht34, p1566_1]
                                      · have p1566_0 := h1566c.1
                                        have p1566_1 := h1566c.2.1
                                        have p1566_2 := h1566c.2.2.1
                                        have p1566_3 := h1566c.2.2.2
                                        linarith only [h1546, hlam, p1566_0]
                                      · have p1566_0 := h1566c.1
                                        have p1566_1 := h1566c.2.1
                                        have p1566_2 := h1566c.2.2.1
                                        have p1566_3 := h1566c.2.2.2
                                        linarith only [hlam, p1566_0]
                                      · have p1566_0 := h1566c.1
                                        have p1566_1 := h1566c.2.1
                                        have p1566_2 := h1566c.2.2.1
                                        have p1566_3 := h1566c.2.2.2
                                        linarith only [h1548, hlam, p1566_0]
                                      · have p1566_0 := h1566c.1
                                        have p1566_1 := h1566c.2.1
                                        have p1566_2 := h1566c.2.2.1
                                        have p1566_3 := h1566c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1566_1, u0elo4]
                                      · have p1566_0 := h1566c.1
                                        have p1566_1 := h1566c.2.1
                                        have p1566_2 := h1566c.2.2.1
                                        have p1566_3 := h1566c.2.2.2
                                        rcases p1566_3 (m.d 0 1) (by simp) with h1592 | h1592
                                        · linarith only [h1309, h1592, hlam]
                                        · linarith only [h0, h1592, hlam]
                                      · have p1566_0 := h1566c.1
                                        have p1566_1 := h1566c.2.1
                                        have p1566_2 := h1566c.2.2.1
                                        have p1566_3 := h1566c.2.2.2
                                        linarith only [h1547, hlam, p1566_0]
                                      · have p1566_0 := h1566c.1
                                        have p1566_1 := h1566c.2.1
                                        have p1566_2 := h1566c.2.2.1
                                        have p1566_3 := h1566c.2.2.2
                                        rcases p1566_3 (m.d 0 1) (by simp) with h1596 | h1596
                                        · linarith only [h1309, h1596, hlam]
                                        · linarith only [h1308, h1596, hlam]
                                      · have p1566_0 := h1566c.1
                                        have p1566_1 := h1566c.2.1
                                        have p1566_2 := h1566c.2.2.1
                                        have p1566_3 := h1566c.2.2.2
                                        linarith only [hlam, p1566_0]
                                · linarith only [h1508, h1547, h1561, hlam]
                              · linarith only [h1308, h1550, h1556, h1557, h1560, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi1]
                          · linarith only [h1, h1547, h1557, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h1, h1308, h1552, h1556, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1604 | h1604
                · linarith only [h1308, h1309, h1604, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1606 | h1606
                  · linarith only [h0, h1, h1508, h1606, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1608 | h1608
                    · linarith only [h0, h1510, h1608, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1610 | h1610
                      · linarith only [h0, h1, h1547, h1610, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1612 | h1612
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1613 | h1613
                          · linarith only [h1, h1308, h1547, h1606, h1608, h1613, hc12, hc23, hlam, hphi]
                          · linarith only [h1, h1308, h1608, h1613, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h1308, h1608, h1612, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h1, h1308, h1546, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1618 | h1618
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1619 | h1619
      · linarith only [h0, h1, h1619, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1621 | h1621
        · linarith only [h0, h1308, h1621, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1623 | h1623
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1624 | h1624
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1625 | h1625
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1626 | h1626
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1627 | h1627
                  · linarith only [h1619, h1623, h1627, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1629 | h1629
                    · linarith only [h0, h1621, h1623, h1629, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1631 | h1631
                      · linarith only [h0, h1, h1627, h1631, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h0, h1, h1623, h1627, h1631, hc12, hc23, hlam, hphi]
                · linarith only [h1308, h1618, h1626, hlam]
              · linarith only [h0, h1, h1623, h1625, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1636 | h1636
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1637 | h1637
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1638 | h1638
                  · linarith only [h0, h1, h1624, h1638, hc23, hc34, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1640 | h1640
                    · linarith only [h0, h1, h1621, h1624, h1640, hc02, hc34, hlam, hphi, ht23]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1642 | h1642
                      · linarith only [h0, h1, h1624, h1642, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · linarith only [h0, h1, h1623, h1624, h1642, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h1, h1618, h1624, h1637, hlam]
              · linarith only [h0, h1, h1623, h1636, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1647 | h1647
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1648 | h1648
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1649 | h1649
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1650 | h1650
                  · linarith only [h0, h1619, h1650, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1652 | h1652
                    · linarith only [h0, h1621, h1649, h1652, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1654 | h1654
                      · linarith only [h0, h1623, h1654, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1656 | h1656
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1657 | h1657
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1658 | h1658
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1659 | h1659
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1660 | h1660
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1661 | h1661
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1662 | h1662
                                    · linarith only [h1647, h1662, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                                    · rcases h0bigk with h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c | h1664c
                                      · have p1664_0 := h1664c.1
                                        have p1664_1 := h1664c.2.1
                                        have p1664_2 := h1664c.2.2.1
                                        have p1664_3 := h1664c.2.2.2
                                        linarith only [hlam, p1664_0]
                                      · have p1664_0 := h1664c.1
                                        have p1664_1 := h1664c.2.1
                                        have p1664_2 := h1664c.2.2.1
                                        have p1664_3 := h1664c.2.2.2
                                        linarith only [h0, h1308, h1650, h1656, hc12, hc23, hlam, hphi, p1664_1]
                                      · have p1664_0 := h1664c.1
                                        have p1664_1 := h1664c.2.1
                                        have p1664_2 := h1664c.2.2.1
                                        have p1664_3 := h1664c.2.2.2
                                        linarith only [h1, hlam, p1664_0]
                                      · have p1664_0 := h1664c.1
                                        have p1664_1 := h1664c.2.1
                                        have p1664_2 := h1664c.2.2.1
                                        have p1664_3 := h1664c.2.2.2
                                        linarith only [h1308, hlam, p1664_1]
                                      · have p1664_0 := h1664c.1
                                        have p1664_1 := h1664c.2.1
                                        have p1664_2 := h1664c.2.2.1
                                        have p1664_3 := h1664c.2.2.2
                                        linarith only [h1308, h1650, h1656, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1664_1, u5ehi0]
                                      · have p1664_0 := h1664c.1
                                        have p1664_1 := h1664c.2.1
                                        have p1664_2 := h1664c.2.2.1
                                        have p1664_3 := h1664c.2.2.2
                                        linarith only [h0, hlam, p1664_0]
                                      · have p1664_0 := h1664c.1
                                        have p1664_1 := h1664c.2.1
                                        have p1664_2 := h1664c.2.2.1
                                        have p1664_3 := h1664c.2.2.2
                                        linarith only [hlam, p1664_0]
                                      · have p1664_0 := h1664c.1
                                        have p1664_1 := h1664c.2.1
                                        have p1664_2 := h1664c.2.2.1
                                        have p1664_3 := h1664c.2.2.2
                                        linarith only [h1619, hlam, p1664_0]
                                      · have p1664_0 := h1664c.1
                                        have p1664_1 := h1664c.2.1
                                        have p1664_2 := h1664c.2.2.1
                                        have p1664_3 := h1664c.2.2.2
                                        linarith only [h1621, hlam, p1664_1]
                                      · have p1664_0 := h1664c.1
                                        have p1664_1 := h1664c.2.1
                                        have p1664_2 := h1664c.2.2.1
                                        have p1664_3 := h1664c.2.2.2
                                        linarith only [h1623, hlam, p1664_0]
                                      · have p1664_0 := h1664c.1
                                        have p1664_1 := h1664c.2.1
                                        have p1664_2 := h1664c.2.2.1
                                        have p1664_3 := h1664c.2.2.2
                                        linarith only [h1618, hlam, hphi, ht0b, ht5b, p1664_1, u0elo2, u5ehi1]
                                      · have p1664_0 := h1664c.1
                                        have p1664_1 := h1664c.2.1
                                        have p1664_2 := h1664c.2.2.1
                                        have p1664_3 := h1664c.2.2.2
                                        rcases p1664_3 (m.d 0 1) (by simp) with h1676 | h1676
                                        · linarith only [h1, h1676, hlam]
                                        · linarith only [h0, h1676, hlam]
                                      · have p1664_0 := h1664c.1
                                        have p1664_1 := h1664c.2.1
                                        have p1664_2 := h1664c.2.2.1
                                        have p1664_3 := h1664c.2.2.2
                                        linarith only [hlam, p1664_0]
                                      · have p1664_0 := h1664c.1
                                        have p1664_1 := h1664c.2.1
                                        have p1664_2 := h1664c.2.2.1
                                        have p1664_3 := h1664c.2.2.2
                                        linarith only [h1308, h1618, h1658, h1662, hc34, hlam, hphi, ht0b, ht45, ht5b, p1664_1, u0elo2]
                                      · have p1664_0 := h1664c.1
                                        have p1664_1 := h1664c.2.1
                                        have p1664_2 := h1664c.2.2.1
                                        have p1664_3 := h1664c.2.2.2
                                        linarith only [h1618, h1658, h1662, hc34, hlam, hphi, ht0b, ht45, ht5b, p1664_1, u0elo2]
                                      · have p1664_0 := h1664c.1
                                        have p1664_1 := h1664c.2.1
                                        have p1664_2 := h1664c.2.2.1
                                        have p1664_3 := h1664c.2.2.2
                                        linarith only [h1618, h1658, h1662, hc34, hlam, hphi, ht0b, ht45, ht5b, p1664_1, u0elo3]
                                      · have p1664_0 := h1664c.1
                                        have p1664_1 := h1664c.2.1
                                        have p1664_2 := h1664c.2.2.1
                                        have p1664_3 := h1664c.2.2.2
                                        rcases p1664_3 (m.d 0 1) (by simp) with h1683 | h1683
                                        · linarith only [h1308, h1683, hlam]
                                        · linarith only [h0, h1683, hlam]
                                      · have p1664_0 := h1664c.1
                                        have p1664_1 := h1664c.2.1
                                        have p1664_2 := h1664c.2.2.1
                                        have p1664_3 := h1664c.2.2.2
                                        linarith only [h1647, hlam, p1664_0]
                                      · have p1664_0 := h1664c.1
                                        have p1664_1 := h1664c.2.1
                                        have p1664_2 := h1664c.2.2.1
                                        have p1664_3 := h1664c.2.2.2
                                        linarith only [hlam, p1664_0]
                                      · have p1664_0 := h1664c.1
                                        have p1664_1 := h1664c.2.1
                                        have p1664_2 := h1664c.2.2.1
                                        have p1664_3 := h1664c.2.2.2
                                        linarith only [h1618, h1647, h1658, h1662, hc34, hlam, hphi, ht0b, ht45, ht5b, p1664_1, u0elo2]
                                      · have p1664_0 := h1664c.1
                                        have p1664_1 := h1664c.2.1
                                        have p1664_2 := h1664c.2.2.1
                                        have p1664_3 := h1664c.2.2.2
                                        linarith only [h1618, hlam, p1664_0]
                                      · have p1664_0 := h1664c.1
                                        have p1664_1 := h1664c.2.1
                                        have p1664_2 := h1664c.2.2.1
                                        have p1664_3 := h1664c.2.2.2
                                        linarith only [h0, h1, h1618, h1650, hc12, hc23, hlam, hphi, p1664_1]
                                      · have p1664_0 := h1664c.1
                                        have p1664_1 := h1664c.2.1
                                        have p1664_2 := h1664c.2.2.1
                                        have p1664_3 := h1664c.2.2.2
                                        linarith only [h1648, hlam, p1664_0]
                                      · have p1664_0 := h1664c.1
                                        have p1664_1 := h1664c.2.1
                                        have p1664_2 := h1664c.2.2.1
                                        have p1664_3 := h1664c.2.2.2
                                        linarith only [h1649, hlam, p1664_1]
                                      · have p1664_0 := h1664c.1
                                        have p1664_1 := h1664c.2.1
                                        have p1664_2 := h1664c.2.2.1
                                        have p1664_3 := h1664c.2.2.2
                                        linarith only [hlam, p1664_0]
                                  · linarith only [h0, h1308, h1652, h1661, hc12, hc45, hlam, hphi, ht23, ht34]
                                · linarith only [h1308, h1618, h1650, h1656, h1657, h1660, hlam]
                              · linarith only [h1308, h1618, h1650, h1656, h1657, h1659, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                            · linarith only [h1308, h1618, h1657, h1658, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                          · linarith only [h1308, h1618, h1656, h1657, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                        · linarith only [h1, h1618, h1647, h1656, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi1]
                · linarith only [h1308, h1618, h1649, hlam]
              · linarith only [h1, h1618, h1648, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1702 | h1702
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1703 | h1703
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1704 | h1704
                  · linarith only [h0, h1, h1618, h1619, h1704, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1706 | h1706
                    · linarith only [h0, h1621, h1706, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1708 | h1708
                      · linarith only [h0, h1, h1623, h1647, h1708, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1710 | h1710
                        · linarith only [h1, h1618, h1647, h1704, h1708, h1710, hc12, hc23, hlam, hphi]
                        · linarith only [h1, h1618, h1710, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                · linarith only [h1308, h1618, h1703, hlam]
              · linarith only [h1, h1618, h1702, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1715 | h1715
      · linarith only [h0, h1, h1715, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1717 | h1717
        · linarith only [h0, h1308, h1717, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1719 | h1719
          · linarith only [h0, h1618, h1719, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1721 | h1721
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1722 | h1722
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1723 | h1723
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1724 | h1724
                  · linarith only [h0, h1715, h1724, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1726 | h1726
                    · linarith only [h0, h1717, h1723, h1726, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1728 | h1728
                      · linarith only [h0, h1719, h1728, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1730 | h1730
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1731 | h1731
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1732 | h1732
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1733 | h1733
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1734 | h1734
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1735 | h1735
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1736 | h1736
                                    · linarith only [h1721, h1736, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi4]
                                    · rcases h0bigk with h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c
                                      · have p1738_0 := h1738c.1
                                        have p1738_1 := h1738c.2.1
                                        have p1738_2 := h1738c.2.2.1
                                        have p1738_3 := h1738c.2.2.2
                                        linarith only [hlam, p1738_0]
                                      · have p1738_0 := h1738c.1
                                        have p1738_1 := h1738c.2.1
                                        have p1738_2 := h1738c.2.2.1
                                        have p1738_3 := h1738c.2.2.2
                                        linarith only [h0, h1618, h1724, h1730, h1732, hc12, hc23, hlam, hphi, p1738_1]
                                      · have p1738_0 := h1738c.1
                                        have p1738_1 := h1738c.2.1
                                        have p1738_2 := h1738c.2.2.1
                                        have p1738_3 := h1738c.2.2.2
                                        linarith only [h1, hlam, p1738_0]
                                      · have p1738_0 := h1738c.1
                                        have p1738_1 := h1738c.2.1
                                        have p1738_2 := h1738c.2.2.1
                                        have p1738_3 := h1738c.2.2.2
                                        linarith only [h1308, hlam, p1738_1]
                                      · have p1738_0 := h1738c.1
                                        have p1738_1 := h1738c.2.1
                                        have p1738_2 := h1738c.2.2.1
                                        have p1738_3 := h1738c.2.2.2
                                        linarith only [h1618, hlam, p1738_1]
                                      · have p1738_0 := h1738c.1
                                        have p1738_1 := h1738c.2.1
                                        have p1738_2 := h1738c.2.2.1
                                        have p1738_3 := h1738c.2.2.2
                                        linarith only [h0, hlam, p1738_0]
                                      · have p1738_0 := h1738c.1
                                        have p1738_1 := h1738c.2.1
                                        have p1738_2 := h1738c.2.2.1
                                        have p1738_3 := h1738c.2.2.2
                                        linarith only [hlam, p1738_0]
                                      · have p1738_0 := h1738c.1
                                        have p1738_1 := h1738c.2.1
                                        have p1738_2 := h1738c.2.2.1
                                        have p1738_3 := h1738c.2.2.2
                                        linarith only [h1715, hlam, p1738_0]
                                      · have p1738_0 := h1738c.1
                                        have p1738_1 := h1738c.2.1
                                        have p1738_2 := h1738c.2.2.1
                                        have p1738_3 := h1738c.2.2.2
                                        linarith only [h1717, hlam, p1738_1]
                                      · have p1738_0 := h1738c.1
                                        have p1738_1 := h1738c.2.1
                                        have p1738_2 := h1738c.2.2.1
                                        have p1738_3 := h1738c.2.2.2
                                        linarith only [h1719, hlam, p1738_0]
                                      · have p1738_0 := h1738c.1
                                        have p1738_1 := h1738c.2.1
                                        have p1738_2 := h1738c.2.2.1
                                        have p1738_3 := h1738c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1738_1, u0elo2]
                                      · have p1738_0 := h1738c.1
                                        have p1738_1 := h1738c.2.1
                                        have p1738_2 := h1738c.2.2.1
                                        have p1738_3 := h1738c.2.2.2
                                        rcases p1738_3 (m.d 0 1) (by simp) with h1750 | h1750
                                        · linarith only [h1, h1750, hlam]
                                        · linarith only [h0, h1750, hlam]
                                      · have p1738_0 := h1738c.1
                                        have p1738_1 := h1738c.2.1
                                        have p1738_2 := h1738c.2.2.1
                                        have p1738_3 := h1738c.2.2.2
                                        linarith only [hlam, p1738_0]
                                      · have p1738_0 := h1738c.1
                                        have p1738_1 := h1738c.2.1
                                        have p1738_2 := h1738c.2.2.1
                                        have p1738_3 := h1738c.2.2.2
                                        linarith only [h1723, hlam, hphi, ht0b, ht5b, p1738_1, u0elo2, u5ehi0]
                                      · have p1738_0 := h1738c.1
                                        have p1738_1 := h1738c.2.1
                                        have p1738_2 := h1738c.2.2.1
                                        have p1738_3 := h1738c.2.2.2
                                        linarith only [h0, h1618, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1738_1, u0elo2]
                                      · have p1738_0 := h1738c.1
                                        have p1738_1 := h1738c.2.1
                                        have p1738_2 := h1738c.2.2.1
                                        have p1738_3 := h1738c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1738_1, u0elo3]
                                      · have p1738_0 := h1738c.1
                                        have p1738_1 := h1738c.2.1
                                        have p1738_2 := h1738c.2.2.1
                                        have p1738_3 := h1738c.2.2.2
                                        rcases p1738_3 (m.d 0 1) (by simp) with h1757 | h1757
                                        · linarith only [h1308, h1757, hlam]
                                        · linarith only [h0, h1757, hlam]
                                      · have p1738_0 := h1738c.1
                                        have p1738_1 := h1738c.2.1
                                        have p1738_2 := h1738c.2.2.1
                                        have p1738_3 := h1738c.2.2.2
                                        linarith only [h1721, hlam, p1738_0]
                                      · have p1738_0 := h1738c.1
                                        have p1738_1 := h1738c.2.1
                                        have p1738_2 := h1738c.2.2.1
                                        have p1738_3 := h1738c.2.2.2
                                        linarith only [hlam, p1738_0]
                                      · have p1738_0 := h1738c.1
                                        have p1738_1 := h1738c.2.1
                                        have p1738_2 := h1738c.2.2.1
                                        have p1738_3 := h1738c.2.2.2
                                        linarith only [h0, h1618, h1721, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1738_1, u0elo2]
                                      · have p1738_0 := h1738c.1
                                        have p1738_1 := h1738c.2.1
                                        have p1738_2 := h1738c.2.2.1
                                        have p1738_3 := h1738c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1738_1, u0elo4]
                                      · have p1738_0 := h1738c.1
                                        have p1738_1 := h1738c.2.1
                                        have p1738_2 := h1738c.2.2.1
                                        have p1738_3 := h1738c.2.2.2
                                        rcases p1738_3 (m.d 0 1) (by simp) with h1764 | h1764
                                        · linarith only [h1618, h1764, hlam]
                                        · linarith only [h0, h1764, hlam]
                                      · have p1738_0 := h1738c.1
                                        have p1738_1 := h1738c.2.1
                                        have p1738_2 := h1738c.2.2.1
                                        have p1738_3 := h1738c.2.2.2
                                        linarith only [h1722, hlam, p1738_0]
                                      · have p1738_0 := h1738c.1
                                        have p1738_1 := h1738c.2.1
                                        have p1738_2 := h1738c.2.2.1
                                        have p1738_3 := h1738c.2.2.2
                                        linarith only [h1723, hlam, p1738_1]
                                      · have p1738_0 := h1738c.1
                                        have p1738_1 := h1738c.2.1
                                        have p1738_2 := h1738c.2.2.1
                                        have p1738_3 := h1738c.2.2.2
                                        linarith only [hlam, p1738_0]
                                  · linarith only [h0, h1308, h1726, h1735, hc12, hc45, hlam, hphi, ht23, ht34]
                                · linarith only [h0, h1, h1724, h1734, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h0, h1618, h1724, h1730, h1732, h1733, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h0, h1308, h1721, h1723, h1732, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h0, h1, h1722, h1731, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h1, h1721, h1730, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1776 | h1776
                  · linarith only [h0, h1308, h1723, h1776, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1778 | h1778
                    · linarith only [h0, h1308, h1723, h1778, hc24, hc45, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1780 | h1780
                      · linarith only [h0, h1308, h1723, h1780, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1782 | h1782
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1783 | h1783
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1784 | h1784
                            · linarith only [h0, h1308, h1723, h1776, h1782, h1784, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h1308, h1784, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h0, h1, h1722, h1783, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h1, h1721, h1722, h1782, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1789 | h1789
                · linarith only [h1721, h1722, h1789, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1791 | h1791
                  · linarith only [h0, h1, h1722, h1791, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1793 | h1793
                    · linarith only [h0, h1308, h1717, h1793, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1795 | h1795
                      · linarith only [h0, h1308, h1721, h1722, h1795, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1797 | h1797
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1798 | h1798
                          · linarith only [h0, h1308, h1721, h1722, h1791, h1798, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h1798, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h1721, h1797, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1802 | h1802
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1803 | h1803
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1804 | h1804
                  · linarith only [h0, h1715, h1804, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1806 | h1806
                    · linarith only [h0, h1717, h1806, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1808 | h1808
                      · linarith only [h0, h1618, h1719, h1808, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1810 | h1810
                        · linarith only [h0, h1618, h1721, h1802, h1804, h1810, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h1810, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h1721, h1802, h1803, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1814 | h1814
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1815 | h1815
                  · linarith only [h0, h1, h1802, h1815, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1817 | h1817
                    · linarith only [h0, h1717, h1817, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1819 | h1819
                      · linarith only [h0, h1, h1802, h1819, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1821 | h1821
                        · linarith only [h0, h1, h1721, h1815, h1821, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h1821, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1824 | h1824
                  · linarith only [h0, h1, h1802, h1824, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1826 | h1826
                    · linarith only [h0, h1, h1721, h1814, h1826, hc24, hc45, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1828 | h1828
                      · linarith only [h0, h1, h1721, h1814, h1828, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1830 | h1830
                        · linarith only [h0, h1, h1721, h1824, h1830, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h1830, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 10642000 in
set_option maxHeartbeats 10642000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_R_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h5ehi := hb5.1
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
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_R_x0_x0 m hb0 hb2 hb3 hb5 h0 h1
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_R_x0_x1 m hb0 hb2 hb3 hb5 h0 h1

set_option maxHeartbeats 10642000 in
set_option maxHeartbeats 10642000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_R_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h5ehi := hb5.1
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
  exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_R_s0 m hb0 hb2 hb3 hb5 h0

set_option maxHeartbeats 10642000 in
set_option maxHeartbeats 10642000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h5ehi := hb5.1
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
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_R_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_R_x1 m hb0 hb2 hb3 hb5 h0

end R2N4
