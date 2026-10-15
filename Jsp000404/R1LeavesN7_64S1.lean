import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_64S0

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_11_13_14_M_IR_L_I_L_R_L_R_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h0ehi := hb0.2.1
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have h4ehi := hb4.1
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
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1072 | h1072
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1073 | h1073
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1074 | h1074
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1075 | h1075
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1076 | h1076
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1077 | h1077
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1078 | h1078
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1079 | h1079
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1080 | h1080
                  · linarith only [h0, h1072, h1080, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h1072, h1075, h1080, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h0, h1073, h1079, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
              · linarith only [h0, h1072, h1075, h1078, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
            · linarith only [h0, h1072, h1075, h1077, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1086 | h1086
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1087 | h1087
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1088 | h1088
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1089 | h1089
                  · linarith only [h0, h1072, h1089, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h1072, h1075, h1086, h1089, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h1072, h1075, h1088, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
              · linarith only [h0, h1072, h1075, h1087, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
            · linarith only [h0, h1072, h1075, h1086, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1095 | h1095
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1096 | h1096
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1097 | h1097
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1098 | h1098
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1099 | h1099
                  · linarith only [h1072, h1075, h1099, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1101 | h1101
                    · linarith only [h0, h1072, h1101, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1103 | h1103
                      · linarith only [h0, h1073, h1103, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h0, h1073, h1095, h1099, h1103, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h0, h1098, hc25, hlam, hphi, ht01, ht12, u0ehi0]
              · linarith only [h0, h1072, h1096, h1097, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h0, h1072, h1096, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1109 | h1109
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1110 | h1110
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1111 | h1111
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1112 | h1112
                  · linarith only [h1072, h1075, h1112, hc01, hlam, hphi, u0ehi2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1114 | h1114
                    · linarith only [h0, h1072, h1114, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1116 | h1116
                      · linarith only [h0, h1073, h1095, h1116, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1118 | h1118
                        · linarith only [h1075, h1118, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1120 | h1120
                          · linarith only [h0, h1074, h1075, h1095, h1110, h1116, h1120, hc12, hlam, hphi, ht01, u0ehi2]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1122 | h1122
                            · linarith only [h1075, h1095, h1122, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                            · linarith only [h0, h1074, h1075, h1109, h1112, h1116, h1122, hc12, hc45, hlam, hphi, ht01, ht34, u0ehi2, u3ehi2]
                · linarith only [h0, h1111, hc25, hlam, hphi, ht01, ht12, u0ehi0]
              · linarith only [h0, h1072, h1109, h1110, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h0, h1072, h1109, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1128 | h1128
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1129 | h1129
          · linarith only [h1073, h1074, h1129, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1131 | h1131
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1132 | h1132
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1133 | h1133
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1134 | h1134
                  · linarith only [h1072, h1074, h1133, h1134, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h1072, h1074, h1128, h1133, h1134, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h0, h1072, h1128, h1133, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
              · linarith only [h0, h1072, h1128, h1132, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
            · linarith only [h0, h1072, h1128, h1131, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1140 | h1140
          · linarith only [h1073, h1074, h1140, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1142 | h1142
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1143 | h1143
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1144 | h1144
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1145 | h1145
                  · linarith only [h1072, h1074, h1144, h1145, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1147 | h1147
                    · linarith only [h1072, h1074, h1144, h1147, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · linarith only [h1073, h1074, h1145, h1147, hc35, hlam, hphi, u3ehi1]
                · linarith only [h0, h1072, h1142, h1144, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h1072, h1142, h1143, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h0, h1072, h1142, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1153 | h1153
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1154 | h1154
        · linarith only [h1072, h1073, h1154, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1156 | h1156
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1157 | h1157
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1158 | h1158
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1159 | h1159
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1160 | h1160
                  · linarith only [h1072, h1154, h1160, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · linarith only [h1072, h1073, h1160, hc34, hlam, hphi, u3ehi1]
                · linarith only [h1072, h1073, h1157, h1158, h1159, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h1072, h1157, h1158, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h0, h1072, h1157, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · linarith only [h1072, h1073, h1156, hc45, hlam, hphi, ht34, u3ehi1]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1167 | h1167
        · linarith only [h1072, h1073, h1167, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1169 | h1169
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1170 | h1170
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1171 | h1171
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1172 | h1172
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1173 | h1173
                  · linarith only [h1072, h1167, h1173, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · linarith only [h1072, h1073, h1170, h1173, hc34, hlam, hphi, u3ehi2]
                · linarith only [h1072, h1073, h1170, h1171, h1172, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h1072, h1170, h1171, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h0, h1072, h1170, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · linarith only [h1072, h1073, h1169, hc45, hlam, hphi, ht34, u3ehi1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1180 | h1180
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1181 | h1181
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1182 | h1182
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1183 | h1183
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1184 | h1184
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1185 | h1185
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1186 | h1186
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1187 | h1187
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1188 | h1188
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1189 | h1189
                      · linarith only [h1072, h1180, h1184, h1189, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h1072, h1180, h1183, h1184, h1189, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                    · linarith only [h1072, h1188, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                  · linarith only [h1072, h1180, h1182, h1183, h1187, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                · linarith only [h1072, h1180, h1183, h1184, h1186, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · linarith only [h1072, h1180, h1183, h1184, h1185, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
            · linarith only [h0, h1180, h1183, h1184, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1197 | h1197
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1198 | h1198
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1199 | h1199
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1200 | h1200
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1201 | h1201
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1202 | h1202
                      · linarith only [h1072, h1180, h1183, h1197, h1202, hc12, hlam, hphi, ht01, u0ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1204 | h1204
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1205 | h1205
                          · linarith only [h1072, h1181, h1183, h1197, h1198, h1202, h1205, hc12, hlam, hphi, ht01, u0ehi3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1207 | h1207
                            · linarith only [h1072, h1181, h1183, h1197, h1198, h1202, h1204, h1207, hc12, hlam, hphi, ht01, u0ehi3]
                            · rcases h1bigk with h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c
                              · have p1209_0 := h1209c.1
                                have p1209_1 := h1209c.2.1
                                have p1209_2 := h1209c.2.2.1
                                have p1209_3 := h1209c.2.2.2
                                linarith only [hlam, p1209_0]
                              · have p1209_0 := h1209c.1
                                have p1209_1 := h1209c.2.1
                                have p1209_2 := h1209c.2.2.1
                                have p1209_3 := h1209c.2.2.2
                                linarith only [h0, hlam, p1209_0]
                              · have p1209_0 := h1209c.1
                                have p1209_1 := h1209c.2.1
                                have p1209_2 := h1209c.2.2.1
                                have p1209_3 := h1209c.2.2.2
                                linarith only [h1072, hlam, p1209_0]
                              · have p1209_0 := h1209c.1
                                have p1209_1 := h1209c.2.1
                                have p1209_2 := h1209c.2.2.1
                                have p1209_3 := h1209c.2.2.2
                                linarith only [h1072, h1197, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1209_1, u4ehi1]
                              · have p1209_0 := h1209c.1
                                have p1209_1 := h1209c.2.1
                                have p1209_2 := h1209c.2.2.1
                                have p1209_3 := h1209c.2.2.2
                                linarith only [h1072, h1197, h1201, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1209_1, u3ehi4]
                              · have p1209_0 := h1209c.1
                                have p1209_1 := h1209c.2.1
                                have p1209_2 := h1209c.2.2.1
                                have p1209_3 := h1209c.2.2.2
                                linarith only [hc12, hlam, hphi, ht01, p1209_1, u0ehi0]
                              · have p1209_0 := h1209c.1
                                have p1209_1 := h1209c.2.1
                                have p1209_2 := h1209c.2.2.1
                                have p1209_3 := h1209c.2.2.2
                                linarith only [hlam, p1209_0]
                              · have p1209_0 := h1209c.1
                                have p1209_1 := h1209c.2.1
                                have p1209_2 := h1209c.2.2.1
                                have p1209_3 := h1209c.2.2.2
                                linarith only [h1072, hc12, hlam, hphi, ht01, p1209_1, u0ehi2]
                              · have p1209_0 := h1209c.1
                                have p1209_1 := h1209c.2.1
                                have p1209_2 := h1209c.2.2.1
                                have p1209_3 := h1209c.2.2.2
                                rcases p1209_3 (m.d 0 1) (by simp) with h1218 | h1218
                                · linarith only [h0, h1218, hlam]
                                · linarith only [h1180, h1218, hlam]
                              · have p1209_0 := h1209c.1
                                have p1209_1 := h1209c.2.1
                                have p1209_2 := h1209c.2.2.1
                                have p1209_3 := h1209c.2.2.2
                                rcases p1209_3 (m.d 0 1) (by simp) with h1221 | h1221
                                · linarith only [h0, h1221, hlam]
                                · linarith only [h1181, h1221, hlam]
                              · have p1209_0 := h1209c.1
                                have p1209_1 := h1209c.2.1
                                have p1209_2 := h1209c.2.2.1
                                have p1209_3 := h1209c.2.2.2
                                linarith only [h1181, h1198, h1202, h1204, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1209_1, u3ehi3]
                              · have p1209_0 := h1209c.1
                                have p1209_1 := h1209c.2.1
                                have p1209_2 := h1209c.2.2.1
                                have p1209_3 := h1209c.2.2.2
                                linarith only [h1197, hlam, p1209_1]
                              · have p1209_0 := h1209c.1
                                have p1209_1 := h1209c.2.1
                                have p1209_2 := h1209c.2.2.1
                                have p1209_3 := h1209c.2.2.2
                                linarith only [hlam, p1209_0]
                              · have p1209_0 := h1209c.1
                                have p1209_1 := h1209c.2.1
                                have p1209_2 := h1209c.2.2.1
                                have p1209_3 := h1209c.2.2.2
                                rcases p1209_3 (m.d 0 1) (by simp) with h1227 | h1227
                                · linarith only [h1072, h1227, hlam]
                                · linarith only [h1180, h1227, hlam]
                              · have p1209_0 := h1209c.1
                                have p1209_1 := h1209c.2.1
                                have p1209_2 := h1209c.2.2.1
                                have p1209_3 := h1209c.2.2.2
                                rcases p1209_3 (m.d 0 1) (by simp) with h1230 | h1230
                                · linarith only [h1072, h1230, hlam]
                                · linarith only [h1181, h1230, hlam]
                              · have p1209_0 := h1209c.1
                                have p1209_1 := h1209c.2.1
                                have p1209_2 := h1209c.2.2.1
                                have p1209_3 := h1209c.2.2.2
                                linarith only [h1180, hlam, p1209_0]
                              · have p1209_0 := h1209c.1
                                have p1209_1 := h1209c.2.1
                                have p1209_2 := h1209c.2.2.1
                                have p1209_3 := h1209c.2.2.2
                                linarith only [h1198, hlam, p1209_1]
                              · have p1209_0 := h1209c.1
                                have p1209_1 := h1209c.2.1
                                have p1209_2 := h1209c.2.2.1
                                have p1209_3 := h1209c.2.2.2
                                linarith only [h1200, hlam, p1209_0]
                              · have p1209_0 := h1209c.1
                                have p1209_1 := h1209c.2.1
                                have p1209_2 := h1209c.2.2.1
                                have p1209_3 := h1209c.2.2.2
                                linarith only [hlam, p1209_0]
                              · have p1209_0 := h1209c.1
                                have p1209_1 := h1209c.2.1
                                have p1209_2 := h1209c.2.2.1
                                have p1209_3 := h1209c.2.2.2
                                linarith only [h1202, hlam, p1209_1]
                              · have p1209_0 := h1209c.1
                                have p1209_1 := h1209c.2.1
                                have p1209_2 := h1209c.2.2.1
                                have p1209_3 := h1209c.2.2.2
                                linarith only [h1181, hlam, p1209_0]
                              · have p1209_0 := h1209c.1
                                have p1209_1 := h1209c.2.1
                                have p1209_2 := h1209c.2.2.1
                                have p1209_3 := h1209c.2.2.2
                                linarith only [h1199, hlam, p1209_1]
                              · have p1209_0 := h1209c.1
                                have p1209_1 := h1209c.2.1
                                have p1209_2 := h1209c.2.2.1
                                have p1209_3 := h1209c.2.2.2
                                linarith only [h1201, hlam, p1209_0]
                              · have p1209_0 := h1209c.1
                                have p1209_1 := h1209c.2.1
                                have p1209_2 := h1209c.2.2.1
                                have p1209_3 := h1209c.2.2.2
                                linarith only [h1181, h1198, h1204, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1209_1, u3ehi3]
                              · have p1209_0 := h1209c.1
                                have p1209_1 := h1209c.2.1
                                have p1209_2 := h1209c.2.2.1
                                have p1209_3 := h1209c.2.2.2
                                linarith only [hlam, p1209_0]
                        · linarith only [h1182, h1183, h1204, hc45, hlam, hphi, ht34, u3ehi2]
                    · linarith only [h1072, h1180, h1201, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
                  · linarith only [h1072, h1180, h1182, h1198, h1200, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                · linarith only [h1072, h1180, h1197, h1198, h1199, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
              · linarith only [h1072, h1180, h1197, h1198, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · linarith only [h0, h1180, h1197, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
        · linarith only [h1072, h1180, h1182, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1250 | h1250
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1251 | h1251
          · linarith only [h1180, h1181, h1251, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1253 | h1253
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1254 | h1254
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1255 | h1255
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1256 | h1256
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1257 | h1257
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1258 | h1258
                      · linarith only [h1072, h1180, h1251, h1258, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                      · linarith only [h1180, h1181, h1256, h1258, hc45, hlam, hphi, ht34, u3ehi3]
                    · linarith only [h1072, h1180, h1256, h1257, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1072, h1180, h1250, h1254, h1256, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                · linarith only [h1072, h1180, h1253, h1254, h1255, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
              · linarith only [h1072, h1180, h1253, h1254, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · linarith only [h0, h1180, h1253, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
        · linarith only [h1072, h1180, h1250, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1267 | h1267
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1268 | h1268
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1269 | h1269
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1270 | h1270
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1271 | h1271
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1272 | h1272
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1273 | h1273
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1274 | h1274
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1275 | h1275
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1276 | h1276
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1277 | h1277
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1278 | h1278
                            · linarith only [h1270, h1276, h1278, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h1180, h1267, h1270, h1273, h1275, h1278, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                          · linarith only [h1180, h1267, h1270, h1273, h1275, h1277, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1282 | h1282
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1283 | h1283
                            · rcases h1bigk with h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [hlam, p1284_0]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [h0, hlam, p1284_0]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [h1072, hlam, p1284_0]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [h1180, hlam, p1284_0]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [h1180, h1270, h1272, h1273, h1282, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1284_1, u4ehi4]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [hc12, hlam, hphi, ht01, p1284_1, u0ehi0]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [hlam, p1284_0]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [h1180, h1273, hc12, hlam, hphi, ht01, p1284_1, u0ehi3]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [h1180, h1267, h1272, h1282, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1284_1, u4ehi4]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                rcases p1284_3 (m.d 0 1) (by simp) with h1294 | h1294
                                · linarith only [h0, h1294, hlam]
                                · linarith only [h1267, h1294, hlam]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [h1267, h1272, h1282, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p1284_1, u4ehi4]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [h1270, hlam, p1284_1]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [hlam, p1284_0]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [h1180, h1267, h1270, h1272, h1282, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1284_1, u4ehi4]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                rcases p1284_3 (m.d 0 1) (by simp) with h1301 | h1301
                                · linarith only [h1072, h1301, hlam]
                                · linarith only [h1267, h1301, hlam]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [h1267, h1272, h1282, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1284_1, u4ehi4]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [h1271, hlam, p1284_1]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [h1273, hlam, p1284_0]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [hlam, p1284_0]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                rcases p1284_3 (m.d 0 1) (by simp) with h1308 | h1308
                                · linarith only [h1180, h1308, hlam]
                                · linarith only [h1267, h1308, hlam]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [h1267, hlam, p1284_0]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [h1272, hlam, p1284_1]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [h1274, hlam, p1284_0]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [h1275, hlam, p1284_0]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [hlam, p1284_0]
                            · linarith only [h1276, h1282, h1283, hlam]
                          · linarith only [h1180, h1267, h1270, h1273, h1275, h1282, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                      · linarith only [h1180, h1267, h1268, h1269, h1275, hc03, hc15, hlam, hphi, ht0b, ht5b]
                    · linarith only [h1072, h1267, h1274, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi4]
                  · linarith only [h1072, h1267, h1268, h1273, hc03, hlam, hphi, u0ehi4]
                · linarith only [h0, h1267, h1272, hc25, hlam, hphi, ht01, ht12, u0ehi4]
              · linarith only [h1072, h1267, h1270, h1271, hc24, hlam, hphi, ht01, ht12, u0ehi4]
            · linarith only [h0, h1267, h1270, hc23, hlam, hphi, ht01, ht12, u0ehi4]
          · linarith only [h1180, h1267, h1269, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1325 | h1325
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1326 | h1326
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1327 | h1327
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1328 | h1328
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1329 | h1329
                  · linarith only [h1268, h1326, h1329, hc12, hlam, hphi, ht01, u0ehi2]
                  · linarith only [h1072, h1267, h1329, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi4]
                · linarith only [h0, h1267, h1328, hc25, hlam, hphi, ht01, ht12, u0ehi4]
              · linarith only [h1072, h1267, h1326, h1327, hc24, hlam, hphi, ht01, ht12, u0ehi4]
            · linarith only [h0, h1267, h1326, hc23, hlam, hphi, ht01, ht12, u0ehi4]
          · linarith only [h1072, h1267, h1268, h1325, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1336 | h1336
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1337 | h1337
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1338 | h1338
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1339 | h1339
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1340 | h1340
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1341 | h1341
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1342 | h1342
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1343 | h1343
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1344 | h1344
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1345 | h1345
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1346 | h1346
                            · linarith only [h1338, h1344, h1346, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h1338, h1344, h1345, h1346, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1349 | h1349
                            · linarith only [h1344, h1345, h1349, hlam]
                            · rcases h1bigk with h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c
                              · have p1351_0 := h1351c.1
                                have p1351_1 := h1351c.2.1
                                have p1351_2 := h1351c.2.2.1
                                have p1351_3 := h1351c.2.2.2
                                linarith only [hlam, p1351_0]
                              · have p1351_0 := h1351c.1
                                have p1351_1 := h1351c.2.1
                                have p1351_2 := h1351c.2.2.1
                                have p1351_3 := h1351c.2.2.2
                                linarith only [h0, hlam, p1351_0]
                              · have p1351_0 := h1351c.1
                                have p1351_1 := h1351c.2.1
                                have p1351_2 := h1351c.2.2.1
                                have p1351_3 := h1351c.2.2.2
                                linarith only [h1072, hlam, p1351_0]
                              · have p1351_0 := h1351c.1
                                have p1351_1 := h1351c.2.1
                                have p1351_2 := h1351c.2.2.1
                                have p1351_3 := h1351c.2.2.2
                                linarith only [h1180, hlam, p1351_0]
                              · have p1351_0 := h1351c.1
                                have p1351_1 := h1351c.2.1
                                have p1351_2 := h1351c.2.2.1
                                have p1351_3 := h1351c.2.2.2
                                linarith only [h1267, hlam, p1351_0]
                              · have p1351_0 := h1351c.1
                                have p1351_1 := h1351c.2.1
                                have p1351_2 := h1351c.2.2.1
                                have p1351_3 := h1351c.2.2.2
                                linarith only [hc12, hlam, hphi, ht01, p1351_1, u0ehi0]
                              · have p1351_0 := h1351c.1
                                have p1351_1 := h1351c.2.1
                                have p1351_2 := h1351c.2.2.1
                                have p1351_3 := h1351c.2.2.2
                                linarith only [hlam, p1351_0]
                              · have p1351_0 := h1351c.1
                                have p1351_1 := h1351c.2.1
                                have p1351_2 := h1351c.2.2.1
                                have p1351_3 := h1351c.2.2.2
                                linarith only [h1180, h1341, hc12, hlam, hphi, ht01, p1351_1, u0ehi3]
                              · have p1351_0 := h1351c.1
                                have p1351_1 := h1351c.2.1
                                have p1351_2 := h1351c.2.2.1
                                have p1351_3 := h1351c.2.2.2
                                linarith only [h1180, h1337, h1344, h1345, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1351_1, u3ehi3]
                              · have p1351_0 := h1351c.1
                                have p1351_1 := h1351c.2.1
                                have p1351_2 := h1351c.2.2.1
                                have p1351_3 := h1351c.2.2.2
                                linarith only [h1267, hc12, hlam, hphi, ht01, p1351_1, u0ehi0]
                              · have p1351_0 := h1351c.1
                                have p1351_1 := h1351c.2.1
                                have p1351_2 := h1351c.2.2.1
                                have p1351_3 := h1351c.2.2.2
                                linarith only [hc13, hlam, hphi, ht01, p1351_1, u0ehi0]
                              · have p1351_0 := h1351c.1
                                have p1351_1 := h1351c.2.1
                                have p1351_2 := h1351c.2.2.1
                                have p1351_3 := h1351c.2.2.2
                                linarith only [h1338, hlam, p1351_1]
                              · have p1351_0 := h1351c.1
                                have p1351_1 := h1351c.2.1
                                have p1351_2 := h1351c.2.2.1
                                have p1351_3 := h1351c.2.2.2
                                linarith only [hlam, p1351_0]
                              · have p1351_0 := h1351c.1
                                have p1351_1 := h1351c.2.1
                                have p1351_2 := h1351c.2.2.1
                                have p1351_3 := h1351c.2.2.2
                                linarith only [h1180, h1337, h1338, h1344, h1345, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1351_1, u3ehi3]
                              · have p1351_0 := h1351c.1
                                have p1351_1 := h1351c.2.1
                                have p1351_2 := h1351c.2.2.1
                                have p1351_3 := h1351c.2.2.2
                                linarith only [h1267, h1338, hc12, hlam, hphi, ht01, p1351_1, u0ehi0]
                              · have p1351_0 := h1351c.1
                                have p1351_1 := h1351c.2.1
                                have p1351_2 := h1351c.2.2.1
                                have p1351_3 := h1351c.2.2.2
                                linarith only [hc14, hlam, hphi, ht01, p1351_1, u0ehi0]
                              · have p1351_0 := h1351c.1
                                have p1351_1 := h1351c.2.1
                                have p1351_2 := h1351c.2.2.1
                                have p1351_3 := h1351c.2.2.2
                                linarith only [h1339, hlam, p1351_1]
                              · have p1351_0 := h1351c.1
                                have p1351_1 := h1351c.2.1
                                have p1351_2 := h1351c.2.2.1
                                have p1351_3 := h1351c.2.2.2
                                linarith only [h1341, hlam, p1351_0]
                              · have p1351_0 := h1351c.1
                                have p1351_1 := h1351c.2.1
                                have p1351_2 := h1351c.2.2.1
                                have p1351_3 := h1351c.2.2.2
                                linarith only [hlam, p1351_0]
                              · have p1351_0 := h1351c.1
                                have p1351_1 := h1351c.2.1
                                have p1351_2 := h1351c.2.2.1
                                have p1351_3 := h1351c.2.2.2
                                linarith only [h1267, h1338, h1341, hc12, hlam, hphi, ht01, p1351_1, u0ehi0]
                              · have p1351_0 := h1351c.1
                                have p1351_1 := h1351c.2.1
                                have p1351_2 := h1351c.2.2.1
                                have p1351_3 := h1351c.2.2.2
                                linarith only [hc15, hlam, hphi, ht01, p1351_1, u0ehi0]
                              · have p1351_0 := h1351c.1
                                have p1351_1 := h1351c.2.1
                                have p1351_2 := h1351c.2.2.1
                                have p1351_3 := h1351c.2.2.2
                                linarith only [h1340, hlam, p1351_1]
                              · have p1351_0 := h1351c.1
                                have p1351_1 := h1351c.2.1
                                have p1351_2 := h1351c.2.2.1
                                have p1351_3 := h1351c.2.2.2
                                linarith only [h1342, hlam, p1351_0]
                              · have p1351_0 := h1351c.1
                                have p1351_1 := h1351c.2.1
                                have p1351_2 := h1351c.2.2.1
                                have p1351_3 := h1351c.2.2.2
                                linarith only [h1343, hlam, p1351_0]
                              · have p1351_0 := h1351c.1
                                have p1351_1 := h1351c.2.1
                                have p1351_2 := h1351c.2.2.1
                                have p1351_3 := h1351c.2.2.2
                                linarith only [hlam, p1351_0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1377 | h1377
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1378 | h1378
                            · rcases h1bigk with h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c
                              · have p1379_0 := h1379c.1
                                have p1379_1 := h1379c.2.1
                                have p1379_2 := h1379c.2.2.1
                                have p1379_3 := h1379c.2.2.2
                                linarith only [hlam, p1379_0]
                              · have p1379_0 := h1379c.1
                                have p1379_1 := h1379c.2.1
                                have p1379_2 := h1379c.2.2.1
                                have p1379_3 := h1379c.2.2.2
                                linarith only [h0, hlam, p1379_0]
                              · have p1379_0 := h1379c.1
                                have p1379_1 := h1379c.2.1
                                have p1379_2 := h1379c.2.2.1
                                have p1379_3 := h1379c.2.2.2
                                linarith only [h1072, hlam, p1379_0]
                              · have p1379_0 := h1379c.1
                                have p1379_1 := h1379c.2.1
                                have p1379_2 := h1379c.2.2.1
                                have p1379_3 := h1379c.2.2.2
                                linarith only [h1180, hlam, p1379_0]
                              · have p1379_0 := h1379c.1
                                have p1379_1 := h1379c.2.1
                                have p1379_2 := h1379c.2.2.1
                                have p1379_3 := h1379c.2.2.2
                                linarith only [h1267, hlam, p1379_0]
                              · have p1379_0 := h1379c.1
                                have p1379_1 := h1379c.2.1
                                have p1379_2 := h1379c.2.2.1
                                have p1379_3 := h1379c.2.2.2
                                linarith only [hc12, hlam, hphi, ht01, p1379_1, u0ehi0]
                              · have p1379_0 := h1379c.1
                                have p1379_1 := h1379c.2.1
                                have p1379_2 := h1379c.2.2.1
                                have p1379_3 := h1379c.2.2.2
                                linarith only [hlam, p1379_0]
                              · have p1379_0 := h1379c.1
                                have p1379_1 := h1379c.2.1
                                have p1379_2 := h1379c.2.2.1
                                have p1379_3 := h1379c.2.2.2
                                linarith only [h1072, h1336, h1344, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1379_1, u4ehi2]
                              · have p1379_0 := h1379c.1
                                have p1379_1 := h1379c.2.1
                                have p1379_2 := h1379c.2.2.1
                                have p1379_3 := h1379c.2.2.2
                                linarith only [h1180, hc12, hlam, hphi, ht01, p1379_1, u0ehi0]
                              · have p1379_0 := h1379c.1
                                have p1379_1 := h1379c.2.1
                                have p1379_2 := h1379c.2.2.1
                                have p1379_3 := h1379c.2.2.2
                                linarith only [h1267, hc12, hlam, hphi, ht01, p1379_1, u0ehi0]
                              · have p1379_0 := h1379c.1
                                have p1379_1 := h1379c.2.1
                                have p1379_2 := h1379c.2.2.1
                                have p1379_3 := h1379c.2.2.2
                                linarith only [hc13, hlam, hphi, ht01, p1379_1, u0ehi0]
                              · have p1379_0 := h1379c.1
                                have p1379_1 := h1379c.2.1
                                have p1379_2 := h1379c.2.2.1
                                have p1379_3 := h1379c.2.2.2
                                linarith only [h1338, hlam, p1379_1]
                              · have p1379_0 := h1379c.1
                                have p1379_1 := h1379c.2.1
                                have p1379_2 := h1379c.2.2.1
                                have p1379_3 := h1379c.2.2.2
                                linarith only [hlam, p1379_0]
                              · have p1379_0 := h1379c.1
                                have p1379_1 := h1379c.2.1
                                have p1379_2 := h1379c.2.2.1
                                have p1379_3 := h1379c.2.2.2
                                linarith only [h1267, h1338, h1343, hc12, hlam, hphi, ht01, p1379_1, u0ehi0]
                              · have p1379_0 := h1379c.1
                                have p1379_1 := h1379c.2.1
                                have p1379_2 := h1379c.2.2.1
                                have p1379_3 := h1379c.2.2.2
                                linarith only [h1267, h1338, hc12, hlam, hphi, ht01, p1379_1, u0ehi0]
                              · have p1379_0 := h1379c.1
                                have p1379_1 := h1379c.2.1
                                have p1379_2 := h1379c.2.2.1
                                have p1379_3 := h1379c.2.2.2
                                linarith only [hc14, hlam, hphi, ht01, p1379_1, u0ehi0]
                              · have p1379_0 := h1379c.1
                                have p1379_1 := h1379c.2.1
                                have p1379_2 := h1379c.2.2.1
                                have p1379_3 := h1379c.2.2.2
                                linarith only [h1339, hlam, p1379_1]
                              · have p1379_0 := h1379c.1
                                have p1379_1 := h1379c.2.1
                                have p1379_2 := h1379c.2.2.1
                                have p1379_3 := h1379c.2.2.2
                                linarith only [h1341, hlam, p1379_0]
                              · have p1379_0 := h1379c.1
                                have p1379_1 := h1379c.2.1
                                have p1379_2 := h1379c.2.2.1
                                have p1379_3 := h1379c.2.2.2
                                linarith only [hlam, p1379_0]
                              · have p1379_0 := h1379c.1
                                have p1379_1 := h1379c.2.1
                                have p1379_2 := h1379c.2.2.1
                                have p1379_3 := h1379c.2.2.2
                                linarith only [h1267, h1338, h1341, hc12, hlam, hphi, ht01, p1379_1, u0ehi0]
                              · have p1379_0 := h1379c.1
                                have p1379_1 := h1379c.2.1
                                have p1379_2 := h1379c.2.2.1
                                have p1379_3 := h1379c.2.2.2
                                linarith only [hc15, hlam, hphi, ht01, p1379_1, u0ehi0]
                              · have p1379_0 := h1379c.1
                                have p1379_1 := h1379c.2.1
                                have p1379_2 := h1379c.2.2.1
                                have p1379_3 := h1379c.2.2.2
                                linarith only [h1340, hlam, p1379_1]
                              · have p1379_0 := h1379c.1
                                have p1379_1 := h1379c.2.1
                                have p1379_2 := h1379c.2.2.1
                                have p1379_3 := h1379c.2.2.2
                                linarith only [h1342, hlam, p1379_0]
                              · have p1379_0 := h1379c.1
                                have p1379_1 := h1379c.2.1
                                have p1379_2 := h1379c.2.2.1
                                have p1379_3 := h1379c.2.2.2
                                linarith only [h1343, hlam, p1379_0]
                              · have p1379_0 := h1379c.1
                                have p1379_1 := h1379c.2.1
                                have p1379_2 := h1379c.2.2.1
                                have p1379_3 := h1379c.2.2.2
                                linarith only [hlam, p1379_0]
                            · linarith only [h1344, h1377, h1378, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1406 | h1406
                            · linarith only [h1344, h1377, h1406, hc34, hlam, hphi, u3ehi2]
                            · linarith only [h1337, h1344, h1406, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h1180, h1337, h1343, hlam]
                    · linarith only [h1072, h1342, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                  · linarith only [h1072, h1341, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                · linarith only [h0, h1340, hc25, hlam, hphi, ht01, ht12, u0ehi0]
              · linarith only [h1072, h1338, h1339, hc24, hlam, hphi, ht01, ht12, u0ehi0]
            · linarith only [h0, h1338, hc23, hlam, hphi, ht01, ht12, u0ehi0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1415 | h1415
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1416 | h1416
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1417 | h1417
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1418 | h1418
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1419 | h1419
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1420 | h1420
                      · linarith only [h1337, h1415, h1418, h1420, hc12, hlam, hphi, ht01, u0ehi3]
                      · linarith only [h1180, h1420, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi0]
                    · linarith only [h1072, h1419, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                  · linarith only [h1072, h1336, h1418, hlam]
                · linarith only [h0, h1417, hc25, hlam, hphi, ht01, ht12, u0ehi0]
              · linarith only [h1072, h1415, h1416, hc24, hlam, hphi, ht01, ht12, u0ehi0]
            · linarith only [h0, h1415, hc23, hlam, hphi, ht01, ht12, u0ehi0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1428 | h1428
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1429 | h1429
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1430 | h1430
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1431 | h1431
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1432 | h1432
                  · linarith only [h1336, h1429, h1432, hc12, hlam, hphi, ht01, u0ehi2]
                  · linarith only [h1072, h1432, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                · linarith only [h1072, h1429, h1431, hc25, hlam, hphi, ht01, ht12, u0ehi0]
              · linarith only [h1072, h1429, h1430, hc24, hlam, hphi, ht01, ht12, u0ehi0]
            · linarith only [h0, h1429, hc23, hlam, hphi, ht01, ht12, u0ehi0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1438 | h1438
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1439 | h1439
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1440 | h1440
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1441 | h1441
                  · linarith only [h1072, h1336, h1438, h1441, hc12, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h1072, h1441, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                · linarith only [h0, h1440, hc25, hlam, hphi, ht01, ht12, u0ehi0]
              · linarith only [h1072, h1438, h1439, hc24, hlam, hphi, ht01, ht12, u0ehi0]
            · linarith only [h0, h1438, hc23, hlam, hphi, ht01, ht12, u0ehi0]

theorem r1l7_20_11_13_14_M_IR_L_I_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h0ehi := hb0.2.1
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have h4ehi := hb4.1
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
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_11_13_14_M_IR_L_I_L_R_L_R_x0 m hb0 hb1 hb3 hb4 h0
  · exact r1l7_20_11_13_14_M_IR_L_I_L_R_L_R_x1 m hb0 hb1 hb3 hb4 h0

end R2N4
