import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4448000 in
set_option maxHeartbeats 4448000 in
theorem r1l7_20_12_13_M_LR_L_I_L_I_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1115 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h0ehi := hb0.2.2.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1116 | h1116
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1117 | h1117
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1118 | h1118
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1119 | h1119
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1120 | h1120
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1121 | h1121
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1122 | h1122
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1123 | h1123
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1124 | h1124
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1125 | h1125
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1126 | h1126
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1127 | h1127
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1128 | h1128
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1129 | h1129
                            · linarith only [h1115, h1121, h1126, h1129, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                            · linarith only [h0, h1115, h1122, h1124, h1128, h1129, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1132 | h1132
                            · linarith only [h0, h1115, h1119, h1128, h1132, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases h2bigk with h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c
                              · have p1134_0 := h1134c.1
                                have p1134_1 := h1134c.2.1
                                have p1134_2 := h1134c.2.2.1
                                have p1134_3 := h1134c.2.2.2
                                linarith only [hlam, p1134_0]
                              · have p1134_0 := h1134c.1
                                have p1134_1 := h1134c.2.1
                                have p1134_2 := h1134c.2.2.1
                                have p1134_3 := h1134c.2.2.2
                                linarith only [h0, hlam, p1134_0]
                              · have p1134_0 := h1134c.1
                                have p1134_1 := h1134c.2.1
                                have p1134_2 := h1134c.2.2.1
                                have p1134_3 := h1134c.2.2.2
                                linarith only [h1127, hc35, hlam, hphi, ht0b, ht5b, p1134_1, u0elo1]
                              · have p1134_0 := h1134c.1
                                have p1134_1 := h1134c.2.1
                                have p1134_2 := h1134c.2.2.1
                                have p1134_3 := h1134c.2.2.2
                                rcases p1134_3 (m.d 0 2) (by simp) with h1138 | h1138
                                · rcases p1134_3 (m.d 1 2) (by simp) with h1139 | h1139
                                  · rcases p1134_3 (m.d 2 3) (by simp) with h1140 | h1140
                                    · linarith only [h1116, h1140, hlam]
                                    · linarith only [h1126, h1140, hlam]
                                  · linarith only [h1122, h1139, hlam]
                                · linarith only [h1138, hlam, p1134_0]
                              · have p1134_0 := h1134c.1
                                have p1134_1 := h1134c.2.1
                                have p1134_2 := h1134c.2.2.1
                                have p1134_3 := h1134c.2.2.2
                                rcases p1134_3 (m.d 0 2) (by simp) with h1145 | h1145
                                · rcases p1134_3 (m.d 1 2) (by simp) with h1146 | h1146
                                  · rcases p1134_3 (m.d 2 3) (by simp) with h1147 | h1147
                                    · linarith only [h1116, h1147, hlam]
                                    · linarith only [h1127, h1147, hlam]
                                  · linarith only [h1123, h1146, hlam]
                                · linarith only [h1145, hlam, p1134_0]
                              · have p1134_0 := h1134c.1
                                have p1134_1 := h1134c.2.1
                                have p1134_2 := h1134c.2.2.1
                                have p1134_3 := h1134c.2.2.2
                                linarith only [h0, hc12, hlam, hphi, ht01, p1134_1, u0ehi5]
                              · have p1134_0 := h1134c.1
                                have p1134_1 := h1134c.2.1
                                have p1134_2 := h1134c.2.2.1
                                have p1134_3 := h1134c.2.2.2
                                linarith only [hlam, p1134_0]
                              · have p1134_0 := h1134c.1
                                have p1134_1 := h1134c.2.1
                                have p1134_2 := h1134c.2.2.1
                                have p1134_3 := h1134c.2.2.2
                                rcases p1134_3 (m.d 0 2) (by simp) with h1154 | h1154
                                · linarith only [h0, h1154, hlam]
                                · linarith only [h1116, h1154, hlam]
                              · have p1134_0 := h1134c.1
                                have p1134_1 := h1134c.2.1
                                have p1134_2 := h1134c.2.2.1
                                have p1134_3 := h1134c.2.2.2
                                rcases p1134_3 (m.d 0 2) (by simp) with h1157 | h1157
                                · linarith only [h0, h1157, hlam]
                                · linarith only [h1117, h1157, hlam]
                              · have p1134_0 := h1134c.1
                                have p1134_1 := h1134c.2.1
                                have p1134_2 := h1134c.2.2.1
                                have p1134_3 := h1134c.2.2.2
                                rcases p1134_3 (m.d 0 2) (by simp) with h1160 | h1160
                                · linarith only [h0, h1160, hlam]
                                · linarith only [h1118, h1160, hlam]
                              · have p1134_0 := h1134c.1
                                have p1134_1 := h1134c.2.1
                                have p1134_2 := h1134c.2.2.1
                                have p1134_3 := h1134c.2.2.2
                                linarith only [h1116, hlam, p1134_0]
                              · have p1134_0 := h1134c.1
                                have p1134_1 := h1134c.2.1
                                have p1134_2 := h1134c.2.2.1
                                have p1134_3 := h1134c.2.2.2
                                linarith only [h1121, hlam, p1134_0]
                              · have p1134_0 := h1134c.1
                                have p1134_1 := h1134c.2.1
                                have p1134_2 := h1134c.2.2.1
                                have p1134_3 := h1134c.2.2.2
                                linarith only [hlam, p1134_0]
                              · have p1134_0 := h1134c.1
                                have p1134_1 := h1134c.2.1
                                have p1134_2 := h1134c.2.2.1
                                have p1134_3 := h1134c.2.2.2
                                linarith only [h1115, h1121, hc24, hlam, hphi, ht0b, ht45, ht5b, p1134_1, u0elo0]
                              · have p1134_0 := h1134c.1
                                have p1134_1 := h1134c.2.1
                                have p1134_2 := h1134c.2.2.1
                                have p1134_3 := h1134c.2.2.2
                                linarith only [h0, h1115, h1121, h1126, h1128, hc34, hlam, hphi, ht0b, ht45, ht5b, p1134_1, u0elo1]
                              · have p1134_0 := h1134c.1
                                have p1134_1 := h1134c.2.1
                                have p1134_2 := h1134c.2.2.1
                                have p1134_3 := h1134c.2.2.2
                                linarith only [h1117, hlam, p1134_0]
                              · have p1134_0 := h1134c.1
                                have p1134_1 := h1134c.2.1
                                have p1134_2 := h1134c.2.2.1
                                have p1134_3 := h1134c.2.2.2
                                linarith only [h1122, hlam, p1134_0]
                              · have p1134_0 := h1134c.1
                                have p1134_1 := h1134c.2.1
                                have p1134_2 := h1134c.2.2.1
                                have p1134_3 := h1134c.2.2.2
                                linarith only [h1126, hlam, p1134_0]
                              · have p1134_0 := h1134c.1
                                have p1134_1 := h1134c.2.1
                                have p1134_2 := h1134c.2.2.1
                                have p1134_3 := h1134c.2.2.2
                                linarith only [hlam, p1134_0]
                              · have p1134_0 := h1134c.1
                                have p1134_1 := h1134c.2.1
                                have p1134_2 := h1134c.2.2.1
                                have p1134_3 := h1134c.2.2.2
                                linarith only [h1128, hlam, p1134_0]
                              · have p1134_0 := h1134c.1
                                have p1134_1 := h1134c.2.1
                                have p1134_2 := h1134c.2.2.1
                                have p1134_3 := h1134c.2.2.2
                                linarith only [h1118, hlam, p1134_0]
                              · have p1134_0 := h1134c.1
                                have p1134_1 := h1134c.2.1
                                have p1134_2 := h1134c.2.2.1
                                have p1134_3 := h1134c.2.2.2
                                linarith only [h1123, hlam, p1134_0]
                              · have p1134_0 := h1134c.1
                                have p1134_1 := h1134c.2.1
                                have p1134_2 := h1134c.2.2.1
                                have p1134_3 := h1134c.2.2.2
                                linarith only [h1127, hlam, p1134_0]
                              · have p1134_0 := h1134c.1
                                have p1134_1 := h1134c.2.1
                                have p1134_2 := h1134c.2.2.1
                                have p1134_3 := h1134c.2.2.2
                                linarith only [h1118, h1126, hc34, hlam, hphi, ht0b, ht45, ht5b, p1134_1, u0elo1]
                              · have p1134_0 := h1134c.1
                                have p1134_1 := h1134c.2.1
                                have p1134_2 := h1134c.2.2.1
                                have p1134_3 := h1134c.2.2.2
                                linarith only [hlam, p1134_0]
                        · linarith only [h0, h1115, h1125, h1127, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h1115, h1124, h1126, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1115, h1120, h1124, h1125, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1181 | h1181
                    · linarith only [h0, h1115, h1119, h1124, h1181, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1183 | h1183
                      · linarith only [h1116, h1124, h1183, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1185 | h1185
                        · linarith only [h0, h1115, h1119, h1121, h1123, h1124, h1181, h1185, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1187 | h1187
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1188 | h1188
                            · rcases h2bigk with h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [hlam, p1189_0]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [h0, hlam, p1189_0]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                rcases p1189_3 (m.d 0 2) (by simp) with h1192 | h1192
                                · rcases p1189_3 (m.d 1 2) (by simp) with h1193 | h1193
                                  · rcases p1189_3 (m.d 2 3) (by simp) with h1194 | h1194
                                    · linarith only [h1194, hlam, p1189_0]
                                    · rcases p1189_3 (m.d 2 4) (by simp) with h1196 | h1196
                                      · linarith only [h1117, h1196, hlam]
                                      · linarith only [h1183, h1196, hlam]
                                  · linarith only [h1121, h1193, hlam]
                                · linarith only [h1192, hlam, p1189_0]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [h1187, hc45, hlam, hphi, ht0b, ht5b, p1189_1, u0elo1]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                rcases p1189_3 (m.d 0 2) (by simp) with h1202 | h1202
                                · rcases p1189_3 (m.d 1 2) (by simp) with h1203 | h1203
                                  · rcases p1189_3 (m.d 2 3) (by simp) with h1204 | h1204
                                    · linarith only [h1116, h1204, hlam]
                                    · rcases p1189_3 (m.d 2 4) (by simp) with h1206 | h1206
                                      · linarith only [h1117, h1206, hlam]
                                      · linarith only [h1187, h1206, hlam]
                                  · linarith only [h1123, h1203, hlam]
                                · linarith only [h1202, hlam, p1189_0]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [h0, h1115, h1119, h1121, h1181, h1188, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1189_1]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [hlam, p1189_0]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [h0, h1115, h1119, h1121, h1181, h1188, hlam, p1189_2]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                rcases p1189_3 (m.d 0 2) (by simp) with h1214 | h1214
                                · linarith only [h0, h1214, hlam]
                                · linarith only [h1117, h1214, hlam]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                rcases p1189_3 (m.d 0 2) (by simp) with h1217 | h1217
                                · linarith only [h0, h1217, hlam]
                                · linarith only [h1118, h1217, hlam]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [h1116, hlam, p1189_0]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [h1121, hlam, p1189_0]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [hlam, p1189_0]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [h1183, hlam, p1189_1]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [h1185, hlam, p1189_1]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [h1117, hlam, p1189_0]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [h1122, hlam, p1189_0]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [h1117, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1189_1, u0elo1]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [hlam, p1189_0]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [h1115, h1119, h1122, h1124, hc25, hlam, hphi, ht0b, ht5b, p1189_1, u0elo0]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [h1118, hlam, p1189_0]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [h1123, hlam, p1189_0]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [h1118, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1189_1, u0elo1]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [h1187, hlam, p1189_1]
                              · have p1189_0 := h1189c.1
                                have p1189_1 := h1189c.2.1
                                have p1189_2 := h1189c.2.2.1
                                have p1189_3 := h1189c.2.2.2
                                linarith only [hlam, p1189_0]
                            · linarith only [h1122, h1124, h1187, h1188, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1236 | h1236
                            · linarith only [h0, h1115, h1119, h1187, h1236, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases h2bigk with h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [hlam, p1238_0]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [h0, hlam, p1238_0]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                rcases p1238_3 (m.d 0 2) (by simp) with h1241 | h1241
                                · rcases p1238_3 (m.d 1 2) (by simp) with h1242 | h1242
                                  · rcases p1238_3 (m.d 2 3) (by simp) with h1243 | h1243
                                    · linarith only [h1243, hlam, p1238_0]
                                    · rcases p1238_3 (m.d 2 4) (by simp) with h1245 | h1245
                                      · linarith only [h1117, h1245, hlam]
                                      · linarith only [h1183, h1245, hlam]
                                  · linarith only [h1121, h1242, hlam]
                                · linarith only [h1241, hlam, p1238_0]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                rcases p1238_3 (m.d 0 2) (by simp) with h1250 | h1250
                                · rcases p1238_3 (m.d 1 2) (by simp) with h1251 | h1251
                                  · rcases p1238_3 (m.d 2 3) (by simp) with h1252 | h1252
                                    · linarith only [h1116, h1252, hlam]
                                    · rcases p1238_3 (m.d 2 4) (by simp) with h1254 | h1254
                                      · linarith only [h1254, hlam, p1238_0]
                                      · rcases p1238_3 (m.d 2 5) (by simp) with h1256 | h1256
                                        · linarith only [h1118, h1256, hlam]
                                        · linarith only [h1187, h1256, hlam]
                                  · linarith only [h1122, h1251, hlam]
                                · linarith only [h1250, hlam, p1238_0]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                rcases p1238_3 (m.d 0 2) (by simp) with h1261 | h1261
                                · rcases p1238_3 (m.d 1 2) (by simp) with h1262 | h1262
                                  · rcases p1238_3 (m.d 2 3) (by simp) with h1263 | h1263
                                    · linarith only [h1116, h1263, hlam]
                                    · rcases p1238_3 (m.d 2 4) (by simp) with h1265 | h1265
                                      · linarith only [h1117, h1265, hlam]
                                      · rcases p1238_3 (m.d 2 5) (by simp) with h1267 | h1267
                                        · linarith only [h1267, hlam, p1238_0]
                                        · rcases h2emax with h1269 | h1269 | h1269 | h1269 | h1269
                                          · linarith only [h1269, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1238_1]
                                          · linarith only [h0, h1269, hc01, hlam, ht12]
                                          · rcases h3bigk with h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c
                                            · have p1272_0 := h1272c.1
                                              have p1272_1 := h1272c.2.1
                                              have p1272_2 := h1272c.2.2.1
                                              have p1272_3 := h1272c.2.2.2
                                              linarith only [hlam, p1272_0]
                                            · have p1272_0 := h1272c.1
                                              have p1272_1 := h1272c.2.1
                                              have p1272_2 := h1272c.2.2.1
                                              have p1272_3 := h1272c.2.2.2
                                              rcases p1272_3 (m.d 0 3) (by simp) with h1274 | h1274
                                              · rcases p1272_3 (m.d 1 3) (by simp) with h1275 | h1275
                                                · linarith only [h1115, h1275, hlam]
                                                · rcases p1272_3 (m.d 2 3) (by simp) with h1277 | h1277
                                                  · linarith only [h1116, h1277, hlam]
                                                  · rcases p1272_3 (m.d 3 4) (by simp) with h1279 | h1279
                                                    · linarith only [h1119, h1279, hlam]
                                                    · linarith only [h1124, h1279, hlam]
                                              · linarith only [h1115, h1274, hlam]
                                            · have p1272_0 := h1272c.1
                                              have p1272_1 := h1272c.2.1
                                              have p1272_2 := h1272c.2.2.1
                                              have p1272_3 := h1272c.2.2.2
                                              rcases p1272_3 (m.d 0 3) (by simp) with h1283 | h1283
                                              · rcases p1272_3 (m.d 1 3) (by simp) with h1284 | h1284
                                                · linarith only [h1115, h1284, hlam]
                                                · linarith only [h1121, h1284, hlam]
                                              · linarith only [h1116, h1283, hlam]
                                            · have p1272_0 := h1272c.1
                                              have p1272_1 := h1272c.2.1
                                              have p1272_2 := h1272c.2.2.1
                                              have p1272_3 := h1272c.2.2.2
                                              linarith only [h1115, h1121, h1124, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1272_1, u0elo0]
                                            · have p1272_0 := h1272c.1
                                              have p1272_1 := h1272c.2.1
                                              have p1272_2 := h1272c.2.2.1
                                              have p1272_3 := h1272c.2.2.2
                                              linarith only [h0, h1115, h1121, h1124, h1236, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1272_1, u0elo1]
                                            · have p1272_0 := h1272c.1
                                              have p1272_1 := h1272c.2.1
                                              have p1272_2 := h1272c.2.2.1
                                              have p1272_3 := h1272c.2.2.2
                                              linarith only [h1115, hlam, p1272_0]
                                            · have p1272_0 := h1272c.1
                                              have p1272_1 := h1272c.2.1
                                              have p1272_2 := h1272c.2.2.1
                                              have p1272_3 := h1272c.2.2.2
                                              linarith only [hlam, p1272_0]
                                            · have p1272_0 := h1272c.1
                                              have p1272_1 := h1272c.2.1
                                              have p1272_2 := h1272c.2.2.1
                                              have p1272_3 := h1272c.2.2.2
                                              linarith only [h1124, hc23, hc34, hlam, hphi, p1272_1]
                                            · have p1272_0 := h1272c.1
                                              have p1272_1 := h1272c.2.1
                                              have p1272_2 := h1272c.2.2.1
                                              have p1272_3 := h1272c.2.2.2
                                              linarith only [h1124, hlam, p1272_0]
                                            · have p1272_0 := h1272c.1
                                              have p1272_1 := h1272c.2.1
                                              have p1272_2 := h1272c.2.2.1
                                              have p1272_3 := h1272c.2.2.2
                                              linarith only [h1181, hlam, p1272_0]
                                            · have p1272_0 := h1272c.1
                                              have p1272_1 := h1272c.2.1
                                              have p1272_2 := h1272c.2.2.1
                                              have p1272_3 := h1272c.2.2.2
                                              linarith only [h1116, hlam, p1272_1]
                                            · have p1272_0 := h1272c.1
                                              have p1272_1 := h1272c.2.1
                                              have p1272_2 := h1272c.2.2.1
                                              have p1272_3 := h1272c.2.2.2
                                              linarith only [h1121, hlam, p1272_1]
                                            · have p1272_0 := h1272c.1
                                              have p1272_1 := h1272c.2.1
                                              have p1272_2 := h1272c.2.2.1
                                              have p1272_3 := h1272c.2.2.2
                                              linarith only [hlam, p1272_0]
                                            · have p1272_0 := h1272c.1
                                              have p1272_1 := h1272c.2.1
                                              have p1272_2 := h1272c.2.2.1
                                              have p1272_3 := h1272c.2.2.2
                                              linarith only [h1183, hlam, p1272_0]
                                            · have p1272_0 := h1272c.1
                                              have p1272_1 := h1272c.2.1
                                              have p1272_2 := h1272c.2.2.1
                                              have p1272_3 := h1272c.2.2.2
                                              linarith only [h1185, hlam, p1272_0]
                                            · have p1272_0 := h1272c.1
                                              have p1272_1 := h1272c.2.1
                                              have p1272_2 := h1272c.2.2.1
                                              have p1272_3 := h1272c.2.2.2
                                              linarith only [h1119, hlam, p1272_0]
                                            · have p1272_0 := h1272c.1
                                              have p1272_1 := h1272c.2.1
                                              have p1272_2 := h1272c.2.2.1
                                              have p1272_3 := h1272c.2.2.2
                                              linarith only [h1236, hc13, hc45, hlam, hphi, ht34, p1272_1]
                                            · have p1272_0 := h1272c.1
                                              have p1272_1 := h1272c.2.1
                                              have p1272_2 := h1272c.2.2.1
                                              have p1272_3 := h1272c.2.2.2
                                              linarith only [h0, h1115, h1119, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1272_1, u0elo1]
                                            · have p1272_0 := h1272c.1
                                              have p1272_1 := h1272c.2.1
                                              have p1272_2 := h1272c.2.2.1
                                              have p1272_3 := h1272c.2.2.2
                                              linarith only [hlam, p1272_0]
                                            · have p1272_0 := h1272c.1
                                              have p1272_1 := h1272c.2.1
                                              have p1272_2 := h1272c.2.2.1
                                              have p1272_3 := h1272c.2.2.2
                                              linarith only [h1236, hlam, p1272_0]
                                            · have p1272_0 := h1272c.1
                                              have p1272_1 := h1272c.2.1
                                              have p1272_2 := h1272c.2.2.1
                                              have p1272_3 := h1272c.2.2.2
                                              linarith only [h1120, hlam, p1272_0]
                                            · have p1272_0 := h1272c.1
                                              have p1272_1 := h1272c.2.1
                                              have p1272_2 := h1272c.2.2.1
                                              have p1272_3 := h1272c.2.2.2
                                              linarith only [h0, h1115, h1120, h1121, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1272_1, u0elo1]
                                            · have p1272_0 := h1272c.1
                                              have p1272_1 := h1272c.2.1
                                              have p1272_2 := h1272c.2.2.1
                                              have p1272_3 := h1272c.2.2.2
                                              linarith only [h0, h1115, h1120, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1272_1, u0elo1]
                                            · have p1272_0 := h1272c.1
                                              have p1272_1 := h1272c.2.1
                                              have p1272_2 := h1272c.2.2.1
                                              have p1272_3 := h1272c.2.2.2
                                              linarith only [h0, h1115, h1120, hc34, hlam, hphi, ht0b, ht45, ht5b, p1272_1, u0elo1]
                                            · have p1272_0 := h1272c.1
                                              have p1272_1 := h1272c.2.1
                                              have p1272_2 := h1272c.2.2.1
                                              have p1272_3 := h1272c.2.2.2
                                              linarith only [hlam, p1272_0]
                                          · rcases h3bigk with h1310c | h1310c | h1310c | h1310c | h1310c | h1310c | h1310c | h1310c | h1310c | h1310c | h1310c | h1310c | h1310c | h1310c | h1310c | h1310c | h1310c | h1310c | h1310c | h1310c | h1310c | h1310c | h1310c | h1310c | h1310c
                                            · have p1310_0 := h1310c.1
                                              have p1310_1 := h1310c.2.1
                                              have p1310_2 := h1310c.2.2.1
                                              have p1310_3 := h1310c.2.2.2
                                              linarith only [hlam, p1310_0]
                                            · have p1310_0 := h1310c.1
                                              have p1310_1 := h1310c.2.1
                                              have p1310_2 := h1310c.2.2.1
                                              have p1310_3 := h1310c.2.2.2
                                              rcases p1310_3 (m.d 0 3) (by simp) with h1312 | h1312
                                              · rcases p1310_3 (m.d 1 3) (by simp) with h1313 | h1313
                                                · linarith only [h1115, h1313, hlam]
                                                · rcases p1310_3 (m.d 2 3) (by simp) with h1315 | h1315
                                                  · linarith only [h1116, h1315, hlam]
                                                  · rcases p1310_3 (m.d 3 4) (by simp) with h1317 | h1317
                                                    · linarith only [h1119, h1317, hlam]
                                                    · linarith only [h1124, h1317, hlam]
                                              · linarith only [h1115, h1312, hlam]
                                            · have p1310_0 := h1310c.1
                                              have p1310_1 := h1310c.2.1
                                              have p1310_2 := h1310c.2.2.1
                                              have p1310_3 := h1310c.2.2.2
                                              rcases p1310_3 (m.d 0 3) (by simp) with h1321 | h1321
                                              · rcases p1310_3 (m.d 1 3) (by simp) with h1322 | h1322
                                                · linarith only [h1115, h1322, hlam]
                                                · linarith only [h1121, h1322, hlam]
                                              · linarith only [h1116, h1321, hlam]
                                            · have p1310_0 := h1310c.1
                                              have p1310_1 := h1310c.2.1
                                              have p1310_2 := h1310c.2.2.1
                                              have p1310_3 := h1310c.2.2.2
                                              linarith only [h0, h1115, h1121, h1124, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1310_1, u0elo1]
                                            · have p1310_0 := h1310c.1
                                              have p1310_1 := h1310c.2.1
                                              have p1310_2 := h1310c.2.2.1
                                              have p1310_3 := h1310c.2.2.2
                                              linarith only [h0, h1115, h1121, h1181, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1310_1, u0elo1]
                                            · have p1310_0 := h1310c.1
                                              have p1310_1 := h1310c.2.1
                                              have p1310_2 := h1310c.2.2.1
                                              have p1310_3 := h1310c.2.2.2
                                              linarith only [h1115, hlam, p1310_0]
                                            · have p1310_0 := h1310c.1
                                              have p1310_1 := h1310c.2.1
                                              have p1310_2 := h1310c.2.2.1
                                              have p1310_3 := h1310c.2.2.2
                                              linarith only [hlam, p1310_0]
                                            · have p1310_0 := h1310c.1
                                              have p1310_1 := h1310c.2.1
                                              have p1310_2 := h1310c.2.2.1
                                              have p1310_3 := h1310c.2.2.2
                                              linarith only [h1124, hc23, hc34, hlam, hphi, p1310_1]
                                            · have p1310_0 := h1310c.1
                                              have p1310_1 := h1310c.2.1
                                              have p1310_2 := h1310c.2.2.1
                                              have p1310_3 := h1310c.2.2.2
                                              linarith only [h1124, hlam, p1310_0]
                                            · have p1310_0 := h1310c.1
                                              have p1310_1 := h1310c.2.1
                                              have p1310_2 := h1310c.2.2.1
                                              have p1310_3 := h1310c.2.2.2
                                              linarith only [h1181, hlam, p1310_0]
                                            · have p1310_0 := h1310c.1
                                              have p1310_1 := h1310c.2.1
                                              have p1310_2 := h1310c.2.2.1
                                              have p1310_3 := h1310c.2.2.2
                                              linarith only [h1116, hlam, p1310_1]
                                            · have p1310_0 := h1310c.1
                                              have p1310_1 := h1310c.2.1
                                              have p1310_2 := h1310c.2.2.1
                                              have p1310_3 := h1310c.2.2.2
                                              linarith only [h1121, hlam, p1310_1]
                                            · have p1310_0 := h1310c.1
                                              have p1310_1 := h1310c.2.1
                                              have p1310_2 := h1310c.2.2.1
                                              have p1310_3 := h1310c.2.2.2
                                              linarith only [hlam, p1310_0]
                                            · have p1310_0 := h1310c.1
                                              have p1310_1 := h1310c.2.1
                                              have p1310_2 := h1310c.2.2.1
                                              have p1310_3 := h1310c.2.2.2
                                              linarith only [h1183, hlam, p1310_0]
                                            · have p1310_0 := h1310c.1
                                              have p1310_1 := h1310c.2.1
                                              have p1310_2 := h1310c.2.2.1
                                              have p1310_3 := h1310c.2.2.2
                                              linarith only [h1185, hlam, p1310_0]
                                            · have p1310_0 := h1310c.1
                                              have p1310_1 := h1310c.2.1
                                              have p1310_2 := h1310c.2.2.1
                                              have p1310_3 := h1310c.2.2.2
                                              linarith only [h1119, hlam, p1310_0]
                                            · have p1310_0 := h1310c.1
                                              have p1310_1 := h1310c.2.1
                                              have p1310_2 := h1310c.2.2.1
                                              have p1310_3 := h1310c.2.2.2
                                              linarith only [h0, h1115, h1119, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1310_1, u0elo1]
                                            · have p1310_0 := h1310c.1
                                              have p1310_1 := h1310c.2.1
                                              have p1310_2 := h1310c.2.2.1
                                              have p1310_3 := h1310c.2.2.2
                                              linarith only [h0, h1115, h1119, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1310_1, u0elo1]
                                            · have p1310_0 := h1310c.1
                                              have p1310_1 := h1310c.2.1
                                              have p1310_2 := h1310c.2.2.1
                                              have p1310_3 := h1310c.2.2.2
                                              linarith only [hlam, p1310_0]
                                            · have p1310_0 := h1310c.1
                                              have p1310_1 := h1310c.2.1
                                              have p1310_2 := h1310c.2.2.1
                                              have p1310_3 := h1310c.2.2.2
                                              linarith only [h1236, hlam, p1310_0]
                                            · have p1310_0 := h1310c.1
                                              have p1310_1 := h1310c.2.1
                                              have p1310_2 := h1310c.2.2.1
                                              have p1310_3 := h1310c.2.2.2
                                              linarith only [h1120, hlam, p1310_0]
                                            · have p1310_0 := h1310c.1
                                              have p1310_1 := h1310c.2.1
                                              have p1310_2 := h1310c.2.2.1
                                              have p1310_3 := h1310c.2.2.2
                                              linarith only [h0, h1115, h1120, h1121, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1310_1, u0elo1]
                                            · have p1310_0 := h1310c.1
                                              have p1310_1 := h1310c.2.1
                                              have p1310_2 := h1310c.2.2.1
                                              have p1310_3 := h1310c.2.2.2
                                              linarith only [h0, h1115, h1120, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1310_1, u0elo1]
                                            · have p1310_0 := h1310c.1
                                              have p1310_1 := h1310c.2.1
                                              have p1310_2 := h1310c.2.2.1
                                              have p1310_3 := h1310c.2.2.2
                                              linarith only [h0, h1115, h1120, hc34, hlam, hphi, ht0b, ht45, ht5b, p1310_1, u0elo1]
                                            · have p1310_0 := h1310c.1
                                              have p1310_1 := h1310c.2.1
                                              have p1310_2 := h1310c.2.2.1
                                              have p1310_3 := h1310c.2.2.2
                                              linarith only [hlam, p1310_0]
                                          · rcases h3bigk with h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c
                                            · have p1348_0 := h1348c.1
                                              have p1348_1 := h1348c.2.1
                                              have p1348_2 := h1348c.2.2.1
                                              have p1348_3 := h1348c.2.2.2
                                              linarith only [hlam, p1348_0]
                                            · have p1348_0 := h1348c.1
                                              have p1348_1 := h1348c.2.1
                                              have p1348_2 := h1348c.2.2.1
                                              have p1348_3 := h1348c.2.2.2
                                              rcases p1348_3 (m.d 0 3) (by simp) with h1350 | h1350
                                              · rcases p1348_3 (m.d 1 3) (by simp) with h1351 | h1351
                                                · linarith only [h1115, h1351, hlam]
                                                · rcases p1348_3 (m.d 2 3) (by simp) with h1353 | h1353
                                                  · linarith only [h1116, h1353, hlam]
                                                  · rcases p1348_3 (m.d 3 4) (by simp) with h1355 | h1355
                                                    · linarith only [h1119, h1355, hlam]
                                                    · linarith only [h1124, h1355, hlam]
                                              · linarith only [h1115, h1350, hlam]
                                            · have p1348_0 := h1348c.1
                                              have p1348_1 := h1348c.2.1
                                              have p1348_2 := h1348c.2.2.1
                                              have p1348_3 := h1348c.2.2.2
                                              rcases p1348_3 (m.d 0 3) (by simp) with h1359 | h1359
                                              · rcases p1348_3 (m.d 1 3) (by simp) with h1360 | h1360
                                                · linarith only [h1115, h1360, hlam]
                                                · linarith only [h1121, h1360, hlam]
                                              · linarith only [h1116, h1359, hlam]
                                            · have p1348_0 := h1348c.1
                                              have p1348_1 := h1348c.2.1
                                              have p1348_2 := h1348c.2.2.1
                                              have p1348_3 := h1348c.2.2.2
                                              linarith only [h0, h1115, h1121, h1124, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1348_1, u0elo1]
                                            · have p1348_0 := h1348c.1
                                              have p1348_1 := h1348c.2.1
                                              have p1348_2 := h1348c.2.2.1
                                              have p1348_3 := h1348c.2.2.2
                                              linarith only [h0, h1115, h1121, h1181, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1348_1, u0elo1]
                                            · have p1348_0 := h1348c.1
                                              have p1348_1 := h1348c.2.1
                                              have p1348_2 := h1348c.2.2.1
                                              have p1348_3 := h1348c.2.2.2
                                              linarith only [h1115, hlam, p1348_0]
                                            · have p1348_0 := h1348c.1
                                              have p1348_1 := h1348c.2.1
                                              have p1348_2 := h1348c.2.2.1
                                              have p1348_3 := h1348c.2.2.2
                                              linarith only [hlam, p1348_0]
                                            · have p1348_0 := h1348c.1
                                              have p1348_1 := h1348c.2.1
                                              have p1348_2 := h1348c.2.2.1
                                              have p1348_3 := h1348c.2.2.2
                                              linarith only [h1124, hc23, hc34, hlam, hphi, p1348_1]
                                            · have p1348_0 := h1348c.1
                                              have p1348_1 := h1348c.2.1
                                              have p1348_2 := h1348c.2.2.1
                                              have p1348_3 := h1348c.2.2.2
                                              linarith only [h1124, hlam, p1348_0]
                                            · have p1348_0 := h1348c.1
                                              have p1348_1 := h1348c.2.1
                                              have p1348_2 := h1348c.2.2.1
                                              have p1348_3 := h1348c.2.2.2
                                              linarith only [h1181, hlam, p1348_0]
                                            · have p1348_0 := h1348c.1
                                              have p1348_1 := h1348c.2.1
                                              have p1348_2 := h1348c.2.2.1
                                              have p1348_3 := h1348c.2.2.2
                                              linarith only [h1116, hlam, p1348_1]
                                            · have p1348_0 := h1348c.1
                                              have p1348_1 := h1348c.2.1
                                              have p1348_2 := h1348c.2.2.1
                                              have p1348_3 := h1348c.2.2.2
                                              linarith only [h1121, hlam, p1348_1]
                                            · have p1348_0 := h1348c.1
                                              have p1348_1 := h1348c.2.1
                                              have p1348_2 := h1348c.2.2.1
                                              have p1348_3 := h1348c.2.2.2
                                              linarith only [hlam, p1348_0]
                                            · have p1348_0 := h1348c.1
                                              have p1348_1 := h1348c.2.1
                                              have p1348_2 := h1348c.2.2.1
                                              have p1348_3 := h1348c.2.2.2
                                              linarith only [h1183, hlam, p1348_0]
                                            · have p1348_0 := h1348c.1
                                              have p1348_1 := h1348c.2.1
                                              have p1348_2 := h1348c.2.2.1
                                              have p1348_3 := h1348c.2.2.2
                                              linarith only [h1185, hlam, p1348_0]
                                            · have p1348_0 := h1348c.1
                                              have p1348_1 := h1348c.2.1
                                              have p1348_2 := h1348c.2.2.1
                                              have p1348_3 := h1348c.2.2.2
                                              linarith only [h1119, hlam, p1348_0]
                                            · have p1348_0 := h1348c.1
                                              have p1348_1 := h1348c.2.1
                                              have p1348_2 := h1348c.2.2.1
                                              have p1348_3 := h1348c.2.2.2
                                              linarith only [h0, h1115, h1119, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1348_1, u0elo1]
                                            · have p1348_0 := h1348c.1
                                              have p1348_1 := h1348c.2.1
                                              have p1348_2 := h1348c.2.2.1
                                              have p1348_3 := h1348c.2.2.2
                                              linarith only [h0, h1115, h1119, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1348_1, u0elo1]
                                            · have p1348_0 := h1348c.1
                                              have p1348_1 := h1348c.2.1
                                              have p1348_2 := h1348c.2.2.1
                                              have p1348_3 := h1348c.2.2.2
                                              linarith only [hlam, p1348_0]
                                            · have p1348_0 := h1348c.1
                                              have p1348_1 := h1348c.2.1
                                              have p1348_2 := h1348c.2.2.1
                                              have p1348_3 := h1348c.2.2.2
                                              linarith only [h1236, hlam, p1348_0]
                                            · have p1348_0 := h1348c.1
                                              have p1348_1 := h1348c.2.1
                                              have p1348_2 := h1348c.2.2.1
                                              have p1348_3 := h1348c.2.2.2
                                              linarith only [h1120, hlam, p1348_0]
                                            · have p1348_0 := h1348c.1
                                              have p1348_1 := h1348c.2.1
                                              have p1348_2 := h1348c.2.2.1
                                              have p1348_3 := h1348c.2.2.2
                                              linarith only [h0, h1115, h1120, h1121, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1348_1, u0elo1]
                                            · have p1348_0 := h1348c.1
                                              have p1348_1 := h1348c.2.1
                                              have p1348_2 := h1348c.2.2.1
                                              have p1348_3 := h1348c.2.2.2
                                              linarith only [h0, h1115, h1120, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1348_1, u0elo1]
                                            · have p1348_0 := h1348c.1
                                              have p1348_1 := h1348c.2.1
                                              have p1348_2 := h1348c.2.2.1
                                              have p1348_3 := h1348c.2.2.2
                                              linarith only [h0, h1115, h1120, hc34, hlam, hphi, ht0b, ht45, ht5b, p1348_1, u0elo1]
                                            · have p1348_0 := h1348c.1
                                              have p1348_1 := h1348c.2.1
                                              have p1348_2 := h1348c.2.2.1
                                              have p1348_3 := h1348c.2.2.2
                                              linarith only [hlam, p1348_0]
                                  · linarith only [h1123, h1262, hlam]
                                · linarith only [h1261, hlam, p1238_0]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [h0, hc12, hlam, hphi, ht01, p1238_1, u0ehi5]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [hlam, p1238_0]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [h0, h1115, h1119, h1121, h1124, hlam, p1238_2]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                rcases p1238_3 (m.d 0 2) (by simp) with h1391 | h1391
                                · linarith only [h0, h1391, hlam]
                                · linarith only [h1117, h1391, hlam]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                rcases p1238_3 (m.d 0 2) (by simp) with h1394 | h1394
                                · linarith only [h0, h1394, hlam]
                                · linarith only [h1118, h1394, hlam]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [h1116, hlam, p1238_0]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [h1121, hlam, p1238_0]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [hlam, p1238_0]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [h1183, hlam, p1238_1]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [h1185, hlam, p1238_1]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [h1117, hlam, p1238_0]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [h1122, hlam, p1238_0]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [h1117, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1238_1, u0elo1]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [hlam, p1238_0]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [h1187, hlam, p1238_0]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [h1118, hlam, p1238_0]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [h1123, hlam, p1238_0]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [h1115, h1120, h1123, h1181, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1238_1, u0elo0]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [h0, h1115, h1120, h1123, h1181, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1238_1]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [hlam, p1238_0]
                · linarith only [h0, h1123, hc25, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h0, h1115, h1119, h1122, hc24, hlam, hphi, ht01, ht12, u0ehi8]
            · linarith only [h0, h1115, h1119, h1121, hc23, hlam, hphi, ht01, ht12, u0ehi8]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1415 | h1415
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1416 | h1416
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1417 | h1417
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1418 | h1418
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1419 | h1419
                    · linarith only [h1119, h1120, h1419, hc13, hlam, hphi, ht01, u0ehi8]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1421 | h1421
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1422 | h1422
                        · linarith only [h0, h1115, h1119, h1120, h1415, h1422, hc12, hlam, hphi, ht01, u0ehi8]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1424 | h1424
                          · linarith only [h1421, h1422, h1424, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1426 | h1426
                            · linarith only [h1119, h1120, h1424, h1426, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                            · rcases h2bigk with h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c
                              · have p1428_0 := h1428c.1
                                have p1428_1 := h1428c.2.1
                                have p1428_2 := h1428c.2.2.1
                                have p1428_3 := h1428c.2.2.2
                                linarith only [hlam, p1428_0]
                              · have p1428_0 := h1428c.1
                                have p1428_1 := h1428c.2.1
                                have p1428_2 := h1428c.2.2.1
                                have p1428_3 := h1428c.2.2.2
                                linarith only [h0, hlam, p1428_0]
                              · have p1428_0 := h1428c.1
                                have p1428_1 := h1428c.2.1
                                have p1428_2 := h1428c.2.2.1
                                have p1428_3 := h1428c.2.2.2
                                linarith only [h1119, h1120, h1421, h1426, hc34, hc45, hlam, hphi, p1428_1, u0ehi8, u0elo1]
                              · have p1428_0 := h1428c.1
                                have p1428_1 := h1428c.2.1
                                have p1428_2 := h1428c.2.2.1
                                have p1428_3 := h1428c.2.2.2
                                rcases p1428_3 (m.d 0 2) (by simp) with h1432 | h1432
                                · rcases p1428_3 (m.d 1 2) (by simp) with h1433 | h1433
                                  · rcases p1428_3 (m.d 2 3) (by simp) with h1434 | h1434
                                    · linarith only [h1116, h1434, hlam]
                                    · linarith only [h1421, h1434, hlam]
                                  · linarith only [h1416, h1433, hlam]
                                · linarith only [h1432, hlam, p1428_0]
                              · have p1428_0 := h1428c.1
                                have p1428_1 := h1428c.2.1
                                have p1428_2 := h1428c.2.2.1
                                have p1428_3 := h1428c.2.2.2
                                linarith only [h1119, h1120, h1421, h1422, h1426, hc34, hc45, hlam, hphi, p1428_1, u0ehi8, u0elo1]
                              · have p1428_0 := h1428c.1
                                have p1428_1 := h1428c.2.1
                                have p1428_2 := h1428c.2.2.1
                                have p1428_3 := h1428c.2.2.2
                                linarith only [hc12, hlam, hphi, ht01, p1428_1, u0ehi6]
                              · have p1428_0 := h1428c.1
                                have p1428_1 := h1428c.2.1
                                have p1428_2 := h1428c.2.2.1
                                have p1428_3 := h1428c.2.2.2
                                linarith only [hlam, p1428_0]
                              · have p1428_0 := h1428c.1
                                have p1428_1 := h1428c.2.1
                                have p1428_2 := h1428c.2.2.1
                                have p1428_3 := h1428c.2.2.2
                                rcases p1428_3 (m.d 0 2) (by simp) with h1442 | h1442
                                · linarith only [h0, h1442, hlam]
                                · linarith only [h1116, h1442, hlam]
                              · have p1428_0 := h1428c.1
                                have p1428_1 := h1428c.2.1
                                have p1428_2 := h1428c.2.2.1
                                have p1428_3 := h1428c.2.2.2
                                rcases p1428_3 (m.d 0 2) (by simp) with h1445 | h1445
                                · linarith only [h0, h1445, hlam]
                                · linarith only [h1117, h1445, hlam]
                              · have p1428_0 := h1428c.1
                                have p1428_1 := h1428c.2.1
                                have p1428_2 := h1428c.2.2.1
                                have p1428_3 := h1428c.2.2.2
                                rcases p1428_3 (m.d 0 2) (by simp) with h1448 | h1448
                                · linarith only [h0, h1448, hlam]
                                · linarith only [h1118, h1448, hlam]
                              · have p1428_0 := h1428c.1
                                have p1428_1 := h1428c.2.1
                                have p1428_2 := h1428c.2.2.1
                                have p1428_3 := h1428c.2.2.2
                                linarith only [h1116, hlam, p1428_0]
                              · have p1428_0 := h1428c.1
                                have p1428_1 := h1428c.2.1
                                have p1428_2 := h1428c.2.2.1
                                have p1428_3 := h1428c.2.2.2
                                linarith only [h1415, hlam, p1428_0]
                              · have p1428_0 := h1428c.1
                                have p1428_1 := h1428c.2.1
                                have p1428_2 := h1428c.2.2.1
                                have p1428_3 := h1428c.2.2.2
                                linarith only [hlam, p1428_0]
                              · have p1428_0 := h1428c.1
                                have p1428_1 := h1428c.2.1
                                have p1428_2 := h1428c.2.2.1
                                have p1428_3 := h1428c.2.2.2
                                linarith only [h1116, h1119, h1120, h1426, hc24, hc45, hlam, hphi, p1428_1, u0ehi8, u0elo1]
                              · have p1428_0 := h1428c.1
                                have p1428_1 := h1428c.2.1
                                have p1428_2 := h1428c.2.2.1
                                have p1428_3 := h1428c.2.2.2
                                linarith only [h1422, hlam, p1428_1]
                              · have p1428_0 := h1428c.1
                                have p1428_1 := h1428c.2.1
                                have p1428_2 := h1428c.2.2.1
                                have p1428_3 := h1428c.2.2.2
                                linarith only [h1117, hlam, p1428_0]
                              · have p1428_0 := h1428c.1
                                have p1428_1 := h1428c.2.1
                                have p1428_2 := h1428c.2.2.1
                                have p1428_3 := h1428c.2.2.2
                                linarith only [h1416, hlam, p1428_0]
                              · have p1428_0 := h1428c.1
                                have p1428_1 := h1428c.2.1
                                have p1428_2 := h1428c.2.2.1
                                have p1428_3 := h1428c.2.2.2
                                linarith only [h1421, hlam, p1428_0]
                              · have p1428_0 := h1428c.1
                                have p1428_1 := h1428c.2.1
                                have p1428_2 := h1428c.2.2.1
                                have p1428_3 := h1428c.2.2.2
                                linarith only [hlam, p1428_0]
                              · have p1428_0 := h1428c.1
                                have p1428_1 := h1428c.2.1
                                have p1428_2 := h1428c.2.2.1
                                have p1428_3 := h1428c.2.2.2
                                linarith only [h1424, hlam, p1428_0]
                              · have p1428_0 := h1428c.1
                                have p1428_1 := h1428c.2.1
                                have p1428_2 := h1428c.2.2.1
                                have p1428_3 := h1428c.2.2.2
                                linarith only [h1118, hlam, p1428_0]
                              · have p1428_0 := h1428c.1
                                have p1428_1 := h1428c.2.1
                                have p1428_2 := h1428c.2.2.1
                                have p1428_3 := h1428c.2.2.2
                                linarith only [h1417, hlam, p1428_0]
                              · have p1428_0 := h1428c.1
                                have p1428_1 := h1428c.2.1
                                have p1428_2 := h1428c.2.2.1
                                have p1428_3 := h1428c.2.2.2
                                linarith only [h1118, h1119, h1120, h1426, hc23, hc45, hlam, hphi, ht34, p1428_1, u0ehi8, u0elo1]
                              · have p1428_0 := h1428c.1
                                have p1428_1 := h1428c.2.1
                                have p1428_2 := h1428c.2.2.1
                                have p1428_3 := h1428c.2.2.2
                                linarith only [h1118, h1119, h1120, h1421, h1426, hc34, hc45, hlam, hphi, p1428_1, u0ehi8, u0elo1]
                              · have p1428_0 := h1428c.1
                                have p1428_1 := h1428c.2.1
                                have p1428_2 := h1428c.2.2.1
                                have p1428_3 := h1428c.2.2.2
                                linarith only [hlam, p1428_0]
                      · linarith only [h1119, h1120, h1421, hc23, hc35, hlam, hphi]
                  · linarith only [h1119, h1120, h1418, hc13, hc35, hlam, hphi]
                · linarith only [h0, h1118, h1417, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h1115, h1119, h1416, hc24, hlam, hphi, ht01, ht12, u0ehi8]
            · linarith only [h0, h1115, h1119, h1415, hc23, hlam, hphi, ht01, ht12, u0ehi8]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1471 | h1471
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1472 | h1472
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1473 | h1473
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1474 | h1474
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1475 | h1475
                  · linarith only [h1119, h1475, hc13, hlam, hphi, ht01, u0ehi7]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1477 | h1477
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1478 | h1478
                      · linarith only [h1115, h1119, h1471, h1472, h1478, hlam, hphi, u0ehi9, u0elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1480 | h1480
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1481 | h1481
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1482 | h1482
                            · rcases h2bigk with h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c
                              · have p1483_0 := h1483c.1
                                have p1483_1 := h1483c.2.1
                                have p1483_2 := h1483c.2.2.1
                                have p1483_3 := h1483c.2.2.2
                                linarith only [hlam, p1483_0]
                              · have p1483_0 := h1483c.1
                                have p1483_1 := h1483c.2.1
                                have p1483_2 := h1483c.2.2.1
                                have p1483_3 := h1483c.2.2.2
                                linarith only [h0, hlam, p1483_0]
                              · have p1483_0 := h1483c.1
                                have p1483_1 := h1483c.2.1
                                have p1483_2 := h1483c.2.2.1
                                have p1483_3 := h1483c.2.2.2
                                linarith only [h1480, hc35, hlam, hphi, ht0b, ht5b, p1483_1, u0elo1]
                              · have p1483_0 := h1483c.1
                                have p1483_1 := h1483c.2.1
                                have p1483_2 := h1483c.2.2.1
                                have p1483_3 := h1483c.2.2.2
                                linarith only [h1478, h1480, h1482, hc45, hlam, hphi, ht0b, ht5b, p1483_1, u0elo1]
                              · have p1483_0 := h1483c.1
                                have p1483_1 := h1483c.2.1
                                have p1483_2 := h1483c.2.2.1
                                have p1483_3 := h1483c.2.2.2
                                rcases p1483_3 (m.d 0 2) (by simp) with h1488 | h1488
                                · rcases p1483_3 (m.d 1 2) (by simp) with h1489 | h1489
                                  · rcases p1483_3 (m.d 2 3) (by simp) with h1490 | h1490
                                    · linarith only [h1116, h1490, hlam]
                                    · linarith only [h1480, h1490, hlam]
                                  · linarith only [h1474, h1489, hlam]
                                · linarith only [h1488, hlam, p1483_0]
                              · have p1483_0 := h1483c.1
                                have p1483_1 := h1483c.2.1
                                have p1483_2 := h1483c.2.2.1
                                have p1483_3 := h1483c.2.2.2
                                linarith only [hc12, hlam, hphi, ht01, p1483_1, u0ehi6]
                              · have p1483_0 := h1483c.1
                                have p1483_1 := h1483c.2.1
                                have p1483_2 := h1483c.2.2.1
                                have p1483_3 := h1483c.2.2.2
                                linarith only [hlam, p1483_0]
                              · have p1483_0 := h1483c.1
                                have p1483_1 := h1483c.2.1
                                have p1483_2 := h1483c.2.2.1
                                have p1483_3 := h1483c.2.2.2
                                rcases p1483_3 (m.d 0 2) (by simp) with h1497 | h1497
                                · linarith only [h0, h1497, hlam]
                                · linarith only [h1116, h1497, hlam]
                              · have p1483_0 := h1483c.1
                                have p1483_1 := h1483c.2.1
                                have p1483_2 := h1483c.2.2.1
                                have p1483_3 := h1483c.2.2.2
                                rcases p1483_3 (m.d 0 2) (by simp) with h1500 | h1500
                                · linarith only [h0, h1500, hlam]
                                · linarith only [h1117, h1500, hlam]
                              · have p1483_0 := h1483c.1
                                have p1483_1 := h1483c.2.1
                                have p1483_2 := h1483c.2.2.1
                                have p1483_3 := h1483c.2.2.2
                                rcases p1483_3 (m.d 0 2) (by simp) with h1503 | h1503
                                · linarith only [h0, h1503, hlam]
                                · linarith only [h1118, h1503, hlam]
                              · have p1483_0 := h1483c.1
                                have p1483_1 := h1483c.2.1
                                have p1483_2 := h1483c.2.2.1
                                have p1483_3 := h1483c.2.2.2
                                linarith only [h1116, hlam, p1483_0]
                              · have p1483_0 := h1483c.1
                                have p1483_1 := h1483c.2.1
                                have p1483_2 := h1483c.2.2.1
                                have p1483_3 := h1483c.2.2.2
                                linarith only [h1472, hlam, p1483_0]
                              · have p1483_0 := h1483c.1
                                have p1483_1 := h1483c.2.1
                                have p1483_2 := h1483c.2.2.1
                                have p1483_3 := h1483c.2.2.2
                                linarith only [hlam, p1483_0]
                              · have p1483_0 := h1483c.1
                                have p1483_1 := h1483c.2.1
                                have p1483_2 := h1483c.2.2.1
                                have p1483_3 := h1483c.2.2.2
                                linarith only [h1478, hlam, p1483_1]
                              · have p1483_0 := h1483c.1
                                have p1483_1 := h1483c.2.1
                                have p1483_2 := h1483c.2.2.1
                                have p1483_3 := h1483c.2.2.2
                                linarith only [h1116, hc25, hlam, hphi, ht0b, ht5b, p1483_1, u0elo1]
                              · have p1483_0 := h1483c.1
                                have p1483_1 := h1483c.2.1
                                have p1483_2 := h1483c.2.2.1
                                have p1483_3 := h1483c.2.2.2
                                linarith only [h1117, hlam, p1483_0]
                              · have p1483_0 := h1483c.1
                                have p1483_1 := h1483c.2.1
                                have p1483_2 := h1483c.2.2.1
                                have p1483_3 := h1483c.2.2.2
                                linarith only [h1473, hlam, p1483_0]
                              · have p1483_0 := h1483c.1
                                have p1483_1 := h1483c.2.1
                                have p1483_2 := h1483c.2.2.1
                                have p1483_3 := h1483c.2.2.2
                                linarith only [h1117, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1483_1, u0elo1]
                              · have p1483_0 := h1483c.1
                                have p1483_1 := h1483c.2.1
                                have p1483_2 := h1483c.2.2.1
                                have p1483_3 := h1483c.2.2.2
                                linarith only [hlam, p1483_0]
                              · have p1483_0 := h1483c.1
                                have p1483_1 := h1483c.2.1
                                have p1483_2 := h1483c.2.2.1
                                have p1483_3 := h1483c.2.2.2
                                linarith only [h1117, h1480, h1482, hc45, hlam, hphi, ht0b, ht5b, p1483_1, u0elo1]
                              · have p1483_0 := h1483c.1
                                have p1483_1 := h1483c.2.1
                                have p1483_2 := h1483c.2.2.1
                                have p1483_3 := h1483c.2.2.2
                                linarith only [h1118, hlam, p1483_0]
                              · have p1483_0 := h1483c.1
                                have p1483_1 := h1483c.2.1
                                have p1483_2 := h1483c.2.2.1
                                have p1483_3 := h1483c.2.2.2
                                linarith only [h1474, hlam, p1483_0]
                              · have p1483_0 := h1483c.1
                                have p1483_1 := h1483c.2.1
                                have p1483_2 := h1483c.2.2.1
                                have p1483_3 := h1483c.2.2.2
                                linarith only [h1480, hlam, p1483_0]
                              · have p1483_0 := h1483c.1
                                have p1483_1 := h1483c.2.1
                                have p1483_2 := h1483c.2.2.1
                                have p1483_3 := h1483c.2.2.2
                                linarith only [h1481, hlam, p1483_1]
                              · have p1483_0 := h1483c.1
                                have p1483_1 := h1483c.2.1
                                have p1483_2 := h1483c.2.2.1
                                have p1483_3 := h1483c.2.2.2
                                linarith only [hlam, p1483_0]
                            · linarith only [h1119, h1471, h1482, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi9]
                          · linarith only [h1478, h1480, h1481, hlam]
                        · linarith only [h1119, h1471, h1480, hc23, hc34, hlam, hphi]
                    · linarith only [h1119, h1471, h1477, hc13, hc34, hlam, hphi]
                · linarith only [h0, h1474, hc25, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h0, h1473, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h1115, h1471, h1472, hc23, hlam, hphi, ht01, ht12, u0ehi9]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1528 | h1528
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1529 | h1529
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1530 | h1530
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1531 | h1531
                  · linarith only [h0, h1115, h1119, h1531, hc12, hlam, hphi, ht01, u0ehi7]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1533 | h1533
                    · linarith only [h0, h1115, h1471, h1533, hc12, hlam, hphi, ht01, u0ehi7]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1535 | h1535
                      · linarith only [h0, h1115, h1119, h1528, h1535, hc12, hlam, hphi, ht01, u0ehi7]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1537 | h1537
                        · linarith only [h0, h1115, h1471, h1528, h1537, hc12, hlam, hphi, ht01, u0ehi7]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1539 | h1539
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1540 | h1540
                            · rcases h2bigk with h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c | h1541c
                              · have p1541_0 := h1541c.1
                                have p1541_1 := h1541c.2.1
                                have p1541_2 := h1541c.2.2.1
                                have p1541_3 := h1541c.2.2.2
                                linarith only [hlam, p1541_0]
                              · have p1541_0 := h1541c.1
                                have p1541_1 := h1541c.2.1
                                have p1541_2 := h1541c.2.2.1
                                have p1541_3 := h1541c.2.2.2
                                linarith only [h0, hlam, p1541_0]
                              · have p1541_0 := h1541c.1
                                have p1541_1 := h1541c.2.1
                                have p1541_2 := h1541c.2.2.1
                                have p1541_3 := h1541c.2.2.2
                                rcases p1541_3 (m.d 0 2) (by simp) with h1544 | h1544
                                · rcases p1541_3 (m.d 1 2) (by simp) with h1545 | h1545
                                  · rcases p1541_3 (m.d 2 3) (by simp) with h1546 | h1546
                                    · linarith only [h1546, hlam, p1541_0]
                                    · rcases p1541_3 (m.d 2 4) (by simp) with h1548 | h1548
                                      · linarith only [h1117, h1548, hlam]
                                      · linarith only [h1535, h1548, hlam]
                                  · linarith only [h1528, h1545, hlam]
                                · linarith only [h1544, hlam, p1541_0]
                              · have p1541_0 := h1541c.1
                                have p1541_1 := h1541c.2.1
                                have p1541_2 := h1541c.2.2.1
                                have p1541_3 := h1541c.2.2.2
                                linarith only [h1539, hc45, hlam, hphi, ht0b, ht5b, p1541_1, u0elo1]
                              · have p1541_0 := h1541c.1
                                have p1541_1 := h1541c.2.1
                                have p1541_2 := h1541c.2.2.1
                                have p1541_3 := h1541c.2.2.2
                                rcases p1541_3 (m.d 0 2) (by simp) with h1554 | h1554
                                · rcases p1541_3 (m.d 1 2) (by simp) with h1555 | h1555
                                  · rcases p1541_3 (m.d 2 3) (by simp) with h1556 | h1556
                                    · linarith only [h1116, h1556, hlam]
                                    · rcases p1541_3 (m.d 2 4) (by simp) with h1558 | h1558
                                      · linarith only [h1117, h1558, hlam]
                                      · linarith only [h1539, h1558, hlam]
                                  · linarith only [h1530, h1555, hlam]
                                · linarith only [h1554, hlam, p1541_0]
                              · have p1541_0 := h1541c.1
                                have p1541_1 := h1541c.2.1
                                have p1541_2 := h1541c.2.2.1
                                have p1541_3 := h1541c.2.2.2
                                linarith only [hc12, hlam, hphi, ht01, p1541_1, u0ehi6]
                              · have p1541_0 := h1541c.1
                                have p1541_1 := h1541c.2.1
                                have p1541_2 := h1541c.2.2.1
                                have p1541_3 := h1541c.2.2.2
                                linarith only [hlam, p1541_0]
                              · have p1541_0 := h1541c.1
                                have p1541_1 := h1541c.2.1
                                have p1541_2 := h1541c.2.2.1
                                have p1541_3 := h1541c.2.2.2
                                rcases p1541_3 (m.d 0 2) (by simp) with h1565 | h1565
                                · linarith only [h0, h1565, hlam]
                                · linarith only [h1116, h1565, hlam]
                              · have p1541_0 := h1541c.1
                                have p1541_1 := h1541c.2.1
                                have p1541_2 := h1541c.2.2.1
                                have p1541_3 := h1541c.2.2.2
                                rcases p1541_3 (m.d 0 2) (by simp) with h1568 | h1568
                                · linarith only [h0, h1568, hlam]
                                · linarith only [h1117, h1568, hlam]
                              · have p1541_0 := h1541c.1
                                have p1541_1 := h1541c.2.1
                                have p1541_2 := h1541c.2.2.1
                                have p1541_3 := h1541c.2.2.2
                                rcases p1541_3 (m.d 0 2) (by simp) with h1571 | h1571
                                · linarith only [h0, h1571, hlam]
                                · linarith only [h1118, h1571, hlam]
                              · have p1541_0 := h1541c.1
                                have p1541_1 := h1541c.2.1
                                have p1541_2 := h1541c.2.2.1
                                have p1541_3 := h1541c.2.2.2
                                linarith only [h1116, hlam, p1541_0]
                              · have p1541_0 := h1541c.1
                                have p1541_1 := h1541c.2.1
                                have p1541_2 := h1541c.2.2.1
                                have p1541_3 := h1541c.2.2.2
                                linarith only [h1528, hlam, p1541_0]
                              · have p1541_0 := h1541c.1
                                have p1541_1 := h1541c.2.1
                                have p1541_2 := h1541c.2.2.1
                                have p1541_3 := h1541c.2.2.2
                                linarith only [hlam, p1541_0]
                              · have p1541_0 := h1541c.1
                                have p1541_1 := h1541c.2.1
                                have p1541_2 := h1541c.2.2.1
                                have p1541_3 := h1541c.2.2.2
                                linarith only [h1535, hlam, p1541_1]
                              · have p1541_0 := h1541c.1
                                have p1541_1 := h1541c.2.1
                                have p1541_2 := h1541c.2.2.1
                                have p1541_3 := h1541c.2.2.2
                                linarith only [h1537, hlam, p1541_1]
                              · have p1541_0 := h1541c.1
                                have p1541_1 := h1541c.2.1
                                have p1541_2 := h1541c.2.2.1
                                have p1541_3 := h1541c.2.2.2
                                linarith only [h1117, hlam, p1541_0]
                              · have p1541_0 := h1541c.1
                                have p1541_1 := h1541c.2.1
                                have p1541_2 := h1541c.2.2.1
                                have p1541_3 := h1541c.2.2.2
                                linarith only [h1529, hlam, p1541_0]
                              · have p1541_0 := h1541c.1
                                have p1541_1 := h1541c.2.1
                                have p1541_2 := h1541c.2.2.1
                                have p1541_3 := h1541c.2.2.2
                                linarith only [h1117, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1541_1, u0elo1]
                              · have p1541_0 := h1541c.1
                                have p1541_1 := h1541c.2.1
                                have p1541_2 := h1541c.2.2.1
                                have p1541_3 := h1541c.2.2.2
                                linarith only [hlam, p1541_0]
                              · have p1541_0 := h1541c.1
                                have p1541_1 := h1541c.2.1
                                have p1541_2 := h1541c.2.2.1
                                have p1541_3 := h1541c.2.2.2
                                linarith only [h1117, h1537, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1541_1, u0elo1]
                              · have p1541_0 := h1541c.1
                                have p1541_1 := h1541c.2.1
                                have p1541_2 := h1541c.2.2.1
                                have p1541_3 := h1541c.2.2.2
                                linarith only [h1118, hlam, p1541_0]
                              · have p1541_0 := h1541c.1
                                have p1541_1 := h1541c.2.1
                                have p1541_2 := h1541c.2.2.1
                                have p1541_3 := h1541c.2.2.2
                                linarith only [h1530, hlam, p1541_0]
                              · have p1541_0 := h1541c.1
                                have p1541_1 := h1541c.2.1
                                have p1541_2 := h1541c.2.2.1
                                have p1541_3 := h1541c.2.2.2
                                linarith only [h1118, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1541_1, u0elo1]
                              · have p1541_0 := h1541c.1
                                have p1541_1 := h1541c.2.1
                                have p1541_2 := h1541c.2.2.1
                                have p1541_3 := h1541c.2.2.2
                                linarith only [h1539, hlam, p1541_1]
                              · have p1541_0 := h1541c.1
                                have p1541_1 := h1541c.2.1
                                have p1541_2 := h1541c.2.2.1
                                have p1541_3 := h1541c.2.2.2
                                linarith only [hlam, p1541_0]
                            · linarith only [h1119, h1540, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1590 | h1590
                            · rcases h2bigk with h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c
                              · have p1591_0 := h1591c.1
                                have p1591_1 := h1591c.2.1
                                have p1591_2 := h1591c.2.2.1
                                have p1591_3 := h1591c.2.2.2
                                linarith only [hlam, p1591_0]
                              · have p1591_0 := h1591c.1
                                have p1591_1 := h1591c.2.1
                                have p1591_2 := h1591c.2.2.1
                                have p1591_3 := h1591c.2.2.2
                                linarith only [h0, hlam, p1591_0]
                              · have p1591_0 := h1591c.1
                                have p1591_1 := h1591c.2.1
                                have p1591_2 := h1591c.2.2.1
                                have p1591_3 := h1591c.2.2.2
                                rcases p1591_3 (m.d 0 2) (by simp) with h1594 | h1594
                                · rcases p1591_3 (m.d 1 2) (by simp) with h1595 | h1595
                                  · rcases p1591_3 (m.d 2 3) (by simp) with h1596 | h1596
                                    · linarith only [h1596, hlam, p1591_0]
                                    · rcases p1591_3 (m.d 2 4) (by simp) with h1598 | h1598
                                      · linarith only [h1117, h1598, hlam]
                                      · linarith only [h1535, h1598, hlam]
                                  · linarith only [h1528, h1595, hlam]
                                · linarith only [h1594, hlam, p1591_0]
                              · have p1591_0 := h1591c.1
                                have p1591_1 := h1591c.2.1
                                have p1591_2 := h1591c.2.2.1
                                have p1591_3 := h1591c.2.2.2
                                rcases p1591_3 (m.d 0 2) (by simp) with h1603 | h1603
                                · rcases p1591_3 (m.d 1 2) (by simp) with h1604 | h1604
                                  · rcases p1591_3 (m.d 2 3) (by simp) with h1605 | h1605
                                    · linarith only [h1116, h1605, hlam]
                                    · rcases p1591_3 (m.d 2 4) (by simp) with h1607 | h1607
                                      · linarith only [h1607, hlam, p1591_0]
                                      · rcases p1591_3 (m.d 2 5) (by simp) with h1609 | h1609
                                        · linarith only [h1118, h1609, hlam]
                                        · linarith only [h1539, h1609, hlam]
                                  · linarith only [h1529, h1604, hlam]
                                · linarith only [h1603, hlam, p1591_0]
                              · have p1591_0 := h1591c.1
                                have p1591_1 := h1591c.2.1
                                have p1591_2 := h1591c.2.2.1
                                have p1591_3 := h1591c.2.2.2
                                rcases p1591_3 (m.d 0 2) (by simp) with h1614 | h1614
                                · rcases p1591_3 (m.d 1 2) (by simp) with h1615 | h1615
                                  · rcases p1591_3 (m.d 2 3) (by simp) with h1616 | h1616
                                    · linarith only [h1116, h1616, hlam]
                                    · rcases p1591_3 (m.d 2 4) (by simp) with h1618 | h1618
                                      · linarith only [h1117, h1618, hlam]
                                      · rcases p1591_3 (m.d 2 5) (by simp) with h1620 | h1620
                                        · linarith only [h1620, hlam, p1591_0]
                                        · rcases h2emax with h1622 | h1622 | h1622 | h1622 | h1622
                                          · linarith only [h1539, h1622, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1591_1]
                                          · linarith only [h0, h1622, hc01, hlam, ht12]
                                          · rcases h3bigk with h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c | h1625c
                                            · have p1625_0 := h1625c.1
                                              have p1625_1 := h1625c.2.1
                                              have p1625_2 := h1625c.2.2.1
                                              have p1625_3 := h1625c.2.2.2
                                              linarith only [hlam, p1625_0]
                                            · have p1625_0 := h1625c.1
                                              have p1625_1 := h1625c.2.1
                                              have p1625_2 := h1625c.2.2.1
                                              have p1625_3 := h1625c.2.2.2
                                              linarith only [h1471, h1528, h1590, hc23, hc34, hlam, hphi, p1625_1]
                                            · have p1625_0 := h1625c.1
                                              have p1625_1 := h1625c.2.1
                                              have p1625_2 := h1625c.2.2.1
                                              have p1625_3 := h1625c.2.2.2
                                              linarith only [h1471, h1590, hc23, hc34, hlam, hphi, p1625_1]
                                            · have p1625_0 := h1625c.1
                                              have p1625_1 := h1625c.2.1
                                              have p1625_2 := h1625c.2.2.1
                                              have p1625_3 := h1625c.2.2.2
                                              linarith only [h1119, hlam, p1625_0]
                                            · have p1625_0 := h1625c.1
                                              have p1625_1 := h1625c.2.1
                                              have p1625_2 := h1625c.2.2.1
                                              have p1625_3 := h1625c.2.2.2
                                              linarith only [h1471, hlam, p1625_0]
                                            · have p1625_0 := h1625c.1
                                              have p1625_1 := h1625c.2.1
                                              have p1625_2 := h1625c.2.2.1
                                              have p1625_3 := h1625c.2.2.2
                                              linarith only [h1115, hlam, p1625_0]
                                            · have p1625_0 := h1625c.1
                                              have p1625_1 := h1625c.2.1
                                              have p1625_2 := h1625c.2.2.1
                                              have p1625_3 := h1625c.2.2.2
                                              linarith only [hlam, p1625_0]
                                            · have p1625_0 := h1625c.1
                                              have p1625_1 := h1625c.2.1
                                              have p1625_2 := h1625c.2.2.1
                                              have p1625_3 := h1625c.2.2.2
                                              linarith only [h1115, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1625_1, u0elo0]
                                            · have p1625_0 := h1625c.1
                                              have p1625_1 := h1625c.2.1
                                              have p1625_2 := h1625c.2.2.1
                                              have p1625_3 := h1625c.2.2.2
                                              linarith only [h1531, hlam, p1625_0]
                                            · have p1625_0 := h1625c.1
                                              have p1625_1 := h1625c.2.1
                                              have p1625_2 := h1625c.2.2.1
                                              have p1625_3 := h1625c.2.2.2
                                              linarith only [h1533, hlam, p1625_0]
                                            · have p1625_0 := h1625c.1
                                              have p1625_1 := h1625c.2.1
                                              have p1625_2 := h1625c.2.2.1
                                              have p1625_3 := h1625c.2.2.2
                                              linarith only [h1116, hlam, p1625_1]
                                            · have p1625_0 := h1625c.1
                                              have p1625_1 := h1625c.2.1
                                              have p1625_2 := h1625c.2.2.1
                                              have p1625_3 := h1625c.2.2.2
                                              linarith only [h1528, hlam, p1625_1]
                                            · have p1625_0 := h1625c.1
                                              have p1625_1 := h1625c.2.1
                                              have p1625_2 := h1625c.2.2.1
                                              have p1625_3 := h1625c.2.2.2
                                              linarith only [hlam, p1625_0]
                                            · have p1625_0 := h1625c.1
                                              have p1625_1 := h1625c.2.1
                                              have p1625_2 := h1625c.2.2.1
                                              have p1625_3 := h1625c.2.2.2
                                              linarith only [h1535, hlam, p1625_0]
                                            · have p1625_0 := h1625c.1
                                              have p1625_1 := h1625c.2.1
                                              have p1625_2 := h1625c.2.2.1
                                              have p1625_3 := h1625c.2.2.2
                                              linarith only [h1537, hlam, p1625_0]
                                            · have p1625_0 := h1625c.1
                                              have p1625_1 := h1625c.2.1
                                              have p1625_2 := h1625c.2.2.1
                                              have p1625_3 := h1625c.2.2.2
                                              linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p1625_1, u0ehi7]
                                            · have p1625_0 := h1625c.1
                                              have p1625_1 := h1625c.2.1
                                              have p1625_2 := h1625c.2.2.1
                                              have p1625_3 := h1625c.2.2.2
                                              rcases p1625_3 (m.d 0 3) (by simp) with h1642 | h1642
                                              · linarith only [h1119, h1642, hlam]
                                              · linarith only [h1115, h1642, hlam]
                                            · have p1625_0 := h1625c.1
                                              have p1625_1 := h1625c.2.1
                                              have p1625_2 := h1625c.2.2.1
                                              have p1625_3 := h1625c.2.2.2
                                              rcases p1625_3 (m.d 0 3) (by simp) with h1645 | h1645
                                              · linarith only [h1119, h1645, hlam]
                                              · linarith only [h1116, h1645, hlam]
                                            · have p1625_0 := h1625c.1
                                              have p1625_1 := h1625c.2.1
                                              have p1625_2 := h1625c.2.2.1
                                              have p1625_3 := h1625c.2.2.2
                                              linarith only [hlam, p1625_0]
                                            · have p1625_0 := h1625c.1
                                              have p1625_1 := h1625c.2.1
                                              have p1625_2 := h1625c.2.2.1
                                              have p1625_3 := h1625c.2.2.2
                                              linarith only [h1471, hc34, hlam, hphi, ht01, ht12, ht23, p1625_1, u0ehi7]
                                            · have p1625_0 := h1625c.1
                                              have p1625_1 := h1625c.2.1
                                              have p1625_2 := h1625c.2.2.1
                                              have p1625_3 := h1625c.2.2.2
                                              linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p1625_1, u0ehi7]
                                            · have p1625_0 := h1625c.1
                                              have p1625_1 := h1625c.2.1
                                              have p1625_2 := h1625c.2.2.1
                                              have p1625_3 := h1625c.2.2.2
                                              rcases p1625_3 (m.d 0 3) (by simp) with h1651 | h1651
                                              · linarith only [h1471, h1651, hlam]
                                              · linarith only [h1115, h1651, hlam]
                                            · have p1625_0 := h1625c.1
                                              have p1625_1 := h1625c.2.1
                                              have p1625_2 := h1625c.2.2.1
                                              have p1625_3 := h1625c.2.2.2
                                              rcases p1625_3 (m.d 0 3) (by simp) with h1654 | h1654
                                              · linarith only [h1471, h1654, hlam]
                                              · linarith only [h1116, h1654, hlam]
                                            · have p1625_0 := h1625c.1
                                              have p1625_1 := h1625c.2.1
                                              have p1625_2 := h1625c.2.2.1
                                              have p1625_3 := h1625c.2.2.2
                                              linarith only [h1590, hlam, p1625_1]
                                            · have p1625_0 := h1625c.1
                                              have p1625_1 := h1625c.2.1
                                              have p1625_2 := h1625c.2.2.1
                                              have p1625_3 := h1625c.2.2.2
                                              linarith only [hlam, p1625_0]
                                          · rcases h3bigk with h1659c | h1659c | h1659c | h1659c | h1659c | h1659c | h1659c | h1659c | h1659c | h1659c | h1659c | h1659c | h1659c | h1659c | h1659c | h1659c | h1659c | h1659c | h1659c | h1659c | h1659c | h1659c | h1659c | h1659c | h1659c
                                            · have p1659_0 := h1659c.1
                                              have p1659_1 := h1659c.2.1
                                              have p1659_2 := h1659c.2.2.1
                                              have p1659_3 := h1659c.2.2.2
                                              linarith only [hlam, p1659_0]
                                            · have p1659_0 := h1659c.1
                                              have p1659_1 := h1659c.2.1
                                              have p1659_2 := h1659c.2.2.1
                                              have p1659_3 := h1659c.2.2.2
                                              linarith only [h1119, hc13, hc34, hlam, hphi, p1659_1]
                                            · have p1659_0 := h1659c.1
                                              have p1659_1 := h1659c.2.1
                                              have p1659_2 := h1659c.2.2.1
                                              have p1659_3 := h1659c.2.2.2
                                              linarith only [h1119, hc23, hc34, hlam, hphi, p1659_1]
                                            · have p1659_0 := h1659c.1
                                              have p1659_1 := h1659c.2.1
                                              have p1659_2 := h1659c.2.2.1
                                              have p1659_3 := h1659c.2.2.2
                                              linarith only [h1119, hlam, p1659_0]
                                            · have p1659_0 := h1659c.1
                                              have p1659_1 := h1659c.2.1
                                              have p1659_2 := h1659c.2.2.1
                                              have p1659_3 := h1659c.2.2.2
                                              linarith only [h1471, hlam, p1659_0]
                                            · have p1659_0 := h1659c.1
                                              have p1659_1 := h1659c.2.1
                                              have p1659_2 := h1659c.2.2.1
                                              have p1659_3 := h1659c.2.2.2
                                              linarith only [h1115, hlam, p1659_0]
                                            · have p1659_0 := h1659c.1
                                              have p1659_1 := h1659c.2.1
                                              have p1659_2 := h1659c.2.2.1
                                              have p1659_3 := h1659c.2.2.2
                                              linarith only [hlam, p1659_0]
                                            · have p1659_0 := h1659c.1
                                              have p1659_1 := h1659c.2.1
                                              have p1659_2 := h1659c.2.2.1
                                              have p1659_3 := h1659c.2.2.2
                                              linarith only [h0, h1115, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1659_1]
                                            · have p1659_0 := h1659c.1
                                              have p1659_1 := h1659c.2.1
                                              have p1659_2 := h1659c.2.2.1
                                              have p1659_3 := h1659c.2.2.2
                                              linarith only [h1531, hlam, p1659_0]
                                            · have p1659_0 := h1659c.1
                                              have p1659_1 := h1659c.2.1
                                              have p1659_2 := h1659c.2.2.1
                                              have p1659_3 := h1659c.2.2.2
                                              linarith only [h1533, hlam, p1659_0]
                                            · have p1659_0 := h1659c.1
                                              have p1659_1 := h1659c.2.1
                                              have p1659_2 := h1659c.2.2.1
                                              have p1659_3 := h1659c.2.2.2
                                              linarith only [h1116, hlam, p1659_1]
                                            · have p1659_0 := h1659c.1
                                              have p1659_1 := h1659c.2.1
                                              have p1659_2 := h1659c.2.2.1
                                              have p1659_3 := h1659c.2.2.2
                                              linarith only [h1528, hlam, p1659_1]
                                            · have p1659_0 := h1659c.1
                                              have p1659_1 := h1659c.2.1
                                              have p1659_2 := h1659c.2.2.1
                                              have p1659_3 := h1659c.2.2.2
                                              linarith only [hlam, p1659_0]
                                            · have p1659_0 := h1659c.1
                                              have p1659_1 := h1659c.2.1
                                              have p1659_2 := h1659c.2.2.1
                                              have p1659_3 := h1659c.2.2.2
                                              linarith only [h1535, hlam, p1659_0]
                                            · have p1659_0 := h1659c.1
                                              have p1659_1 := h1659c.2.1
                                              have p1659_2 := h1659c.2.2.1
                                              have p1659_3 := h1659c.2.2.2
                                              linarith only [h1537, hlam, p1659_0]
                                            · have p1659_0 := h1659c.1
                                              have p1659_1 := h1659c.2.1
                                              have p1659_2 := h1659c.2.2.1
                                              have p1659_3 := h1659c.2.2.2
                                              linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p1659_1, u0ehi7]
                                            · have p1659_0 := h1659c.1
                                              have p1659_1 := h1659c.2.1
                                              have p1659_2 := h1659c.2.2.1
                                              have p1659_3 := h1659c.2.2.2
                                              rcases p1659_3 (m.d 0 3) (by simp) with h1676 | h1676
                                              · linarith only [h1119, h1676, hlam]
                                              · linarith only [h1115, h1676, hlam]
                                            · have p1659_0 := h1659c.1
                                              have p1659_1 := h1659c.2.1
                                              have p1659_2 := h1659c.2.2.1
                                              have p1659_3 := h1659c.2.2.2
                                              rcases p1659_3 (m.d 0 3) (by simp) with h1679 | h1679
                                              · linarith only [h1119, h1679, hlam]
                                              · linarith only [h1116, h1679, hlam]
                                            · have p1659_0 := h1659c.1
                                              have p1659_1 := h1659c.2.1
                                              have p1659_2 := h1659c.2.2.1
                                              have p1659_3 := h1659c.2.2.2
                                              linarith only [hlam, p1659_0]
                                            · have p1659_0 := h1659c.1
                                              have p1659_1 := h1659c.2.1
                                              have p1659_2 := h1659c.2.2.1
                                              have p1659_3 := h1659c.2.2.2
                                              linarith only [h1471, hc34, hlam, hphi, ht01, ht12, ht23, p1659_1, u0ehi7]
                                            · have p1659_0 := h1659c.1
                                              have p1659_1 := h1659c.2.1
                                              have p1659_2 := h1659c.2.2.1
                                              have p1659_3 := h1659c.2.2.2
                                              linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p1659_1, u0ehi7]
                                            · have p1659_0 := h1659c.1
                                              have p1659_1 := h1659c.2.1
                                              have p1659_2 := h1659c.2.2.1
                                              have p1659_3 := h1659c.2.2.2
                                              rcases p1659_3 (m.d 0 3) (by simp) with h1685 | h1685
                                              · linarith only [h1471, h1685, hlam]
                                              · linarith only [h1115, h1685, hlam]
                                            · have p1659_0 := h1659c.1
                                              have p1659_1 := h1659c.2.1
                                              have p1659_2 := h1659c.2.2.1
                                              have p1659_3 := h1659c.2.2.2
                                              rcases p1659_3 (m.d 0 3) (by simp) with h1688 | h1688
                                              · linarith only [h1471, h1688, hlam]
                                              · linarith only [h1116, h1688, hlam]
                                            · have p1659_0 := h1659c.1
                                              have p1659_1 := h1659c.2.1
                                              have p1659_2 := h1659c.2.2.1
                                              have p1659_3 := h1659c.2.2.2
                                              linarith only [h1590, hlam, p1659_1]
                                            · have p1659_0 := h1659c.1
                                              have p1659_1 := h1659c.2.1
                                              have p1659_2 := h1659c.2.2.1
                                              have p1659_3 := h1659c.2.2.2
                                              linarith only [hlam, p1659_0]
                                          · rcases h3bigk with h1693c | h1693c | h1693c | h1693c | h1693c | h1693c | h1693c | h1693c | h1693c | h1693c | h1693c | h1693c | h1693c | h1693c | h1693c | h1693c | h1693c | h1693c | h1693c | h1693c | h1693c | h1693c | h1693c | h1693c | h1693c
                                            · have p1693_0 := h1693c.1
                                              have p1693_1 := h1693c.2.1
                                              have p1693_2 := h1693c.2.2.1
                                              have p1693_3 := h1693c.2.2.2
                                              linarith only [hlam, p1693_0]
                                            · have p1693_0 := h1693c.1
                                              have p1693_1 := h1693c.2.1
                                              have p1693_2 := h1693c.2.2.1
                                              have p1693_3 := h1693c.2.2.2
                                              linarith only [h1119, hc13, hc34, hlam, hphi, p1693_1]
                                            · have p1693_0 := h1693c.1
                                              have p1693_1 := h1693c.2.1
                                              have p1693_2 := h1693c.2.2.1
                                              have p1693_3 := h1693c.2.2.2
                                              linarith only [h1119, hc23, hc34, hlam, hphi, p1693_1]
                                            · have p1693_0 := h1693c.1
                                              have p1693_1 := h1693c.2.1
                                              have p1693_2 := h1693c.2.2.1
                                              have p1693_3 := h1693c.2.2.2
                                              linarith only [h1119, hlam, p1693_0]
                                            · have p1693_0 := h1693c.1
                                              have p1693_1 := h1693c.2.1
                                              have p1693_2 := h1693c.2.2.1
                                              have p1693_3 := h1693c.2.2.2
                                              linarith only [h1471, hlam, p1693_0]
                                            · have p1693_0 := h1693c.1
                                              have p1693_1 := h1693c.2.1
                                              have p1693_2 := h1693c.2.2.1
                                              have p1693_3 := h1693c.2.2.2
                                              linarith only [h1115, hlam, p1693_0]
                                            · have p1693_0 := h1693c.1
                                              have p1693_1 := h1693c.2.1
                                              have p1693_2 := h1693c.2.2.1
                                              have p1693_3 := h1693c.2.2.2
                                              linarith only [hlam, p1693_0]
                                            · have p1693_0 := h1693c.1
                                              have p1693_1 := h1693c.2.1
                                              have p1693_2 := h1693c.2.2.1
                                              have p1693_3 := h1693c.2.2.2
                                              linarith only [h0, h1115, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1693_1]
                                            · have p1693_0 := h1693c.1
                                              have p1693_1 := h1693c.2.1
                                              have p1693_2 := h1693c.2.2.1
                                              have p1693_3 := h1693c.2.2.2
                                              linarith only [h1531, hlam, p1693_0]
                                            · have p1693_0 := h1693c.1
                                              have p1693_1 := h1693c.2.1
                                              have p1693_2 := h1693c.2.2.1
                                              have p1693_3 := h1693c.2.2.2
                                              linarith only [h1533, hlam, p1693_0]
                                            · have p1693_0 := h1693c.1
                                              have p1693_1 := h1693c.2.1
                                              have p1693_2 := h1693c.2.2.1
                                              have p1693_3 := h1693c.2.2.2
                                              linarith only [h1116, hlam, p1693_1]
                                            · have p1693_0 := h1693c.1
                                              have p1693_1 := h1693c.2.1
                                              have p1693_2 := h1693c.2.2.1
                                              have p1693_3 := h1693c.2.2.2
                                              linarith only [h1528, hlam, p1693_1]
                                            · have p1693_0 := h1693c.1
                                              have p1693_1 := h1693c.2.1
                                              have p1693_2 := h1693c.2.2.1
                                              have p1693_3 := h1693c.2.2.2
                                              linarith only [hlam, p1693_0]
                                            · have p1693_0 := h1693c.1
                                              have p1693_1 := h1693c.2.1
                                              have p1693_2 := h1693c.2.2.1
                                              have p1693_3 := h1693c.2.2.2
                                              linarith only [h1535, hlam, p1693_0]
                                            · have p1693_0 := h1693c.1
                                              have p1693_1 := h1693c.2.1
                                              have p1693_2 := h1693c.2.2.1
                                              have p1693_3 := h1693c.2.2.2
                                              linarith only [h1537, hlam, p1693_0]
                                            · have p1693_0 := h1693c.1
                                              have p1693_1 := h1693c.2.1
                                              have p1693_2 := h1693c.2.2.1
                                              have p1693_3 := h1693c.2.2.2
                                              linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p1693_1, u0ehi7]
                                            · have p1693_0 := h1693c.1
                                              have p1693_1 := h1693c.2.1
                                              have p1693_2 := h1693c.2.2.1
                                              have p1693_3 := h1693c.2.2.2
                                              rcases p1693_3 (m.d 0 3) (by simp) with h1710 | h1710
                                              · linarith only [h1119, h1710, hlam]
                                              · linarith only [h1115, h1710, hlam]
                                            · have p1693_0 := h1693c.1
                                              have p1693_1 := h1693c.2.1
                                              have p1693_2 := h1693c.2.2.1
                                              have p1693_3 := h1693c.2.2.2
                                              rcases p1693_3 (m.d 0 3) (by simp) with h1713 | h1713
                                              · linarith only [h1119, h1713, hlam]
                                              · linarith only [h1116, h1713, hlam]
                                            · have p1693_0 := h1693c.1
                                              have p1693_1 := h1693c.2.1
                                              have p1693_2 := h1693c.2.2.1
                                              have p1693_3 := h1693c.2.2.2
                                              linarith only [hlam, p1693_0]
                                            · have p1693_0 := h1693c.1
                                              have p1693_1 := h1693c.2.1
                                              have p1693_2 := h1693c.2.2.1
                                              have p1693_3 := h1693c.2.2.2
                                              linarith only [h1471, hc34, hlam, hphi, ht01, ht12, ht23, p1693_1, u0ehi7]
                                            · have p1693_0 := h1693c.1
                                              have p1693_1 := h1693c.2.1
                                              have p1693_2 := h1693c.2.2.1
                                              have p1693_3 := h1693c.2.2.2
                                              linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p1693_1, u0ehi7]
                                            · have p1693_0 := h1693c.1
                                              have p1693_1 := h1693c.2.1
                                              have p1693_2 := h1693c.2.2.1
                                              have p1693_3 := h1693c.2.2.2
                                              rcases p1693_3 (m.d 0 3) (by simp) with h1719 | h1719
                                              · linarith only [h1471, h1719, hlam]
                                              · linarith only [h1115, h1719, hlam]
                                            · have p1693_0 := h1693c.1
                                              have p1693_1 := h1693c.2.1
                                              have p1693_2 := h1693c.2.2.1
                                              have p1693_3 := h1693c.2.2.2
                                              rcases p1693_3 (m.d 0 3) (by simp) with h1722 | h1722
                                              · linarith only [h1471, h1722, hlam]
                                              · linarith only [h1116, h1722, hlam]
                                            · have p1693_0 := h1693c.1
                                              have p1693_1 := h1693c.2.1
                                              have p1693_2 := h1693c.2.2.1
                                              have p1693_3 := h1693c.2.2.2
                                              linarith only [h1590, hlam, p1693_1]
                                            · have p1693_0 := h1693c.1
                                              have p1693_1 := h1693c.2.1
                                              have p1693_2 := h1693c.2.2.1
                                              have p1693_3 := h1693c.2.2.2
                                              linarith only [hlam, p1693_0]
                                  · linarith only [h1530, h1615, hlam]
                                · linarith only [h1614, hlam, p1591_0]
                              · have p1591_0 := h1591c.1
                                have p1591_1 := h1591c.2.1
                                have p1591_2 := h1591c.2.2.1
                                have p1591_3 := h1591c.2.2.2
                                linarith only [h0, hc12, hlam, hphi, ht01, p1591_1, u0ehi5]
                              · have p1591_0 := h1591c.1
                                have p1591_1 := h1591c.2.1
                                have p1591_2 := h1591c.2.2.1
                                have p1591_3 := h1591c.2.2.2
                                linarith only [hlam, p1591_0]
                              · have p1591_0 := h1591c.1
                                have p1591_1 := h1591c.2.1
                                have p1591_2 := h1591c.2.2.1
                                have p1591_3 := h1591c.2.2.2
                                rcases p1591_3 (m.d 0 2) (by simp) with h1731 | h1731
                                · linarith only [h0, h1731, hlam]
                                · linarith only [h1116, h1731, hlam]
                              · have p1591_0 := h1591c.1
                                have p1591_1 := h1591c.2.1
                                have p1591_2 := h1591c.2.2.1
                                have p1591_3 := h1591c.2.2.2
                                rcases p1591_3 (m.d 0 2) (by simp) with h1734 | h1734
                                · linarith only [h0, h1734, hlam]
                                · linarith only [h1117, h1734, hlam]
                              · have p1591_0 := h1591c.1
                                have p1591_1 := h1591c.2.1
                                have p1591_2 := h1591c.2.2.1
                                have p1591_3 := h1591c.2.2.2
                                rcases p1591_3 (m.d 0 2) (by simp) with h1737 | h1737
                                · linarith only [h0, h1737, hlam]
                                · linarith only [h1118, h1737, hlam]
                              · have p1591_0 := h1591c.1
                                have p1591_1 := h1591c.2.1
                                have p1591_2 := h1591c.2.2.1
                                have p1591_3 := h1591c.2.2.2
                                linarith only [h1116, hlam, p1591_0]
                              · have p1591_0 := h1591c.1
                                have p1591_1 := h1591c.2.1
                                have p1591_2 := h1591c.2.2.1
                                have p1591_3 := h1591c.2.2.2
                                linarith only [h1528, hlam, p1591_0]
                              · have p1591_0 := h1591c.1
                                have p1591_1 := h1591c.2.1
                                have p1591_2 := h1591c.2.2.1
                                have p1591_3 := h1591c.2.2.2
                                linarith only [hlam, p1591_0]
                              · have p1591_0 := h1591c.1
                                have p1591_1 := h1591c.2.1
                                have p1591_2 := h1591c.2.2.1
                                have p1591_3 := h1591c.2.2.2
                                linarith only [h1535, hlam, p1591_1]
                              · have p1591_0 := h1591c.1
                                have p1591_1 := h1591c.2.1
                                have p1591_2 := h1591c.2.2.1
                                have p1591_3 := h1591c.2.2.2
                                linarith only [h1537, hlam, p1591_1]
                              · have p1591_0 := h1591c.1
                                have p1591_1 := h1591c.2.1
                                have p1591_2 := h1591c.2.2.1
                                have p1591_3 := h1591c.2.2.2
                                linarith only [h1117, hlam, p1591_0]
                              · have p1591_0 := h1591c.1
                                have p1591_1 := h1591c.2.1
                                have p1591_2 := h1591c.2.2.1
                                have p1591_3 := h1591c.2.2.2
                                linarith only [h1529, hlam, p1591_0]
                              · have p1591_0 := h1591c.1
                                have p1591_1 := h1591c.2.1
                                have p1591_2 := h1591c.2.2.1
                                have p1591_3 := h1591c.2.2.2
                                linarith only [h1117, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1591_1, u0elo1]
                              · have p1591_0 := h1591c.1
                                have p1591_1 := h1591c.2.1
                                have p1591_2 := h1591c.2.2.1
                                have p1591_3 := h1591c.2.2.2
                                linarith only [hlam, p1591_0]
                              · have p1591_0 := h1591c.1
                                have p1591_1 := h1591c.2.1
                                have p1591_2 := h1591c.2.2.1
                                have p1591_3 := h1591c.2.2.2
                                linarith only [h1539, hlam, p1591_0]
                              · have p1591_0 := h1591c.1
                                have p1591_1 := h1591c.2.1
                                have p1591_2 := h1591c.2.2.1
                                have p1591_3 := h1591c.2.2.2
                                linarith only [h1118, hlam, p1591_0]
                              · have p1591_0 := h1591c.1
                                have p1591_1 := h1591c.2.1
                                have p1591_2 := h1591c.2.2.1
                                have p1591_3 := h1591c.2.2.2
                                linarith only [h1530, hlam, p1591_0]
                              · have p1591_0 := h1591c.1
                                have p1591_1 := h1591c.2.1
                                have p1591_2 := h1591c.2.2.1
                                have p1591_3 := h1591c.2.2.2
                                linarith only [h1118, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1591_1, u0elo1]
                              · have p1591_0 := h1591c.1
                                have p1591_1 := h1591c.2.1
                                have p1591_2 := h1591c.2.2.1
                                have p1591_3 := h1591c.2.2.2
                                linarith only [h1118, hc24, hlam, hphi, ht0b, ht45, ht5b, p1591_1, u0elo1]
                              · have p1591_0 := h1591c.1
                                have p1591_1 := h1591c.2.1
                                have p1591_2 := h1591c.2.2.1
                                have p1591_3 := h1591c.2.2.2
                                linarith only [hlam, p1591_0]
                            · linarith only [h1119, h1590, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                · linarith only [h0, h1118, h1530, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h1115, h1529, hc24, hlam, hphi, ht01, ht12, u0ehi7]
            · linarith only [h0, h1115, h1528, hc23, hlam, hphi, ht01, ht12, u0ehi7]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1759 | h1759
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1760 | h1760
          · linarith only [h0, h1115, h1118, h1760, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1762 | h1762
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1763 | h1763
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1764 | h1764
                · linarith only [h0, h1118, h1764, hc12, hlam, hphi, ht01, u0ehi5]
                · linarith only [h0, h1115, h1759, h1764, hc25, hlam, hphi, ht01, ht12, u0ehi8]
              · linarith only [h0, h1115, h1117, h1759, h1763, hlam, hphi, u0ehi8, u0elo1]
            · linarith only [h0, h1115, h1759, h1762, hc23, hlam, hphi, ht01, ht12, u0ehi8]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1769 | h1769
          · linarith only [h0, h1115, h1118, h1769, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1771 | h1771
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1772 | h1772
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1773 | h1773
                · linarith only [h0, h1118, h1773, hc12, hlam, hphi, ht01, u0ehi5]
                · linarith only [h0, h1115, h1773, hc25, hlam, hphi, ht01, ht12, u0ehi7]
              · linarith only [h0, h1115, h1117, h1772, hlam, hphi, u0ehi7, u0elo1]
            · linarith only [h0, h1115, h1771, hc23, hlam, hphi, ht01, ht12, u0ehi7]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1778 | h1778
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1779 | h1779
        · linarith only [h0, h1115, h1117, h1779, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1781 | h1781
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1782 | h1782
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1783 | h1783
              · linarith only [h0, h1117, h1783, hc12, hlam, hphi, ht01, u0ehi5]
              · linarith only [h0, h1115, h1781, h1783, hc24, hlam, hphi, ht01, ht12, u0ehi9]
            · linarith only [h0, h1115, h1781, h1782, hc23, hlam, hphi, ht01, ht12, u0ehi9]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1787 | h1787
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1788 | h1788
              · linarith only [h0, h1117, h1788, hc12, hlam, hphi, ht01, u0ehi5]
              · linarith only [h0, h1115, h1788, hc24, hlam, hphi, ht01, ht12, u0ehi7]
            · linarith only [h0, h1115, h1787, hc23, hlam, hphi, ht01, ht12, u0ehi7]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1792 | h1792
        · linarith only [h0, h1115, h1117, h1792, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1794 | h1794
          · linarith only [h0, h1115, h1778, h1794, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1796 | h1796
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1797 | h1797
              · linarith only [h0, h1115, h1117, h1797, hc12, hlam, hphi, ht01, u0ehi7]
              · linarith only [h0, h1115, h1797, hc24, hlam, hphi, ht01, ht12, u0ehi7]
            · linarith only [h0, h1115, h1796, hc23, hlam, hphi, ht01, ht12, u0ehi7]
  · linarith only [h0, h1115, h1116, hlam]

end R2N4
