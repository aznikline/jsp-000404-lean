import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_30S15

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7534000 in
set_option maxHeartbeats 7534000 in
theorem r1l7_20_12_13_15_H_L_L_I_L_I_L_I_s0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h0elo := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1106 | h1106
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1107 | h1107
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1108 | h1108
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1109 | h1109
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1110 | h1110
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1111 | h1111
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1112 | h1112
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1113 | h1113
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1114 | h1114
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1115 | h1115
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1116 | h1116
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1117 | h1117
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1118 | h1118
                          · linarith only [h1106, h1118, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h0, h1106, h1112, h1118, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h0, h1111, h1117, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h1106, h1110, h1115, h1116, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1109, h1115, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1124 | h1124
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1125 | h1125
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1126 | h1126
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1127 | h1127
                          · linarith only [h1106, h1127, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h1112, h1127, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h1111, h1126, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h1106, h1110, h1124, h1125, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1109, h1124, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1133 | h1133
                  · linarith only [h1112, h1113, h1133, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1135 | h1135
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1136 | h1136
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1137 | h1137
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1138 | h1138
                          · linarith only [h1106, h1138, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h0, h1106, h1112, h1135, h1138, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h0, h1111, h1137, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h1106, h1110, h1135, h1136, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1109, h1135, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1144 | h1144
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1145 | h1145
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1146 | h1146
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1147 | h1147
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1148 | h1148
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1149 | h1149
                          · linarith only [h1106, h1112, h1149, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1151 | h1151
                            · linarith only [h0, h1107, h1149, h1151, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                            · linarith only [h1144, h1151, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h1111, h1148, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h1106, h1110, h1146, h1147, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1109, h1146, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h1112, h1144, h1145, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1158 | h1158
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1159 | h1159
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1160 | h1160
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1161 | h1161
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1162 | h1162
                          · linarith only [h1106, h1112, h1162, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1164 | h1164
                            · linarith only [h0, h1106, h1144, h1164, hc05, hlam, hphi, ht0b, ht5b, u0elo1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1166 | h1166
                              · linarith only [h0, h1107, h1166, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                              · linarith only [h0, h1107, h1158, h1162, h1166, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h0, h1111, h1161, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h1110, h1160, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1106, h1109, h1159, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1172 | h1172
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1173 | h1173
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1174 | h1174
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1175 | h1175
                          · linarith only [h1106, h1112, h1175, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1177 | h1177
                            · linarith only [h1106, h1144, h1177, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1179 | h1179
                              · linarith only [h1107, h1158, h1179, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1181 | h1181
                                · linarith only [h1106, h1112, h1172, h1181, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1183 | h1183
                                  · linarith only [h0, h1108, h1144, h1172, h1175, h1179, h1183, hc05, hlam, hphi, ht0b, ht5b, u0elo1]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1185 | h1185
                                    · linarith only [h1107, h1110, h1158, h1172, h1175, h1185, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1187 | h1187
                                      · rcases h2bigk with h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c | h1188c
                                        · have p1188_0 := h1188c.1
                                          have p1188_1 := h1188c.2.1
                                          have p1188_2 := h1188c.2.2.1
                                          have p1188_3 := h1188c.2.2.2
                                          linarith only [hlam, p1188_0]
                                        · have p1188_0 := h1188c.1
                                          have p1188_1 := h1188c.2.1
                                          have p1188_2 := h1188c.2.2.1
                                          have p1188_3 := h1188c.2.2.2
                                          linarith only [h0, hlam, p1188_1]
                                        · have p1188_0 := h1188c.1
                                          have p1188_1 := h1188c.2.1
                                          have p1188_2 := h1188c.2.2.1
                                          have p1188_3 := h1188c.2.2.2
                                          linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1188_1, u0elo1]
                                        · have p1188_0 := h1188c.1
                                          have p1188_1 := h1188c.2.1
                                          have p1188_2 := h1188c.2.2.1
                                          have p1188_3 := h1188c.2.2.2
                                          linarith only [hc24, hlam, hphi, ht0b, ht45, ht5b, p1188_1, u0elo1]
                                        · have p1188_0 := h1188c.1
                                          have p1188_1 := h1188c.2.1
                                          have p1188_2 := h1188c.2.2.1
                                          have p1188_3 := h1188c.2.2.2
                                          linarith only [hc25, hlam, hphi, ht0b, ht5b, p1188_1, u0elo1]
                                        · have p1188_0 := h1188c.1
                                          have p1188_1 := h1188c.2.1
                                          have p1188_2 := h1188c.2.2.1
                                          have p1188_3 := h1188c.2.2.2
                                          rcases p1188_3 (m.d 0 2) (by simp) with h1194 | h1194
                                          · linarith only [h0, h1194, hlam]
                                          · rcases p1188_3 (m.d 1 2) (by simp) with h1196 | h1196
                                            · rcases p1188_3 (m.d 2 3) (by simp) with h1197 | h1197
                                              · linarith only [h1172, h1197, hlam]
                                              · rcases p1188_3 (m.d 2 4) (by simp) with h1199 | h1199
                                                · linarith only [h1173, h1199, hlam]
                                                · rcases p1188_3 (m.d 2 5) (by simp) with h1201 | h1201
                                                  · linarith only [h1174, h1201, hlam]
                                                  · rcases h3bigk with h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c
                                                    · have p1203_0 := h1203c.1
                                                      have p1203_1 := h1203c.2.1
                                                      have p1203_2 := h1203c.2.2.1
                                                      have p1203_3 := h1203c.2.2.2
                                                      linarith only [hlam, p1203_0]
                                                    · have p1203_0 := h1203c.1
                                                      have p1203_1 := h1203c.2.1
                                                      have p1203_2 := h1203c.2.2.1
                                                      have p1203_3 := h1203c.2.2.2
                                                      linarith only [h1172, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1203_1, u0elo2]
                                                    · have p1203_0 := h1203c.1
                                                      have p1203_1 := h1203c.2.1
                                                      have p1203_2 := h1203c.2.2.1
                                                      have p1203_3 := h1203c.2.2.2
                                                      linarith only [h1106, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1203_1, u0elo0]
                                                    · have p1203_0 := h1203c.1
                                                      have p1203_1 := h1203c.2.1
                                                      have p1203_2 := h1203c.2.2.1
                                                      have p1203_3 := h1203c.2.2.2
                                                      linarith only [h1112, hlam, p1203_0]
                                                    · have p1203_0 := h1203c.1
                                                      have p1203_1 := h1203c.2.1
                                                      have p1203_2 := h1203c.2.2.1
                                                      have p1203_3 := h1203c.2.2.2
                                                      linarith only [h1144, hlam, p1203_0]
                                                    · have p1203_0 := h1203c.1
                                                      have p1203_1 := h1203c.2.1
                                                      have p1203_2 := h1203c.2.2.1
                                                      have p1203_3 := h1203c.2.2.2
                                                      linarith only [h1106, hlam, p1203_0]
                                                    · have p1203_0 := h1203c.1
                                                      have p1203_1 := h1203c.2.1
                                                      have p1203_2 := h1203c.2.2.1
                                                      have p1203_3 := h1203c.2.2.2
                                                      linarith only [hlam, p1203_0]
                                                    · have p1203_0 := h1203c.1
                                                      have p1203_1 := h1203c.2.1
                                                      have p1203_2 := h1203c.2.2.1
                                                      have p1203_3 := h1203c.2.2.2
                                                      linarith only [h1107, h1175, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1203_1, u0elo3]
                                                    · have p1203_0 := h1203c.1
                                                      have p1203_1 := h1203c.2.1
                                                      have p1203_2 := h1203c.2.2.1
                                                      have p1203_3 := h1203c.2.2.2
                                                      linarith only [h1175, hlam, p1203_0]
                                                    · have p1203_0 := h1203c.1
                                                      have p1203_1 := h1203c.2.1
                                                      have p1203_2 := h1203c.2.2.1
                                                      have p1203_3 := h1203c.2.2.2
                                                      linarith only [h1177, hlam, p1203_0]
                                                    · have p1203_0 := h1203c.1
                                                      have p1203_1 := h1203c.2.1
                                                      have p1203_2 := h1203c.2.2.1
                                                      have p1203_3 := h1203c.2.2.2
                                                      linarith only [h1109, hlam, p1203_0]
                                                    · have p1203_0 := h1203c.1
                                                      have p1203_1 := h1203c.2.1
                                                      have p1203_2 := h1203c.2.2.1
                                                      have p1203_3 := h1203c.2.2.2
                                                      linarith only [h1172, hlam, p1203_0]
                                                    · have p1203_0 := h1203c.1
                                                      have p1203_1 := h1203c.2.1
                                                      have p1203_2 := h1203c.2.2.1
                                                      have p1203_3 := h1203c.2.2.2
                                                      linarith only [hlam, p1203_0]
                                                    · have p1203_0 := h1203c.1
                                                      have p1203_1 := h1203c.2.1
                                                      have p1203_2 := h1203c.2.2.1
                                                      have p1203_3 := h1203c.2.2.2
                                                      linarith only [h1181, hlam, p1203_0]
                                                    · have p1203_0 := h1203c.1
                                                      have p1203_1 := h1203c.2.1
                                                      have p1203_2 := h1203c.2.2.1
                                                      have p1203_3 := h1203c.2.2.2
                                                      linarith only [h1183, hlam, p1203_0]
                                                    · have p1203_0 := h1203c.1
                                                      have p1203_1 := h1203c.2.1
                                                      have p1203_2 := h1203c.2.2.1
                                                      have p1203_3 := h1203c.2.2.2
                                                      rcases p1203_3 (m.d 0 3) (by simp) with h1219 | h1219
                                                      · linarith only [h1219, hlam, p1203_0]
                                                      · rcases p1203_3 (m.d 1 3) (by simp) with h1221 | h1221
                                                        · linarith only [h1175, h1221, hlam]
                                                        · rcases p1203_3 (m.d 2 3) (by simp) with h1223 | h1223
                                                          · linarith only [h1181, h1223, hlam]
                                                          · rcases p1203_3 (m.d 3 4) (by simp) with h1225 | h1225
                                                            · rcases p1203_3 (m.d 3 5) (by simp) with h1226 | h1226
                                                              · linarith only [h1187, h1226, hlam]
                                                              · linarith only [h1144, h1226, hlam]
                                                            · linarith only [h1225, hlam, p1203_0]
                                                    · have p1203_0 := h1203c.1
                                                      have p1203_1 := h1203c.2.1
                                                      have p1203_2 := h1203c.2.2.1
                                                      have p1203_3 := h1203c.2.2.2
                                                      rcases p1203_3 (m.d 0 3) (by simp) with h1230 | h1230
                                                      · linarith only [h1112, h1230, hlam]
                                                      · linarith only [h1106, h1230, hlam]
                                                    · have p1203_0 := h1203c.1
                                                      have p1203_1 := h1203c.2.1
                                                      have p1203_2 := h1203c.2.2.1
                                                      have p1203_3 := h1203c.2.2.2
                                                      rcases p1203_3 (m.d 0 3) (by simp) with h1233 | h1233
                                                      · linarith only [h1112, h1233, hlam]
                                                      · linarith only [h1109, h1233, hlam]
                                                    · have p1203_0 := h1203c.1
                                                      have p1203_1 := h1203c.2.1
                                                      have p1203_2 := h1203c.2.2.1
                                                      have p1203_3 := h1203c.2.2.2
                                                      linarith only [hlam, p1203_0]
                                                    · have p1203_0 := h1203c.1
                                                      have p1203_1 := h1203c.2.1
                                                      have p1203_2 := h1203c.2.2.1
                                                      have p1203_3 := h1203c.2.2.2
                                                      linarith only [h1112, h1158, h1187, hc03, hc34, hlam, hphi, p1203_1]
                                                    · have p1203_0 := h1203c.1
                                                      have p1203_1 := h1203c.2.1
                                                      have p1203_2 := h1203c.2.2.1
                                                      have p1203_3 := h1203c.2.2.2
                                                      rcases p1203_3 (m.d 0 3) (by simp) with h1238 | h1238
                                                      · linarith only [h1238, hlam, p1203_0]
                                                      · rcases p1203_3 (m.d 1 3) (by simp) with h1240 | h1240
                                                        · linarith only [h1177, h1240, hlam]
                                                        · rcases p1203_3 (m.d 2 3) (by simp) with h1242 | h1242
                                                          · linarith only [h1183, h1242, hlam]
                                                          · rcases p1203_3 (m.d 3 4) (by simp) with h1244 | h1244
                                                            · rcases p1203_3 (m.d 3 5) (by simp) with h1245 | h1245
                                                              · rcases h5bigk with h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c
                                                                · have p1246_0 := h1246c.1
                                                                  have p1246_1 := h1246c.2.1
                                                                  have p1246_2 := h1246c.2.2.1
                                                                  have p1246_3 := h1246c.2.2.2
                                                                  linarith only [hlam, p1246_0]
                                                                · have p1246_0 := h1246c.1
                                                                  have p1246_1 := h1246c.2.1
                                                                  have p1246_2 := h1246c.2.2.1
                                                                  have p1246_3 := h1246c.2.2.2
                                                                  linarith only [h0, h1108, h1173, h1179, h1181, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1188_1, p1246_1]
                                                                · have p1246_0 := h1246c.1
                                                                  have p1246_1 := h1246c.2.1
                                                                  have p1246_2 := h1246c.2.2.1
                                                                  have p1246_3 := h1246c.2.2.2
                                                                  linarith only [h0, h1108, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1188_1, p1246_1]
                                                                · have p1246_0 := h1246c.1
                                                                  have p1246_1 := h1246c.2.1
                                                                  have p1246_2 := h1246c.2.2.1
                                                                  have p1246_3 := h1246c.2.2.2
                                                                  linarith only [h1144, hlam, p1246_1]
                                                                · have p1246_0 := h1246c.1
                                                                  have p1246_1 := h1246c.2.1
                                                                  have p1246_2 := h1246c.2.2.1
                                                                  have p1246_3 := h1246c.2.2.2
                                                                  linarith only [h1158, hlam, p1246_1]
                                                                · have p1246_0 := h1246c.1
                                                                  have p1246_1 := h1246c.2.1
                                                                  have p1246_2 := h1246c.2.2.1
                                                                  have p1246_3 := h1246c.2.2.2
                                                                  linarith only [h1108, hlam, p1246_0]
                                                                · have p1246_0 := h1246c.1
                                                                  have p1246_1 := h1246c.2.1
                                                                  have p1246_2 := h1246c.2.2.1
                                                                  have p1246_3 := h1246c.2.2.2
                                                                  linarith only [hlam, p1246_0]
                                                                · have p1246_0 := h1246c.1
                                                                  have p1246_1 := h1246c.2.1
                                                                  have p1246_2 := h1246c.2.2.1
                                                                  have p1246_3 := h1246c.2.2.2
                                                                  linarith only [h0, h1108, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1188_1, p1246_1]
                                                                · have p1246_0 := h1246c.1
                                                                  have p1246_1 := h1246c.2.1
                                                                  have p1246_2 := h1246c.2.2.1
                                                                  have p1246_3 := h1246c.2.2.2
                                                                  linarith only [h1177, hlam, p1246_1]
                                                                · have p1246_0 := h1246c.1
                                                                  have p1246_1 := h1246c.2.1
                                                                  have p1246_2 := h1246c.2.2.1
                                                                  have p1246_3 := h1246c.2.2.2
                                                                  linarith only [h1179, hlam, p1246_1]
                                                                · have p1246_0 := h1246c.1
                                                                  have p1246_1 := h1246c.2.1
                                                                  have p1246_2 := h1246c.2.2.1
                                                                  have p1246_3 := h1246c.2.2.2
                                                                  linarith only [h1111, hlam, p1246_1]
                                                                · have p1246_0 := h1246c.1
                                                                  have p1246_1 := h1246c.2.1
                                                                  have p1246_2 := h1246c.2.2.1
                                                                  have p1246_3 := h1246c.2.2.2
                                                                  linarith only [h1174, hlam, p1246_1]
                                                                · have p1246_0 := h1246c.1
                                                                  have p1246_1 := h1246c.2.1
                                                                  have p1246_2 := h1246c.2.2.1
                                                                  have p1246_3 := h1246c.2.2.2
                                                                  linarith only [hlam, p1246_0]
                                                                · have p1246_0 := h1246c.1
                                                                  have p1246_1 := h1246c.2.1
                                                                  have p1246_2 := h1246c.2.2.1
                                                                  have p1246_3 := h1246c.2.2.2
                                                                  linarith only [h1183, hlam, p1246_1]
                                                                · have p1246_0 := h1246c.1
                                                                  have p1246_1 := h1246c.2.1
                                                                  have p1246_2 := h1246c.2.2.1
                                                                  have p1246_3 := h1246c.2.2.2
                                                                  linarith only [h1185, hlam, p1246_1]
                                                                · have p1246_0 := h1246c.1
                                                                  have p1246_1 := h1246c.2.1
                                                                  have p1246_2 := h1246c.2.2.1
                                                                  have p1246_3 := h1246c.2.2.2
                                                                  rcases p1246_3 (m.d 0 5) (by simp) with h1262 | h1262
                                                                  · linarith only [h1144, h1262, hlam]
                                                                  · rcases p1246_3 (m.d 1 5) (by simp) with h1264 | h1264
                                                                    · linarith only [h1177, h1264, hlam]
                                                                    · rcases p1246_3 (m.d 2 5) (by simp) with h1266 | h1266
                                                                      · linarith only [h1183, h1266, hlam]
                                                                      · rcases p1246_3 (m.d 3 5) (by simp) with h1268 | h1268
                                                                        · rcases p1246_3 (m.d 4 5) (by simp) with h1269 | h1269
                                                                          · linarith only [h1187, h1269, hlam]
                                                                          · linarith only [h1158, h1269, hlam]
                                                                        · linarith only [h1144, h1268, hlam]
                                                                · have p1246_0 := h1246c.1
                                                                  have p1246_1 := h1246c.2.1
                                                                  have p1246_2 := h1246c.2.2.1
                                                                  have p1246_3 := h1246c.2.2.2
                                                                  rcases p1246_3 (m.d 0 5) (by simp) with h1273 | h1273
                                                                  · linarith only [h1144, h1273, hlam]
                                                                  · linarith only [h1108, h1273, hlam]
                                                                · have p1246_0 := h1246c.1
                                                                  have p1246_1 := h1246c.2.1
                                                                  have p1246_2 := h1246c.2.2.1
                                                                  have p1246_3 := h1246c.2.2.2
                                                                  rcases p1246_3 (m.d 0 5) (by simp) with h1276 | h1276
                                                                  · linarith only [h1144, h1276, hlam]
                                                                  · linarith only [h1111, h1276, hlam]
                                                                · have p1246_0 := h1246c.1
                                                                  have p1246_1 := h1246c.2.1
                                                                  have p1246_2 := h1246c.2.2.1
                                                                  have p1246_3 := h1246c.2.2.2
                                                                  linarith only [hlam, p1246_0]
                                                                · have p1246_0 := h1246c.1
                                                                  have p1246_1 := h1246c.2.1
                                                                  have p1246_2 := h1246c.2.2.1
                                                                  have p1246_3 := h1246c.2.2.2
                                                                  linarith only [h1107, h1158, h1173, h1181, h1187, hc23, hc34, hlam, hphi, p1246_1]
                                                                · have p1246_0 := h1246c.1
                                                                  have p1246_1 := h1246c.2.1
                                                                  have p1246_2 := h1246c.2.2.1
                                                                  have p1246_3 := h1246c.2.2.2
                                                                  linarith only [h1107, h1158, h1173, h1181, h1187, hc23, hc34, hlam, hphi, p1246_1]
                                                                · have p1246_0 := h1246c.1
                                                                  have p1246_1 := h1246c.2.1
                                                                  have p1246_2 := h1246c.2.2.1
                                                                  have p1246_3 := h1246c.2.2.2
                                                                  linarith only [h1174, h1181, h1185, h1187, hc23, hc34, hlam, hphi, p1246_1]
                                                                · have p1246_0 := h1246c.1
                                                                  have p1246_1 := h1246c.2.1
                                                                  have p1246_2 := h1246c.2.2.1
                                                                  have p1246_3 := h1246c.2.2.2
                                                                  linarith only [h1181, h1185, h1187, hc23, hc34, hlam, hphi, p1246_1]
                                                                · have p1246_0 := h1246c.1
                                                                  have p1246_1 := h1246c.2.1
                                                                  have p1246_2 := h1246c.2.2.1
                                                                  have p1246_3 := h1246c.2.2.2
                                                                  linarith only [h1187, hlam, p1246_0]
                                                                · have p1246_0 := h1246c.1
                                                                  have p1246_1 := h1246c.2.1
                                                                  have p1246_2 := h1246c.2.2.1
                                                                  have p1246_3 := h1246c.2.2.2
                                                                  linarith only [hlam, p1246_0]
                                                              · linarith only [h1245, hlam, p1203_0]
                                                            · linarith only [h1112, h1244, hlam]
                                                    · have p1203_0 := h1203c.1
                                                      have p1203_1 := h1203c.2.1
                                                      have p1203_2 := h1203c.2.2.1
                                                      have p1203_3 := h1203c.2.2.2
                                                      rcases p1203_3 (m.d 0 3) (by simp) with h1288 | h1288
                                                      · linarith only [h1144, h1288, hlam]
                                                      · linarith only [h1106, h1288, hlam]
                                                    · have p1203_0 := h1203c.1
                                                      have p1203_1 := h1203c.2.1
                                                      have p1203_2 := h1203c.2.2.1
                                                      have p1203_3 := h1203c.2.2.2
                                                      rcases p1203_3 (m.d 0 3) (by simp) with h1291 | h1291
                                                      · linarith only [h1144, h1291, hlam]
                                                      · linarith only [h1109, h1291, hlam]
                                                    · have p1203_0 := h1203c.1
                                                      have p1203_1 := h1203c.2.1
                                                      have p1203_2 := h1203c.2.2.1
                                                      have p1203_3 := h1203c.2.2.2
                                                      linarith only [h1187, hlam, p1203_0]
                                                    · have p1203_0 := h1203c.1
                                                      have p1203_1 := h1203c.2.1
                                                      have p1203_2 := h1203c.2.2.1
                                                      have p1203_3 := h1203c.2.2.2
                                                      linarith only [hlam, p1203_0]
                                            · linarith only [h0, h1196, hlam]
                                        · have p1188_0 := h1188c.1
                                          have p1188_1 := h1188c.2.1
                                          have p1188_2 := h1188c.2.2.1
                                          have p1188_3 := h1188c.2.2.2
                                          linarith only [hlam, p1188_0]
                                        · have p1188_0 := h1188c.1
                                          have p1188_1 := h1188c.2.1
                                          have p1188_2 := h1188c.2.2.1
                                          have p1188_3 := h1188c.2.2.2
                                          rcases p1188_3 (m.d 0 2) (by simp) with h1298 | h1298
                                          · linarith only [h0, h1298, hlam]
                                          · linarith only [h1109, h1298, hlam]
                                        · have p1188_0 := h1188c.1
                                          have p1188_1 := h1188c.2.1
                                          have p1188_2 := h1188c.2.2.1
                                          have p1188_3 := h1188c.2.2.2
                                          rcases p1188_3 (m.d 0 2) (by simp) with h1301 | h1301
                                          · linarith only [h0, h1301, hlam]
                                          · linarith only [h1110, h1301, hlam]
                                        · have p1188_0 := h1188c.1
                                          have p1188_1 := h1188c.2.1
                                          have p1188_2 := h1188c.2.2.1
                                          have p1188_3 := h1188c.2.2.2
                                          rcases p1188_3 (m.d 0 2) (by simp) with h1304 | h1304
                                          · linarith only [h0, h1304, hlam]
                                          · linarith only [h1111, h1304, hlam]
                                        · have p1188_0 := h1188c.1
                                          have p1188_1 := h1188c.2.1
                                          have p1188_2 := h1188c.2.2.1
                                          have p1188_3 := h1188c.2.2.2
                                          linarith only [h1109, hlam, p1188_0]
                                        · have p1188_0 := h1188c.1
                                          have p1188_1 := h1188c.2.1
                                          have p1188_2 := h1188c.2.2.1
                                          have p1188_3 := h1188c.2.2.2
                                          linarith only [h1172, hlam, p1188_0]
                                        · have p1188_0 := h1188c.1
                                          have p1188_1 := h1188c.2.1
                                          have p1188_2 := h1188c.2.2.1
                                          have p1188_3 := h1188c.2.2.2
                                          linarith only [hlam, p1188_0]
                                        · have p1188_0 := h1188c.1
                                          have p1188_1 := h1188c.2.1
                                          have p1188_2 := h1188c.2.2.1
                                          have p1188_3 := h1188c.2.2.2
                                          linarith only [h1181, hlam, p1188_0]
                                        · have p1188_0 := h1188c.1
                                          have p1188_1 := h1188c.2.1
                                          have p1188_2 := h1188c.2.2.1
                                          have p1188_3 := h1188c.2.2.2
                                          linarith only [h1183, hlam, p1188_0]
                                        · have p1188_0 := h1188c.1
                                          have p1188_1 := h1188c.2.1
                                          have p1188_2 := h1188c.2.2.1
                                          have p1188_3 := h1188c.2.2.2
                                          linarith only [h1110, hlam, p1188_0]
                                        · have p1188_0 := h1188c.1
                                          have p1188_1 := h1188c.2.1
                                          have p1188_2 := h1188c.2.2.1
                                          have p1188_3 := h1188c.2.2.2
                                          linarith only [h1173, hlam, p1188_0]
                                        · have p1188_0 := h1188c.1
                                          have p1188_1 := h1188c.2.1
                                          have p1188_2 := h1188c.2.2.1
                                          have p1188_3 := h1188c.2.2.2
                                          linarith only [h1108, h1174, h1185, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1188_1, u0elo0]
                                        · have p1188_0 := h1188c.1
                                          have p1188_1 := h1188c.2.1
                                          have p1188_2 := h1188c.2.2.1
                                          have p1188_3 := h1188c.2.2.2
                                          linarith only [hlam, p1188_0]
                                        · have p1188_0 := h1188c.1
                                          have p1188_1 := h1188c.2.1
                                          have p1188_2 := h1188c.2.2.1
                                          have p1188_3 := h1188c.2.2.2
                                          linarith only [h1185, hlam, p1188_1]
                                        · have p1188_0 := h1188c.1
                                          have p1188_1 := h1188c.2.1
                                          have p1188_2 := h1188c.2.2.1
                                          have p1188_3 := h1188c.2.2.2
                                          linarith only [h1111, hlam, p1188_0]
                                        · have p1188_0 := h1188c.1
                                          have p1188_1 := h1188c.2.1
                                          have p1188_2 := h1188c.2.2.1
                                          have p1188_3 := h1188c.2.2.2
                                          linarith only [h1174, hlam, p1188_0]
                                        · have p1188_0 := h1188c.1
                                          have p1188_1 := h1188c.2.1
                                          have p1188_2 := h1188c.2.2.1
                                          have p1188_3 := h1188c.2.2.2
                                          linarith only [h0, h1108, h1174, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1188_1, u0elo1]
                                        · have p1188_0 := h1188c.1
                                          have p1188_1 := h1188c.2.1
                                          have p1188_2 := h1188c.2.2.1
                                          have p1188_3 := h1188c.2.2.2
                                          linarith only [h0, h1108, h1174, hc24, hlam, hphi, ht0b, ht45, ht5b, p1188_1, u0elo1]
                                        · have p1188_0 := h1188c.1
                                          have p1188_1 := h1188c.2.1
                                          have p1188_2 := h1188c.2.2.1
                                          have p1188_3 := h1188c.2.2.2
                                          linarith only [hlam, p1188_0]
                                      · rcases h2bigk with h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c | h1322c
                                        · have p1322_0 := h1322c.1
                                          have p1322_1 := h1322c.2.1
                                          have p1322_2 := h1322c.2.2.1
                                          have p1322_3 := h1322c.2.2.2
                                          linarith only [hlam, p1322_0]
                                        · have p1322_0 := h1322c.1
                                          have p1322_1 := h1322c.2.1
                                          have p1322_2 := h1322c.2.2.1
                                          have p1322_3 := h1322c.2.2.2
                                          linarith only [h0, hlam, p1322_1]
                                        · have p1322_0 := h1322c.1
                                          have p1322_1 := h1322c.2.1
                                          have p1322_2 := h1322c.2.2.1
                                          have p1322_3 := h1322c.2.2.2
                                          linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1322_1, u0elo1]
                                        · have p1322_0 := h1322c.1
                                          have p1322_1 := h1322c.2.1
                                          have p1322_2 := h1322c.2.2.1
                                          have p1322_3 := h1322c.2.2.2
                                          linarith only [h1181, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1322_1, u0elo1]
                                        · have p1322_0 := h1322c.1
                                          have p1322_1 := h1322c.2.1
                                          have p1322_2 := h1322c.2.2.1
                                          have p1322_3 := h1322c.2.2.2
                                          linarith only [hc25, hlam, hphi, ht0b, ht5b, p1322_1, u0elo1]
                                        · have p1322_0 := h1322c.1
                                          have p1322_1 := h1322c.2.1
                                          have p1322_2 := h1322c.2.2.1
                                          have p1322_3 := h1322c.2.2.2
                                          rcases p1322_3 (m.d 0 2) (by simp) with h1328 | h1328
                                          · linarith only [h0, h1328, hlam]
                                          · rcases p1322_3 (m.d 1 2) (by simp) with h1330 | h1330
                                            · rcases p1322_3 (m.d 2 3) (by simp) with h1331 | h1331
                                              · linarith only [h1172, h1331, hlam]
                                              · rcases p1322_3 (m.d 2 4) (by simp) with h1333 | h1333
                                                · linarith only [h1173, h1333, hlam]
                                                · rcases p1322_3 (m.d 2 5) (by simp) with h1335 | h1335
                                                  · linarith only [h1174, h1335, hlam]
                                                  · rcases h3bigk with h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c | h1337c
                                                    · have p1337_0 := h1337c.1
                                                      have p1337_1 := h1337c.2.1
                                                      have p1337_2 := h1337c.2.2.1
                                                      have p1337_3 := h1337c.2.2.2
                                                      linarith only [hlam, p1337_0]
                                                    · have p1337_0 := h1337c.1
                                                      have p1337_1 := h1337c.2.1
                                                      have p1337_2 := h1337c.2.2.1
                                                      have p1337_3 := h1337c.2.2.2
                                                      linarith only [h1172, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1337_1, u0elo2]
                                                    · have p1337_0 := h1337c.1
                                                      have p1337_1 := h1337c.2.1
                                                      have p1337_2 := h1337c.2.2.1
                                                      have p1337_3 := h1337c.2.2.2
                                                      linarith only [h0, h1106, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1322_1, p1337_1]
                                                    · have p1337_0 := h1337c.1
                                                      have p1337_1 := h1337c.2.1
                                                      have p1337_2 := h1337c.2.2.1
                                                      have p1337_3 := h1337c.2.2.2
                                                      linarith only [h1112, hlam, p1337_0]
                                                    · have p1337_0 := h1337c.1
                                                      have p1337_1 := h1337c.2.1
                                                      have p1337_2 := h1337c.2.2.1
                                                      have p1337_3 := h1337c.2.2.2
                                                      linarith only [h1144, hlam, p1337_0]
                                                    · have p1337_0 := h1337c.1
                                                      have p1337_1 := h1337c.2.1
                                                      have p1337_2 := h1337c.2.2.1
                                                      have p1337_3 := h1337c.2.2.2
                                                      linarith only [h1106, hlam, p1337_0]
                                                    · have p1337_0 := h1337c.1
                                                      have p1337_1 := h1337c.2.1
                                                      have p1337_2 := h1337c.2.2.1
                                                      have p1337_3 := h1337c.2.2.2
                                                      linarith only [hlam, p1337_0]
                                                    · have p1337_0 := h1337c.1
                                                      have p1337_1 := h1337c.2.1
                                                      have p1337_2 := h1337c.2.2.1
                                                      have p1337_3 := h1337c.2.2.2
                                                      linarith only [h0, h1106, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1322_1, p1337_1]
                                                    · have p1337_0 := h1337c.1
                                                      have p1337_1 := h1337c.2.1
                                                      have p1337_2 := h1337c.2.2.1
                                                      have p1337_3 := h1337c.2.2.2
                                                      linarith only [h1175, hlam, p1337_0]
                                                    · have p1337_0 := h1337c.1
                                                      have p1337_1 := h1337c.2.1
                                                      have p1337_2 := h1337c.2.2.1
                                                      have p1337_3 := h1337c.2.2.2
                                                      linarith only [h1177, hlam, p1337_0]
                                                    · have p1337_0 := h1337c.1
                                                      have p1337_1 := h1337c.2.1
                                                      have p1337_2 := h1337c.2.2.1
                                                      have p1337_3 := h1337c.2.2.2
                                                      linarith only [h1109, hlam, p1337_0]
                                                    · have p1337_0 := h1337c.1
                                                      have p1337_1 := h1337c.2.1
                                                      have p1337_2 := h1337c.2.2.1
                                                      have p1337_3 := h1337c.2.2.2
                                                      linarith only [h1172, hlam, p1337_0]
                                                    · have p1337_0 := h1337c.1
                                                      have p1337_1 := h1337c.2.1
                                                      have p1337_2 := h1337c.2.2.1
                                                      have p1337_3 := h1337c.2.2.2
                                                      linarith only [hlam, p1337_0]
                                                    · have p1337_0 := h1337c.1
                                                      have p1337_1 := h1337c.2.1
                                                      have p1337_2 := h1337c.2.2.1
                                                      have p1337_3 := h1337c.2.2.2
                                                      linarith only [h1181, hlam, p1337_0]
                                                    · have p1337_0 := h1337c.1
                                                      have p1337_1 := h1337c.2.1
                                                      have p1337_2 := h1337c.2.2.1
                                                      have p1337_3 := h1337c.2.2.2
                                                      linarith only [h1183, hlam, p1337_0]
                                                    · have p1337_0 := h1337c.1
                                                      have p1337_1 := h1337c.2.1
                                                      have p1337_2 := h1337c.2.2.1
                                                      have p1337_3 := h1337c.2.2.2
                                                      linarith only [h1187, hc03, hc45, hlam, hphi, ht34, p1337_1]
                                                    · have p1337_0 := h1337c.1
                                                      have p1337_1 := h1337c.2.1
                                                      have p1337_2 := h1337c.2.2.1
                                                      have p1337_3 := h1337c.2.2.2
                                                      linarith only [h1172, h1187, hc23, hc45, hlam, hphi, ht34, p1337_1]
                                                    · have p1337_0 := h1337c.1
                                                      have p1337_1 := h1337c.2.1
                                                      have p1337_2 := h1337c.2.2.1
                                                      have p1337_3 := h1337c.2.2.2
                                                      linarith only [h1187, hc23, hc45, hlam, hphi, ht34, p1337_1]
                                                    · have p1337_0 := h1337c.1
                                                      have p1337_1 := h1337c.2.1
                                                      have p1337_2 := h1337c.2.2.1
                                                      have p1337_3 := h1337c.2.2.2
                                                      linarith only [hlam, p1337_0]
                                                    · have p1337_0 := h1337c.1
                                                      have p1337_1 := h1337c.2.1
                                                      have p1337_2 := h1337c.2.2.1
                                                      have p1337_3 := h1337c.2.2.2
                                                      linarith only [h1187, hlam, p1337_1]
                                                    · have p1337_0 := h1337c.1
                                                      have p1337_1 := h1337c.2.1
                                                      have p1337_2 := h1337c.2.2.1
                                                      have p1337_3 := h1337c.2.2.2
                                                      rcases p1337_3 (m.d 0 3) (by simp) with h1358 | h1358
                                                      · linarith only [h1358, hlam, p1337_0]
                                                      · rcases p1337_3 (m.d 1 3) (by simp) with h1360 | h1360
                                                        · linarith only [h1177, h1360, hlam]
                                                        · rcases p1337_3 (m.d 2 3) (by simp) with h1362 | h1362
                                                          · linarith only [h1183, h1362, hlam]
                                                          · rcases p1337_3 (m.d 3 4) (by simp) with h1364 | h1364
                                                            · linarith only [h1187, h1364, hlam]
                                                            · linarith only [h1112, h1364, hlam]
                                                    · have p1337_0 := h1337c.1
                                                      have p1337_1 := h1337c.2.1
                                                      have p1337_2 := h1337c.2.2.1
                                                      have p1337_3 := h1337c.2.2.2
                                                      rcases p1337_3 (m.d 0 3) (by simp) with h1367 | h1367
                                                      · linarith only [h1144, h1367, hlam]
                                                      · linarith only [h1106, h1367, hlam]
                                                    · have p1337_0 := h1337c.1
                                                      have p1337_1 := h1337c.2.1
                                                      have p1337_2 := h1337c.2.2.1
                                                      have p1337_3 := h1337c.2.2.2
                                                      rcases p1337_3 (m.d 0 3) (by simp) with h1370 | h1370
                                                      · linarith only [h1144, h1370, hlam]
                                                      · linarith only [h1109, h1370, hlam]
                                                    · have p1337_0 := h1337c.1
                                                      have p1337_1 := h1337c.2.1
                                                      have p1337_2 := h1337c.2.2.1
                                                      have p1337_3 := h1337c.2.2.2
                                                      linarith only [h1106, h1112, h1172, h1187, hc23, hc45, hlam, hphi, ht34, p1337_1]
                                                    · have p1337_0 := h1337c.1
                                                      have p1337_1 := h1337c.2.1
                                                      have p1337_2 := h1337c.2.2.1
                                                      have p1337_3 := h1337c.2.2.2
                                                      linarith only [hlam, p1337_0]
                                            · linarith only [h0, h1330, hlam]
                                        · have p1322_0 := h1322c.1
                                          have p1322_1 := h1322c.2.1
                                          have p1322_2 := h1322c.2.2.1
                                          have p1322_3 := h1322c.2.2.2
                                          linarith only [hlam, p1322_0]
                                        · have p1322_0 := h1322c.1
                                          have p1322_1 := h1322c.2.1
                                          have p1322_2 := h1322c.2.2.1
                                          have p1322_3 := h1322c.2.2.2
                                          rcases p1322_3 (m.d 0 2) (by simp) with h1377 | h1377
                                          · linarith only [h0, h1377, hlam]
                                          · linarith only [h1109, h1377, hlam]
                                        · have p1322_0 := h1322c.1
                                          have p1322_1 := h1322c.2.1
                                          have p1322_2 := h1322c.2.2.1
                                          have p1322_3 := h1322c.2.2.2
                                          rcases p1322_3 (m.d 0 2) (by simp) with h1380 | h1380
                                          · linarith only [h0, h1380, hlam]
                                          · linarith only [h1110, h1380, hlam]
                                        · have p1322_0 := h1322c.1
                                          have p1322_1 := h1322c.2.1
                                          have p1322_2 := h1322c.2.2.1
                                          have p1322_3 := h1322c.2.2.2
                                          rcases p1322_3 (m.d 0 2) (by simp) with h1383 | h1383
                                          · linarith only [h0, h1383, hlam]
                                          · linarith only [h1111, h1383, hlam]
                                        · have p1322_0 := h1322c.1
                                          have p1322_1 := h1322c.2.1
                                          have p1322_2 := h1322c.2.2.1
                                          have p1322_3 := h1322c.2.2.2
                                          linarith only [h1109, hlam, p1322_0]
                                        · have p1322_0 := h1322c.1
                                          have p1322_1 := h1322c.2.1
                                          have p1322_2 := h1322c.2.2.1
                                          have p1322_3 := h1322c.2.2.2
                                          linarith only [h1172, hlam, p1322_0]
                                        · have p1322_0 := h1322c.1
                                          have p1322_1 := h1322c.2.1
                                          have p1322_2 := h1322c.2.2.1
                                          have p1322_3 := h1322c.2.2.2
                                          linarith only [hlam, p1322_0]
                                        · have p1322_0 := h1322c.1
                                          have p1322_1 := h1322c.2.1
                                          have p1322_2 := h1322c.2.2.1
                                          have p1322_3 := h1322c.2.2.2
                                          linarith only [h1181, hlam, p1322_0]
                                        · have p1322_0 := h1322c.1
                                          have p1322_1 := h1322c.2.1
                                          have p1322_2 := h1322c.2.2.1
                                          have p1322_3 := h1322c.2.2.2
                                          linarith only [h1183, hlam, p1322_0]
                                        · have p1322_0 := h1322c.1
                                          have p1322_1 := h1322c.2.1
                                          have p1322_2 := h1322c.2.2.1
                                          have p1322_3 := h1322c.2.2.2
                                          linarith only [h1110, hlam, p1322_0]
                                        · have p1322_0 := h1322c.1
                                          have p1322_1 := h1322c.2.1
                                          have p1322_2 := h1322c.2.2.1
                                          have p1322_3 := h1322c.2.2.2
                                          linarith only [h1173, hlam, p1322_0]
                                        · have p1322_0 := h1322c.1
                                          have p1322_1 := h1322c.2.1
                                          have p1322_2 := h1322c.2.2.1
                                          have p1322_3 := h1322c.2.2.2
                                          linarith only [h0, h1108, h1173, h1179, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1322_1, u0elo1]
                                        · have p1322_0 := h1322c.1
                                          have p1322_1 := h1322c.2.1
                                          have p1322_2 := h1322c.2.2.1
                                          have p1322_3 := h1322c.2.2.2
                                          linarith only [hlam, p1322_0]
                                        · have p1322_0 := h1322c.1
                                          have p1322_1 := h1322c.2.1
                                          have p1322_2 := h1322c.2.2.1
                                          have p1322_3 := h1322c.2.2.2
                                          linarith only [h1185, hlam, p1322_1]
                                        · have p1322_0 := h1322c.1
                                          have p1322_1 := h1322c.2.1
                                          have p1322_2 := h1322c.2.2.1
                                          have p1322_3 := h1322c.2.2.2
                                          linarith only [h1111, hlam, p1322_0]
                                        · have p1322_0 := h1322c.1
                                          have p1322_1 := h1322c.2.1
                                          have p1322_2 := h1322c.2.2.1
                                          have p1322_3 := h1322c.2.2.2
                                          linarith only [h1174, hlam, p1322_0]
                                        · have p1322_0 := h1322c.1
                                          have p1322_1 := h1322c.2.1
                                          have p1322_2 := h1322c.2.2.1
                                          have p1322_3 := h1322c.2.2.2
                                          linarith only [h1111, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1322_1, u0elo1]
                                        · have p1322_0 := h1322c.1
                                          have p1322_1 := h1322c.2.1
                                          have p1322_2 := h1322c.2.2.1
                                          have p1322_3 := h1322c.2.2.2
                                          linarith only [h0, h1108, h1174, hc24, hlam, hphi, ht0b, ht45, ht5b, p1322_1, u0elo1]
                                        · have p1322_0 := h1322c.1
                                          have p1322_1 := h1322c.2.1
                                          have p1322_2 := h1322c.2.2.1
                                          have p1322_3 := h1322c.2.2.2
                                          linarith only [hlam, p1322_0]
                        · linarith only [h0, h1111, h1174, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h1106, h1110, h1172, h1173, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1109, h1172, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h1108, h1111, hlam]
          · linarith only [h0, h1107, h1110, hlam]
        · linarith only [h0, h1106, h1109, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1407 | h1407
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1408 | h1408
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1409 | h1409
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1410 | h1410
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1411 | h1411
                · linarith only [h1106, h1108, h1411, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1413 | h1413
                  · linarith only [h1106, h1108, h1410, h1413, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1415 | h1415
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1416 | h1416
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1417 | h1417
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1418 | h1418
                          · linarith only [h1106, h1108, h1409, h1418, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · linarith only [h1106, h1108, h1409, h1410, h1415, h1418, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h1409, h1417, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h1408, h1416, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1106, h1407, h1410, h1415, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1424 | h1424
                · linarith only [h1107, h1108, h1410, h1424, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1426 | h1426
                  · linarith only [h1107, h1108, h1426, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1428 | h1428
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1429 | h1429
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1430 | h1430
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1431 | h1431
                          · linarith only [h1106, h1410, h1431, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1433 | h1433
                            · linarith only [h1106, h1108, h1424, h1433, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1435 | h1435
                              · linarith only [h1107, h1108, h1409, h1410, h1426, h1435, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1437 | h1437
                                · linarith only [h1106, h1410, h1428, h1437, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1439 | h1439
                                  · linarith only [h1106, h1108, h1428, h1433, h1439, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1441 | h1441
                                    · linarith only [h1107, h1108, h1429, h1435, h1441, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1443 | h1443
                                      · linarith only [h1107, h1108, h1429, h1435, h1437, h1443, hc23, hc34, hlam, hphi]
                                      · rcases h2bigk with h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c
                                        · have p1445_0 := h1445c.1
                                          have p1445_1 := h1445c.2.1
                                          have p1445_2 := h1445c.2.2.1
                                          have p1445_3 := h1445c.2.2.2
                                          linarith only [hlam, p1445_0]
                                        · have p1445_0 := h1445c.1
                                          have p1445_1 := h1445c.2.1
                                          have p1445_2 := h1445c.2.2.1
                                          have p1445_3 := h1445c.2.2.2
                                          linarith only [h0, hlam, p1445_1]
                                        · have p1445_0 := h1445c.1
                                          have p1445_1 := h1445c.2.1
                                          have p1445_2 := h1445c.2.2.1
                                          have p1445_3 := h1445c.2.2.2
                                          linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1445_1, u0elo1]
                                        · have p1445_0 := h1445c.1
                                          have p1445_1 := h1445c.2.1
                                          have p1445_2 := h1445c.2.2.1
                                          have p1445_3 := h1445c.2.2.2
                                          linarith only [h1437, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1445_1, u0elo1]
                                        · have p1445_0 := h1445c.1
                                          have p1445_1 := h1445c.2.1
                                          have p1445_2 := h1445c.2.2.1
                                          have p1445_3 := h1445c.2.2.2
                                          linarith only [h1437, h1441, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1445_1, u0elo1]
                                        · have p1445_0 := h1445c.1
                                          have p1445_1 := h1445c.2.1
                                          have p1445_2 := h1445c.2.2.1
                                          have p1445_3 := h1445c.2.2.2
                                          rcases p1445_3 (m.d 0 2) (by simp) with h1451 | h1451
                                          · linarith only [h0, h1451, hlam]
                                          · rcases p1445_3 (m.d 1 2) (by simp) with h1453 | h1453
                                            · rcases p1445_3 (m.d 2 3) (by simp) with h1454 | h1454
                                              · linarith only [h1428, h1454, hlam]
                                              · rcases p1445_3 (m.d 2 4) (by simp) with h1456 | h1456
                                                · linarith only [h1429, h1456, hlam]
                                                · rcases p1445_3 (m.d 2 5) (by simp) with h1458 | h1458
                                                  · linarith only [h1430, h1458, hlam]
                                                  · rcases h3bigk with h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c
                                                    · have p1460_0 := h1460c.1
                                                      have p1460_1 := h1460c.2.1
                                                      have p1460_2 := h1460c.2.2.1
                                                      have p1460_3 := h1460c.2.2.2
                                                      linarith only [hlam, p1460_0]
                                                    · have p1460_0 := h1460c.1
                                                      have p1460_1 := h1460c.2.1
                                                      have p1460_2 := h1460c.2.2.1
                                                      have p1460_3 := h1460c.2.2.2
                                                      linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1460_1, u0elo2]
                                                    · have p1460_0 := h1460c.1
                                                      have p1460_1 := h1460c.2.1
                                                      have p1460_2 := h1460c.2.2.1
                                                      have p1460_3 := h1460c.2.2.2
                                                      linarith only [h1410, h1443, hc23, hc45, hlam, hphi, ht34, p1460_1]
                                                    · have p1460_0 := h1460c.1
                                                      have p1460_1 := h1460c.2.1
                                                      have p1460_2 := h1460c.2.2.1
                                                      have p1460_3 := h1460c.2.2.2
                                                      linarith only [h1410, hlam, p1460_0]
                                                    · have p1460_0 := h1460c.1
                                                      have p1460_1 := h1460c.2.1
                                                      have p1460_2 := h1460c.2.2.1
                                                      have p1460_3 := h1460c.2.2.2
                                                      linarith only [h1424, hlam, p1460_0]
                                                    · have p1460_0 := h1460c.1
                                                      have p1460_1 := h1460c.2.1
                                                      have p1460_2 := h1460c.2.2.1
                                                      have p1460_3 := h1460c.2.2.2
                                                      linarith only [h1106, hlam, p1460_0]
                                                    · have p1460_0 := h1460c.1
                                                      have p1460_1 := h1460c.2.1
                                                      have p1460_2 := h1460c.2.2.1
                                                      have p1460_3 := h1460c.2.2.2
                                                      linarith only [hlam, p1460_0]
                                                    · have p1460_0 := h1460c.1
                                                      have p1460_1 := h1460c.2.1
                                                      have p1460_2 := h1460c.2.2.1
                                                      have p1460_3 := h1460c.2.2.2
                                                      linarith only [h1106, h1108, h1409, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1445_1, p1460_1]
                                                    · have p1460_0 := h1460c.1
                                                      have p1460_1 := h1460c.2.1
                                                      have p1460_2 := h1460c.2.2.1
                                                      have p1460_3 := h1460c.2.2.2
                                                      linarith only [h1431, hlam, p1460_0]
                                                    · have p1460_0 := h1460c.1
                                                      have p1460_1 := h1460c.2.1
                                                      have p1460_2 := h1460c.2.2.1
                                                      have p1460_3 := h1460c.2.2.2
                                                      linarith only [h1433, hlam, p1460_0]
                                                    · have p1460_0 := h1460c.1
                                                      have p1460_1 := h1460c.2.1
                                                      have p1460_2 := h1460c.2.2.1
                                                      have p1460_3 := h1460c.2.2.2
                                                      linarith only [h1407, hlam, p1460_0]
                                                    · have p1460_0 := h1460c.1
                                                      have p1460_1 := h1460c.2.1
                                                      have p1460_2 := h1460c.2.2.1
                                                      have p1460_3 := h1460c.2.2.2
                                                      linarith only [h1428, hlam, p1460_0]
                                                    · have p1460_0 := h1460c.1
                                                      have p1460_1 := h1460c.2.1
                                                      have p1460_2 := h1460c.2.2.1
                                                      have p1460_3 := h1460c.2.2.2
                                                      linarith only [hlam, p1460_0]
                                                    · have p1460_0 := h1460c.1
                                                      have p1460_1 := h1460c.2.1
                                                      have p1460_2 := h1460c.2.2.1
                                                      have p1460_3 := h1460c.2.2.2
                                                      linarith only [h1437, hlam, p1460_0]
                                                    · have p1460_0 := h1460c.1
                                                      have p1460_1 := h1460c.2.1
                                                      have p1460_2 := h1460c.2.2.1
                                                      have p1460_3 := h1460c.2.2.2
                                                      linarith only [h1439, hlam, p1460_0]
                                                    · have p1460_0 := h1460c.1
                                                      have p1460_1 := h1460c.2.1
                                                      have p1460_2 := h1460c.2.2.1
                                                      have p1460_3 := h1460c.2.2.2
                                                      linarith only [h1443, hc03, hc45, hlam, hphi, ht34, p1460_1]
                                                    · have p1460_0 := h1460c.1
                                                      have p1460_1 := h1460c.2.1
                                                      have p1460_2 := h1460c.2.2.1
                                                      have p1460_3 := h1460c.2.2.2
                                                      linarith only [h1443, hc13, hc45, hlam, hphi, ht34, p1460_1]
                                                    · have p1460_0 := h1460c.1
                                                      have p1460_1 := h1460c.2.1
                                                      have p1460_2 := h1460c.2.2.1
                                                      have p1460_3 := h1460c.2.2.2
                                                      linarith only [h1443, hc23, hc45, hlam, hphi, ht34, p1460_1]
                                                    · have p1460_0 := h1460c.1
                                                      have p1460_1 := h1460c.2.1
                                                      have p1460_2 := h1460c.2.2.1
                                                      have p1460_3 := h1460c.2.2.2
                                                      linarith only [hlam, p1460_0]
                                                    · have p1460_0 := h1460c.1
                                                      have p1460_1 := h1460c.2.1
                                                      have p1460_2 := h1460c.2.2.1
                                                      have p1460_3 := h1460c.2.2.2
                                                      linarith only [h1443, hlam, p1460_1]
                                                    · have p1460_0 := h1460c.1
                                                      have p1460_1 := h1460c.2.1
                                                      have p1460_2 := h1460c.2.2.1
                                                      have p1460_3 := h1460c.2.2.2
                                                      rcases p1460_3 (m.d 0 3) (by simp) with h1481 | h1481
                                                      · linarith only [h1481, hlam, p1460_0]
                                                      · rcases p1460_3 (m.d 1 3) (by simp) with h1483 | h1483
                                                        · linarith only [h1433, h1483, hlam]
                                                        · rcases p1460_3 (m.d 2 3) (by simp) with h1485 | h1485
                                                          · linarith only [h1439, h1485, hlam]
                                                          · rcases p1460_3 (m.d 3 4) (by simp) with h1487 | h1487
                                                            · linarith only [h1443, h1487, hlam]
                                                            · linarith only [h1410, h1487, hlam]
                                                    · have p1460_0 := h1460c.1
                                                      have p1460_1 := h1460c.2.1
                                                      have p1460_2 := h1460c.2.2.1
                                                      have p1460_3 := h1460c.2.2.2
                                                      rcases p1460_3 (m.d 0 3) (by simp) with h1490 | h1490
                                                      · linarith only [h1424, h1490, hlam]
                                                      · linarith only [h1106, h1490, hlam]
                                                    · have p1460_0 := h1460c.1
                                                      have p1460_1 := h1460c.2.1
                                                      have p1460_2 := h1460c.2.2.1
                                                      have p1460_3 := h1460c.2.2.2
                                                      rcases p1460_3 (m.d 0 3) (by simp) with h1493 | h1493
                                                      · linarith only [h1424, h1493, hlam]
                                                      · linarith only [h1407, h1493, hlam]
                                                    · have p1460_0 := h1460c.1
                                                      have p1460_1 := h1460c.2.1
                                                      have p1460_2 := h1460c.2.2.1
                                                      have p1460_3 := h1460c.2.2.2
                                                      linarith only [h1106, h1410, h1428, h1443, hc23, hc45, hlam, hphi, ht34, p1460_1]
                                                    · have p1460_0 := h1460c.1
                                                      have p1460_1 := h1460c.2.1
                                                      have p1460_2 := h1460c.2.2.1
                                                      have p1460_3 := h1460c.2.2.2
                                                      linarith only [hlam, p1460_0]
                                            · linarith only [h0, h1453, hlam]
                                        · have p1445_0 := h1445c.1
                                          have p1445_1 := h1445c.2.1
                                          have p1445_2 := h1445c.2.2.1
                                          have p1445_3 := h1445c.2.2.2
                                          linarith only [hlam, p1445_0]
                                        · have p1445_0 := h1445c.1
                                          have p1445_1 := h1445c.2.1
                                          have p1445_2 := h1445c.2.2.1
                                          have p1445_3 := h1445c.2.2.2
                                          rcases p1445_3 (m.d 0 2) (by simp) with h1500 | h1500
                                          · linarith only [h0, h1500, hlam]
                                          · linarith only [h1407, h1500, hlam]
                                        · have p1445_0 := h1445c.1
                                          have p1445_1 := h1445c.2.1
                                          have p1445_2 := h1445c.2.2.1
                                          have p1445_3 := h1445c.2.2.2
                                          rcases p1445_3 (m.d 0 2) (by simp) with h1503 | h1503
                                          · linarith only [h0, h1503, hlam]
                                          · linarith only [h1408, h1503, hlam]
                                        · have p1445_0 := h1445c.1
                                          have p1445_1 := h1445c.2.1
                                          have p1445_2 := h1445c.2.2.1
                                          have p1445_3 := h1445c.2.2.2
                                          rcases p1445_3 (m.d 0 2) (by simp) with h1506 | h1506
                                          · linarith only [h0, h1506, hlam]
                                          · linarith only [h1409, h1506, hlam]
                                        · have p1445_0 := h1445c.1
                                          have p1445_1 := h1445c.2.1
                                          have p1445_2 := h1445c.2.2.1
                                          have p1445_3 := h1445c.2.2.2
                                          linarith only [h1407, hlam, p1445_0]
                                        · have p1445_0 := h1445c.1
                                          have p1445_1 := h1445c.2.1
                                          have p1445_2 := h1445c.2.2.1
                                          have p1445_3 := h1445c.2.2.2
                                          linarith only [h1428, hlam, p1445_0]
                                        · have p1445_0 := h1445c.1
                                          have p1445_1 := h1445c.2.1
                                          have p1445_2 := h1445c.2.2.1
                                          have p1445_3 := h1445c.2.2.2
                                          linarith only [hlam, p1445_0]
                                        · have p1445_0 := h1445c.1
                                          have p1445_1 := h1445c.2.1
                                          have p1445_2 := h1445c.2.2.1
                                          have p1445_3 := h1445c.2.2.2
                                          linarith only [h1437, hlam, p1445_0]
                                        · have p1445_0 := h1445c.1
                                          have p1445_1 := h1445c.2.1
                                          have p1445_2 := h1445c.2.2.1
                                          have p1445_3 := h1445c.2.2.2
                                          linarith only [h1439, hlam, p1445_0]
                                        · have p1445_0 := h1445c.1
                                          have p1445_1 := h1445c.2.1
                                          have p1445_2 := h1445c.2.2.1
                                          have p1445_3 := h1445c.2.2.2
                                          linarith only [h1408, hlam, p1445_0]
                                        · have p1445_0 := h1445c.1
                                          have p1445_1 := h1445c.2.1
                                          have p1445_2 := h1445c.2.2.1
                                          have p1445_3 := h1445c.2.2.2
                                          linarith only [h1429, hlam, p1445_0]
                                        · have p1445_0 := h1445c.1
                                          have p1445_1 := h1445c.2.1
                                          have p1445_2 := h1445c.2.2.1
                                          have p1445_3 := h1445c.2.2.2
                                          linarith only [h1107, h1108, h1409, h1429, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1445_1, u0elo1]
                                        · have p1445_0 := h1445c.1
                                          have p1445_1 := h1445c.2.1
                                          have p1445_2 := h1445c.2.2.1
                                          have p1445_3 := h1445c.2.2.2
                                          linarith only [hlam, p1445_0]
                                        · have p1445_0 := h1445c.1
                                          have p1445_1 := h1445c.2.1
                                          have p1445_2 := h1445c.2.2.1
                                          have p1445_3 := h1445c.2.2.2
                                          linarith only [h1441, hlam, p1445_1]
                                        · have p1445_0 := h1445c.1
                                          have p1445_1 := h1445c.2.1
                                          have p1445_2 := h1445c.2.2.1
                                          have p1445_3 := h1445c.2.2.2
                                          linarith only [h1409, hlam, p1445_0]
                                        · have p1445_0 := h1445c.1
                                          have p1445_1 := h1445c.2.1
                                          have p1445_2 := h1445c.2.2.1
                                          have p1445_3 := h1445c.2.2.2
                                          linarith only [h1430, hlam, p1445_0]
                                        · have p1445_0 := h1445c.1
                                          have p1445_1 := h1445c.2.1
                                          have p1445_2 := h1445c.2.2.1
                                          have p1445_3 := h1445c.2.2.2
                                          linarith only [h1409, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1445_1, u0elo1]
                                        · have p1445_0 := h1445c.1
                                          have p1445_1 := h1445c.2.1
                                          have p1445_2 := h1445c.2.2.1
                                          have p1445_3 := h1445c.2.2.2
                                          linarith only [h1409, hc24, hlam, hphi, ht0b, ht45, ht5b, p1445_1, u0elo1]
                                        · have p1445_0 := h1445c.1
                                          have p1445_1 := h1445c.2.1
                                          have p1445_2 := h1445c.2.2.1
                                          have p1445_3 := h1445c.2.2.2
                                          linarith only [hlam, p1445_0]
                        · linarith only [h1409, h1430, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h1408, h1429, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1106, h1407, h1428, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1527 | h1527
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1528 | h1528
                · linarith only [h0, h1106, h1409, h1528, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1530 | h1530
                  · linarith only [h0, h1106, h1409, h1527, h1530, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1532 | h1532
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1533 | h1533
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1534 | h1534
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1535 | h1535
                          · linarith only [h0, h1106, h1409, h1535, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                          · linarith only [h0, h1106, h1409, h1527, h1535, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1538 | h1538
                          · linarith only [h0, h1106, h1409, h1538, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                          · linarith only [h0, h1106, h1409, h1527, h1538, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                      · linarith only [h1408, h1409, h1533, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                    · linarith only [h0, h1407, h1409, h1532, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1543 | h1543
                · linarith only [h0, h1107, h1409, h1527, h1543, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1545 | h1545
                  · linarith only [h0, h1107, h1409, h1545, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1547 | h1547
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1548 | h1548
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1549 | h1549
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1550 | h1550
                          · linarith only [h1106, h1527, h1550, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1552 | h1552
                            · linarith only [h0, h1106, h1107, h1409, h1543, h1552, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1554 | h1554
                              · linarith only [h1107, h1527, h1545, h1554, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1556 | h1556
                                · linarith only [h1106, h1527, h1547, h1556, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1558 | h1558
                                  · linarith only [h0, h1106, h1409, h1547, h1558, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1560 | h1560
                                    · linarith only [h0, h1107, h1409, h1548, h1554, h1560, hc15, hlam, hphi, ht0b, ht5b, u0elo4]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1562 | h1562
                                      · linarith only [h0, h1107, h1409, h1547, h1549, h1550, h1554, h1562, hc23, hc34, hlam, hphi]
                                      · rcases h2bigk with h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c
                                        · have p1564_0 := h1564c.1
                                          have p1564_1 := h1564c.2.1
                                          have p1564_2 := h1564c.2.2.1
                                          have p1564_3 := h1564c.2.2.2
                                          linarith only [hlam, p1564_0]
                                        · have p1564_0 := h1564c.1
                                          have p1564_1 := h1564c.2.1
                                          have p1564_2 := h1564c.2.2.1
                                          have p1564_3 := h1564c.2.2.2
                                          linarith only [h0, hlam, p1564_1]
                                        · have p1564_0 := h1564c.1
                                          have p1564_1 := h1564c.2.1
                                          have p1564_2 := h1564c.2.2.1
                                          have p1564_3 := h1564c.2.2.2
                                          linarith only [h1409, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1564_1, u0elo4]
                                        · have p1564_0 := h1564c.1
                                          have p1564_1 := h1564c.2.1
                                          have p1564_2 := h1564c.2.2.1
                                          have p1564_3 := h1564c.2.2.2
                                          linarith only [h1409, hc24, hlam, hphi, ht0b, ht45, ht5b, p1564_1, u0elo4]
                                        · have p1564_0 := h1564c.1
                                          have p1564_1 := h1564c.2.1
                                          have p1564_2 := h1564c.2.2.1
                                          have p1564_3 := h1564c.2.2.2
                                          linarith only [h1409, hlam, p1564_0]
                                        · have p1564_0 := h1564c.1
                                          have p1564_1 := h1564c.2.1
                                          have p1564_2 := h1564c.2.2.1
                                          have p1564_3 := h1564c.2.2.2
                                          rcases p1564_3 (m.d 0 2) (by simp) with h1570 | h1570
                                          · linarith only [h0, h1570, hlam]
                                          · rcases p1564_3 (m.d 1 2) (by simp) with h1572 | h1572
                                            · rcases p1564_3 (m.d 2 3) (by simp) with h1573 | h1573
                                              · linarith only [h1547, h1573, hlam]
                                              · rcases p1564_3 (m.d 2 4) (by simp) with h1575 | h1575
                                                · linarith only [h1548, h1575, hlam]
                                                · rcases p1564_3 (m.d 2 5) (by simp) with h1577 | h1577
                                                  · linarith only [h1549, h1577, hlam]
                                                  · linarith only [h1409, h1577, hlam]
                                            · linarith only [h0, h1572, hlam]
                                        · have p1564_0 := h1564c.1
                                          have p1564_1 := h1564c.2.1
                                          have p1564_2 := h1564c.2.2.1
                                          have p1564_3 := h1564c.2.2.2
                                          linarith only [hlam, p1564_0]
                                        · have p1564_0 := h1564c.1
                                          have p1564_1 := h1564c.2.1
                                          have p1564_2 := h1564c.2.2.1
                                          have p1564_3 := h1564c.2.2.2
                                          linarith only [h1407, h1409, h1549, hlam, p1564_2]
                                        · have p1564_0 := h1564c.1
                                          have p1564_1 := h1564c.2.1
                                          have p1564_2 := h1564c.2.2.1
                                          have p1564_3 := h1564c.2.2.2
                                          linarith only [h1408, h1409, h1549, hlam, p1564_2]
                                        · have p1564_0 := h1564c.1
                                          have p1564_1 := h1564c.2.1
                                          have p1564_2 := h1564c.2.2.1
                                          have p1564_3 := h1564c.2.2.2
                                          linarith only [h0, h1409, hc01, hc12, hlam, hphi, p1564_1]
                                        · have p1564_0 := h1564c.1
                                          have p1564_1 := h1564c.2.1
                                          have p1564_2 := h1564c.2.2.1
                                          have p1564_3 := h1564c.2.2.2
                                          linarith only [h1407, hlam, p1564_0]
                                        · have p1564_0 := h1564c.1
                                          have p1564_1 := h1564c.2.1
                                          have p1564_2 := h1564c.2.2.1
                                          have p1564_3 := h1564c.2.2.2
                                          linarith only [h1547, hlam, p1564_0]
                                        · have p1564_0 := h1564c.1
                                          have p1564_1 := h1564c.2.1
                                          have p1564_2 := h1564c.2.2.1
                                          have p1564_3 := h1564c.2.2.2
                                          linarith only [hlam, p1564_0]
                                        · have p1564_0 := h1564c.1
                                          have p1564_1 := h1564c.2.1
                                          have p1564_2 := h1564c.2.2.1
                                          have p1564_3 := h1564c.2.2.2
                                          linarith only [h1556, hlam, p1564_0]
                                        · have p1564_0 := h1564c.1
                                          have p1564_1 := h1564c.2.1
                                          have p1564_2 := h1564c.2.2.1
                                          have p1564_3 := h1564c.2.2.2
                                          linarith only [h1558, hlam, p1564_0]
                                        · have p1564_0 := h1564c.1
                                          have p1564_1 := h1564c.2.1
                                          have p1564_2 := h1564c.2.2.1
                                          have p1564_3 := h1564c.2.2.2
                                          linarith only [h1408, hlam, p1564_0]
                                        · have p1564_0 := h1564c.1
                                          have p1564_1 := h1564c.2.1
                                          have p1564_2 := h1564c.2.2.1
                                          have p1564_3 := h1564c.2.2.2
                                          linarith only [h1548, hlam, p1564_0]
                                        · have p1564_0 := h1564c.1
                                          have p1564_1 := h1564c.2.1
                                          have p1564_2 := h1564c.2.2.1
                                          have p1564_3 := h1564c.2.2.2
                                          linarith only [h1107, h1548, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1564_1, u0elo0]
                                        · have p1564_0 := h1564c.1
                                          have p1564_1 := h1564c.2.1
                                          have p1564_2 := h1564c.2.2.1
                                          have p1564_3 := h1564c.2.2.2
                                          linarith only [hlam, p1564_0]
                                        · have p1564_0 := h1564c.1
                                          have p1564_1 := h1564c.2.1
                                          have p1564_2 := h1564c.2.2.1
                                          have p1564_3 := h1564c.2.2.2
                                          linarith only [h1560, hlam, p1564_1]
                                        · have p1564_0 := h1564c.1
                                          have p1564_1 := h1564c.2.1
                                          have p1564_2 := h1564c.2.2.1
                                          have p1564_3 := h1564c.2.2.2
                                          linarith only [h0, h1107, h1549, h1550, h1552, hc13, hc35, hlam, hphi, p1564_1]
                                        · have p1564_0 := h1564c.1
                                          have p1564_1 := h1564c.2.1
                                          have p1564_2 := h1564c.2.2.1
                                          have p1564_3 := h1564c.2.2.2
                                          linarith only [h1549, hlam, p1564_0]
                                        · have p1564_0 := h1564c.1
                                          have p1564_1 := h1564c.2.1
                                          have p1564_2 := h1564c.2.2.1
                                          have p1564_3 := h1564c.2.2.2
                                          rcases p1564_3 (m.d 0 2) (by simp) with h1597 | h1597
                                          · linarith only [h1409, h1597, hlam]
                                          · linarith only [h1407, h1597, hlam]
                                        · have p1564_0 := h1564c.1
                                          have p1564_1 := h1564c.2.1
                                          have p1564_2 := h1564c.2.2.1
                                          have p1564_3 := h1564c.2.2.2
                                          rcases p1564_3 (m.d 0 2) (by simp) with h1600 | h1600
                                          · linarith only [h1409, h1600, hlam]
                                          · linarith only [h1408, h1600, hlam]
                                        · have p1564_0 := h1564c.1
                                          have p1564_1 := h1564c.2.1
                                          have p1564_2 := h1564c.2.2.1
                                          have p1564_3 := h1564c.2.2.2
                                          linarith only [hlam, p1564_0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1604 | h1604
                          · linarith only [h0, h1106, h1409, h1604, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1606 | h1606
                            · linarith only [h0, h1107, h1409, h1604, h1606, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1608 | h1608
                              · linarith only [h0, h1107, h1409, h1608, hc45, hlam, hphi, ht0b, ht5b, u0elo4]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1610 | h1610
                                · linarith only [h1106, h1527, h1547, h1610, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1612 | h1612
                                  · linarith only [h0, h1107, h1409, h1547, h1604, h1606, h1612, hc15, hlam, hphi, ht0b, ht5b, u0elo4]
                                  · linarith only [h0, h1107, h1547, h1549, h1604, h1612, hc23, hc35, hlam, hphi]
                      · linarith only [h0, h1408, h1409, h1548, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                    · linarith only [h0, h1106, h1407, h1409, h1547, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
          · linarith only [h0, h1107, h1408, hlam]
        · linarith only [h0, h1106, h1407, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1619 | h1619
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1620 | h1620
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1621 | h1621
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1622 | h1622
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1623 | h1623
              · linarith only [h1106, h1107, h1623, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1625 | h1625
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1626 | h1626
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1627 | h1627
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1628 | h1628
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1629 | h1629
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1630 | h1630
                          · linarith only [h1106, h1623, h1630, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1632 | h1632
                            · linarith only [h1106, h1107, h1621, h1632, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                            · linarith only [h1625, h1632, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h1107, h1622, h1628, h1629, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h1621, h1628, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1620, h1627, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h1106, h1107, h1625, h1626, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1639 | h1639
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1640 | h1640
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1641 | h1641
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1642 | h1642
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1643 | h1643
                          · linarith only [h1106, h1623, h1643, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1645 | h1645
                            · linarith only [h1106, h1107, h1621, h1625, h1645, hc05, hlam, hphi, ht0b, ht5b, u0elo1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1647 | h1647
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1648 | h1648
                                · linarith only [h1107, h1620, h1643, h1648, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1650 | h1650
                                  · linarith only [h1106, h1625, h1640, h1650, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1652 | h1652
                                    · linarith only [h1621, h1652, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                    · linarith only [h1639, h1652, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                              · linarith only [h1107, h1619, h1639, h1640, h1645, h1647, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                        · linarith only [h1107, h1622, h1641, h1642, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h1621, h1641, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1106, h1620, h1640, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h1107, h1619, h1639, hlam]
            · linarith only [h0, h1619, h1622, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1661 | h1661
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1662 | h1662
              · linarith only [h0, h1106, h1621, h1662, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1664 | h1664
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1665 | h1665
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1666 | h1666
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1667 | h1667
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1668 | h1668
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1669 | h1669
                          · linarith only [h1106, h1662, h1669, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1671 | h1671
                            · linarith only [h0, h1106, h1621, h1671, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                            · linarith only [h1664, h1671, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h1621, h1667, h1668, hc01, hc25, hlam, hphi, ht12]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1675 | h1675
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1676 | h1676
                          · linarith only [h1106, h1662, h1676, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1678 | h1678
                            · linarith only [h0, h1106, h1621, h1678, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                            · linarith only [h1664, h1678, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h1621, h1661, h1675, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h0, h1620, h1621, h1666, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h0, h1106, h1621, h1664, h1665, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1684 | h1684
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1685 | h1685
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1686 | h1686
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1687 | h1687
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1688 | h1688
                          · linarith only [h0, h1106, h1621, h1662, h1688, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1690 | h1690
                            · linarith only [h0, h1106, h1621, h1664, h1690, hc05, hlam, hphi, ht0b, ht5b, u0elo3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1692 | h1692
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1693 | h1693
                                · linarith only [h1620, h1621, h1686, h1688, h1693, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1695 | h1695
                                  · linarith only [h1106, h1664, h1685, h1695, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1697 | h1697
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1698 | h1698
                                      · rcases h2bigk with h1699c | h1699c | h1699c | h1699c | h1699c | h1699c | h1699c | h1699c | h1699c | h1699c | h1699c | h1699c | h1699c | h1699c | h1699c | h1699c | h1699c | h1699c | h1699c | h1699c | h1699c | h1699c | h1699c | h1699c | h1699c
                                        · have p1699_0 := h1699c.1
                                          have p1699_1 := h1699c.2.1
                                          have p1699_2 := h1699c.2.2.1
                                          have p1699_3 := h1699c.2.2.2
                                          linarith only [hlam, p1699_0]
                                        · have p1699_0 := h1699c.1
                                          have p1699_1 := h1699c.2.1
                                          have p1699_2 := h1699c.2.2.1
                                          have p1699_3 := h1699c.2.2.2
                                          linarith only [h0, hlam, p1699_1]
                                        · have p1699_0 := h1699c.1
                                          have p1699_1 := h1699c.2.1
                                          have p1699_2 := h1699c.2.2.1
                                          have p1699_3 := h1699c.2.2.2
                                          linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1699_1, u0elo1]
                                        · have p1699_0 := h1699c.1
                                          have p1699_1 := h1699c.2.1
                                          have p1699_2 := h1699c.2.2.1
                                          have p1699_3 := h1699c.2.2.2
                                          linarith only [h1621, hlam, p1699_0]
                                        · have p1699_0 := h1699c.1
                                          have p1699_1 := h1699c.2.1
                                          have p1699_2 := h1699c.2.2.1
                                          have p1699_3 := h1699c.2.2.2
                                          linarith only [h1621, h1695, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1699_1, u0elo3]
                                        · have p1699_0 := h1699c.1
                                          have p1699_1 := h1699c.2.1
                                          have p1699_2 := h1699c.2.2.1
                                          have p1699_3 := h1699c.2.2.2
                                          rcases p1699_3 (m.d 0 2) (by simp) with h1705 | h1705
                                          · linarith only [h0, h1705, hlam]
                                          · rcases p1699_3 (m.d 1 2) (by simp) with h1707 | h1707
                                            · rcases p1699_3 (m.d 2 3) (by simp) with h1708 | h1708
                                              · linarith only [h1685, h1708, hlam]
                                              · rcases p1699_3 (m.d 2 4) (by simp) with h1710 | h1710
                                                · linarith only [h1686, h1710, hlam]
                                                · linarith only [h1621, h1710, hlam]
                                            · linarith only [h0, h1707, hlam]
                                        · have p1699_0 := h1699c.1
                                          have p1699_1 := h1699c.2.1
                                          have p1699_2 := h1699c.2.2.1
                                          have p1699_3 := h1699c.2.2.2
                                          linarith only [hlam, p1699_0]
                                        · have p1699_0 := h1699c.1
                                          have p1699_1 := h1699c.2.1
                                          have p1699_2 := h1699c.2.2.1
                                          have p1699_3 := h1699c.2.2.2
                                          linarith only [h1620, h1621, h1686, hlam, p1699_2]
                                        · have p1699_0 := h1699c.1
                                          have p1699_1 := h1699c.2.1
                                          have p1699_2 := h1699c.2.2.1
                                          have p1699_3 := h1699c.2.2.2
                                          linarith only [h0, h1621, hc01, hc12, hlam, hphi, p1699_1]
                                        · have p1699_0 := h1699c.1
                                          have p1699_1 := h1699c.2.1
                                          have p1699_2 := h1699c.2.2.1
                                          have p1699_3 := h1699c.2.2.2
                                          linarith only [h1621, h1661, h1686, hlam, p1699_2]
                                        · have p1699_0 := h1699c.1
                                          have p1699_1 := h1699c.2.1
                                          have p1699_2 := h1699c.2.2.1
                                          have p1699_3 := h1699c.2.2.2
                                          linarith only [h1620, hlam, p1699_0]
                                        · have p1699_0 := h1699c.1
                                          have p1699_1 := h1699c.2.1
                                          have p1699_2 := h1699c.2.2.1
                                          have p1699_3 := h1699c.2.2.2
                                          linarith only [h1685, hlam, p1699_0]
                                        · have p1699_0 := h1699c.1
                                          have p1699_1 := h1699c.2.1
                                          have p1699_2 := h1699c.2.2.1
                                          have p1699_3 := h1699c.2.2.2
                                          linarith only [hlam, p1699_0]
                                        · have p1699_0 := h1699c.1
                                          have p1699_1 := h1699c.2.1
                                          have p1699_2 := h1699c.2.2.1
                                          have p1699_3 := h1699c.2.2.2
                                          linarith only [h1693, hlam, p1699_0]
                                        · have p1699_0 := h1699c.1
                                          have p1699_1 := h1699c.2.1
                                          have p1699_2 := h1699c.2.2.1
                                          have p1699_3 := h1699c.2.2.2
                                          linarith only [h1695, hlam, p1699_0]
                                        · have p1699_0 := h1699c.1
                                          have p1699_1 := h1699c.2.1
                                          have p1699_2 := h1699c.2.2.1
                                          have p1699_3 := h1699c.2.2.2
                                          linarith only [h0, h1619, h1685, h1686, h1688, h1690, hc23, hc34, hlam, hphi, p1699_1]
                                        · have p1699_0 := h1699c.1
                                          have p1699_1 := h1699c.2.1
                                          have p1699_2 := h1699c.2.2.1
                                          have p1699_3 := h1699c.2.2.2
                                          linarith only [h1686, hlam, p1699_0]
                                        · have p1699_0 := h1699c.1
                                          have p1699_1 := h1699c.2.1
                                          have p1699_2 := h1699c.2.2.1
                                          have p1699_3 := h1699c.2.2.2
                                          rcases p1699_3 (m.d 0 2) (by simp) with h1725 | h1725
                                          · linarith only [h1621, h1725, hlam]
                                          · linarith only [h1620, h1725, hlam]
                                        · have p1699_0 := h1699c.1
                                          have p1699_1 := h1699c.2.1
                                          have p1699_2 := h1699c.2.2.1
                                          have p1699_3 := h1699c.2.2.2
                                          linarith only [hlam, p1699_0]
                                        · have p1699_0 := h1699c.1
                                          have p1699_1 := h1699c.2.1
                                          have p1699_2 := h1699c.2.2.1
                                          have p1699_3 := h1699c.2.2.2
                                          rcases p1699_3 (m.d 0 2) (by simp) with h1729 | h1729
                                          · linarith only [h1621, h1729, hlam]
                                          · linarith only [h1661, h1729, hlam]
                                        · have p1699_0 := h1699c.1
                                          have p1699_1 := h1699c.2.1
                                          have p1699_2 := h1699c.2.2.1
                                          have p1699_3 := h1699c.2.2.2
                                          linarith only [h1661, hlam, p1699_0]
                                        · have p1699_0 := h1699c.1
                                          have p1699_1 := h1699c.2.1
                                          have p1699_2 := h1699c.2.2.1
                                          have p1699_3 := h1699c.2.2.2
                                          linarith only [h1687, hlam, p1699_0]
                                        · have p1699_0 := h1699c.1
                                          have p1699_1 := h1699c.2.1
                                          have p1699_2 := h1699c.2.2.1
                                          have p1699_3 := h1699c.2.2.2
                                          linarith only [h1619, h1687, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1699_1, u0elo0]
                                        · have p1699_0 := h1699c.1
                                          have p1699_1 := h1699c.2.1
                                          have p1699_2 := h1699c.2.2.1
                                          have p1699_3 := h1699c.2.2.2
                                          linarith only [h1697, hlam, p1699_0]
                                        · have p1699_0 := h1699c.1
                                          have p1699_1 := h1699c.2.1
                                          have p1699_2 := h1699c.2.2.1
                                          have p1699_3 := h1699c.2.2.2
                                          linarith only [hlam, p1699_0]
                                      · linarith only [h0, h1619, h1621, h1687, h1688, h1697, h1698, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                                    · linarith only [h0, h1106, h1621, h1685, h1697, hc23, hc45, hlam, hphi, ht34]
                              · linarith only [h0, h1621, h1684, h1686, h1692, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                        · linarith only [h0, h1106, h1621, h1685, h1686, h1687, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1741 | h1741
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1742 | h1742
                          · linarith only [h1106, h1742, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1744 | h1744
                            · linarith only [h1106, h1664, h1744, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1746 | h1746
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1747 | h1747
                                · linarith only [h1619, h1685, h1686, h1742, h1744, h1747, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                                · linarith only [h0, h1619, h1686, h1744, h1747, hc13, hc34, hlam, hphi]
                              · linarith only [h0, h1619, h1685, h1686, h1744, h1746, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h0, h1621, h1661, h1741, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h0, h1106, h1620, h1621, h1685, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h0, h1619, h1621, h1684, hlam]
            · linarith only [h0, h1619, h1661, hlam]
        · linarith only [h0, h1106, h1620, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1756 | h1756
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1757 | h1757
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1758 | h1758
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1759 | h1759
              · linarith only [h1106, h1107, h1759, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1761 | h1761
                · linarith only [h1106, h1619, h1761, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1763 | h1763
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1764 | h1764
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1765 | h1765
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1766 | h1766
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1767 | h1767
                          · linarith only [h1106, h1759, h1767, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1769 | h1769
                            · linarith only [h1106, h1619, h1761, h1769, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1771 | h1771
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1772 | h1772
                                · linarith only [h1106, h1619, h1764, h1767, h1771, h1772, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1774 | h1774
                                  · linarith only [h1106, h1619, h1764, h1769, h1774, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1776 | h1776
                                    · linarith only [h1757, h1776, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                    · linarith only [h1763, h1776, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                              · linarith only [h1757, h1763, h1771, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h1106, h1107, h1758, h1764, h1765, h1766, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h1106, h1757, h1764, h1765, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1756, h1764, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1783 | h1783
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1784 | h1784
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1785 | h1785
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1786 | h1786
                          · linarith only [h1106, h1759, h1786, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1788 | h1788
                            · linarith only [h1106, h1107, h1761, h1763, h1788, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1790 | h1790
                              · linarith only [h1106, h1107, h1763, h1783, h1786, h1790, hc23, hc34, hlam, hphi]
                              · linarith only [h1106, h1107, h1783, h1790, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h1106, h1107, h1758, h1783, h1784, h1785, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h1757, h1784, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1756, h1783, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1796 | h1796
              · linarith only [h1106, h1107, h1796, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1798 | h1798
                · linarith only [h0, h1106, h1758, h1798, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1800 | h1800
                  · linarith only [h1757, h1758, h1800, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1802 | h1802
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1803 | h1803
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1804 | h1804
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1805 | h1805
                          · linarith only [h1106, h1796, h1805, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1807 | h1807
                            · linarith only [h1106, h1757, h1758, h1798, h1807, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1809 | h1809
                              · linarith only [h1106, h1107, h1800, h1802, h1805, h1809, hc23, hc34, hlam, hphi]
                              · linarith only [h1106, h1107, h1802, h1809, hc23, hc45, hlam, hphi, ht34]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1812 | h1812
                          · linarith only [h1106, h1812, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1814 | h1814
                            · linarith only [h1106, h1107, h1757, h1758, h1814, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1816 | h1816
                              · linarith only [h1106, h1107, h1800, h1802, h1812, h1816, hc23, hc34, hlam, hphi]
                              · linarith only [h1106, h1107, h1802, h1816, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h1757, h1758, h1803, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                    · linarith only [h0, h1756, h1758, h1802, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1821 | h1821
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1822 | h1822
              · linarith only [h0, h1106, h1757, h1822, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1824 | h1824
                · linarith only [h1106, h1619, h1824, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1826 | h1826
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1827 | h1827
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1828 | h1828
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1829 | h1829
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1830 | h1830
                          · linarith only [h1106, h1822, h1830, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1832 | h1832
                            · linarith only [h1106, h1619, h1824, h1832, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1834 | h1834
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1835 | h1835
                                · linarith only [h1756, h1757, h1828, h1830, h1835, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1837 | h1837
                                  · linarith only [h1106, h1827, h1832, h1837, hc15, hlam, hphi, ht0b, ht5b, u0elo0]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1839 | h1839
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1840 | h1840
                                      · rcases h2bigk with h1841c | h1841c | h1841c | h1841c | h1841c | h1841c | h1841c | h1841c | h1841c | h1841c | h1841c | h1841c | h1841c | h1841c | h1841c | h1841c | h1841c | h1841c | h1841c | h1841c | h1841c | h1841c | h1841c | h1841c | h1841c
                                        · have p1841_0 := h1841c.1
                                          have p1841_1 := h1841c.2.1
                                          have p1841_2 := h1841c.2.2.1
                                          have p1841_3 := h1841c.2.2.2
                                          linarith only [hlam, p1841_0]
                                        · have p1841_0 := h1841c.1
                                          have p1841_1 := h1841c.2.1
                                          have p1841_2 := h1841c.2.2.1
                                          have p1841_3 := h1841c.2.2.2
                                          linarith only [h0, hlam, p1841_1]
                                        · have p1841_0 := h1841c.1
                                          have p1841_1 := h1841c.2.1
                                          have p1841_2 := h1841c.2.2.1
                                          have p1841_3 := h1841c.2.2.2
                                          linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1841_1, u0elo1]
                                        · have p1841_0 := h1841c.1
                                          have p1841_1 := h1841c.2.1
                                          have p1841_2 := h1841c.2.2.1
                                          have p1841_3 := h1841c.2.2.2
                                          linarith only [h1757, hlam, p1841_0]
                                        · have p1841_0 := h1841c.1
                                          have p1841_1 := h1841c.2.1
                                          have p1841_2 := h1841c.2.2.1
                                          have p1841_3 := h1841c.2.2.2
                                          linarith only [h1757, h1828, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1841_1]
                                        · have p1841_0 := h1841c.1
                                          have p1841_1 := h1841c.2.1
                                          have p1841_2 := h1841c.2.2.1
                                          have p1841_3 := h1841c.2.2.2
                                          rcases p1841_3 (m.d 0 2) (by simp) with h1847 | h1847
                                          · linarith only [h0, h1847, hlam]
                                          · rcases p1841_3 (m.d 1 2) (by simp) with h1849 | h1849
                                            · rcases p1841_3 (m.d 2 3) (by simp) with h1850 | h1850
                                              · linarith only [h1827, h1850, hlam]
                                              · rcases p1841_3 (m.d 2 4) (by simp) with h1852 | h1852
                                                · linarith only [h1828, h1852, hlam]
                                                · linarith only [h1757, h1852, hlam]
                                            · linarith only [h0, h1849, hlam]
                                        · have p1841_0 := h1841c.1
                                          have p1841_1 := h1841c.2.1
                                          have p1841_2 := h1841c.2.2.1
                                          have p1841_3 := h1841c.2.2.2
                                          linarith only [hlam, p1841_0]
                                        · have p1841_0 := h1841c.1
                                          have p1841_1 := h1841c.2.1
                                          have p1841_2 := h1841c.2.2.1
                                          have p1841_3 := h1841c.2.2.2
                                          linarith only [h0, h1106, h1757, h1827, h1828, hlam, p1841_2]
                                        · have p1841_0 := h1841c.1
                                          have p1841_1 := h1841c.2.1
                                          have p1841_2 := h1841c.2.2.1
                                          have p1841_3 := h1841c.2.2.2
                                          linarith only [h0, h1106, h1757, h1827, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1841_1]
                                        · have p1841_0 := h1841c.1
                                          have p1841_1 := h1841c.2.1
                                          have p1841_2 := h1841c.2.2.1
                                          have p1841_3 := h1841c.2.2.2
                                          linarith only [h1757, h1821, h1828, hlam, p1841_2]
                                        · have p1841_0 := h1841c.1
                                          have p1841_1 := h1841c.2.1
                                          have p1841_2 := h1841c.2.2.1
                                          have p1841_3 := h1841c.2.2.2
                                          linarith only [h1756, hlam, p1841_0]
                                        · have p1841_0 := h1841c.1
                                          have p1841_1 := h1841c.2.1
                                          have p1841_2 := h1841c.2.2.1
                                          have p1841_3 := h1841c.2.2.2
                                          linarith only [h1827, hlam, p1841_0]
                                        · have p1841_0 := h1841c.1
                                          have p1841_1 := h1841c.2.1
                                          have p1841_2 := h1841c.2.2.1
                                          have p1841_3 := h1841c.2.2.2
                                          linarith only [hlam, p1841_0]
                                        · have p1841_0 := h1841c.1
                                          have p1841_1 := h1841c.2.1
                                          have p1841_2 := h1841c.2.2.1
                                          have p1841_3 := h1841c.2.2.2
                                          linarith only [h1835, hlam, p1841_0]
                                        · have p1841_0 := h1841c.1
                                          have p1841_1 := h1841c.2.1
                                          have p1841_2 := h1841c.2.2.1
                                          have p1841_3 := h1841c.2.2.2
                                          linarith only [h1837, hlam, p1841_0]
                                        · have p1841_0 := h1841c.1
                                          have p1841_1 := h1841c.2.1
                                          have p1841_2 := h1841c.2.2.1
                                          have p1841_3 := h1841c.2.2.2
                                          linarith only [h1106, h1619, h1821, h1827, h1828, h1830, hc23, hc34, hlam, hphi, p1841_1]
                                        · have p1841_0 := h1841c.1
                                          have p1841_1 := h1841c.2.1
                                          have p1841_2 := h1841c.2.2.1
                                          have p1841_3 := h1841c.2.2.2
                                          linarith only [h1828, hlam, p1841_0]
                                        · have p1841_0 := h1841c.1
                                          have p1841_1 := h1841c.2.1
                                          have p1841_2 := h1841c.2.2.1
                                          have p1841_3 := h1841c.2.2.2
                                          rcases p1841_3 (m.d 0 2) (by simp) with h1867 | h1867
                                          · linarith only [h1757, h1867, hlam]
                                          · linarith only [h1756, h1867, hlam]
                                        · have p1841_0 := h1841c.1
                                          have p1841_1 := h1841c.2.1
                                          have p1841_2 := h1841c.2.2.1
                                          have p1841_3 := h1841c.2.2.2
                                          linarith only [hlam, p1841_0]
                                        · have p1841_0 := h1841c.1
                                          have p1841_1 := h1841c.2.1
                                          have p1841_2 := h1841c.2.2.1
                                          have p1841_3 := h1841c.2.2.2
                                          rcases p1841_3 (m.d 0 2) (by simp) with h1871 | h1871
                                          · linarith only [h1757, h1871, hlam]
                                          · linarith only [h1821, h1871, hlam]
                                        · have p1841_0 := h1841c.1
                                          have p1841_1 := h1841c.2.1
                                          have p1841_2 := h1841c.2.2.1
                                          have p1841_3 := h1841c.2.2.2
                                          linarith only [h1821, hlam, p1841_0]
                                        · have p1841_0 := h1841c.1
                                          have p1841_1 := h1841c.2.1
                                          have p1841_2 := h1841c.2.2.1
                                          have p1841_3 := h1841c.2.2.2
                                          linarith only [h1829, hlam, p1841_0]
                                        · have p1841_0 := h1841c.1
                                          have p1841_1 := h1841c.2.1
                                          have p1841_2 := h1841c.2.2.1
                                          have p1841_3 := h1841c.2.2.2
                                          linarith only [h1821, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1841_1, u0elo1]
                                        · have p1841_0 := h1841c.1
                                          have p1841_1 := h1841c.2.1
                                          have p1841_2 := h1841c.2.2.1
                                          have p1841_3 := h1841c.2.2.2
                                          linarith only [h1839, hlam, p1841_0]
                                        · have p1841_0 := h1841c.1
                                          have p1841_1 := h1841c.2.1
                                          have p1841_2 := h1841c.2.2.1
                                          have p1841_3 := h1841c.2.2.2
                                          linarith only [hlam, p1841_0]
                                      · linarith only [h1106, h1107, h1827, h1830, h1840, hc23, hc45, hlam, hphi, ht34]
                                    · linarith only [h1757, h1826, h1839, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                              · linarith only [h1106, h1619, h1757, h1821, h1826, h1827, h1828, h1834, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                        · linarith only [h1821, h1829, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1883 | h1883
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1884 | h1884
                          · linarith only [h1106, h1619, h1828, h1883, h1884, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1886 | h1886
                            · linarith only [h1106, h1619, h1828, h1883, h1886, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1888 | h1888
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1889 | h1889
                                · linarith only [h1106, h1619, h1827, h1828, h1883, h1884, h1889, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h1106, h1619, h1827, h1828, h1883, h1889, hc23, hc34, hlam, hphi]
                              · linarith only [h1106, h1619, h1826, h1827, h1828, h1883, h1888, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                        · linarith only [h0, h1106, h1757, h1821, h1827, h1883, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h0, h1756, h1757, h1827, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h1757, h1821, h1826, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1896 | h1896
              · linarith only [h0, h1106, h1757, h1896, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1898 | h1898
                · linarith only [h1106, h1619, h1898, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1900 | h1900
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1901 | h1901
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1902 | h1902
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1903 | h1903
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1904 | h1904
                          · linarith only [h1106, h1896, h1904, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1906 | h1906
                            · linarith only [h0, h1106, h1821, h1898, h1906, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1908 | h1908
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1909 | h1909
                                · linarith only [h0, h1106, h1821, h1901, h1903, h1904, h1908, h1909, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1911 | h1911
                                  · linarith only [h0, h1106, h1821, h1901, h1903, h1906, h1911, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1913 | h1913
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1914 | h1914
                                      · rcases h2bigk with h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c | h1915c
                                        · have p1915_0 := h1915c.1
                                          have p1915_1 := h1915c.2.1
                                          have p1915_2 := h1915c.2.2.1
                                          have p1915_3 := h1915c.2.2.2
                                          linarith only [hlam, p1915_0]
                                        · have p1915_0 := h1915c.1
                                          have p1915_1 := h1915c.2.1
                                          have p1915_2 := h1915c.2.2.1
                                          have p1915_3 := h1915c.2.2.2
                                          linarith only [h0, hlam, p1915_1]
                                        · have p1915_0 := h1915c.1
                                          have p1915_1 := h1915c.2.1
                                          have p1915_2 := h1915c.2.2.1
                                          have p1915_3 := h1915c.2.2.2
                                          linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1915_1, u0elo1]
                                        · have p1915_0 := h1915c.1
                                          have p1915_1 := h1915c.2.1
                                          have p1915_2 := h1915c.2.2.1
                                          have p1915_3 := h1915c.2.2.2
                                          linarith only [h1757, hlam, p1915_0]
                                        · have p1915_0 := h1915c.1
                                          have p1915_1 := h1915c.2.1
                                          have p1915_2 := h1915c.2.2.1
                                          have p1915_3 := h1915c.2.2.2
                                          linarith only [h1821, hlam, p1915_0]
                                        · have p1915_0 := h1915c.1
                                          have p1915_1 := h1915c.2.1
                                          have p1915_2 := h1915c.2.2.1
                                          have p1915_3 := h1915c.2.2.2
                                          rcases p1915_3 (m.d 0 2) (by simp) with h1921 | h1921
                                          · linarith only [h0, h1921, hlam]
                                          · rcases p1915_3 (m.d 1 2) (by simp) with h1923 | h1923
                                            · rcases p1915_3 (m.d 2 3) (by simp) with h1924 | h1924
                                              · linarith only [h1901, h1924, hlam]
                                              · rcases p1915_3 (m.d 2 4) (by simp) with h1926 | h1926
                                                · linarith only [h1902, h1926, hlam]
                                                · linarith only [h1757, h1926, hlam]
                                            · linarith only [h0, h1923, hlam]
                                        · have p1915_0 := h1915c.1
                                          have p1915_1 := h1915c.2.1
                                          have p1915_2 := h1915c.2.2.1
                                          have p1915_3 := h1915c.2.2.2
                                          linarith only [hlam, p1915_0]
                                        · have p1915_0 := h1915c.1
                                          have p1915_1 := h1915c.2.1
                                          have p1915_2 := h1915c.2.2.1
                                          have p1915_3 := h1915c.2.2.2
                                          linarith only [h1756, h1821, h1902, h1913, hlam, p1915_2]
                                        · have p1915_0 := h1915c.1
                                          have p1915_1 := h1915c.2.1
                                          have p1915_2 := h1915c.2.2.1
                                          have p1915_3 := h1915c.2.2.2
                                          linarith only [h0, h1821, h1913, hc01, hc12, hlam, hphi, p1915_1]
                                        · have p1915_0 := h1915c.1
                                          have p1915_1 := h1915c.2.1
                                          have p1915_2 := h1915c.2.2.1
                                          have p1915_3 := h1915c.2.2.2
                                          linarith only [h0, h1106, h1821, h1901, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1915_1]
                                        · have p1915_0 := h1915c.1
                                          have p1915_1 := h1915c.2.1
                                          have p1915_2 := h1915c.2.2.1
                                          have p1915_3 := h1915c.2.2.2
                                          linarith only [h1756, hlam, p1915_0]
                                        · have p1915_0 := h1915c.1
                                          have p1915_1 := h1915c.2.1
                                          have p1915_2 := h1915c.2.2.1
                                          have p1915_3 := h1915c.2.2.2
                                          linarith only [h1901, hlam, p1915_0]
                                        · have p1915_0 := h1915c.1
                                          have p1915_1 := h1915c.2.1
                                          have p1915_2 := h1915c.2.2.1
                                          have p1915_3 := h1915c.2.2.2
                                          linarith only [hlam, p1915_0]
                                        · have p1915_0 := h1915c.1
                                          have p1915_1 := h1915c.2.1
                                          have p1915_2 := h1915c.2.2.1
                                          have p1915_3 := h1915c.2.2.2
                                          linarith only [h1909, hlam, p1915_0]
                                        · have p1915_0 := h1915c.1
                                          have p1915_1 := h1915c.2.1
                                          have p1915_2 := h1915c.2.2.1
                                          have p1915_3 := h1915c.2.2.2
                                          linarith only [h1911, hlam, p1915_0]
                                        · have p1915_0 := h1915c.1
                                          have p1915_1 := h1915c.2.1
                                          have p1915_2 := h1915c.2.2.1
                                          have p1915_3 := h1915c.2.2.2
                                          linarith only [h0, h1106, h1901, h1902, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1915_1]
                                        · have p1915_0 := h1915c.1
                                          have p1915_1 := h1915c.2.1
                                          have p1915_2 := h1915c.2.2.1
                                          have p1915_3 := h1915c.2.2.2
                                          linarith only [h1902, hlam, p1915_0]
                                        · have p1915_0 := h1915c.1
                                          have p1915_1 := h1915c.2.1
                                          have p1915_2 := h1915c.2.2.1
                                          have p1915_3 := h1915c.2.2.2
                                          rcases p1915_3 (m.d 0 2) (by simp) with h1941 | h1941
                                          · linarith only [h1757, h1941, hlam]
                                          · linarith only [h1756, h1941, hlam]
                                        · have p1915_0 := h1915c.1
                                          have p1915_1 := h1915c.2.1
                                          have p1915_2 := h1915c.2.2.1
                                          have p1915_3 := h1915c.2.2.2
                                          linarith only [hlam, p1915_0]
                                        · have p1915_0 := h1915c.1
                                          have p1915_1 := h1915c.2.1
                                          have p1915_2 := h1915c.2.2.1
                                          have p1915_3 := h1915c.2.2.2
                                          linarith only [h0, h1106, h1821, h1901, h1902, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1915_1]
                                        · have p1915_0 := h1915c.1
                                          have p1915_1 := h1915c.2.1
                                          have p1915_2 := h1915c.2.2.1
                                          have p1915_3 := h1915c.2.2.2
                                          linarith only [h0, h1106, h1901, h1903, h1906, hc23, hc35, hlam, hphi, p1915_1]
                                        · have p1915_0 := h1915c.1
                                          have p1915_1 := h1915c.2.1
                                          have p1915_2 := h1915c.2.2.1
                                          have p1915_3 := h1915c.2.2.2
                                          linarith only [h1903, hlam, p1915_0]
                                        · have p1915_0 := h1915c.1
                                          have p1915_1 := h1915c.2.1
                                          have p1915_2 := h1915c.2.2.1
                                          have p1915_3 := h1915c.2.2.2
                                          rcases p1915_3 (m.d 0 2) (by simp) with h1948 | h1948
                                          · linarith only [h1821, h1948, hlam]
                                          · linarith only [h1756, h1948, hlam]
                                        · have p1915_0 := h1915c.1
                                          have p1915_1 := h1915c.2.1
                                          have p1915_2 := h1915c.2.2.1
                                          have p1915_3 := h1915c.2.2.2
                                          linarith only [h1913, hlam, p1915_0]
                                        · have p1915_0 := h1915c.1
                                          have p1915_1 := h1915c.2.1
                                          have p1915_2 := h1915c.2.2.1
                                          have p1915_3 := h1915c.2.2.2
                                          linarith only [hlam, p1915_0]
                                      · linarith only [h1106, h1107, h1901, h1904, h1914, hc23, hc45, hlam, hphi, ht34]
                                    · linarith only [h0, h1106, h1757, h1900, h1901, h1913, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                              · linarith only [h1900, h1908, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                        · linarith only [h0, h1106, h1757, h1901, h1902, h1903, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1957 | h1957
                        · linarith only [h0, h1106, h1821, h1901, h1902, h1957, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1959 | h1959
                          · linarith only [h1106, h1896, h1959, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1961 | h1961
                            · linarith only [h0, h1106, h1821, h1900, h1961, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1963 | h1963
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1964 | h1964
                                · linarith only [h0, h1756, h1821, h1900, h1957, h1959, h1963, h1964, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                                · linarith only [h0, h1106, h1901, h1902, h1964, hc23, hc34, hlam, hphi]
                              · linarith only [h1900, h1963, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                    · linarith only [h0, h1756, h1821, h1900, h1901, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1969 | h1969
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1970 | h1970
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1971 | h1971
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1972 | h1972
                          · linarith only [h1106, h1972, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1974 | h1974
                            · linarith only [h1106, h1974, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1976 | h1976
                              · linarith only [h0, h1106, h1757, h1900, h1969, h1972, h1976, hc23, hc34, hlam, hphi]
                              · linarith only [h1106, h1107, h1969, h1976, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h0, h1106, h1757, h1969, h1970, h1971, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1980 | h1980
                        · linarith only [h0, h1106, h1821, h1969, h1970, h1980, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1982 | h1982
                          · linarith only [h1106, h1982, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1984 | h1984
                            · linarith only [h0, h1106, h1757, h1900, h1984, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1986 | h1986
                              · linarith only [h0, h1106, h1757, h1900, h1982, h1986, hc13, hc34, hlam, hphi]
                              · linarith only [h1106, h1107, h1969, h1986, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h1106, h1756, h1757, h1900, h1969, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
        · linarith only [h0, h1106, h1756, hlam]
  · exact r1l7_20_12_13_15_H_L_L_I_L_I_L_I_s1 m hb0 hb2 hb3 hb5 h0 h1106

end R2N4
