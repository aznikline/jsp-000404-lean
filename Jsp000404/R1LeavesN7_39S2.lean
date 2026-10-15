import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_39S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7188000 in
theorem r1l7_11_13_25_L_I_L_0_H_I_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h1bigk := hb1.1
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h1111 | h1111
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1112 | h1112
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1113 | h1113
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1114 | h1114
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1115 | h1115
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1116 | h1116
            · linarith only [h1116, h5, hc03, hlam, hphi, u3elo1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1118 | h1118
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1119 | h1119
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1120 | h1120
                  · linarith only [h1, h1118, h1120, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1122 | h1122
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1123 | h1123
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1124 | h1124
                        · rcases h1bigk with h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c
                          · have p1125_0 := h1125c.1
                            have p1125_1 := h1125c.2.1
                            have p1125_2 := h1125c.2.2.1
                            have p1125_3 := h1125c.2.2.2
                            linarith only [hlam, p1125_0]
                          · have p1125_0 := h1125c.1
                            have p1125_1 := h1125c.2.1
                            have p1125_2 := h1125c.2.2.1
                            have p1125_3 := h1125c.2.2.2
                            linarith only [h1113, h1122, h1124, hc01, hc45, hlam, hphi, ht0b, ht5b, p1125_1]
                          · have p1125_0 := h1125c.1
                            have p1125_1 := h1125c.2.1
                            have p1125_2 := h1125c.2.2.1
                            have p1125_3 := h1125c.2.2.2
                            rcases p1125_3 (m.d 0 1) (by simp) with h1128 | h1128
                            · rcases p1125_3 (m.d 1 2) (by simp) with h1129 | h1129
                              · linarith only [h0, h1129, hlam]
                              · linarith only [h1113, h1129, hlam]
                            · linarith only [h1128, hlam, p1125_0]
                          · have p1125_0 := h1125c.1
                            have p1125_1 := h1125c.2.1
                            have p1125_2 := h1125c.2.2.1
                            have p1125_3 := h1125c.2.2.2
                            rcases p1125_3 (m.d 0 1) (by simp) with h1133 | h1133
                            · rcases p1125_3 (m.d 1 2) (by simp) with h1134 | h1134
                              · linarith only [h0, h1134, hlam]
                              · linarith only [h1114, h1134, hlam]
                            · linarith only [h1133, hlam, p1125_0]
                          · have p1125_0 := h1125c.1
                            have p1125_1 := h1125c.2.1
                            have p1125_2 := h1125c.2.2.1
                            have p1125_3 := h1125c.2.2.2
                            rcases p1125_3 (m.d 0 1) (by simp) with h1138 | h1138
                            · rcases p1125_3 (m.d 1 2) (by simp) with h1139 | h1139
                              · linarith only [h0, h1139, hlam]
                              · linarith only [h1115, h1139, hlam]
                            · linarith only [h1138, hlam, p1125_0]
                          · have p1125_0 := h1125c.1
                            have p1125_1 := h1125c.2.1
                            have p1125_2 := h1125c.2.2.1
                            have p1125_3 := h1125c.2.2.2
                            linarith only [h0, hlam, p1125_0]
                          · have p1125_0 := h1125c.1
                            have p1125_1 := h1125c.2.1
                            have p1125_2 := h1125c.2.2.1
                            have p1125_3 := h1125c.2.2.2
                            linarith only [hlam, p1125_0]
                          · have p1125_0 := h1125c.1
                            have p1125_1 := h1125c.2.1
                            have p1125_2 := h1125c.2.2.1
                            have p1125_3 := h1125c.2.2.2
                            linarith only [h0, h1113, h1122, h1124, hc01, hc45, hlam, hphi, ht0b, ht5b, p1125_1]
                          · have p1125_0 := h1125c.1
                            have p1125_1 := h1125c.2.1
                            have p1125_2 := h1125c.2.2.1
                            have p1125_3 := h1125c.2.2.2
                            linarith only [h0, h1113, h1116, h1122, h1124, hc01, hc45, hlam, hphi, ht0b, ht5b, p1125_1]
                          · have p1125_0 := h1125c.1
                            have p1125_1 := h1125c.2.1
                            have p1125_2 := h1125c.2.2.1
                            have p1125_3 := h1125c.2.2.2
                            rcases p1125_3 (m.d 0 1) (by simp) with h1147 | h1147
                            · rcases p1125_3 (m.d 1 2) (by simp) with h1148 | h1148
                              · rcases p1125_3 (m.d 1 3) (by simp) with h1149 | h1149
                                · linarith only [h1113, h1149, hlam]
                                · linarith only [h1118, h1149, hlam]
                              · linarith only [h1115, h1148, hlam]
                            · linarith only [h1147, h3, hlam]
                          · have p1125_0 := h1125c.1
                            have p1125_1 := h1125c.2.1
                            have p1125_2 := h1125c.2.2.1
                            have p1125_3 := h1125c.2.2.2
                            linarith only [h1, hlam, p1125_0]
                          · have p1125_0 := h1125c.1
                            have p1125_1 := h1125c.2.1
                            have p1125_2 := h1125c.2.2.1
                            have p1125_3 := h1125c.2.2.2
                            linarith only [h1113, hlam, p1125_1]
                          · have p1125_0 := h1125c.1
                            have p1125_1 := h1125c.2.1
                            have p1125_2 := h1125c.2.2.1
                            have p1125_3 := h1125c.2.2.2
                            linarith only [hlam, p1125_0]
                          · have p1125_0 := h1125c.1
                            have p1125_1 := h1125c.2.1
                            have p1125_2 := h1125c.2.2.1
                            have p1125_3 := h1125c.2.2.2
                            linarith only [h1116, hlam, p1125_1]
                          · have p1125_0 := h1125c.1
                            have p1125_1 := h1125c.2.1
                            have p1125_2 := h1125c.2.2.1
                            have p1125_3 := h1125c.2.2.2
                            linarith only [h1, h1115, h5, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1125_1, u3elo3]
                          · have p1125_0 := h1125c.1
                            have p1125_1 := h1125c.2.1
                            have p1125_2 := h1125c.2.2.1
                            have p1125_3 := h1125c.2.2.2
                            linarith only [h2, hlam, p1125_0]
                          · have p1125_0 := h1125c.1
                            have p1125_1 := h1125c.2.1
                            have p1125_2 := h1125c.2.2.1
                            have p1125_3 := h1125c.2.2.2
                            linarith only [h1114, hlam, p1125_1]
                          · have p1125_0 := h1125c.1
                            have p1125_1 := h1125c.2.1
                            have p1125_2 := h1125c.2.2.1
                            have p1125_3 := h1125c.2.2.2
                            linarith only [h2, h5, hc13, hlam, hphi, p1125_1, u3elo3]
                          · have p1125_0 := h1125c.1
                            have p1125_1 := h1125c.2.1
                            have p1125_2 := h1125c.2.2.1
                            have p1125_3 := h1125c.2.2.2
                            linarith only [hlam, p1125_0]
                          · have p1125_0 := h1125c.1
                            have p1125_1 := h1125c.2.1
                            have p1125_2 := h1125c.2.2.1
                            have p1125_3 := h1125c.2.2.2
                            rcases p1125_3 (m.d 0 1) (by simp) with h1163 | h1163
                            · rcases p1125_3 (m.d 1 2) (by simp) with h1164 | h1164
                              · rcases p1125_3 (m.d 1 3) (by simp) with h1165 | h1165
                                · linarith only [h1116, h1165, hlam]
                                · linarith only [h1118, h1165, hlam]
                              · linarith only [h1115, h1164, hlam]
                            · linarith only [h1163, h3, hlam]
                          · have p1125_0 := h1125c.1
                            have p1125_1 := h1125c.2.1
                            have p1125_2 := h1125c.2.2.1
                            have p1125_3 := h1125c.2.2.2
                            linarith only [h3, hlam, p1125_0]
                          · have p1125_0 := h1125c.1
                            have p1125_1 := h1125c.2.1
                            have p1125_2 := h1125c.2.2.1
                            have p1125_3 := h1125c.2.2.2
                            linarith only [h1115, hlam, p1125_1]
                          · have p1125_0 := h1125c.1
                            have p1125_1 := h1125c.2.1
                            have p1125_2 := h1125c.2.2.1
                            have p1125_3 := h1125c.2.2.2
                            linarith only [h1118, hlam, p1125_0]
                          · have p1125_0 := h1125c.1
                            have p1125_1 := h1125c.2.1
                            have p1125_2 := h1125c.2.2.1
                            have p1125_3 := h1125c.2.2.2
                            linarith only [h1119, hlam, p1125_0]
                          · have p1125_0 := h1125c.1
                            have p1125_1 := h1125c.2.1
                            have p1125_2 := h1125c.2.2.1
                            have p1125_3 := h1125c.2.2.2
                            linarith only [hlam, p1125_0]
                        · linarith only [h1112, h1124, h5, hlam]
                      · linarith only [h1111, h1119, h1120, h1122, h1123, h3, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                    · linarith only [h1111, h1122, h5, hc23, hlam, hphi, u3elo3]
                · linarith only [h1111, h1112, h1116, h1119, h5, hc13, hlam, hphi, u3elo3]
              · linarith only [h1111, h1113, h1118, h5, hc23, hlam, hphi, u3elo3]
          · linarith only [h1111, h1115, h4, h5, hc12, hlam, hphi, ht23, u3elo3]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1181 | h1181
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1182 | h1182
            · linarith only [h1182, h5, hc03, hlam, hphi, u3elo1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1184 | h1184
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1185 | h1185
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1186 | h1186
                  · linarith only [h1, h1113, h1114, h1184, h1186, h2, h5, hc04, hc35, hlam, hphi, ht0b, ht5b]
                  · linarith only [h1113, h1114, h1186, hc23, hlam, hphi, u3elo3]
                · linarith only [h1111, h1112, h1113, h1114, h1185, hc23, hlam, hphi, u3elo0]
              · linarith only [h1111, h1184, h5, hc13, hlam, hphi, u3elo3]
          · linarith only [h1111, h1113, h1181, h4, h5, hc23, hlam, hphi, u3elo3]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1192 | h1192
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1193 | h1193
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1194 | h1194
            · linarith only [h1, h1194, h5, hlam]
            · linarith only [h1113, h1192, h1194, hlam]
          · linarith only [h1111, h1192, h1193, h4, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1198 | h1198
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1199 | h1199
            · linarith only [h1, h1199, h5, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1201 | h1201
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1202 | h1202
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1203 | h1203
                  · linarith only [h1203, h5, hc03, hlam, hphi, u3elo2]
                  · linarith only [h1113, h1198, h1203, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                · linarith only [h1112, h1113, h1198, h1199, h1202, h5, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
              · linarith only [h1111, h1113, h1198, h1201, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
          · linarith only [h1111, h1198, h4, h5, hc12, hlam, hphi, ht23, u3elo3]
    · linarith only [h1111, h1112, h5, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1210 | h1210
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1211 | h1211
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1212 | h1212
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1213 | h1213
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1214 | h1214
            · linarith only [h1214, h5, hc03, hlam, hphi, u3elo1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1216 | h1216
              · linarith only [h1, h1111, h1216, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1218 | h1218
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1219 | h1219
                  · linarith only [h1, h1211, h1219, h5, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1221 | h1221
                    · linarith only [h1, h1111, h1211, h1221, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1223 | h1223
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1224 | h1224
                        · rcases h1bigk with h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c | h1225c
                          · have p1225_0 := h1225c.1
                            have p1225_1 := h1225c.2.1
                            have p1225_2 := h1225c.2.2.1
                            have p1225_3 := h1225c.2.2.2
                            linarith only [hlam, p1225_0]
                          · have p1225_0 := h1225c.1
                            have p1225_1 := h1225c.2.1
                            have p1225_2 := h1225c.2.2.1
                            have p1225_3 := h1225c.2.2.2
                            linarith only [h1212, h1223, hc01, hc45, hlam, hphi, ht0b, ht5b, p1225_1]
                          · have p1225_0 := h1225c.1
                            have p1225_1 := h1225c.2.1
                            have p1225_2 := h1225c.2.2.1
                            have p1225_3 := h1225c.2.2.2
                            rcases p1225_3 (m.d 0 1) (by simp) with h1228 | h1228
                            · rcases p1225_3 (m.d 1 2) (by simp) with h1229 | h1229
                              · linarith only [h0, h1229, hlam]
                              · linarith only [h1211, h1229, hlam]
                            · linarith only [h1228, hlam, p1225_0]
                          · have p1225_0 := h1225c.1
                            have p1225_1 := h1225c.2.1
                            have p1225_2 := h1225c.2.2.1
                            have p1225_3 := h1225c.2.2.2
                            rcases p1225_3 (m.d 0 1) (by simp) with h1233 | h1233
                            · rcases p1225_3 (m.d 1 2) (by simp) with h1234 | h1234
                              · linarith only [h0, h1234, hlam]
                              · linarith only [h1212, h1234, hlam]
                            · linarith only [h1233, hlam, p1225_0]
                          · have p1225_0 := h1225c.1
                            have p1225_1 := h1225c.2.1
                            have p1225_2 := h1225c.2.2.1
                            have p1225_3 := h1225c.2.2.2
                            rcases p1225_3 (m.d 0 1) (by simp) with h1238 | h1238
                            · rcases p1225_3 (m.d 1 2) (by simp) with h1239 | h1239
                              · linarith only [h0, h1239, hlam]
                              · linarith only [h1213, h1239, hlam]
                            · linarith only [h1238, hlam, p1225_0]
                          · have p1225_0 := h1225c.1
                            have p1225_1 := h1225c.2.1
                            have p1225_2 := h1225c.2.2.1
                            have p1225_3 := h1225c.2.2.2
                            linarith only [h0, hlam, p1225_0]
                          · have p1225_0 := h1225c.1
                            have p1225_1 := h1225c.2.1
                            have p1225_2 := h1225c.2.2.1
                            have p1225_3 := h1225c.2.2.2
                            linarith only [hlam, p1225_0]
                          · have p1225_0 := h1225c.1
                            have p1225_1 := h1225c.2.1
                            have p1225_2 := h1225c.2.2.1
                            have p1225_3 := h1225c.2.2.2
                            rcases p1225_3 (m.d 0 1) (by simp) with h1245 | h1245
                            · rcases p1225_3 (m.d 1 2) (by simp) with h1246 | h1246
                              · rcases p1225_3 (m.d 1 3) (by simp) with h1247 | h1247
                                · linarith only [h1211, h1247, hlam]
                                · rcases p1225_3 (m.d 1 4) (by simp) with h1249 | h1249
                                  · linarith only [h1212, h1249, hlam]
                                  · linarith only [h1214, h1249, hlam]
                              · linarith only [h1211, h1246, hlam]
                            · linarith only [h1, h1245, hlam]
                          · have p1225_0 := h1225c.1
                            have p1225_1 := h1225c.2.1
                            have p1225_2 := h1225c.2.2.1
                            have p1225_3 := h1225c.2.2.2
                            linarith only [h0, h1212, h1223, hc01, hc45, hlam, hphi, ht0b, ht5b, p1225_1]
                          · have p1225_0 := h1225c.1
                            have p1225_1 := h1225c.2.1
                            have p1225_2 := h1225c.2.2.1
                            have p1225_3 := h1225c.2.2.2
                            rcases p1225_3 (m.d 0 1) (by simp) with h1255 | h1255
                            · rcases p1225_3 (m.d 1 2) (by simp) with h1256 | h1256
                              · rcases p1225_3 (m.d 1 3) (by simp) with h1257 | h1257
                                · linarith only [h1211, h1257, hlam]
                                · rcases p1225_3 (m.d 1 4) (by simp) with h1259 | h1259
                                  · linarith only [h1212, h1259, hlam]
                                  · linarith only [h1218, h1259, hlam]
                              · linarith only [h1213, h1256, hlam]
                            · linarith only [h1255, h3, hlam]
                          · have p1225_0 := h1225c.1
                            have p1225_1 := h1225c.2.1
                            have p1225_2 := h1225c.2.2.1
                            have p1225_3 := h1225c.2.2.2
                            linarith only [h1, hlam, p1225_0]
                          · have p1225_0 := h1225c.1
                            have p1225_1 := h1225c.2.1
                            have p1225_2 := h1225c.2.2.1
                            have p1225_3 := h1225c.2.2.2
                            linarith only [h1211, hlam, p1225_1]
                          · have p1225_0 := h1225c.1
                            have p1225_1 := h1225c.2.1
                            have p1225_2 := h1225c.2.2.1
                            have p1225_3 := h1225c.2.2.2
                            linarith only [hlam, p1225_0]
                          · have p1225_0 := h1225c.1
                            have p1225_1 := h1225c.2.1
                            have p1225_2 := h1225c.2.2.1
                            have p1225_3 := h1225c.2.2.2
                            linarith only [h1214, hlam, p1225_1]
                          · have p1225_0 := h1225c.1
                            have p1225_1 := h1225c.2.1
                            have p1225_2 := h1225c.2.2.1
                            have p1225_3 := h1225c.2.2.2
                            linarith only [h1216, hlam, p1225_1]
                          · have p1225_0 := h1225c.1
                            have p1225_1 := h1225c.2.1
                            have p1225_2 := h1225c.2.2.1
                            have p1225_3 := h1225c.2.2.2
                            linarith only [h2, hlam, p1225_0]
                          · have p1225_0 := h1225c.1
                            have p1225_1 := h1225c.2.1
                            have p1225_2 := h1225c.2.2.1
                            have p1225_3 := h1225c.2.2.2
                            linarith only [h1212, hlam, p1225_1]
                          · have p1225_0 := h1225c.1
                            have p1225_1 := h1225c.2.1
                            have p1225_2 := h1225c.2.2.1
                            have p1225_3 := h1225c.2.2.2
                            linarith only [h1211, h2, h5, hc23, hlam, hphi, p1225_1, u3elo3]
                          · have p1225_0 := h1225c.1
                            have p1225_1 := h1225c.2.1
                            have p1225_2 := h1225c.2.2.1
                            have p1225_3 := h1225c.2.2.2
                            linarith only [hlam, p1225_0]
                          · have p1225_0 := h1225c.1
                            have p1225_1 := h1225c.2.1
                            have p1225_2 := h1225c.2.2.1
                            have p1225_3 := h1225c.2.2.2
                            linarith only [h1211, h1216, h2, h5, hc23, hlam, hphi, p1225_1, u3elo3]
                          · have p1225_0 := h1225c.1
                            have p1225_1 := h1225c.2.1
                            have p1225_2 := h1225c.2.2.1
                            have p1225_3 := h1225c.2.2.2
                            linarith only [h3, hlam, p1225_0]
                          · have p1225_0 := h1225c.1
                            have p1225_1 := h1225c.2.1
                            have p1225_2 := h1225c.2.2.1
                            have p1225_3 := h1225c.2.2.2
                            linarith only [h1213, hlam, p1225_1]
                          · have p1225_0 := h1225c.1
                            have p1225_1 := h1225c.2.1
                            have p1225_2 := h1225c.2.2.1
                            have p1225_3 := h1225c.2.2.2
                            linarith only [h1111, h1211, h3, hc23, hlam, hphi, p1225_1, u3elo4]
                          · have p1225_0 := h1225c.1
                            have p1225_1 := h1225c.2.1
                            have p1225_2 := h1225c.2.2.1
                            have p1225_3 := h1225c.2.2.2
                            linarith only [h1218, hlam, p1225_0]
                          · have p1225_0 := h1225c.1
                            have p1225_1 := h1225c.2.1
                            have p1225_2 := h1225c.2.2.1
                            have p1225_3 := h1225c.2.2.2
                            linarith only [hlam, p1225_0]
                        · linarith only [h1210, h1224, h5, hlam]
                      · linarith only [h1218, h1219, h1223, h2, h5, hc23, hlam, hphi, u3elo3]
                · linarith only [h1210, h1211, h1214, h1218, h5, hc23, hlam, hphi, u3elo3]
          · linarith only [h1210, h1211, h1213, h4, h5, hc23, hlam, hphi, u3elo3]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1283 | h1283
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1284 | h1284
            · linarith only [h1, h1211, h1212, h1284, h2, h5, hc23, hlam, hphi, u3elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1286 | h1286
              · linarith only [h1, h1111, h1286, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1288 | h1288
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1289 | h1289
                  · linarith only [h1, h1211, h1212, h1289, h5, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h1211, h1212, h1289, hc23, hlam, hphi, u3elo3]
                · linarith only [h1210, h1211, h1212, h1288, h5, hc23, hlam, hphi, u3elo3]
          · linarith only [h1111, h1211, h1283, h4, hc23, hlam, hphi, u3elo4]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1294 | h1294
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1295 | h1295
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1296 | h1296
            · linarith only [h1, h1296, h5, hlam]
            · linarith only [h1211, h1294, h1296, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1299 | h1299
            · linarith only [h1299, h5, hc03, hlam, hphi, u3elo1]
            · linarith only [h1211, h1294, h1299, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1302 | h1302
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1303 | h1303
            · linarith only [h1, h1303, h5, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1305 | h1305
              · linarith only [h1, h1111, h1305, hlam]
              · linarith only [h1211, h1302, h1305, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1308 | h1308
            · linarith only [h1, h1308, h5, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1310 | h1310
              · linarith only [h1, h1111, h1310, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1312 | h1312
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1313 | h1313
                  · linarith only [h1313, h5, hc03, hlam, hphi, u3elo2]
                  · linarith only [h1211, h1313, hc12, hlam, hphi, ht23, u3elo3]
                · linarith only [h1210, h1294, h1312, h5, hc12, hlam, hphi, ht23, u3elo3]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1317 | h1317
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1318 | h1318
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1319 | h1319
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1320 | h1320
            · linarith only [h1, h1320, h5, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1322 | h1322
              · linarith only [h1, h1111, h1322, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1324 | h1324
                · linarith only [h1210, h1324, h2, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1326 | h1326
                  · linarith only [h1, h1317, h1326, h5, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1328 | h1328
                    · linarith only [h1111, h1317, h1320, h1324, h1328, h3, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1330 | h1330
                      · linarith only [h0, h1210, h1318, h1330, h5, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1332 | h1332
                        · linarith only [h1, h1210, h1317, h1332, h5, hc23, hlam, hphi, u3elo3]
                        · rcases h1bigk with h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c | h1334c
                          · have p1334_0 := h1334c.1
                            have p1334_1 := h1334c.2.1
                            have p1334_2 := h1334c.2.2.1
                            have p1334_3 := h1334c.2.2.2
                            linarith only [hlam, p1334_0]
                          · have p1334_0 := h1334c.1
                            have p1334_1 := h1334c.2.1
                            have p1334_2 := h1334c.2.2.1
                            have p1334_3 := h1334c.2.2.2
                            rcases p1334_3 (m.d 0 1) (by simp) with h1336 | h1336
                            · rcases p1334_3 (m.d 1 2) (by simp) with h1337 | h1337
                              · linarith only [h1337, hlam, p1334_0]
                              · rcases p1334_3 (m.d 1 3) (by simp) with h1339 | h1339
                                · linarith only [h1, h1339, hlam]
                                · rcases p1334_3 (m.d 1 4) (by simp) with h1341 | h1341
                                  · linarith only [h1341, h2, hlam]
                                  · rcases p1334_3 (m.d 1 5) (by simp) with h1343 | h1343
                                    · linarith only [h1343, h3, hlam]
                                    · rcases h1emin with h1345 | h1345 | h1345 | h1345 | h1345
                                      · rcases h5bigk with h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c
                                        · have p1346_0 := h1346c.1
                                          have p1346_1 := h1346c.2.1
                                          have p1346_2 := h1346c.2.2.1
                                          have p1346_3 := h1346c.2.2.2
                                          linarith only [hlam, p1346_0]
                                        · have p1346_0 := h1346c.1
                                          have p1346_1 := h1346c.2.1
                                          have p1346_2 := h1346c.2.2.1
                                          have p1346_3 := h1346c.2.2.2
                                          linarith only [h1111, h1317, h1320, h1324, hc23, hlam, hphi, p1346_1, u3elo4]
                                        · have p1346_0 := h1346c.1
                                          have p1346_1 := h1346c.2.1
                                          have p1346_2 := h1346c.2.2.1
                                          have p1346_3 := h1346c.2.2.2
                                          linarith only [h1111, h1326, h1330, hc23, hlam, hphi, p1346_1, u3elo4]
                                        · have p1346_0 := h1346c.1
                                          have p1346_1 := h1346c.2.1
                                          have p1346_2 := h1346c.2.2.1
                                          have p1346_3 := h1346c.2.2.2
                                          linarith only [h1111, hlam, p1346_1]
                                        · have p1346_0 := h1346c.1
                                          have p1346_1 := h1346c.2.1
                                          have p1346_2 := h1346c.2.2.1
                                          have p1346_3 := h1346c.2.2.2
                                          linarith only [h1210, hlam, p1346_1]
                                        · have p1346_0 := h1346c.1
                                          have p1346_1 := h1346c.2.1
                                          have p1346_2 := h1346c.2.2.1
                                          have p1346_3 := h1346c.2.2.2
                                          linarith only [h3, hlam, p1346_0]
                                        · have p1346_0 := h1346c.1
                                          have p1346_1 := h1346c.2.1
                                          have p1346_2 := h1346c.2.2.1
                                          have p1346_3 := h1346c.2.2.2
                                          linarith only [hlam, p1346_0]
                                        · have p1346_0 := h1346c.1
                                          have p1346_1 := h1346c.2.1
                                          have p1346_2 := h1346c.2.2.1
                                          have p1346_3 := h1346c.2.2.2
                                          linarith only [h1326, h1330, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1346_1]
                                        · have p1346_0 := h1346c.1
                                          have p1346_1 := h1346c.2.1
                                          have p1346_2 := h1346c.2.2.1
                                          have p1346_3 := h1346c.2.2.2
                                          linarith only [h1322, hlam, p1346_1]
                                        · have p1346_0 := h1346c.1
                                          have p1346_1 := h1346c.2.1
                                          have p1346_2 := h1346c.2.2.1
                                          have p1346_3 := h1346c.2.2.2
                                          linarith only [h1324, hlam, p1346_1]
                                        · have p1346_0 := h1346c.1
                                          have p1346_1 := h1346c.2.1
                                          have p1346_2 := h1346c.2.2.1
                                          have p1346_3 := h1346c.2.2.2
                                          linarith only [h4, hlam, p1346_1]
                                        · have p1346_0 := h1346c.1
                                          have p1346_1 := h1346c.2.1
                                          have p1346_2 := h1346c.2.2.1
                                          have p1346_3 := h1346c.2.2.2
                                          linarith only [h1319, hlam, p1346_1]
                                        · have p1346_0 := h1346c.1
                                          have p1346_1 := h1346c.2.1
                                          have p1346_2 := h1346c.2.2.1
                                          have p1346_3 := h1346c.2.2.2
                                          linarith only [hlam, p1346_0]
                                        · have p1346_0 := h1346c.1
                                          have p1346_1 := h1346c.2.1
                                          have p1346_2 := h1346c.2.2.1
                                          have p1346_3 := h1346c.2.2.2
                                          linarith only [h1328, hlam, p1346_1]
                                        · have p1346_0 := h1346c.1
                                          have p1346_1 := h1346c.2.1
                                          have p1346_2 := h1346c.2.2.1
                                          have p1346_3 := h1346c.2.2.2
                                          linarith only [h1330, hlam, p1346_1]
                                        · have p1346_0 := h1346c.1
                                          have p1346_1 := h1346c.2.1
                                          have p1346_2 := h1346c.2.2.1
                                          have p1346_3 := h1346c.2.2.2
                                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1346_1, u3elo4]
                                        · have p1346_0 := h1346c.1
                                          have p1346_1 := h1346c.2.1
                                          have p1346_2 := h1346c.2.2.1
                                          have p1346_3 := h1346c.2.2.2
                                          linarith only [h1319, h1326, h1330, hc23, hlam, hphi, p1346_1, u3elo4]
                                        · have p1346_0 := h1346c.1
                                          have p1346_1 := h1346c.2.1
                                          have p1346_2 := h1346c.2.2.1
                                          have p1346_3 := h1346c.2.2.2
                                          linarith only [h1326, h1330, hc23, hlam, hphi, p1346_1, u3elo4]
                                        · have p1346_0 := h1346c.1
                                          have p1346_1 := h1346c.2.1
                                          have p1346_2 := h1346c.2.2.1
                                          have p1346_3 := h1346c.2.2.2
                                          linarith only [hlam, p1346_0]
                                        · have p1346_0 := h1346c.1
                                          have p1346_1 := h1346c.2.1
                                          have p1346_2 := h1346c.2.2.1
                                          have p1346_3 := h1346c.2.2.2
                                          linarith only [h1332, hlam, p1346_1]
                                        · have p1346_0 := h1346c.1
                                          have p1346_1 := h1346c.2.1
                                          have p1346_2 := h1346c.2.2.1
                                          have p1346_3 := h1346c.2.2.2
                                          linarith only [h1, h1210, h1317, h5, hc23, hc45, hlam, hphi, ht34, p1346_1]
                                        · have p1346_0 := h1346c.1
                                          have p1346_1 := h1346c.2.1
                                          have p1346_2 := h1346c.2.2.1
                                          have p1346_3 := h1346c.2.2.2
                                          linarith only [h1319, h1326, h1330, hc23, hc45, hlam, hphi, ht34, p1346_1]
                                        · have p1346_0 := h1346c.1
                                          have p1346_1 := h1346c.2.1
                                          have p1346_2 := h1346c.2.2.1
                                          have p1346_3 := h1346c.2.2.2
                                          linarith only [h1326, h1330, hc23, hc45, hlam, hphi, ht34, p1346_1]
                                        · have p1346_0 := h1346c.1
                                          have p1346_1 := h1346c.2.1
                                          have p1346_2 := h1346c.2.2.1
                                          have p1346_3 := h1346c.2.2.2
                                          linarith only [h1, h1111, h1317, hc23, hc45, hlam, hphi, ht34, p1346_1]
                                        · have p1346_0 := h1346c.1
                                          have p1346_1 := h1346c.2.1
                                          have p1346_2 := h1346c.2.2.1
                                          have p1346_3 := h1346c.2.2.2
                                          linarith only [hlam, p1346_0]
                                      · linarith only [h1345, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1334_1]
                                      · linarith only [h1, h1345, h5, hlam, ht12, ht23, u3elo3]
                                      · linarith only [h1345, h2, h5, hlam, ht12, ht23, u3elo3]
                                      · linarith only [h1111, h1345, h3, hlam, ht12, ht23, u3elo4]
                            · linarith only [h1336, hlam, p1334_0]
                          · have p1334_0 := h1334c.1
                            have p1334_1 := h1334c.2.1
                            have p1334_2 := h1334c.2.2.1
                            have p1334_3 := h1334c.2.2.2
                            rcases p1334_3 (m.d 0 1) (by simp) with h1377 | h1377
                            · rcases p1334_3 (m.d 1 2) (by simp) with h1378 | h1378
                              · linarith only [h0, h1378, hlam]
                              · linarith only [h1317, h1378, hlam]
                            · linarith only [h1377, hlam, p1334_0]
                          · have p1334_0 := h1334c.1
                            have p1334_1 := h1334c.2.1
                            have p1334_2 := h1334c.2.2.1
                            have p1334_3 := h1334c.2.2.2
                            rcases p1334_3 (m.d 0 1) (by simp) with h1382 | h1382
                            · rcases p1334_3 (m.d 1 2) (by simp) with h1383 | h1383
                              · linarith only [h0, h1383, hlam]
                              · linarith only [h1318, h1383, hlam]
                            · linarith only [h1382, hlam, p1334_0]
                          · have p1334_0 := h1334c.1
                            have p1334_1 := h1334c.2.1
                            have p1334_2 := h1334c.2.2.1
                            have p1334_3 := h1334c.2.2.2
                            rcases p1334_3 (m.d 0 1) (by simp) with h1387 | h1387
                            · rcases p1334_3 (m.d 1 2) (by simp) with h1388 | h1388
                              · linarith only [h0, h1388, hlam]
                              · linarith only [h1319, h1388, hlam]
                            · linarith only [h1387, hlam, p1334_0]
                          · have p1334_0 := h1334c.1
                            have p1334_1 := h1334c.2.1
                            have p1334_2 := h1334c.2.2.1
                            have p1334_3 := h1334c.2.2.2
                            linarith only [h0, hlam, p1334_0]
                          · have p1334_0 := h1334c.1
                            have p1334_1 := h1334c.2.1
                            have p1334_2 := h1334c.2.2.1
                            have p1334_3 := h1334c.2.2.2
                            linarith only [hlam, p1334_0]
                          · have p1334_0 := h1334c.1
                            have p1334_1 := h1334c.2.1
                            have p1334_2 := h1334c.2.2.1
                            have p1334_3 := h1334c.2.2.2
                            rcases p1334_3 (m.d 0 1) (by simp) with h1394 | h1394
                            · rcases p1334_3 (m.d 1 2) (by simp) with h1395 | h1395
                              · rcases p1334_3 (m.d 1 3) (by simp) with h1396 | h1396
                                · linarith only [h1317, h1396, hlam]
                                · rcases p1334_3 (m.d 1 4) (by simp) with h1398 | h1398
                                  · linarith only [h1318, h1398, hlam]
                                  · linarith only [h1320, h1398, hlam]
                              · linarith only [h1317, h1395, hlam]
                            · linarith only [h1, h1394, hlam]
                          · have p1334_0 := h1334c.1
                            have p1334_1 := h1334c.2.1
                            have p1334_2 := h1334c.2.2.1
                            have p1334_3 := h1334c.2.2.2
                            rcases p1334_3 (m.d 0 1) (by simp) with h1403 | h1403
                            · rcases p1334_3 (m.d 1 2) (by simp) with h1404 | h1404
                              · rcases p1334_3 (m.d 1 3) (by simp) with h1405 | h1405
                                · linarith only [h1317, h1405, hlam]
                                · rcases p1334_3 (m.d 1 4) (by simp) with h1407 | h1407
                                  · linarith only [h1318, h1407, hlam]
                                  · rcases p1334_3 (m.d 1 5) (by simp) with h1409 | h1409
                                    · linarith only [h1319, h1409, hlam]
                                    · linarith only [h1324, h1409, hlam]
                              · linarith only [h1318, h1404, hlam]
                            · linarith only [h1403, h2, hlam]
                          · have p1334_0 := h1334c.1
                            have p1334_1 := h1334c.2.1
                            have p1334_2 := h1334c.2.2.1
                            have p1334_3 := h1334c.2.2.2
                            rcases p1334_3 (m.d 0 1) (by simp) with h1414 | h1414
                            · rcases p1334_3 (m.d 1 2) (by simp) with h1415 | h1415
                              · rcases p1334_3 (m.d 1 3) (by simp) with h1416 | h1416
                                · linarith only [h1317, h1416, hlam]
                                · rcases p1334_3 (m.d 1 4) (by simp) with h1418 | h1418
                                  · linarith only [h1318, h1418, hlam]
                                  · rcases p1334_3 (m.d 1 5) (by simp) with h1420 | h1420
                                    · linarith only [h1319, h1420, hlam]
                                    · rcases h1emin with h1422 | h1422 | h1422 | h1422 | h1422
                                      · rcases h5bigk with h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c
                                        · have p1423_0 := h1423c.1
                                          have p1423_1 := h1423c.2.1
                                          have p1423_2 := h1423c.2.2.1
                                          have p1423_3 := h1423c.2.2.2
                                          linarith only [hlam, p1423_0]
                                        · have p1423_0 := h1423c.1
                                          have p1423_1 := h1423c.2.1
                                          have p1423_2 := h1423c.2.2.1
                                          have p1423_3 := h1423c.2.2.2
                                          linarith only [h1111, h1324, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1423_1, u3elo4]
                                        · have p1423_0 := h1423c.1
                                          have p1423_1 := h1423c.2.1
                                          have p1423_2 := h1423c.2.2.1
                                          have p1423_3 := h1423c.2.2.2
                                          linarith only [h1111, h1326, h1330, hc23, hlam, hphi, p1423_1, u3elo4]
                                        · have p1423_0 := h1423c.1
                                          have p1423_1 := h1423c.2.1
                                          have p1423_2 := h1423c.2.2.1
                                          have p1423_3 := h1423c.2.2.2
                                          linarith only [h1111, hlam, p1423_1]
                                        · have p1423_0 := h1423c.1
                                          have p1423_1 := h1423c.2.1
                                          have p1423_2 := h1423c.2.2.1
                                          have p1423_3 := h1423c.2.2.2
                                          linarith only [h1210, hlam, p1423_1]
                                        · have p1423_0 := h1423c.1
                                          have p1423_1 := h1423c.2.1
                                          have p1423_2 := h1423c.2.2.1
                                          have p1423_3 := h1423c.2.2.2
                                          linarith only [h3, hlam, p1423_0]
                                        · have p1423_0 := h1423c.1
                                          have p1423_1 := h1423c.2.1
                                          have p1423_2 := h1423c.2.2.1
                                          have p1423_3 := h1423c.2.2.2
                                          linarith only [hlam, p1423_0]
                                        · have p1423_0 := h1423c.1
                                          have p1423_1 := h1423c.2.1
                                          have p1423_2 := h1423c.2.2.1
                                          have p1423_3 := h1423c.2.2.2
                                          linarith only [h0, h1326, h1330, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1334_1, p1423_1]
                                        · have p1423_0 := h1423c.1
                                          have p1423_1 := h1423c.2.1
                                          have p1423_2 := h1423c.2.2.1
                                          have p1423_3 := h1423c.2.2.2
                                          linarith only [h1322, hlam, p1423_1]
                                        · have p1423_0 := h1423c.1
                                          have p1423_1 := h1423c.2.1
                                          have p1423_2 := h1423c.2.2.1
                                          have p1423_3 := h1423c.2.2.2
                                          linarith only [h1324, hlam, p1423_1]
                                        · have p1423_0 := h1423c.1
                                          have p1423_1 := h1423c.2.1
                                          have p1423_2 := h1423c.2.2.1
                                          have p1423_3 := h1423c.2.2.2
                                          linarith only [h4, hlam, p1423_1]
                                        · have p1423_0 := h1423c.1
                                          have p1423_1 := h1423c.2.1
                                          have p1423_2 := h1423c.2.2.1
                                          have p1423_3 := h1423c.2.2.2
                                          linarith only [h1319, hlam, p1423_1]
                                        · have p1423_0 := h1423c.1
                                          have p1423_1 := h1423c.2.1
                                          have p1423_2 := h1423c.2.2.1
                                          have p1423_3 := h1423c.2.2.2
                                          linarith only [hlam, p1423_0]
                                        · have p1423_0 := h1423c.1
                                          have p1423_1 := h1423c.2.1
                                          have p1423_2 := h1423c.2.2.1
                                          have p1423_3 := h1423c.2.2.2
                                          linarith only [h1328, hlam, p1423_1]
                                        · have p1423_0 := h1423c.1
                                          have p1423_1 := h1423c.2.1
                                          have p1423_2 := h1423c.2.2.1
                                          have p1423_3 := h1423c.2.2.2
                                          linarith only [h1330, hlam, p1423_1]
                                        · have p1423_0 := h1423c.1
                                          have p1423_1 := h1423c.2.1
                                          have p1423_2 := h1423c.2.2.1
                                          have p1423_3 := h1423c.2.2.2
                                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1423_1, u3elo4]
                                        · have p1423_0 := h1423c.1
                                          have p1423_1 := h1423c.2.1
                                          have p1423_2 := h1423c.2.2.1
                                          have p1423_3 := h1423c.2.2.2
                                          linarith only [h1318, h1324, h1326, hc23, hlam, hphi, p1423_1, u3elo4]
                                        · have p1423_0 := h1423c.1
                                          have p1423_1 := h1423c.2.1
                                          have p1423_2 := h1423c.2.2.1
                                          have p1423_3 := h1423c.2.2.2
                                          linarith only [h1326, h1330, hc23, hlam, hphi, p1423_1, u3elo4]
                                        · have p1423_0 := h1423c.1
                                          have p1423_1 := h1423c.2.1
                                          have p1423_2 := h1423c.2.2.1
                                          have p1423_3 := h1423c.2.2.2
                                          linarith only [hlam, p1423_0]
                                        · have p1423_0 := h1423c.1
                                          have p1423_1 := h1423c.2.1
                                          have p1423_2 := h1423c.2.2.1
                                          have p1423_3 := h1423c.2.2.2
                                          linarith only [h1332, hlam, p1423_1]
                                        · have p1423_0 := h1423c.1
                                          have p1423_1 := h1423c.2.1
                                          have p1423_2 := h1423c.2.2.1
                                          have p1423_3 := h1423c.2.2.2
                                          linarith only [h1, h1210, h1317, h5, hc23, hc45, hlam, hphi, ht34, p1423_1]
                                        · have p1423_0 := h1423c.1
                                          have p1423_1 := h1423c.2.1
                                          have p1423_2 := h1423c.2.2.1
                                          have p1423_3 := h1423c.2.2.2
                                          linarith only [h1318, h1324, h1326, hc23, hc45, hlam, hphi, ht34, p1423_1]
                                        · have p1423_0 := h1423c.1
                                          have p1423_1 := h1423c.2.1
                                          have p1423_2 := h1423c.2.2.1
                                          have p1423_3 := h1423c.2.2.2
                                          linarith only [h1326, h1330, hc23, hc45, hlam, hphi, ht34, p1423_1]
                                        · have p1423_0 := h1423c.1
                                          have p1423_1 := h1423c.2.1
                                          have p1423_2 := h1423c.2.2.1
                                          have p1423_3 := h1423c.2.2.2
                                          linarith only [h1, h1111, h1317, hc23, hc45, hlam, hphi, ht34, p1423_1]
                                        · have p1423_0 := h1423c.1
                                          have p1423_1 := h1423c.2.1
                                          have p1423_2 := h1423c.2.2.1
                                          have p1423_3 := h1423c.2.2.2
                                          linarith only [hlam, p1423_0]
                                      · rcases h5bigk with h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c
                                        · have p1449_0 := h1449c.1
                                          have p1449_1 := h1449c.2.1
                                          have p1449_2 := h1449c.2.2.1
                                          have p1449_3 := h1449c.2.2.2
                                          linarith only [hlam, p1449_0]
                                        · have p1449_0 := h1449c.1
                                          have p1449_1 := h1449c.2.1
                                          have p1449_2 := h1449c.2.2.1
                                          have p1449_3 := h1449c.2.2.2
                                          linarith only [h1111, h1318, h1324, h1326, hc23, hlam, hphi, p1449_1, u3elo4]
                                        · have p1449_0 := h1449c.1
                                          have p1449_1 := h1449c.2.1
                                          have p1449_2 := h1449c.2.2.1
                                          have p1449_3 := h1449c.2.2.2
                                          linarith only [h1111, h1326, h1330, hc23, hlam, hphi, p1449_1, u3elo4]
                                        · have p1449_0 := h1449c.1
                                          have p1449_1 := h1449c.2.1
                                          have p1449_2 := h1449c.2.2.1
                                          have p1449_3 := h1449c.2.2.2
                                          linarith only [h1111, hlam, p1449_1]
                                        · have p1449_0 := h1449c.1
                                          have p1449_1 := h1449c.2.1
                                          have p1449_2 := h1449c.2.2.1
                                          have p1449_3 := h1449c.2.2.2
                                          linarith only [h1210, hlam, p1449_1]
                                        · have p1449_0 := h1449c.1
                                          have p1449_1 := h1449c.2.1
                                          have p1449_2 := h1449c.2.2.1
                                          have p1449_3 := h1449c.2.2.2
                                          linarith only [h3, hlam, p1449_0]
                                        · have p1449_0 := h1449c.1
                                          have p1449_1 := h1449c.2.1
                                          have p1449_2 := h1449c.2.2.1
                                          have p1449_3 := h1449c.2.2.2
                                          linarith only [hlam, p1449_0]
                                        · have p1449_0 := h1449c.1
                                          have p1449_1 := h1449c.2.1
                                          have p1449_2 := h1449c.2.2.1
                                          have p1449_3 := h1449c.2.2.2
                                          linarith only [h0, h1326, h1330, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1334_1, p1449_1]
                                        · have p1449_0 := h1449c.1
                                          have p1449_1 := h1449c.2.1
                                          have p1449_2 := h1449c.2.2.1
                                          have p1449_3 := h1449c.2.2.2
                                          linarith only [h1322, hlam, p1449_1]
                                        · have p1449_0 := h1449c.1
                                          have p1449_1 := h1449c.2.1
                                          have p1449_2 := h1449c.2.2.1
                                          have p1449_3 := h1449c.2.2.2
                                          linarith only [h1324, hlam, p1449_1]
                                        · have p1449_0 := h1449c.1
                                          have p1449_1 := h1449c.2.1
                                          have p1449_2 := h1449c.2.2.1
                                          have p1449_3 := h1449c.2.2.2
                                          linarith only [h4, hlam, p1449_1]
                                        · have p1449_0 := h1449c.1
                                          have p1449_1 := h1449c.2.1
                                          have p1449_2 := h1449c.2.2.1
                                          have p1449_3 := h1449c.2.2.2
                                          linarith only [h1319, hlam, p1449_1]
                                        · have p1449_0 := h1449c.1
                                          have p1449_1 := h1449c.2.1
                                          have p1449_2 := h1449c.2.2.1
                                          have p1449_3 := h1449c.2.2.2
                                          linarith only [hlam, p1449_0]
                                        · have p1449_0 := h1449c.1
                                          have p1449_1 := h1449c.2.1
                                          have p1449_2 := h1449c.2.2.1
                                          have p1449_3 := h1449c.2.2.2
                                          linarith only [h1328, hlam, p1449_1]
                                        · have p1449_0 := h1449c.1
                                          have p1449_1 := h1449c.2.1
                                          have p1449_2 := h1449c.2.2.1
                                          have p1449_3 := h1449c.2.2.2
                                          linarith only [h1330, hlam, p1449_1]
                                        · have p1449_0 := h1449c.1
                                          have p1449_1 := h1449c.2.1
                                          have p1449_2 := h1449c.2.2.1
                                          have p1449_3 := h1449c.2.2.2
                                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1449_1, u3elo4]
                                        · have p1449_0 := h1449c.1
                                          have p1449_1 := h1449c.2.1
                                          have p1449_2 := h1449c.2.2.1
                                          have p1449_3 := h1449c.2.2.2
                                          linarith only [h1319, h1326, h1330, hc23, hlam, hphi, p1449_1, u3elo4]
                                        · have p1449_0 := h1449c.1
                                          have p1449_1 := h1449c.2.1
                                          have p1449_2 := h1449c.2.2.1
                                          have p1449_3 := h1449c.2.2.2
                                          linarith only [h1326, h1330, hc23, hlam, hphi, p1449_1, u3elo4]
                                        · have p1449_0 := h1449c.1
                                          have p1449_1 := h1449c.2.1
                                          have p1449_2 := h1449c.2.2.1
                                          have p1449_3 := h1449c.2.2.2
                                          linarith only [hlam, p1449_0]
                                        · have p1449_0 := h1449c.1
                                          have p1449_1 := h1449c.2.1
                                          have p1449_2 := h1449c.2.2.1
                                          have p1449_3 := h1449c.2.2.2
                                          linarith only [h1332, hlam, p1449_1]
                                        · have p1449_0 := h1449c.1
                                          have p1449_1 := h1449c.2.1
                                          have p1449_2 := h1449c.2.2.1
                                          have p1449_3 := h1449c.2.2.2
                                          linarith only [h1, h1210, h1317, h5, hc23, hc45, hlam, hphi, ht34, p1449_1]
                                        · have p1449_0 := h1449c.1
                                          have p1449_1 := h1449c.2.1
                                          have p1449_2 := h1449c.2.2.1
                                          have p1449_3 := h1449c.2.2.2
                                          linarith only [h1319, h1326, h1330, hc23, hc45, hlam, hphi, ht34, p1449_1]
                                        · have p1449_0 := h1449c.1
                                          have p1449_1 := h1449c.2.1
                                          have p1449_2 := h1449c.2.2.1
                                          have p1449_3 := h1449c.2.2.2
                                          linarith only [h1326, h1330, hc23, hc45, hlam, hphi, ht34, p1449_1]
                                        · have p1449_0 := h1449c.1
                                          have p1449_1 := h1449c.2.1
                                          have p1449_2 := h1449c.2.2.1
                                          have p1449_3 := h1449c.2.2.2
                                          linarith only [h1, h1111, h1317, hc23, hc45, hlam, hphi, ht34, p1449_1]
                                        · have p1449_0 := h1449c.1
                                          have p1449_1 := h1449c.2.1
                                          have p1449_2 := h1449c.2.2.1
                                          have p1449_3 := h1449c.2.2.2
                                          linarith only [hlam, p1449_0]
                                      · linarith only [h1, h1422, hlam, ht12, ht23, u3elo0]
                                      · linarith only [h1332, h1422, h2, h5, hc45, hlam, ht12, ht23, ht34]
                                      · linarith only [h0, h1422, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1334_1]
                              · linarith only [h1319, h1415, hlam]
                            · linarith only [h1414, h3, hlam]
                          · have p1334_0 := h1334c.1
                            have p1334_1 := h1334c.2.1
                            have p1334_2 := h1334c.2.2.1
                            have p1334_3 := h1334c.2.2.2
                            linarith only [h1, hlam, p1334_0]
                          · have p1334_0 := h1334c.1
                            have p1334_1 := h1334c.2.1
                            have p1334_2 := h1334c.2.2.1
                            have p1334_3 := h1334c.2.2.2
                            linarith only [h1317, hlam, p1334_1]
                          · have p1334_0 := h1334c.1
                            have p1334_1 := h1334c.2.1
                            have p1334_2 := h1334c.2.2.1
                            have p1334_3 := h1334c.2.2.2
                            linarith only [hlam, p1334_0]
                          · have p1334_0 := h1334c.1
                            have p1334_1 := h1334c.2.1
                            have p1334_2 := h1334c.2.2.1
                            have p1334_3 := h1334c.2.2.2
                            linarith only [h1320, hlam, p1334_1]
                          · have p1334_0 := h1334c.1
                            have p1334_1 := h1334c.2.1
                            have p1334_2 := h1334c.2.2.1
                            have p1334_3 := h1334c.2.2.2
                            linarith only [h1322, hlam, p1334_1]
                          · have p1334_0 := h1334c.1
                            have p1334_1 := h1334c.2.1
                            have p1334_2 := h1334c.2.2.1
                            have p1334_3 := h1334c.2.2.2
                            linarith only [h2, hlam, p1334_0]
                          · have p1334_0 := h1334c.1
                            have p1334_1 := h1334c.2.1
                            have p1334_2 := h1334c.2.2.1
                            have p1334_3 := h1334c.2.2.2
                            linarith only [h1318, hlam, p1334_1]
                          · have p1334_0 := h1334c.1
                            have p1334_1 := h1334c.2.1
                            have p1334_2 := h1334c.2.2.1
                            have p1334_3 := h1334c.2.2.2
                            linarith only [h1332, h2, h5, hc13, hc45, hlam, hphi, ht34, p1334_1]
                          · have p1334_0 := h1334c.1
                            have p1334_1 := h1334c.2.1
                            have p1334_2 := h1334c.2.2.1
                            have p1334_3 := h1334c.2.2.2
                            linarith only [hlam, p1334_0]
                          · have p1334_0 := h1334c.1
                            have p1334_1 := h1334c.2.1
                            have p1334_2 := h1334c.2.2.1
                            have p1334_3 := h1334c.2.2.2
                            linarith only [h1324, hlam, p1334_1]
                          · have p1334_0 := h1334c.1
                            have p1334_1 := h1334c.2.1
                            have p1334_2 := h1334c.2.2.1
                            have p1334_3 := h1334c.2.2.2
                            linarith only [h3, hlam, p1334_0]
                          · have p1334_0 := h1334c.1
                            have p1334_1 := h1334c.2.1
                            have p1334_2 := h1334c.2.2.1
                            have p1334_3 := h1334c.2.2.2
                            linarith only [h1319, hlam, p1334_1]
                          · have p1334_0 := h1334c.1
                            have p1334_1 := h1334c.2.1
                            have p1334_2 := h1334c.2.2.1
                            have p1334_3 := h1334c.2.2.2
                            linarith only [h1111, h1317, h3, hc23, hlam, hphi, p1334_1, u3elo4]
                          · have p1334_0 := h1334c.1
                            have p1334_1 := h1334c.2.1
                            have p1334_2 := h1334c.2.2.1
                            have p1334_3 := h1334c.2.2.2
                            linarith only [h1111, h1317, h1320, h3, hc23, hlam, hphi, p1334_1, u3elo4]
                          · have p1334_0 := h1334c.1
                            have p1334_1 := h1334c.2.1
                            have p1334_2 := h1334c.2.2.1
                            have p1334_3 := h1334c.2.2.2
                            linarith only [hlam, p1334_0]
          · linarith only [h1111, h1317, h1319, h4, hc23, hlam, hphi, u3elo4]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1496 | h1496
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1497 | h1497
            · linarith only [h1497, h5, hc03, hlam, hphi, u3elo1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1499 | h1499
              · linarith only [h1, h1111, h1499, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1501 | h1501
                · linarith only [h1210, h1501, h2, hlam]
                · linarith only [h1318, h1496, h1501, hlam]
          · linarith only [h1111, h1317, h1496, h4, hc23, hlam, hphi, u3elo4]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1505 | h1505
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1506 | h1506
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1507 | h1507
            · linarith only [h1, h1507, h5, hlam]
            · linarith only [h1317, h1505, h1507, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1510 | h1510
            · linarith only [h1, h1510, h5, hlam]
            · linarith only [h1317, h1505, h1510, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1513 | h1513
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1514 | h1514
            · linarith only [h1, h1514, h5, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1516 | h1516
              · linarith only [h1, h1111, h1516, hlam]
              · linarith only [h1317, h1513, h1516, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1519 | h1519
            · linarith only [h1, h1519, h5, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1521 | h1521
              · linarith only [h1, h1111, h1521, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1523 | h1523
                · linarith only [h1210, h1523, h2, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1525 | h1525
                  · linarith only [h1, h1317, h1525, h5, hc12, hlam, hphi, ht23, u3elo2]
                  · linarith only [h1317, h1525, hc12, hlam, hphi, ht23, u3elo3]

set_option maxHeartbeats 7188000 in
theorem r1l7_11_13_25_L_I_L_0_H_I_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h1bigk := hb1.1
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_11_13_25_L_I_L_0_H_I_x0_x0_x0_x0_x0_x0 m hb1 hb3 hb5 h0 h1 h2 h3 h4 h5
  · exact r1l7_11_13_25_L_I_L_0_H_I_x0_x0_x0_x0_x0_x1 m hb1 hb3 hb5 h0 h1 h2 h3 h4 h5

set_option maxHeartbeats 7188000 in
theorem r1l7_11_13_25_L_I_L_0_H_I_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h1bigk := hb1.1
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h1528 | h1528
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1529 | h1529
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1530 | h1530
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1531 | h1531
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1532 | h1532
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1533 | h1533
            · linarith only [h0, h1533, h4, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1535 | h1535
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1536 | h1536
                · linarith only [h1531, h1533, h1536, hlam]
                · linarith only [h1529, h1536, hc13, hlam, hphi, u3elo0]
              · linarith only [h1528, h1531, h1535, hc23, hlam, hphi, u3elo0]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1540 | h1540
            · linarith only [h0, h1540, h4, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1542 | h1542
              · linarith only [h1531, h1532, h1542, hlam]
              · linarith only [h1528, h1542, hc13, hlam, hphi, u3elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1545 | h1545
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1546 | h1546
            · linarith only [h1531, h1546, h4, hc02, hlam, hphi, ht23, u3elo1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1548 | h1548
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1549 | h1549
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1550 | h1550
                  · linarith only [h1545, h1546, h1550, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1552 | h1552
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1553 | h1553
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1554 | h1554
                        · linarith only [h1545, h1546, h1550, h1554, hlam]
                        · linarith only [h1528, h1530, h1554, h4, hc02, hlam, hphi, ht23, u3elo0]
                      · linarith only [h1528, h1530, h1549, h1550, h1553, hc23, hlam, hphi, u3elo0]
                    · linarith only [h1528, h1531, h1552, hc13, hlam, hphi, u3elo0]
                · linarith only [h1529, h1531, h1549, hc12, hlam, hphi, ht23, u3elo0]
              · linarith only [h1528, h1531, h1545, h1548, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1561 | h1561
            · linarith only [h0, h1561, h4, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1563 | h1563
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1564 | h1564
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1565 | h1565
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1566 | h1566
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1567 | h1567
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1568 | h1568
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1569 | h1569
                          · rcases h1bigk with h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c
                            · have p1570_0 := h1570c.1
                              have p1570_1 := h1570c.2.1
                              have p1570_2 := h1570c.2.2.1
                              have p1570_3 := h1570c.2.2.2
                              linarith only [hlam, p1570_0]
                            · have p1570_0 := h1570c.1
                              have p1570_1 := h1570c.2.1
                              have p1570_2 := h1570c.2.2.1
                              have p1570_3 := h1570c.2.2.2
                              rcases p1570_3 (m.d 0 1) (by simp) with h1572 | h1572
                              · rcases p1570_3 (m.d 1 2) (by simp) with h1573 | h1573
                                · linarith only [h1573, hlam, p1570_0]
                                · rcases p1570_3 (m.d 1 3) (by simp) with h1575 | h1575
                                  · linarith only [h1, h1575, hlam]
                                  · linarith only [h1531, h1575, hlam]
                              · linarith only [h1572, hlam, p1570_0]
                            · have p1570_0 := h1570c.1
                              have p1570_1 := h1570c.2.1
                              have p1570_2 := h1570c.2.2.1
                              have p1570_3 := h1570c.2.2.2
                              linarith only [h1563, h1569, hc01, hc45, hlam, hphi, ht0b, ht5b, p1570_1]
                            · have p1570_0 := h1570c.1
                              have p1570_1 := h1570c.2.1
                              have p1570_2 := h1570c.2.2.1
                              have p1570_3 := h1570c.2.2.2
                              rcases p1570_3 (m.d 0 1) (by simp) with h1580 | h1580
                              · rcases p1570_3 (m.d 1 2) (by simp) with h1581 | h1581
                                · linarith only [h0, h1581, hlam]
                                · rcases p1570_3 (m.d 1 3) (by simp) with h1583 | h1583
                                  · linarith only [h1, h1583, hlam]
                                  · linarith only [h1563, h1583, hlam]
                              · linarith only [h1580, hlam, p1570_0]
                            · have p1570_0 := h1570c.1
                              have p1570_1 := h1570c.2.1
                              have p1570_2 := h1570c.2.2.1
                              have p1570_3 := h1570c.2.2.2
                              rcases p1570_3 (m.d 0 1) (by simp) with h1587 | h1587
                              · rcases p1570_3 (m.d 1 2) (by simp) with h1588 | h1588
                                · linarith only [h0, h1588, hlam]
                                · rcases p1570_3 (m.d 1 3) (by simp) with h1590 | h1590
                                  · linarith only [h1, h1590, hlam]
                                  · linarith only [h1564, h1590, hlam]
                              · linarith only [h1587, hlam, p1570_0]
                            · have p1570_0 := h1570c.1
                              have p1570_1 := h1570c.2.1
                              have p1570_2 := h1570c.2.2.1
                              have p1570_3 := h1570c.2.2.2
                              linarith only [h0, hlam, p1570_0]
                            · have p1570_0 := h1570c.1
                              have p1570_1 := h1570c.2.1
                              have p1570_2 := h1570c.2.2.1
                              have p1570_3 := h1570c.2.2.2
                              linarith only [hlam, p1570_0]
                            · have p1570_0 := h1570c.1
                              have p1570_1 := h1570c.2.1
                              have p1570_2 := h1570c.2.2.1
                              have p1570_3 := h1570c.2.2.2
                              linarith only [h1531, hlam, p1570_0]
                            · have p1570_0 := h1570c.1
                              have p1570_1 := h1570c.2.1
                              have p1570_2 := h1570c.2.2.1
                              have p1570_3 := h1570c.2.2.2
                              linarith only [h1545, hlam, p1570_0]
                            · have p1570_0 := h1570c.1
                              have p1570_1 := h1570c.2.1
                              have p1570_2 := h1570c.2.2.1
                              have p1570_3 := h1570c.2.2.2
                              linarith only [h1561, hlam, p1570_0]
                            · have p1570_0 := h1570c.1
                              have p1570_1 := h1570c.2.1
                              have p1570_2 := h1570c.2.2.1
                              have p1570_3 := h1570c.2.2.2
                              linarith only [h1, hlam, p1570_0]
                            · have p1570_0 := h1570c.1
                              have p1570_1 := h1570c.2.1
                              have p1570_2 := h1570c.2.2.1
                              have p1570_3 := h1570c.2.2.2
                              linarith only [hc12, hlam, hphi, ht23, p1570_1, u3elo1]
                            · have p1570_0 := h1570c.1
                              have p1570_1 := h1570c.2.1
                              have p1570_2 := h1570c.2.2.1
                              have p1570_3 := h1570c.2.2.2
                              linarith only [hlam, p1570_0]
                            · have p1570_0 := h1570c.1
                              have p1570_1 := h1570c.2.1
                              have p1570_2 := h1570c.2.2.1
                              have p1570_3 := h1570c.2.2.2
                              linarith only [h1, h1545, hc12, hlam, hphi, ht23, p1570_1, u3elo0]
                            · have p1570_0 := h1570c.1
                              have p1570_1 := h1570c.2.1
                              have p1570_2 := h1570c.2.2.1
                              have p1570_3 := h1570c.2.2.2
                              linarith only [h1, h1561, hc12, hlam, hphi, ht23, p1570_1, u3elo0]
                            · have p1570_0 := h1570c.1
                              have p1570_1 := h1570c.2.1
                              have p1570_2 := h1570c.2.2.1
                              have p1570_3 := h1570c.2.2.2
                              linarith only [h2, hlam, p1570_0]
                            · have p1570_0 := h1570c.1
                              have p1570_1 := h1570c.2.1
                              have p1570_2 := h1570c.2.2.1
                              have p1570_3 := h1570c.2.2.2
                              linarith only [h1528, h2, hc12, hlam, hphi, ht23, p1570_1, u3elo0]
                            · have p1570_0 := h1570c.1
                              have p1570_1 := h1570c.2.1
                              have p1570_2 := h1570c.2.2.1
                              have p1570_3 := h1570c.2.2.2
                              linarith only [h1563, hlam, p1570_0]
                            · have p1570_0 := h1570c.1
                              have p1570_1 := h1570c.2.1
                              have p1570_2 := h1570c.2.2.1
                              have p1570_3 := h1570c.2.2.2
                              linarith only [hlam, p1570_0]
                            · have p1570_0 := h1570c.1
                              have p1570_1 := h1570c.2.1
                              have p1570_2 := h1570c.2.2.1
                              have p1570_3 := h1570c.2.2.2
                              linarith only [h1528, h1561, h2, hc12, hlam, hphi, ht23, p1570_1, u3elo0]
                            · have p1570_0 := h1570c.1
                              have p1570_1 := h1570c.2.1
                              have p1570_2 := h1570c.2.2.1
                              have p1570_3 := h1570c.2.2.2
                              linarith only [h3, hlam, p1570_0]
                            · have p1570_0 := h1570c.1
                              have p1570_1 := h1570c.2.1
                              have p1570_2 := h1570c.2.2.1
                              have p1570_3 := h1570c.2.2.2
                              linarith only [h1566, h1568, h3, h4, hc12, hlam, hphi, ht23, p1570_1, u3elo2]
                            · have p1570_0 := h1570c.1
                              have p1570_1 := h1570c.2.1
                              have p1570_2 := h1570c.2.2.1
                              have p1570_3 := h1570c.2.2.2
                              linarith only [h1564, hlam, p1570_0]
                            · have p1570_0 := h1570c.1
                              have p1570_1 := h1570c.2.1
                              have p1570_2 := h1570c.2.2.1
                              have p1570_3 := h1570c.2.2.2
                              linarith only [h1565, hlam, p1570_0]
                            · have p1570_0 := h1570c.1
                              have p1570_1 := h1570c.2.1
                              have p1570_2 := h1570c.2.2.1
                              have p1570_3 := h1570c.2.2.2
                              linarith only [hlam, p1570_0]
                          · rcases h1bigk with h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c
                            · have p1614_0 := h1614c.1
                              have p1614_1 := h1614c.2.1
                              have p1614_2 := h1614c.2.2.1
                              have p1614_3 := h1614c.2.2.2
                              linarith only [hlam, p1614_0]
                            · have p1614_0 := h1614c.1
                              have p1614_1 := h1614c.2.1
                              have p1614_2 := h1614c.2.2.1
                              have p1614_3 := h1614c.2.2.2
                              rcases p1614_3 (m.d 0 1) (by simp) with h1616 | h1616
                              · rcases p1614_3 (m.d 1 2) (by simp) with h1617 | h1617
                                · linarith only [h1617, hlam, p1614_0]
                                · rcases p1614_3 (m.d 1 3) (by simp) with h1619 | h1619
                                  · linarith only [h1, h1619, hlam]
                                  · linarith only [h1531, h1619, hlam]
                              · linarith only [h1616, hlam, p1614_0]
                            · have p1614_0 := h1614c.1
                              have p1614_1 := h1614c.2.1
                              have p1614_2 := h1614c.2.2.1
                              have p1614_3 := h1614c.2.2.2
                              linarith only [h1563, h1565, h1569, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1614_1]
                            · have p1614_0 := h1614c.1
                              have p1614_1 := h1614c.2.1
                              have p1614_2 := h1614c.2.2.1
                              have p1614_3 := h1614c.2.2.2
                              linarith only [h1565, h1569, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1614_1]
                            · have p1614_0 := h1614c.1
                              have p1614_1 := h1614c.2.1
                              have p1614_2 := h1614c.2.2.1
                              have p1614_3 := h1614c.2.2.2
                              rcases p1614_3 (m.d 0 1) (by simp) with h1625 | h1625
                              · rcases p1614_3 (m.d 1 2) (by simp) with h1626 | h1626
                                · linarith only [h0, h1626, hlam]
                                · rcases p1614_3 (m.d 1 3) (by simp) with h1628 | h1628
                                  · linarith only [h1, h1628, hlam]
                                  · linarith only [h1564, h1628, hlam]
                              · linarith only [h1625, hlam, p1614_0]
                            · have p1614_0 := h1614c.1
                              have p1614_1 := h1614c.2.1
                              have p1614_2 := h1614c.2.2.1
                              have p1614_3 := h1614c.2.2.2
                              linarith only [h0, hlam, p1614_0]
                            · have p1614_0 := h1614c.1
                              have p1614_1 := h1614c.2.1
                              have p1614_2 := h1614c.2.2.1
                              have p1614_3 := h1614c.2.2.2
                              linarith only [hlam, p1614_0]
                            · have p1614_0 := h1614c.1
                              have p1614_1 := h1614c.2.1
                              have p1614_2 := h1614c.2.2.1
                              have p1614_3 := h1614c.2.2.2
                              linarith only [h1531, hlam, p1614_0]
                            · have p1614_0 := h1614c.1
                              have p1614_1 := h1614c.2.1
                              have p1614_2 := h1614c.2.2.1
                              have p1614_3 := h1614c.2.2.2
                              linarith only [h1545, hlam, p1614_0]
                            · have p1614_0 := h1614c.1
                              have p1614_1 := h1614c.2.1
                              have p1614_2 := h1614c.2.2.1
                              have p1614_3 := h1614c.2.2.2
                              linarith only [h1561, hlam, p1614_0]
                            · have p1614_0 := h1614c.1
                              have p1614_1 := h1614c.2.1
                              have p1614_2 := h1614c.2.2.1
                              have p1614_3 := h1614c.2.2.2
                              linarith only [h1, hlam, p1614_0]
                            · have p1614_0 := h1614c.1
                              have p1614_1 := h1614c.2.1
                              have p1614_2 := h1614c.2.2.1
                              have p1614_3 := h1614c.2.2.2
                              linarith only [hc12, hlam, hphi, ht23, p1614_1, u3elo1]
                            · have p1614_0 := h1614c.1
                              have p1614_1 := h1614c.2.1
                              have p1614_2 := h1614c.2.2.1
                              have p1614_3 := h1614c.2.2.2
                              linarith only [hlam, p1614_0]
                            · have p1614_0 := h1614c.1
                              have p1614_1 := h1614c.2.1
                              have p1614_2 := h1614c.2.2.1
                              have p1614_3 := h1614c.2.2.2
                              linarith only [h1, h1565, h1569, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1614_1, u3elo0]
                            · have p1614_0 := h1614c.1
                              have p1614_1 := h1614c.2.1
                              have p1614_2 := h1614c.2.2.1
                              have p1614_3 := h1614c.2.2.2
                              linarith only [h1, h1561, hc12, hlam, hphi, ht23, p1614_1, u3elo0]
                            · have p1614_0 := h1614c.1
                              have p1614_1 := h1614c.2.1
                              have p1614_2 := h1614c.2.2.1
                              have p1614_3 := h1614c.2.2.2
                              linarith only [h2, hlam, p1614_0]
                            · have p1614_0 := h1614c.1
                              have p1614_1 := h1614c.2.1
                              have p1614_2 := h1614c.2.2.1
                              have p1614_3 := h1614c.2.2.2
                              linarith only [h1528, h2, hc12, hlam, hphi, ht23, p1614_1, u3elo0]
                            · have p1614_0 := h1614c.1
                              have p1614_1 := h1614c.2.1
                              have p1614_2 := h1614c.2.2.1
                              have p1614_3 := h1614c.2.2.2
                              linarith only [h1563, hlam, p1614_0]
                            · have p1614_0 := h1614c.1
                              have p1614_1 := h1614c.2.1
                              have p1614_2 := h1614c.2.2.1
                              have p1614_3 := h1614c.2.2.2
                              linarith only [hlam, p1614_0]
                            · have p1614_0 := h1614c.1
                              have p1614_1 := h1614c.2.1
                              have p1614_2 := h1614c.2.2.1
                              have p1614_3 := h1614c.2.2.2
                              linarith only [h1528, h1561, h2, hc12, hlam, hphi, ht23, p1614_1, u3elo0]
                            · have p1614_0 := h1614c.1
                              have p1614_1 := h1614c.2.1
                              have p1614_2 := h1614c.2.2.1
                              have p1614_3 := h1614c.2.2.2
                              linarith only [h3, hlam, p1614_0]
                            · have p1614_0 := h1614c.1
                              have p1614_1 := h1614c.2.1
                              have p1614_2 := h1614c.2.2.1
                              have p1614_3 := h1614c.2.2.2
                              linarith only [h1566, h1568, h3, h4, hc12, hlam, hphi, ht23, p1614_1, u3elo2]
                            · have p1614_0 := h1614c.1
                              have p1614_1 := h1614c.2.1
                              have p1614_2 := h1614c.2.2.1
                              have p1614_3 := h1614c.2.2.2
                              linarith only [h1564, hlam, p1614_0]
                            · have p1614_0 := h1614c.1
                              have p1614_1 := h1614c.2.1
                              have p1614_2 := h1614c.2.2.1
                              have p1614_3 := h1614c.2.2.2
                              linarith only [h1565, hlam, p1614_0]
                            · have p1614_0 := h1614c.1
                              have p1614_1 := h1614c.2.1
                              have p1614_2 := h1614c.2.2.1
                              have p1614_3 := h1614c.2.2.2
                              linarith only [hlam, p1614_0]
                        · linarith only [h1528, h1530, h1545, h1568, hc12, hlam, hphi, ht23, u3elo0]
                      · linarith only [h1, h1564, h1567, hc23, hlam, hphi, u3elo0]
                    · linarith only [h1528, h1531, h1566, hc13, hlam, hphi, u3elo0]
                  · linarith only [h1528, h1530, h1545, h1565, hc12, hlam, hphi, ht23, u3elo0]
                · linarith only [h1529, h1563, h1564, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
              · linarith only [h1528, h1563, hc13, hlam, hphi, u3elo0]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1658 | h1658
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1659 | h1659
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1660 | h1660
            · linarith only [h0, h1660, h4, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1662 | h1662
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1663 | h1663
                · linarith only [h1658, h1660, h1663, hlam]
                · linarith only [h1529, h1663, hc13, hlam, hphi, u3elo0]
              · linarith only [h1528, h1658, h1662, hc23, hlam, hphi, u3elo0]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1667 | h1667
            · linarith only [h0, h1667, h4, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1669 | h1669
              · linarith only [h1658, h1659, h1669, hlam]
              · linarith only [h1528, h1669, hc13, hlam, hphi, u3elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1672 | h1672
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1673 | h1673
            · linarith only [h1658, h1673, h4, hc02, hlam, hphi, ht23, u3elo1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1675 | h1675
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1676 | h1676
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1677 | h1677
                  · linarith only [h1530, h1658, h1672, h1677, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1679 | h1679
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1680 | h1680
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1681 | h1681
                        · linarith only [h0, h1530, h1672, h1680, h1681, h4, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1683 | h1683
                          · linarith only [h0, h1672, h1679, h1681, h1683, h4, hlam]
                          · rcases h1bigk with h1685c | h1685c | h1685c | h1685c | h1685c | h1685c | h1685c | h1685c | h1685c | h1685c | h1685c | h1685c | h1685c | h1685c | h1685c | h1685c | h1685c | h1685c | h1685c | h1685c | h1685c | h1685c | h1685c | h1685c | h1685c
                            · have p1685_0 := h1685c.1
                              have p1685_1 := h1685c.2.1
                              have p1685_2 := h1685c.2.2.1
                              have p1685_3 := h1685c.2.2.2
                              linarith only [hlam, p1685_0]
                            · have p1685_0 := h1685c.1
                              have p1685_1 := h1685c.2.1
                              have p1685_2 := h1685c.2.2.1
                              have p1685_3 := h1685c.2.2.2
                              rcases p1685_3 (m.d 0 1) (by simp) with h1687 | h1687
                              · rcases p1685_3 (m.d 1 2) (by simp) with h1688 | h1688
                                · linarith only [h1688, hlam, p1685_0]
                                · rcases p1685_3 (m.d 1 3) (by simp) with h1690 | h1690
                                  · linarith only [h1, h1690, hlam]
                                  · linarith only [h1658, h1690, hlam]
                              · linarith only [h1687, hlam, p1685_0]
                            · have p1685_0 := h1685c.1
                              have p1685_1 := h1685c.2.1
                              have p1685_2 := h1685c.2.2.1
                              have p1685_3 := h1685c.2.2.2
                              rcases p1685_3 (m.d 0 1) (by simp) with h1694 | h1694
                              · rcases p1685_3 (m.d 1 2) (by simp) with h1695 | h1695
                                · linarith only [h0, h1695, hlam]
                                · rcases p1685_3 (m.d 1 3) (by simp) with h1697 | h1697
                                  · linarith only [h1697, hlam, p1685_0]
                                  · rcases p1685_3 (m.d 1 4) (by simp) with h1699 | h1699
                                    · linarith only [h1699, h2, hlam]
                                    · rcases p1685_3 (m.d 1 5) (by simp) with h1701 | h1701
                                      · linarith only [h1701, h3, hlam]
                                      · rcases h1emin with h1703 | h1703 | h1703 | h1703 | h1703
                                        · rcases h5bigk with h1704c | h1704c | h1704c | h1704c | h1704c | h1704c | h1704c | h1704c | h1704c | h1704c | h1704c | h1704c | h1704c | h1704c | h1704c | h1704c | h1704c | h1704c | h1704c | h1704c | h1704c | h1704c | h1704c | h1704c | h1704c
                                          · have p1704_0 := h1704c.1
                                            have p1704_1 := h1704c.2.1
                                            have p1704_2 := h1704c.2.2.1
                                            have p1704_3 := h1704c.2.2.2
                                            linarith only [hlam, p1704_0]
                                          · have p1704_0 := h1704c.1
                                            have p1704_1 := h1704c.2.1
                                            have p1704_2 := h1704c.2.2.1
                                            have p1704_3 := h1704c.2.2.2
                                            linarith only [h1672, h1673, hc05, hc24, hlam, hphi, ht0b, ht45, ht5b, p1704_1]
                                          · have p1704_0 := h1704c.1
                                            have p1704_1 := h1704c.2.1
                                            have p1704_2 := h1704c.2.2.1
                                            have p1704_3 := h1704c.2.2.2
                                            linarith only [h4, hlam, p1704_0]
                                          · have p1704_0 := h1704c.1
                                            have p1704_1 := h1704c.2.1
                                            have p1704_2 := h1704c.2.2.1
                                            have p1704_3 := h1704c.2.2.2
                                            linarith only [h1680, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1704_1, u3elo2]
                                          · have p1704_0 := h1704c.1
                                            have p1704_1 := h1704c.2.1
                                            have p1704_2 := h1704c.2.2.1
                                            have p1704_3 := h1704c.2.2.2
                                            linarith only [h1530, hlam, p1704_1]
                                          · have p1704_0 := h1704c.1
                                            have p1704_1 := h1704c.2.1
                                            have p1704_2 := h1704c.2.2.1
                                            have p1704_3 := h1704c.2.2.2
                                            linarith only [h3, hlam, p1704_0]
                                          · have p1704_0 := h1704c.1
                                            have p1704_1 := h1704c.2.1
                                            have p1704_2 := h1704c.2.2.1
                                            have p1704_3 := h1704c.2.2.2
                                            linarith only [hlam, p1704_0]
                                          · have p1704_0 := h1704c.1
                                            have p1704_1 := h1704c.2.1
                                            have p1704_2 := h1704c.2.2.1
                                            have p1704_3 := h1704c.2.2.2
                                            linarith only [h1673, hlam, p1704_0]
                                          · have p1704_0 := h1704c.1
                                            have p1704_1 := h1704c.2.1
                                            have p1704_2 := h1704c.2.2.1
                                            have p1704_3 := h1704c.2.2.2
                                            linarith only [h3, hc01, hc35, hlam, hphi, ht0b, ht5b, p1704_1]
                                          · have p1704_0 := h1704c.1
                                            have p1704_1 := h1704c.2.1
                                            have p1704_2 := h1704c.2.2.1
                                            have p1704_3 := h1704c.2.2.2
                                            linarith only [h1677, hlam, p1704_1]
                                          · have p1704_0 := h1704c.1
                                            have p1704_1 := h1704c.2.1
                                            have p1704_2 := h1704c.2.2.1
                                            have p1704_3 := h1704c.2.2.2
                                            linarith only [h1680, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1704_1, u3elo2]
                                          · have p1704_0 := h1704c.1
                                            have p1704_1 := h1704c.2.1
                                            have p1704_2 := h1704c.2.2.1
                                            have p1704_3 := h1704c.2.2.2
                                            linarith only [h1680, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1704_1, u3elo2]
                                          · have p1704_0 := h1704c.1
                                            have p1704_1 := h1704c.2.1
                                            have p1704_2 := h1704c.2.2.1
                                            have p1704_3 := h1704c.2.2.2
                                            linarith only [hlam, p1704_0]
                                          · have p1704_0 := h1704c.1
                                            have p1704_1 := h1704c.2.1
                                            have p1704_2 := h1704c.2.2.1
                                            have p1704_3 := h1704c.2.2.2
                                            linarith only [h1680, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1704_1, u3elo2]
                                          · have p1704_0 := h1704c.1
                                            have p1704_1 := h1704c.2.1
                                            have p1704_2 := h1704c.2.2.1
                                            have p1704_3 := h1704c.2.2.2
                                            linarith only [h1681, hlam, p1704_1]
                                          · have p1704_0 := h1704c.1
                                            have p1704_1 := h1704c.2.1
                                            have p1704_2 := h1704c.2.2.1
                                            have p1704_3 := h1704c.2.2.2
                                            linarith only [h1529, hlam, p1704_0]
                                          · have p1704_0 := h1704c.1
                                            have p1704_1 := h1704c.2.1
                                            have p1704_2 := h1704c.2.2.1
                                            have p1704_3 := h1704c.2.2.2
                                            linarith only [h1676, hlam, p1704_0]
                                          · have p1704_0 := h1704c.1
                                            have p1704_1 := h1704c.2.1
                                            have p1704_2 := h1704c.2.2.1
                                            have p1704_3 := h1704c.2.2.2
                                            linarith only [h1680, hlam, p1704_0]
                                          · have p1704_0 := h1704c.1
                                            have p1704_1 := h1704c.2.1
                                            have p1704_2 := h1704c.2.2.1
                                            have p1704_3 := h1704c.2.2.2
                                            linarith only [hlam, p1704_0]
                                          · have p1704_0 := h1704c.1
                                            have p1704_1 := h1704c.2.1
                                            have p1704_2 := h1704c.2.2.1
                                            have p1704_3 := h1704c.2.2.2
                                            linarith only [h1683, hlam, p1704_1]
                                          · have p1704_0 := h1704c.1
                                            have p1704_1 := h1704c.2.1
                                            have p1704_2 := h1704c.2.2.1
                                            have p1704_3 := h1704c.2.2.2
                                            linarith only [h0, h1672, h1679, h4, hc34, hc45, hlam, hphi, p1704_1]
                                          · have p1704_0 := h1704c.1
                                            have p1704_1 := h1704c.2.1
                                            have p1704_2 := h1704c.2.2.1
                                            have p1704_3 := h1704c.2.2.2
                                            linarith only [h1672, h1673, h1679, hc34, hc45, hlam, hphi, p1704_1]
                                          · have p1704_0 := h1704c.1
                                            have p1704_1 := h1704c.2.1
                                            have p1704_2 := h1704c.2.2.1
                                            have p1704_3 := h1704c.2.2.2
                                            linarith only [h0, h1672, h1679, h4, hc34, hc45, hlam, hphi, p1704_1]
                                          · have p1704_0 := h1704c.1
                                            have p1704_1 := h1704c.2.1
                                            have p1704_2 := h1704c.2.2.1
                                            have p1704_3 := h1704c.2.2.2
                                            linarith only [h1683, hc34, hc45, hlam, hphi, p1704_1]
                                          · have p1704_0 := h1704c.1
                                            have p1704_1 := h1704c.2.1
                                            have p1704_2 := h1704c.2.2.1
                                            have p1704_3 := h1704c.2.2.2
                                            linarith only [hlam, p1704_0]
                                        · linarith only [h0, h1680, h1703, h4, hlam, ht12, ht23, u3elo2]
                                        · linarith only [h0, h1672, h1679, h1680, h1703, h4, hc01, hc34, hlam, hphi, ht0b, ht12, ht23, ht45, ht5b, p1685_1, u3elo2]
                                        · linarith only [h0, h1672, h1680, h1703, h4, hlam, ht12, ht23, u3elo2]
                                        · linarith only [h1680, h1703, h3, h4, hlam, ht12, ht23, u3elo2]
                              · linarith only [h1694, hlam, p1685_0]
                            · have p1685_0 := h1685c.1
                              have p1685_1 := h1685c.2.1
                              have p1685_2 := h1685c.2.2.1
                              have p1685_3 := h1685c.2.2.2
                              rcases p1685_3 (m.d 0 1) (by simp) with h1735 | h1735
                              · rcases p1685_3 (m.d 1 2) (by simp) with h1736 | h1736
                                · linarith only [h0, h1736, hlam]
                                · linarith only [h1672, h1736, hlam]
                              · linarith only [h1735, hlam, p1685_0]
                            · have p1685_0 := h1685c.1
                              have p1685_1 := h1685c.2.1
                              have p1685_2 := h1685c.2.2.1
                              have p1685_3 := h1685c.2.2.2
                              rcases p1685_3 (m.d 0 1) (by simp) with h1740 | h1740
                              · rcases p1685_3 (m.d 1 2) (by simp) with h1741 | h1741
                                · linarith only [h0, h1741, hlam]
                                · rcases p1685_3 (m.d 1 3) (by simp) with h1743 | h1743
                                  · linarith only [h1, h1743, hlam]
                                  · linarith only [h1676, h1743, hlam]
                              · linarith only [h1740, hlam, p1685_0]
                            · have p1685_0 := h1685c.1
                              have p1685_1 := h1685c.2.1
                              have p1685_2 := h1685c.2.2.1
                              have p1685_3 := h1685c.2.2.2
                              linarith only [h0, hlam, p1685_0]
                            · have p1685_0 := h1685c.1
                              have p1685_1 := h1685c.2.1
                              have p1685_2 := h1685c.2.2.1
                              have p1685_3 := h1685c.2.2.2
                              linarith only [hlam, p1685_0]
                            · have p1685_0 := h1685c.1
                              have p1685_1 := h1685c.2.1
                              have p1685_2 := h1685c.2.2.1
                              have p1685_3 := h1685c.2.2.2
                              linarith only [h1658, hlam, p1685_0]
                            · have p1685_0 := h1685c.1
                              have p1685_1 := h1685c.2.1
                              have p1685_2 := h1685c.2.2.1
                              have p1685_3 := h1685c.2.2.2
                              linarith only [h0, h1680, h4, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1685_1, u3elo2]
                            · have p1685_0 := h1685c.1
                              have p1685_1 := h1685c.2.1
                              have p1685_2 := h1685c.2.2.1
                              have p1685_3 := h1685c.2.2.2
                              linarith only [h1673, hlam, p1685_0]
                            · have p1685_0 := h1685c.1
                              have p1685_1 := h1685c.2.1
                              have p1685_2 := h1685c.2.2.1
                              have p1685_3 := h1685c.2.2.2
                              linarith only [h1, hlam, p1685_0]
                            · have p1685_0 := h1685c.1
                              have p1685_1 := h1685c.2.1
                              have p1685_2 := h1685c.2.2.1
                              have p1685_3 := h1685c.2.2.2
                              linarith only [hc12, hlam, hphi, ht23, p1685_1, u3elo1]
                            · have p1685_0 := h1685c.1
                              have p1685_1 := h1685c.2.1
                              have p1685_2 := h1685c.2.2.1
                              have p1685_3 := h1685c.2.2.2
                              linarith only [hlam, p1685_0]
                            · have p1685_0 := h1685c.1
                              have p1685_1 := h1685c.2.1
                              have p1685_2 := h1685c.2.2.1
                              have p1685_3 := h1685c.2.2.2
                              rcases p1685_3 (m.d 0 1) (by simp) with h1755 | h1755
                              · rcases p1685_3 (m.d 1 2) (by simp) with h1756 | h1756
                                · linarith only [h1658, h1756, hlam]
                                · linarith only [h1672, h1756, hlam]
                              · linarith only [h1755, h2, hlam]
                            · have p1685_0 := h1685c.1
                              have p1685_1 := h1685c.2.1
                              have p1685_2 := h1685c.2.2.1
                              have p1685_3 := h1685c.2.2.2
                              linarith only [h1, h1672, h1673, h1679, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1685_1, u3elo0]
                            · have p1685_0 := h1685c.1
                              have p1685_1 := h1685c.2.1
                              have p1685_2 := h1685c.2.2.1
                              have p1685_3 := h1685c.2.2.2
                              linarith only [h2, hlam, p1685_0]
                            · have p1685_0 := h1685c.1
                              have p1685_1 := h1685c.2.1
                              have p1685_2 := h1685c.2.2.1
                              have p1685_3 := h1685c.2.2.2
                              linarith only [h1672, hlam, p1685_1]
                            · have p1685_0 := h1685c.1
                              have p1685_1 := h1685c.2.1
                              have p1685_2 := h1685c.2.2.1
                              have p1685_3 := h1685c.2.2.2
                              linarith only [h1675, hlam, p1685_0]
                            · have p1685_0 := h1685c.1
                              have p1685_1 := h1685c.2.1
                              have p1685_2 := h1685c.2.2.1
                              have p1685_3 := h1685c.2.2.2
                              linarith only [hlam, p1685_0]
                            · have p1685_0 := h1685c.1
                              have p1685_1 := h1685c.2.1
                              have p1685_2 := h1685c.2.2.1
                              have p1685_3 := h1685c.2.2.2
                              linarith only [h1677, hlam, p1685_1]
                            · have p1685_0 := h1685c.1
                              have p1685_1 := h1685c.2.1
                              have p1685_2 := h1685c.2.2.1
                              have p1685_3 := h1685c.2.2.2
                              linarith only [h3, hlam, p1685_0]
                            · have p1685_0 := h1685c.1
                              have p1685_1 := h1685c.2.1
                              have p1685_2 := h1685c.2.2.1
                              have p1685_3 := h1685c.2.2.2
                              linarith only [h1672, h1679, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1685_1]
                            · have p1685_0 := h1685c.1
                              have p1685_1 := h1685c.2.1
                              have p1685_2 := h1685c.2.2.1
                              have p1685_3 := h1685c.2.2.2
                              linarith only [h1676, hlam, p1685_0]
                            · have p1685_0 := h1685c.1
                              have p1685_1 := h1685c.2.1
                              have p1685_2 := h1685c.2.2.1
                              have p1685_3 := h1685c.2.2.2
                              rcases p1685_3 (m.d 0 1) (by simp) with h1769 | h1769
                              · rcases p1685_3 (m.d 1 2) (by simp) with h1770 | h1770
                                · linarith only [h1673, h1770, hlam]
                                · linarith only [h1672, h1770, hlam]
                              · linarith only [h1769, h2, hlam]
                            · have p1685_0 := h1685c.1
                              have p1685_1 := h1685c.2.1
                              have p1685_2 := h1685c.2.2.1
                              have p1685_3 := h1685c.2.2.2
                              linarith only [hlam, p1685_0]
                      · linarith only [h1529, h1680, hc23, hlam, hphi, u3elo0]
                    · linarith only [h1528, h1658, h1679, hc13, hlam, hphi, u3elo0]
                · linarith only [h1529, h1658, h1676, hc12, hlam, hphi, ht23, u3elo0]
              · linarith only [h1528, h1658, h1672, h1675, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1779 | h1779
            · linarith only [h1658, h1779, h4, hc02, hc23, hlam, hphi]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1781 | h1781
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1782 | h1782
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1783 | h1783
                  · linarith only [h1530, h1783, h2, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1785 | h1785
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1786 | h1786
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1787 | h1787
                        · linarith only [h1530, h1672, h1785, h1787, h2, hc12, hlam, hphi, ht23, u3elo2]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1789 | h1789
                          · linarith only [h1530, h1672, h1789, h2, hc12, hlam, hphi, ht23, u3elo3]
                          · rcases h1bigk with h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c
                            · have p1791_0 := h1791c.1
                              have p1791_1 := h1791c.2.1
                              have p1791_2 := h1791c.2.2.1
                              have p1791_3 := h1791c.2.2.2
                              linarith only [hlam, p1791_0]
                            · have p1791_0 := h1791c.1
                              have p1791_1 := h1791c.2.1
                              have p1791_2 := h1791c.2.2.1
                              have p1791_3 := h1791c.2.2.2
                              rcases p1791_3 (m.d 0 1) (by simp) with h1793 | h1793
                              · rcases p1791_3 (m.d 1 2) (by simp) with h1794 | h1794
                                · linarith only [h1794, hlam, p1791_0]
                                · rcases p1791_3 (m.d 1 3) (by simp) with h1796 | h1796
                                  · linarith only [h1, h1796, hlam]
                                  · linarith only [h1658, h1796, hlam]
                              · linarith only [h1793, hlam, p1791_0]
                            · have p1791_0 := h1791c.1
                              have p1791_1 := h1791c.2.1
                              have p1791_2 := h1791c.2.2.1
                              have p1791_3 := h1791c.2.2.2
                              rcases p1791_3 (m.d 0 1) (by simp) with h1800 | h1800
                              · rcases p1791_3 (m.d 1 2) (by simp) with h1801 | h1801
                                · linarith only [h0, h1801, hlam]
                                · rcases p1791_3 (m.d 1 3) (by simp) with h1803 | h1803
                                  · linarith only [h1803, hlam, p1791_0]
                                  · rcases p1791_3 (m.d 1 4) (by simp) with h1805 | h1805
                                    · linarith only [h1805, h2, hlam]
                                    · rcases p1791_3 (m.d 1 5) (by simp) with h1807 | h1807
                                      · linarith only [h1807, h3, hlam]
                                      · rcases h1emin with h1809 | h1809 | h1809 | h1809 | h1809
                                        · rcases h5bigk with h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c
                                          · have p1810_0 := h1810c.1
                                            have p1810_1 := h1810c.2.1
                                            have p1810_2 := h1810c.2.2.1
                                            have p1810_3 := h1810c.2.2.2
                                            linarith only [hlam, p1810_0]
                                          · have p1810_0 := h1810c.1
                                            have p1810_1 := h1810c.2.1
                                            have p1810_2 := h1810c.2.2.1
                                            have p1810_3 := h1810c.2.2.2
                                            linarith only [h1529, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1810_1, u3elo0]
                                          · have p1810_0 := h1810c.1
                                            have p1810_1 := h1810c.2.1
                                            have p1810_2 := h1810c.2.2.1
                                            have p1810_3 := h1810c.2.2.2
                                            linarith only [h4, hlam, p1810_0]
                                          · have p1810_0 := h1810c.1
                                            have p1810_1 := h1810c.2.1
                                            have p1810_2 := h1810c.2.2.1
                                            have p1810_3 := h1810c.2.2.2
                                            linarith only [h1529, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1810_1, u3elo0]
                                          · have p1810_0 := h1810c.1
                                            have p1810_1 := h1810c.2.1
                                            have p1810_2 := h1810c.2.2.1
                                            have p1810_3 := h1810c.2.2.2
                                            linarith only [h1530, hlam, p1810_1]
                                          · have p1810_0 := h1810c.1
                                            have p1810_1 := h1810c.2.1
                                            have p1810_2 := h1810c.2.2.1
                                            have p1810_3 := h1810c.2.2.2
                                            linarith only [h3, hlam, p1810_0]
                                          · have p1810_0 := h1810c.1
                                            have p1810_1 := h1810c.2.1
                                            have p1810_2 := h1810c.2.2.1
                                            have p1810_3 := h1810c.2.2.2
                                            linarith only [hlam, p1810_0]
                                          · have p1810_0 := h1810c.1
                                            have p1810_1 := h1810c.2.1
                                            have p1810_2 := h1810c.2.2.1
                                            have p1810_3 := h1810c.2.2.2
                                            linarith only [h1779, hlam, p1810_0]
                                          · have p1810_0 := h1810c.1
                                            have p1810_1 := h1810c.2.1
                                            have p1810_2 := h1810c.2.2.1
                                            have p1810_3 := h1810c.2.2.2
                                            linarith only [h3, hc01, hc35, hlam, hphi, ht0b, ht5b, p1810_1]
                                          · have p1810_0 := h1810c.1
                                            have p1810_1 := h1810c.2.1
                                            have p1810_2 := h1810c.2.2.1
                                            have p1810_3 := h1810c.2.2.2
                                            linarith only [h1783, hlam, p1810_1]
                                          · have p1810_0 := h1810c.1
                                            have p1810_1 := h1810c.2.1
                                            have p1810_2 := h1810c.2.2.1
                                            have p1810_3 := h1810c.2.2.2
                                            linarith only [h0, h4, hc12, hc25, hlam, hphi, p1810_1]
                                          · have p1810_0 := h1810c.1
                                            have p1810_1 := h1810c.2.1
                                            have p1810_2 := h1810c.2.2.1
                                            have p1810_3 := h1810c.2.2.2
                                            linarith only [h1779, hc12, hc25, hlam, hphi, p1810_1]
                                          · have p1810_0 := h1810c.1
                                            have p1810_1 := h1810c.2.1
                                            have p1810_2 := h1810c.2.2.1
                                            have p1810_3 := h1810c.2.2.2
                                            linarith only [hlam, p1810_0]
                                          · have p1810_0 := h1810c.1
                                            have p1810_1 := h1810c.2.1
                                            have p1810_2 := h1810c.2.2.1
                                            have p1810_3 := h1810c.2.2.2
                                            linarith only [h1786, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1810_1, u3elo2]
                                          · have p1810_0 := h1810c.1
                                            have p1810_1 := h1810c.2.1
                                            have p1810_2 := h1810c.2.2.1
                                            have p1810_3 := h1810c.2.2.2
                                            linarith only [h1787, hlam, p1810_1]
                                          · have p1810_0 := h1810c.1
                                            have p1810_1 := h1810c.2.1
                                            have p1810_2 := h1810c.2.2.1
                                            have p1810_3 := h1810c.2.2.2
                                            linarith only [h1529, hlam, p1810_0]
                                          · have p1810_0 := h1810c.1
                                            have p1810_1 := h1810c.2.1
                                            have p1810_2 := h1810c.2.2.1
                                            have p1810_3 := h1810c.2.2.2
                                            linarith only [h1782, hlam, p1810_0]
                                          · have p1810_0 := h1810c.1
                                            have p1810_1 := h1810c.2.1
                                            have p1810_2 := h1810c.2.2.1
                                            have p1810_3 := h1810c.2.2.2
                                            linarith only [h1786, hlam, p1810_0]
                                          · have p1810_0 := h1810c.1
                                            have p1810_1 := h1810c.2.1
                                            have p1810_2 := h1810c.2.2.1
                                            have p1810_3 := h1810c.2.2.2
                                            linarith only [hlam, p1810_0]
                                          · have p1810_0 := h1810c.1
                                            have p1810_1 := h1810c.2.1
                                            have p1810_2 := h1810c.2.2.1
                                            have p1810_3 := h1810c.2.2.2
                                            linarith only [h1789, hlam, p1810_1]
                                          · have p1810_0 := h1810c.1
                                            have p1810_1 := h1810c.2.1
                                            have p1810_2 := h1810c.2.2.1
                                            have p1810_3 := h1810c.2.2.2
                                            linarith only [h1530, h1672, h2, hc12, hc45, hlam, hphi, ht23, ht34, p1810_1]
                                          · have p1810_0 := h1810c.1
                                            have p1810_1 := h1810c.2.1
                                            have p1810_2 := h1810c.2.2.1
                                            have p1810_3 := h1810c.2.2.2
                                            linarith only [h1672, h1783, hc12, hc45, hlam, hphi, ht23, ht34, p1810_1]
                                          · have p1810_0 := h1810c.1
                                            have p1810_1 := h1810c.2.1
                                            have p1810_2 := h1810c.2.2.1
                                            have p1810_3 := h1810c.2.2.2
                                            linarith only [h0, h4, hc12, hc45, hlam, hphi, ht23, ht34, p1810_1]
                                          · have p1810_0 := h1810c.1
                                            have p1810_1 := h1810c.2.1
                                            have p1810_2 := h1810c.2.2.1
                                            have p1810_3 := h1810c.2.2.2
                                            linarith only [h1789, hc34, hc45, hlam, hphi, p1810_1]
                                          · have p1810_0 := h1810c.1
                                            have p1810_1 := h1810c.2.1
                                            have p1810_2 := h1810c.2.2.1
                                            have p1810_3 := h1810c.2.2.2
                                            linarith only [hlam, p1810_0]
                                        · linarith only [h1672, h1809, hc24, hlam, ht12]
                                        · linarith only [h1809, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1791_1]
                                        · linarith only [h1528, h1809, h2, hlam, ht12, ht23, u3elo0]
                                        · linarith only [h1529, h1809, h3, hlam, ht12, ht23, u3elo0]
                              · linarith only [h1800, hlam, p1791_0]
                            · have p1791_0 := h1791c.1
                              have p1791_1 := h1791c.2.1
                              have p1791_2 := h1791c.2.2.1
                              have p1791_3 := h1791c.2.2.2
                              rcases p1791_3 (m.d 0 1) (by simp) with h1841 | h1841
                              · rcases p1791_3 (m.d 1 2) (by simp) with h1842 | h1842
                                · linarith only [h0, h1842, hlam]
                                · rcases p1791_3 (m.d 1 3) (by simp) with h1844 | h1844
                                  · linarith only [h1, h1844, hlam]
                                  · linarith only [h1781, h1844, hlam]
                              · linarith only [h1841, hlam, p1791_0]
                            · have p1791_0 := h1791c.1
                              have p1791_1 := h1791c.2.1
                              have p1791_2 := h1791c.2.2.1
                              have p1791_3 := h1791c.2.2.2
                              rcases p1791_3 (m.d 0 1) (by simp) with h1848 | h1848
                              · rcases p1791_3 (m.d 1 2) (by simp) with h1849 | h1849
                                · linarith only [h0, h1849, hlam]
                                · rcases p1791_3 (m.d 1 3) (by simp) with h1851 | h1851
                                  · linarith only [h1, h1851, hlam]
                                  · linarith only [h1782, h1851, hlam]
                              · linarith only [h1848, hlam, p1791_0]
                            · have p1791_0 := h1791c.1
                              have p1791_1 := h1791c.2.1
                              have p1791_2 := h1791c.2.2.1
                              have p1791_3 := h1791c.2.2.2
                              linarith only [h0, hlam, p1791_0]
                            · have p1791_0 := h1791c.1
                              have p1791_1 := h1791c.2.1
                              have p1791_2 := h1791c.2.2.1
                              have p1791_3 := h1791c.2.2.2
                              linarith only [hlam, p1791_0]
                            · have p1791_0 := h1791c.1
                              have p1791_1 := h1791c.2.1
                              have p1791_2 := h1791c.2.2.1
                              have p1791_3 := h1791c.2.2.2
                              linarith only [h1658, hlam, p1791_0]
                            · have p1791_0 := h1791c.1
                              have p1791_1 := h1791c.2.1
                              have p1791_2 := h1791c.2.2.1
                              have p1791_3 := h1791c.2.2.2
                              linarith only [h1672, hlam, p1791_0]
                            · have p1791_0 := h1791c.1
                              have p1791_1 := h1791c.2.1
                              have p1791_2 := h1791c.2.2.1
                              have p1791_3 := h1791c.2.2.2
                              linarith only [h1779, hlam, p1791_0]
                            · have p1791_0 := h1791c.1
                              have p1791_1 := h1791c.2.1
                              have p1791_2 := h1791c.2.2.1
                              have p1791_3 := h1791c.2.2.2
                              linarith only [h1, hlam, p1791_0]
                            · have p1791_0 := h1791c.1
                              have p1791_1 := h1791c.2.1
                              have p1791_2 := h1791c.2.2.1
                              have p1791_3 := h1791c.2.2.2
                              linarith only [hc12, hlam, hphi, ht23, p1791_1, u3elo1]
                            · have p1791_0 := h1791c.1
                              have p1791_1 := h1791c.2.1
                              have p1791_2 := h1791c.2.2.1
                              have p1791_3 := h1791c.2.2.2
                              linarith only [hlam, p1791_0]
                            · have p1791_0 := h1791c.1
                              have p1791_1 := h1791c.2.1
                              have p1791_2 := h1791c.2.2.1
                              have p1791_3 := h1791c.2.2.2
                              linarith only [h1, h1672, hc12, hlam, hphi, ht23, p1791_1, u3elo0]
                            · have p1791_0 := h1791c.1
                              have p1791_1 := h1791c.2.1
                              have p1791_2 := h1791c.2.2.1
                              have p1791_3 := h1791c.2.2.2
                              linarith only [h1, h1779, hc12, hlam, hphi, ht23, p1791_1, u3elo0]
                            · have p1791_0 := h1791c.1
                              have p1791_1 := h1791c.2.1
                              have p1791_2 := h1791c.2.2.1
                              have p1791_3 := h1791c.2.2.2
                              linarith only [h2, hlam, p1791_0]
                            · have p1791_0 := h1791c.1
                              have p1791_1 := h1791c.2.1
                              have p1791_2 := h1791c.2.2.1
                              have p1791_3 := h1791c.2.2.2
                              linarith only [h1530, h1786, h2, h4, hc12, hlam, hphi, ht23, p1791_1, u3elo2]
                            · have p1791_0 := h1791c.1
                              have p1791_1 := h1791c.2.1
                              have p1791_2 := h1791c.2.2.1
                              have p1791_3 := h1791c.2.2.2
                              linarith only [h1781, hlam, p1791_0]
                            · have p1791_0 := h1791c.1
                              have p1791_1 := h1791c.2.1
                              have p1791_2 := h1791c.2.2.1
                              have p1791_3 := h1791c.2.2.2
                              linarith only [hlam, p1791_0]
                            · have p1791_0 := h1791c.1
                              have p1791_1 := h1791c.2.1
                              have p1791_2 := h1791c.2.2.1
                              have p1791_3 := h1791c.2.2.2
                              linarith only [h1783, hlam, p1791_1]
                            · have p1791_0 := h1791c.1
                              have p1791_1 := h1791c.2.1
                              have p1791_2 := h1791c.2.2.1
                              have p1791_3 := h1791c.2.2.2
                              linarith only [h3, hlam, p1791_0]
                            · have p1791_0 := h1791c.1
                              have p1791_1 := h1791c.2.1
                              have p1791_2 := h1791c.2.2.1
                              have p1791_3 := h1791c.2.2.2
                              linarith only [h1786, h3, h4, hc12, hlam, hphi, ht23, p1791_1, u3elo2]
                            · have p1791_0 := h1791c.1
                              have p1791_1 := h1791c.2.1
                              have p1791_2 := h1791c.2.2.1
                              have p1791_3 := h1791c.2.2.2
                              linarith only [h1782, hlam, p1791_0]
                            · have p1791_0 := h1791c.1
                              have p1791_1 := h1791c.2.1
                              have p1791_2 := h1791c.2.2.1
                              have p1791_3 := h1791c.2.2.2
                              linarith only [h1672, h1786, h3, h4, hc12, hlam, hphi, ht23, p1791_1, u3elo2]
                            · have p1791_0 := h1791c.1
                              have p1791_1 := h1791c.2.1
                              have p1791_2 := h1791c.2.2.1
                              have p1791_3 := h1791c.2.2.2
                              linarith only [hlam, p1791_0]
                      · linarith only [h1529, h1786, hc23, hlam, hphi, u3elo0]
                    · linarith only [h1528, h1658, h1785, hc13, hlam, hphi, u3elo0]
                · linarith only [h1529, h1781, h1782, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
              · linarith only [h1528, h1658, h1781, hc12, hlam, hphi, ht23, u3elo0]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1879 | h1879
      · linarith only [h1528, h1529, h1879, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1881 | h1881
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1882 | h1882
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1883 | h1883
            · linarith only [h0, h1883, h4, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1885 | h1885
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1886 | h1886
                · linarith only [h1529, h1886, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1888 | h1888
                  · linarith only [h1879, h1888, h2, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1890 | h1890
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1891 | h1891
                      · linarith only [h0, h1529, h1881, h1891, h4, hlam]
                      · linarith only [h0, h1881, h1890, h1891, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · linarith only [h1528, h1890, hc23, hlam, hphi, u3elo0]
              · linarith only [h1528, h1529, h1881, h1885, hc23, hlam, hphi, u3elo4]
          · linarith only [h1528, h1529, h1881, h1882, h2, hc23, hlam, hphi, u3elo4]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1897 | h1897
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1898 | h1898
            · linarith only [h1881, h1898, h4, hc02, hlam, hphi, ht23, u3elo1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1900 | h1900
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1901 | h1901
                · linarith only [h1, h1529, h1901, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1903 | h1903
                  · linarith only [h1, h1529, h1879, h1881, h1897, h1903, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1905 | h1905
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1906 | h1906
                      · linarith only [h1529, h1906, hc03, hlam, hphi, u3elo2]
                      · linarith only [h1881, h1897, h1905, h1906, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · linarith only [h1881, h1897, h1905, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
              · linarith only [h1528, h1529, h1881, h1897, h1900, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1911 | h1911
            · linarith only [h0, h1911, h4, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1913 | h1913
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1914 | h1914
                · linarith only [h1529, h1914, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1916 | h1916
                  · linarith only [h1879, h1916, h2, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1918 | h1918
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1919 | h1919
                      · linarith only [h1, h1529, h1913, h1919, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                      · linarith only [h1881, h1919, hc12, hlam, hphi, ht23, u3elo4]
                    · linarith only [h1881, h1918, hc12, hlam, hphi, ht23, u3elo3]
              · linarith only [h1528, h1529, h1913, hc13, hlam, hphi, u3elo4]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1924 | h1924
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1925 | h1925
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1926 | h1926
        · linarith only [h0, h1528, h1924, h1926, h4, hc23, hlam, hphi, u3elo3]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1928 | h1928
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1929 | h1929
            · linarith only [h0, h1929, h4, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1931 | h1931
              · linarith only [h0, h1528, h1924, h1928, h1931, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
              · linarith only [h1926, h1928, h1931, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1934 | h1934
            · linarith only [h0, h1934, h4, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1936 | h1936
              · linarith only [h1528, h1924, h1936, h4, hc02, hlam, hphi, ht23, u3elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1938 | h1938
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1939 | h1939
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1940 | h1940
                    · linarith only [h1, h1528, h1938, h1940, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                    · linarith only [h1926, h1940, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h1528, h1925, h1936, h1938, h1939, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                · linarith only [h1528, h1924, h1938, hc13, hlam, hphi, u3elo3]
      · linarith only [h1528, h1924, h1925, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1946 | h1946
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1947 | h1947
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1948 | h1948
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1949 | h1949
            · linarith only [h0, h1949, h4, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1951 | h1951
              · linarith only [h1528, h1951, hc03, hlam, hphi, u3elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1953 | h1953
                · linarith only [h0, h1, h1924, h1947, h1953, h4, hc23, hlam, hphi, u3elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1955 | h1955
                  · linarith only [h1948, h1949, h1955, hlam]
                  · linarith only [h1528, h1946, h1951, h1955, hc13, hlam, hphi, u3elo3]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1958 | h1958
            · linarith only [h0, h1958, h4, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1960 | h1960
              · linarith only [h1528, h1960, hc03, hlam, hphi, u3elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1962 | h1962
                · linarith only [h1, h1924, h1962, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1964 | h1964
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1965 | h1965
                    · linarith only [h0, h1528, h1946, h1947, h1965, h4, hlam]
                    · linarith only [h1947, h1948, h1965, hc23, hlam, hphi, u3elo3]
                  · linarith only [h1528, h1946, h1947, h1948, h1964, hc23, hlam, hphi, u3elo3]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1969 | h1969
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1970 | h1970
            · linarith only [h0, h1970, h4, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1972 | h1972
              · linarith only [h1, h1528, h1972, hlam]
              · linarith only [h1947, h1969, h1972, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1975 | h1975
            · linarith only [h0, h1975, h4, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1977 | h1977
              · linarith only [h1, h1528, h1977, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1979 | h1979
                · linarith only [h1, h1924, h1979, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1981 | h1981
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1982 | h1982
                    · linarith only [h1528, h1982, hc03, hlam, hphi, u3elo2]
                    · linarith only [h1947, h1982, hc12, hlam, hphi, ht23, u3elo3]
                  · linarith only [h1528, h1946, h1969, h1981, hc12, hlam, hphi, ht23, u3elo3]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1986 | h1986
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1987 | h1987
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1988 | h1988
            · linarith only [h0, h1988, h4, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1990 | h1990
              · linarith only [h1, h1528, h1990, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1992 | h1992
                · linarith only [h1924, h1946, h1990, h1992, h2, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1994 | h1994
                  · linarith only [h1528, h1946, h1986, h1988, h1994, h2, h3, hc23, hlam, hphi, u3elo3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1996 | h1996
                    · linarith only [h1528, h1986, h1988, h1996, h3, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1998 | h1998
                      · linarith only [h1924, h1987, h1988, h1996, h1998, h3, hlam]
                      · linarith only [h0, h1987, h1996, h1998, h4, hc23, hlam, hphi, u3elo4]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2001 | h2001
            · linarith only [h0, h2001, h4, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2003 | h2003
              · linarith only [h1, h1528, h2003, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2005 | h2005
                · linarith only [h0, h1, h1528, h1924, h1986, h2005, h4, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2007 | h2007
                  · linarith only [h1946, h2, h2007, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2009 | h2009
                    · linarith only [h1528, h1986, h1987, h2007, h2009, h3, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h1986, h1987, h2009, hc23, hlam, hphi, u3elo3]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2012 | h2012
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2013 | h2013
            · linarith only [h1, h1528, h1986, h2013, h4, hc02, hlam, hphi, ht23, u3elo3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2015 | h2015
              · linarith only [h1, h1528, h2015, hlam]
              · linarith only [h1986, h2012, h2015, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2018 | h2018
            · linarith only [h0, h2018, h4, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2020 | h2020
              · linarith only [h1, h1528, h2020, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2022 | h2022
                · linarith only [h1, h1924, h2022, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2024 | h2024
                  · linarith only [h1946, h2, h2024, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2026 | h2026
                    · linarith only [h1528, h2026, hc03, hlam, hphi, u3elo2]
                    · linarith only [h1986, h2026, hc12, hlam, hphi, ht23, u3elo3]

set_option maxHeartbeats 7188000 in
theorem r1l7_11_13_25_L_I_L_0_H_I_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h1bigk := hb1.1
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
  · exact r1l7_11_13_25_L_I_L_0_H_I_x0_x0_x0_x0_x0 m hb1 hb3 hb5 h0 h1 h2 h3 h4
  · exact r1l7_11_13_25_L_I_L_0_H_I_x0_x0_x0_x0_x1 m hb1 hb3 hb5 h0 h1 h2 h3 h4

set_option maxHeartbeats 7188000 in
theorem r1l7_11_13_25_L_I_L_0_H_I_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h1bigk := hb1.1
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h2029 | h2029
  · linarith only [h0, h2029, h3, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2031 | h2031
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2032 | h2032
      · linarith only [h1, h2032, h3, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2034 | h2034
        · linarith only [h2, h2034, h3, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2036 | h2036
          · linarith only [h0, h2032, h2036, h3, hc23, hlam, hphi, u3elo4]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2038 | h2038
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2039 | h2039
              · linarith only [h1, h2029, h2032, h2036, h2039, h3, hc02, hlam, hphi, ht23, u3elo4]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2041 | h2041
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2042 | h2042
                  · linarith only [h1, h2032, h2042, h3, hlam]
                  · linarith only [h1, h2036, h2042, h3, hc12, hlam, hphi, ht23, u3elo4]
                · linarith only [h2031, h2032, h2036, h2038, h2041, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2046 | h2046
              · linarith only [h0, h2029, h2046, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2048 | h2048
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2049 | h2049
                  · linarith only [h1, h2032, h2049, h3, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h1, h2048, h2049, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                · linarith only [h2031, h2032, h2036, h2048, hc12, hlam, hphi, ht23, u3elo4]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2053 | h2053
      · linarith only [h0, h2031, h2053, h3, hc12, hlam, hphi, ht23, u3elo3]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2055 | h2055
        · linarith only [h2, h2055, h3, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2057 | h2057
          · linarith only [h0, h2053, h2057, h3, hc23, hlam, hphi, u3elo4]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2059 | h2059
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2060 | h2060
              · linarith only [h0, h2029, h2060, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2062 | h2062
                · linarith only [h1, h2031, h2053, h2062, h3, hc03, hlam, hphi, u3elo4]
                · linarith only [h2057, h2059, h2062, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2065 | h2065
              · linarith only [h0, h2029, h2065, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2067 | h2067
                · linarith only [h1, h2031, h2067, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2069 | h2069
                  · linarith only [h2, h2053, h2067, h2069, h3, hlam]
                  · linarith only [h2, h2057, h2067, h2069, h3, hc12, hlam, hphi, ht23, u3elo4]

end R2N4
