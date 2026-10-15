import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5810000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h692 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h921 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1036 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1117 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1118 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1119 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1120 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1121 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1122 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h0bigk := hb0.1
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h1123 | h1123
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1124 | h1124
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1125 | h1125
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1126 | h1126
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1127 | h1127
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1128 | h1128
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1129 | h1129
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1130 | h1130
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1131 | h1131
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1132 | h1132
                    · linarith only [h1117, h1129, h1132, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases h0bigk with h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [hlam, p1134_0]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [h0, hlam, p1134_1]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [h692, hlam, p1134_0]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [h921, hlam, p1134_1]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [h1036, hlam, p1134_1]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        rcases p1134_3 (m.d 0 1) (by simp) with h1140 | h1140
                        · linarith only [h0, h1140, hlam]
                        · rcases p1134_3 (m.d 0 2) (by simp) with h1142 | h1142
                          · rcases p1134_3 (m.d 0 3) (by simp) with h1143 | h1143
                            · linarith only [h1117, h1143, hlam]
                            · linarith only [h1143, h692, hlam]
                          · linarith only [h0, h1142, hlam]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [hlam, p1134_0]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [h0, h1118, h1120, h1131, h1132, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1134_1]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [h0, h1118, h1131, h1132, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1134_1]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        rcases p1134_3 (m.d 0 1) (by simp) with h1150 | h1150
                        · linarith only [h0, h1150, hlam]
                        · rcases p1134_3 (m.d 0 2) (by simp) with h1152 | h1152
                          · rcases p1134_3 (m.d 0 3) (by simp) with h1153 | h1153
                            · linarith only [h1117, h1153, hlam]
                            · linarith only [h1121, h1153, hlam]
                          · linarith only [h1119, h1152, hlam]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        rcases p1134_3 (m.d 0 1) (by simp) with h1157 | h1157
                        · linarith only [h1157, h692, hlam]
                        · rcases p1134_3 (m.d 0 2) (by simp) with h1159 | h1159
                          · rcases p1134_3 (m.d 0 3) (by simp) with h1160 | h1160
                            · rcases p1134_3 (m.d 0 4) (by simp) with h1161 | h1161
                              · linarith only [h1120, h1161, hlam]
                              · linarith only [h1161, h921, hlam]
                            · linarith only [h1160, h692, hlam]
                          · linarith only [h0, h1159, hlam]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [h1117, hlam, p1134_1]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [hlam, p1134_0]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [h1118, h1131, h1132, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1134_1]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        rcases p1134_3 (m.d 0 1) (by simp) with h1169 | h1169
                        · linarith only [h1169, h692, hlam]
                        · rcases p1134_3 (m.d 0 2) (by simp) with h1171 | h1171
                          · rcases p1134_3 (m.d 0 3) (by simp) with h1172 | h1172
                            · rcases p1134_3 (m.d 0 4) (by simp) with h1173 | h1173
                              · linarith only [h1120, h1173, hlam]
                              · linarith only [h1122, h1173, hlam]
                            · linarith only [h1121, h1172, hlam]
                          · linarith only [h1119, h1171, hlam]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        rcases p1134_3 (m.d 0 1) (by simp) with h1178 | h1178
                        · linarith only [h1178, h921, hlam]
                        · rcases p1134_3 (m.d 0 2) (by simp) with h1180 | h1180
                          · rcases p1134_3 (m.d 0 3) (by simp) with h1181 | h1181
                            · rcases p1134_3 (m.d 0 4) (by simp) with h1182 | h1182
                              · rcases p1134_3 (m.d 0 5) (by simp) with h1183 | h1183
                                · linarith only [h1122, h1183, hlam]
                                · linarith only [h1036, h1183, hlam]
                              · linarith only [h1182, h921, hlam]
                            · linarith only [h1181, h692, hlam]
                          · linarith only [h0, h1180, hlam]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [h1118, hlam, p1134_0]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [h1120, hlam, p1134_0]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [hlam, p1134_0]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        rcases p1134_3 (m.d 0 1) (by simp) with h1192 | h1192
                        · linarith only [h1192, h921, hlam]
                        · rcases p1134_3 (m.d 0 2) (by simp) with h1194 | h1194
                          · rcases p1134_3 (m.d 0 3) (by simp) with h1195 | h1195
                            · rcases p1134_3 (m.d 0 4) (by simp) with h1196 | h1196
                              · rcases p1134_3 (m.d 0 5) (by simp) with h1197 | h1197
                                · linarith only [h1122, h1197, hlam]
                                · rcases h3bigk with h1199c | h1199c | h1199c | h1199c | h1199c | h1199c | h1199c | h1199c | h1199c | h1199c | h1199c | h1199c | h1199c | h1199c | h1199c | h1199c | h1199c | h1199c | h1199c | h1199c | h1199c | h1199c | h1199c | h1199c | h1199c
                                  · have p1199_0 := h1199c.1
                                    have p1199_1 := h1199c.2.1
                                    have p1199_2 := h1199c.2.2.1
                                    have p1199_3 := h1199c.2.2.2
                                    linarith only [hlam, p1199_0]
                                  · have p1199_0 := h1199c.1
                                    have p1199_1 := h1199c.2.1
                                    have p1199_2 := h1199c.2.2.1
                                    have p1199_3 := h1199c.2.2.2
                                    linarith only [h692, hlam, p1199_1]
                                  · have p1199_0 := h1199c.1
                                    have p1199_1 := h1199c.2.1
                                    have p1199_2 := h1199c.2.2.1
                                    have p1199_3 := h1199c.2.2.2
                                    linarith only [h1123, h1129, h1131, h1132, h692, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1199_1]
                                  · have p1199_0 := h1199c.1
                                    have p1199_1 := h1199c.2.1
                                    have p1199_2 := h1199c.2.2.1
                                    have p1199_3 := h1199c.2.2.2
                                    linarith only [h1120, h1122, h1132, hlam, p1134_1, p1199_2]
                                  · have p1199_0 := h1199c.1
                                    have p1199_1 := h1199c.2.1
                                    have p1199_2 := h1199c.2.2.1
                                    have p1199_3 := h1199c.2.2.2
                                    rcases p1199_3 (m.d 0 3) (by simp) with h1204 | h1204
                                    · rcases p1199_3 (m.d 1 3) (by simp) with h1205 | h1205
                                      · rcases p1199_3 (m.d 2 3) (by simp) with h1206 | h1206
                                        · linarith only [h1117, h1206, hlam]
                                        · linarith only [h1130, h1206, hlam]
                                      · linarith only [h1127, h1205, hlam]
                                    · linarith only [h1204, hlam, p1199_0]
                                  · have p1199_0 := h1199c.1
                                    have p1199_1 := h1199c.2.1
                                    have p1199_2 := h1199c.2.2.1
                                    have p1199_3 := h1199c.2.2.2
                                    linarith only [h1119, h1120, h1123, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1134_1, p1199_1, u2ehi4]
                                  · have p1199_0 := h1199c.1
                                    have p1199_1 := h1199c.2.1
                                    have p1199_2 := h1199c.2.2.1
                                    have p1199_3 := h1199c.2.2.2
                                    linarith only [hlam, p1199_0]
                                  · have p1199_0 := h1199c.1
                                    have p1199_1 := h1199c.2.1
                                    have p1199_2 := h1199c.2.2.1
                                    have p1199_3 := h1199c.2.2.2
                                    linarith only [h1123, h1129, h1131, h1132, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1199_1]
                                  · have p1199_0 := h1199c.1
                                    have p1199_1 := h1199c.2.1
                                    have p1199_2 := h1199c.2.2.1
                                    have p1199_3 := h1199c.2.2.2
                                    linarith only [h1120, h1122, h1132, h692, hlam, p1134_1, p1199_2]
                                  · have p1199_0 := h1199c.1
                                    have p1199_1 := h1199c.2.1
                                    have p1199_2 := h1199c.2.2.1
                                    have p1199_3 := h1199c.2.2.2
                                    rcases p1199_3 (m.d 0 3) (by simp) with h1215 | h1215
                                    · linarith only [h1215, h692, hlam]
                                    · linarith only [h1121, h1215, hlam]
                                  · have p1199_0 := h1199c.1
                                    have p1199_1 := h1199c.2.1
                                    have p1199_2 := h1199c.2.2.1
                                    have p1199_3 := h1199c.2.2.2
                                    linarith only [h1117, hlam, p1199_0]
                                  · have p1199_0 := h1199c.1
                                    have p1199_1 := h1199c.2.1
                                    have p1199_2 := h1199c.2.2.1
                                    have p1199_3 := h1199c.2.2.2
                                    linarith only [h1123, hlam, p1199_0]
                                  · have p1199_0 := h1199c.1
                                    have p1199_1 := h1199c.2.1
                                    have p1199_2 := h1199c.2.2.1
                                    have p1199_3 := h1199c.2.2.2
                                    linarith only [hlam, p1199_0]
                                  · have p1199_0 := h1199c.1
                                    have p1199_1 := h1199c.2.1
                                    have p1199_2 := h1199c.2.2.1
                                    have p1199_3 := h1199c.2.2.2
                                    rcases p1199_3 (m.d 0 3) (by simp) with h1221 | h1221
                                    · rcases p1199_3 (m.d 1 3) (by simp) with h1222 | h1222
                                      · rcases p1199_3 (m.d 2 3) (by simp) with h1223 | h1223
                                        · rcases p1199_3 (m.d 3 4) (by simp) with h1224 | h1224
                                          · linarith only [h1224, hlam, p1199_0]
                                          · rcases p1199_3 (m.d 3 5) (by simp) with h1226 | h1226
                                            · linarith only [h1130, h1226, hlam]
                                            · linarith only [h1132, h1226, hlam]
                                        · linarith only [h1223, hlam, p1199_0]
                                      · linarith only [h1126, h1222, hlam]
                                    · linarith only [h1120, h1221, hlam]
                                  · have p1199_0 := h1199c.1
                                    have p1199_1 := h1199c.2.1
                                    have p1199_2 := h1199c.2.2.1
                                    have p1199_3 := h1199c.2.2.2
                                    linarith only [h0, h1117, hc12, hlam, hphi, ht01, ht0b, ht5b, p1199_1, u5ehi3]
                                  · have p1199_0 := h1199c.1
                                    have p1199_1 := h1199c.2.1
                                    have p1199_2 := h1199c.2.2.1
                                    have p1199_3 := h1199c.2.2.2
                                    linarith only [h1120, hlam, p1199_0]
                                  · have p1199_0 := h1199c.1
                                    have p1199_1 := h1199c.2.1
                                    have p1199_2 := h1199c.2.2.1
                                    have p1199_3 := h1199c.2.2.2
                                    linarith only [h1126, hlam, p1199_0]
                                  · have p1199_0 := h1199c.1
                                    have p1199_1 := h1199c.2.1
                                    have p1199_2 := h1199c.2.2.1
                                    have p1199_3 := h1199c.2.2.2
                                    linarith only [h1129, hlam, p1199_0]
                                  · have p1199_0 := h1199c.1
                                    have p1199_1 := h1199c.2.1
                                    have p1199_2 := h1199c.2.2.1
                                    have p1199_3 := h1199c.2.2.2
                                    linarith only [hlam, p1199_0]
                                  · have p1199_0 := h1199c.1
                                    have p1199_1 := h1199c.2.1
                                    have p1199_2 := h1199c.2.2.1
                                    have p1199_3 := h1199c.2.2.2
                                    linarith only [h1132, hlam, p1199_1]
                                  · have p1199_0 := h1199c.1
                                    have p1199_1 := h1199c.2.1
                                    have p1199_2 := h1199c.2.2.1
                                    have p1199_3 := h1199c.2.2.2
                                    linarith only [h1121, hlam, p1199_0]
                                  · have p1199_0 := h1199c.1
                                    have p1199_1 := h1199c.2.1
                                    have p1199_2 := h1199c.2.2.1
                                    have p1199_3 := h1199c.2.2.2
                                    linarith only [h1127, hlam, p1199_0]
                                  · have p1199_0 := h1199c.1
                                    have p1199_1 := h1199c.2.1
                                    have p1199_2 := h1199c.2.2.1
                                    have p1199_3 := h1199c.2.2.2
                                    linarith only [h1130, hlam, p1199_0]
                                  · have p1199_0 := h1199c.1
                                    have p1199_1 := h1199c.2.1
                                    have p1199_2 := h1199c.2.2.1
                                    have p1199_3 := h1199c.2.2.2
                                    linarith only [h1120, h1121, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1134_1, p1199_1]
                                  · have p1199_0 := h1199c.1
                                    have p1199_1 := h1199c.2.1
                                    have p1199_2 := h1199c.2.2.1
                                    have p1199_3 := h1199c.2.2.2
                                    linarith only [hlam, p1199_0]
                              · linarith only [h1122, h1196, hlam]
                            · linarith only [h1121, h1195, hlam]
                          · linarith only [h1119, h1194, hlam]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        rcases p1134_3 (m.d 0 1) (by simp) with h1246 | h1246
                        · linarith only [h1036, h1246, hlam]
                        · rcases p1134_3 (m.d 0 2) (by simp) with h1248 | h1248
                          · rcases p1134_3 (m.d 0 3) (by simp) with h1249 | h1249
                            · rcases p1134_3 (m.d 0 4) (by simp) with h1250 | h1250
                              · rcases p1134_3 (m.d 0 5) (by simp) with h1251 | h1251
                                · rcases h3bigk with h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c
                                  · have p1252_0 := h1252c.1
                                    have p1252_1 := h1252c.2.1
                                    have p1252_2 := h1252c.2.2.1
                                    have p1252_3 := h1252c.2.2.2
                                    linarith only [hlam, p1252_0]
                                  · have p1252_0 := h1252c.1
                                    have p1252_1 := h1252c.2.1
                                    have p1252_2 := h1252c.2.2.1
                                    have p1252_3 := h1252c.2.2.2
                                    linarith only [h692, hlam, p1252_1]
                                  · have p1252_0 := h1252c.1
                                    have p1252_1 := h1252c.2.1
                                    have p1252_2 := h1252c.2.2.1
                                    have p1252_3 := h1252c.2.2.2
                                    linarith only [h0, h1117, h1129, h1131, h1132, hc12, hlam, hphi, ht01, ht0b, ht5b, p1252_1, u5ehi3]
                                  · have p1252_0 := h1252c.1
                                    have p1252_1 := h1252c.2.1
                                    have p1252_2 := h1252c.2.2.1
                                    have p1252_3 := h1252c.2.2.2
                                    rcases p1252_3 (m.d 0 3) (by simp) with h1256 | h1256
                                    · rcases p1252_3 (m.d 1 3) (by simp) with h1257 | h1257
                                      · rcases p1252_3 (m.d 2 3) (by simp) with h1258 | h1258
                                        · linarith only [h1117, h1258, hlam]
                                        · linarith only [h1129, h1258, hlam]
                                      · linarith only [h1126, h1257, hlam]
                                    · linarith only [h1256, hlam, p1252_0]
                                  · have p1252_0 := h1252c.1
                                    have p1252_1 := h1252c.2.1
                                    have p1252_2 := h1252c.2.2.1
                                    have p1252_3 := h1252c.2.2.2
                                    rcases p1252_3 (m.d 0 3) (by simp) with h1263 | h1263
                                    · rcases p1252_3 (m.d 1 3) (by simp) with h1264 | h1264
                                      · rcases p1252_3 (m.d 2 3) (by simp) with h1265 | h1265
                                        · linarith only [h1117, h1265, hlam]
                                        · linarith only [h1130, h1265, hlam]
                                      · linarith only [h1127, h1264, hlam]
                                    · linarith only [h1263, hlam, p1252_0]
                                  · have p1252_0 := h1252c.1
                                    have p1252_1 := h1252c.2.1
                                    have p1252_2 := h1252c.2.2.1
                                    have p1252_3 := h1252c.2.2.2
                                    linarith only [h1117, h1123, h1129, h1131, h1132, hc12, hlam, hphi, ht01, ht0b, ht5b, p1252_1, u5ehi3]
                                  · have p1252_0 := h1252c.1
                                    have p1252_1 := h1252c.2.1
                                    have p1252_2 := h1252c.2.2.1
                                    have p1252_3 := h1252c.2.2.2
                                    linarith only [hlam, p1252_0]
                                  · have p1252_0 := h1252c.1
                                    have p1252_1 := h1252c.2.1
                                    have p1252_2 := h1252c.2.2.1
                                    have p1252_3 := h1252c.2.2.2
                                    linarith only [h1123, h1129, h1131, h1132, hc12, hlam, hphi, ht01, ht0b, ht5b, p1252_1, u5ehi3]
                                  · have p1252_0 := h1252c.1
                                    have p1252_1 := h1252c.2.1
                                    have p1252_2 := h1252c.2.2.1
                                    have p1252_3 := h1252c.2.2.2
                                    rcases p1252_3 (m.d 0 3) (by simp) with h1273 | h1273
                                    · linarith only [h1273, h692, hlam]
                                    · linarith only [h1120, h1273, hlam]
                                  · have p1252_0 := h1252c.1
                                    have p1252_1 := h1252c.2.1
                                    have p1252_2 := h1252c.2.2.1
                                    have p1252_3 := h1252c.2.2.2
                                    rcases p1252_3 (m.d 0 3) (by simp) with h1276 | h1276
                                    · linarith only [h1276, h692, hlam]
                                    · linarith only [h1121, h1276, hlam]
                                  · have p1252_0 := h1252c.1
                                    have p1252_1 := h1252c.2.1
                                    have p1252_2 := h1252c.2.2.1
                                    have p1252_3 := h1252c.2.2.2
                                    linarith only [h1117, hlam, p1252_0]
                                  · have p1252_0 := h1252c.1
                                    have p1252_1 := h1252c.2.1
                                    have p1252_2 := h1252c.2.2.1
                                    have p1252_3 := h1252c.2.2.2
                                    linarith only [h1123, hlam, p1252_0]
                                  · have p1252_0 := h1252c.1
                                    have p1252_1 := h1252c.2.1
                                    have p1252_2 := h1252c.2.2.1
                                    have p1252_3 := h1252c.2.2.2
                                    linarith only [hlam, p1252_0]
                                  · have p1252_0 := h1252c.1
                                    have p1252_1 := h1252c.2.1
                                    have p1252_2 := h1252c.2.2.1
                                    have p1252_3 := h1252c.2.2.2
                                    rcases p1252_3 (m.d 0 3) (by simp) with h1282 | h1282
                                    · rcases p1252_3 (m.d 1 3) (by simp) with h1283 | h1283
                                      · rcases p1252_3 (m.d 2 3) (by simp) with h1284 | h1284
                                        · rcases p1252_3 (m.d 3 4) (by simp) with h1285 | h1285
                                          · linarith only [h1285, hlam, p1252_0]
                                          · rcases p1252_3 (m.d 3 5) (by simp) with h1287 | h1287
                                            · linarith only [h1130, h1287, hlam]
                                            · linarith only [h1132, h1287, hlam]
                                        · linarith only [h1284, hlam, p1252_0]
                                      · linarith only [h1126, h1283, hlam]
                                    · linarith only [h1120, h1282, hlam]
                                  · have p1252_0 := h1252c.1
                                    have p1252_1 := h1252c.2.1
                                    have p1252_2 := h1252c.2.2.1
                                    have p1252_3 := h1252c.2.2.2
                                    linarith only [h0, h1117, hc12, hlam, hphi, ht01, ht0b, ht5b, p1252_1, u5ehi3]
                                  · have p1252_0 := h1252c.1
                                    have p1252_1 := h1252c.2.1
                                    have p1252_2 := h1252c.2.2.1
                                    have p1252_3 := h1252c.2.2.2
                                    linarith only [h1120, hlam, p1252_0]
                                  · have p1252_0 := h1252c.1
                                    have p1252_1 := h1252c.2.1
                                    have p1252_2 := h1252c.2.2.1
                                    have p1252_3 := h1252c.2.2.2
                                    linarith only [h1126, hlam, p1252_0]
                                  · have p1252_0 := h1252c.1
                                    have p1252_1 := h1252c.2.1
                                    have p1252_2 := h1252c.2.2.1
                                    have p1252_3 := h1252c.2.2.2
                                    linarith only [h1129, hlam, p1252_0]
                                  · have p1252_0 := h1252c.1
                                    have p1252_1 := h1252c.2.1
                                    have p1252_2 := h1252c.2.2.1
                                    have p1252_3 := h1252c.2.2.2
                                    linarith only [hlam, p1252_0]
                                  · have p1252_0 := h1252c.1
                                    have p1252_1 := h1252c.2.1
                                    have p1252_2 := h1252c.2.2.1
                                    have p1252_3 := h1252c.2.2.2
                                    linarith only [h1132, hlam, p1252_1]
                                  · have p1252_0 := h1252c.1
                                    have p1252_1 := h1252c.2.1
                                    have p1252_2 := h1252c.2.2.1
                                    have p1252_3 := h1252c.2.2.2
                                    linarith only [h1121, hlam, p1252_0]
                                  · have p1252_0 := h1252c.1
                                    have p1252_1 := h1252c.2.1
                                    have p1252_2 := h1252c.2.2.1
                                    have p1252_3 := h1252c.2.2.2
                                    linarith only [h1127, hlam, p1252_0]
                                  · have p1252_0 := h1252c.1
                                    have p1252_1 := h1252c.2.1
                                    have p1252_2 := h1252c.2.2.1
                                    have p1252_3 := h1252c.2.2.2
                                    linarith only [h1130, hlam, p1252_0]
                                  · have p1252_0 := h1252c.1
                                    have p1252_1 := h1252c.2.1
                                    have p1252_2 := h1252c.2.2.1
                                    have p1252_3 := h1252c.2.2.2
                                    linarith only [h0, h1118, h1131, h1132, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1252_1]
                                  · have p1252_0 := h1252c.1
                                    have p1252_1 := h1252c.2.1
                                    have p1252_2 := h1252c.2.2.1
                                    have p1252_3 := h1252c.2.2.2
                                    linarith only [hlam, p1252_0]
                                · linarith only [h1036, h1251, hlam]
                              · linarith only [h1250, h921, hlam]
                            · linarith only [h1249, h692, hlam]
                          · linarith only [h0, h1248, hlam]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [h1119, hlam, p1134_1]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [h1121, hlam, p1134_0]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [h1122, hlam, p1134_1]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [hlam, p1134_0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1312 | h1312
                    · linarith only [h1131, h1312, hc34, hlam, hphi, ht23, u2ehi3]
                    · rcases h0bigk with h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [hlam, p1314_0]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [h0, hlam, p1314_1]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [h692, hlam, p1314_0]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [h921, hlam, p1314_1]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [h1036, hlam, p1314_1]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        rcases p1314_3 (m.d 0 1) (by simp) with h1320 | h1320
                        · linarith only [h0, h1320, hlam]
                        · rcases p1314_3 (m.d 0 2) (by simp) with h1322 | h1322
                          · rcases p1314_3 (m.d 0 3) (by simp) with h1323 | h1323
                            · linarith only [h1117, h1323, hlam]
                            · linarith only [h1323, h692, hlam]
                          · linarith only [h0, h1322, hlam]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [hlam, p1314_0]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [h0, h1120, h1122, h1131, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1314_1, u2ehi3]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [h0, h1122, h1131, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1314_1, u2ehi3]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [h0, h1122, h1131, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1314_1, u2ehi3]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        rcases p1314_3 (m.d 0 1) (by simp) with h1331 | h1331
                        · linarith only [h1331, h692, hlam]
                        · rcases p1314_3 (m.d 0 2) (by simp) with h1333 | h1333
                          · rcases p1314_3 (m.d 0 3) (by simp) with h1334 | h1334
                            · rcases p1314_3 (m.d 0 4) (by simp) with h1335 | h1335
                              · linarith only [h1120, h1335, hlam]
                              · linarith only [h1335, h921, hlam]
                            · linarith only [h1334, h692, hlam]
                          · linarith only [h0, h1333, hlam]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [h1117, hlam, p1314_1]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [hlam, p1314_0]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [h1122, h1131, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1314_1, u2ehi3]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [h0, h1117, h1122, h1131, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1314_1, u2ehi3]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        rcases p1314_3 (m.d 0 1) (by simp) with h1344 | h1344
                        · linarith only [h1344, h921, hlam]
                        · rcases p1314_3 (m.d 0 2) (by simp) with h1346 | h1346
                          · rcases p1314_3 (m.d 0 3) (by simp) with h1347 | h1347
                            · rcases p1314_3 (m.d 0 4) (by simp) with h1348 | h1348
                              · rcases p1314_3 (m.d 0 5) (by simp) with h1349 | h1349
                                · linarith only [h1122, h1349, hlam]
                                · linarith only [h1036, h1349, hlam]
                              · linarith only [h1348, h921, hlam]
                            · linarith only [h1347, h692, hlam]
                          · linarith only [h0, h1346, hlam]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [h1118, hlam, p1314_0]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [h1120, hlam, p1314_0]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [hlam, p1314_0]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [h1122, h1131, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1314_1, u2ehi3]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        rcases p1314_3 (m.d 0 1) (by simp) with h1359 | h1359
                        · linarith only [h1036, h1359, hlam]
                        · rcases p1314_3 (m.d 0 2) (by simp) with h1361 | h1361
                          · rcases p1314_3 (m.d 0 3) (by simp) with h1362 | h1362
                            · rcases p1314_3 (m.d 0 4) (by simp) with h1363 | h1363
                              · rcases p1314_3 (m.d 0 5) (by simp) with h1364 | h1364
                                · rcases h3bigk with h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c
                                  · have p1365_0 := h1365c.1
                                    have p1365_1 := h1365c.2.1
                                    have p1365_2 := h1365c.2.2.1
                                    have p1365_3 := h1365c.2.2.2
                                    linarith only [hlam, p1365_0]
                                  · have p1365_0 := h1365c.1
                                    have p1365_1 := h1365c.2.1
                                    have p1365_2 := h1365c.2.2.1
                                    have p1365_3 := h1365c.2.2.2
                                    linarith only [h692, hlam, p1365_1]
                                  · have p1365_0 := h1365c.1
                                    have p1365_1 := h1365c.2.1
                                    have p1365_2 := h1365c.2.2.1
                                    have p1365_3 := h1365c.2.2.2
                                    linarith only [h0, h1117, h1130, hc12, hlam, hphi, ht01, ht0b, ht5b, p1365_1, u5ehi3]
                                  · have p1365_0 := h1365c.1
                                    have p1365_1 := h1365c.2.1
                                    have p1365_2 := h1365c.2.2.1
                                    have p1365_3 := h1365c.2.2.2
                                    rcases p1365_3 (m.d 0 3) (by simp) with h1369 | h1369
                                    · rcases p1365_3 (m.d 1 3) (by simp) with h1370 | h1370
                                      · rcases p1365_3 (m.d 2 3) (by simp) with h1371 | h1371
                                        · linarith only [h1117, h1371, hlam]
                                        · linarith only [h1129, h1371, hlam]
                                      · linarith only [h1126, h1370, hlam]
                                    · linarith only [h1369, hlam, p1365_0]
                                  · have p1365_0 := h1365c.1
                                    have p1365_1 := h1365c.2.1
                                    have p1365_2 := h1365c.2.2.1
                                    have p1365_3 := h1365c.2.2.2
                                    rcases p1365_3 (m.d 0 3) (by simp) with h1376 | h1376
                                    · rcases p1365_3 (m.d 1 3) (by simp) with h1377 | h1377
                                      · rcases p1365_3 (m.d 2 3) (by simp) with h1378 | h1378
                                        · linarith only [h1117, h1378, hlam]
                                        · linarith only [h1130, h1378, hlam]
                                      · linarith only [h1127, h1377, hlam]
                                    · linarith only [h1376, hlam, p1365_0]
                                  · have p1365_0 := h1365c.1
                                    have p1365_1 := h1365c.2.1
                                    have p1365_2 := h1365c.2.2.1
                                    have p1365_3 := h1365c.2.2.2
                                    linarith only [h1117, h1123, h1130, hc12, hlam, hphi, ht01, ht0b, ht5b, p1365_1, u5ehi3]
                                  · have p1365_0 := h1365c.1
                                    have p1365_1 := h1365c.2.1
                                    have p1365_2 := h1365c.2.2.1
                                    have p1365_3 := h1365c.2.2.2
                                    linarith only [hlam, p1365_0]
                                  · have p1365_0 := h1365c.1
                                    have p1365_1 := h1365c.2.1
                                    have p1365_2 := h1365c.2.2.1
                                    have p1365_3 := h1365c.2.2.2
                                    linarith only [h1123, h1130, hc12, hlam, hphi, ht01, ht0b, ht5b, p1365_1, u5ehi3]
                                  · have p1365_0 := h1365c.1
                                    have p1365_1 := h1365c.2.1
                                    have p1365_2 := h1365c.2.2.1
                                    have p1365_3 := h1365c.2.2.2
                                    rcases p1365_3 (m.d 0 3) (by simp) with h1386 | h1386
                                    · linarith only [h1386, h692, hlam]
                                    · linarith only [h1120, h1386, hlam]
                                  · have p1365_0 := h1365c.1
                                    have p1365_1 := h1365c.2.1
                                    have p1365_2 := h1365c.2.2.1
                                    have p1365_3 := h1365c.2.2.2
                                    rcases p1365_3 (m.d 0 3) (by simp) with h1389 | h1389
                                    · linarith only [h1389, h692, hlam]
                                    · linarith only [h1121, h1389, hlam]
                                  · have p1365_0 := h1365c.1
                                    have p1365_1 := h1365c.2.1
                                    have p1365_2 := h1365c.2.2.1
                                    have p1365_3 := h1365c.2.2.2
                                    linarith only [h1117, hlam, p1365_0]
                                  · have p1365_0 := h1365c.1
                                    have p1365_1 := h1365c.2.1
                                    have p1365_2 := h1365c.2.2.1
                                    have p1365_3 := h1365c.2.2.2
                                    linarith only [h1123, hlam, p1365_0]
                                  · have p1365_0 := h1365c.1
                                    have p1365_1 := h1365c.2.1
                                    have p1365_2 := h1365c.2.2.1
                                    have p1365_3 := h1365c.2.2.2
                                    linarith only [hlam, p1365_0]
                                  · have p1365_0 := h1365c.1
                                    have p1365_1 := h1365c.2.1
                                    have p1365_2 := h1365c.2.2.1
                                    have p1365_3 := h1365c.2.2.2
                                    rcases p1365_3 (m.d 0 3) (by simp) with h1395 | h1395
                                    · rcases p1365_3 (m.d 1 3) (by simp) with h1396 | h1396
                                      · rcases p1365_3 (m.d 2 3) (by simp) with h1397 | h1397
                                        · rcases p1365_3 (m.d 3 4) (by simp) with h1398 | h1398
                                          · linarith only [h1398, hlam, p1365_0]
                                          · rcases p1365_3 (m.d 3 5) (by simp) with h1400 | h1400
                                            · linarith only [h1130, h1400, hlam]
                                            · linarith only [h1312, h1400, hlam]
                                        · linarith only [h1397, hlam, p1365_0]
                                      · linarith only [h1126, h1396, hlam]
                                    · linarith only [h1120, h1395, hlam]
                                  · have p1365_0 := h1365c.1
                                    have p1365_1 := h1365c.2.1
                                    have p1365_2 := h1365c.2.2.1
                                    have p1365_3 := h1365c.2.2.2
                                    linarith only [h0, h1117, hc12, hlam, hphi, ht01, ht0b, ht5b, p1365_1, u5ehi3]
                                  · have p1365_0 := h1365c.1
                                    have p1365_1 := h1365c.2.1
                                    have p1365_2 := h1365c.2.2.1
                                    have p1365_3 := h1365c.2.2.2
                                    linarith only [h1120, hlam, p1365_0]
                                  · have p1365_0 := h1365c.1
                                    have p1365_1 := h1365c.2.1
                                    have p1365_2 := h1365c.2.2.1
                                    have p1365_3 := h1365c.2.2.2
                                    linarith only [h1126, hlam, p1365_0]
                                  · have p1365_0 := h1365c.1
                                    have p1365_1 := h1365c.2.1
                                    have p1365_2 := h1365c.2.2.1
                                    have p1365_3 := h1365c.2.2.2
                                    linarith only [h1129, hlam, p1365_0]
                                  · have p1365_0 := h1365c.1
                                    have p1365_1 := h1365c.2.1
                                    have p1365_2 := h1365c.2.2.1
                                    have p1365_3 := h1365c.2.2.2
                                    linarith only [hlam, p1365_0]
                                  · have p1365_0 := h1365c.1
                                    have p1365_1 := h1365c.2.1
                                    have p1365_2 := h1365c.2.2.1
                                    have p1365_3 := h1365c.2.2.2
                                    linarith only [h1312, hlam, p1365_1]
                                  · have p1365_0 := h1365c.1
                                    have p1365_1 := h1365c.2.1
                                    have p1365_2 := h1365c.2.2.1
                                    have p1365_3 := h1365c.2.2.2
                                    linarith only [h1121, hlam, p1365_0]
                                  · have p1365_0 := h1365c.1
                                    have p1365_1 := h1365c.2.1
                                    have p1365_2 := h1365c.2.2.1
                                    have p1365_3 := h1365c.2.2.2
                                    linarith only [h1127, hlam, p1365_0]
                                  · have p1365_0 := h1365c.1
                                    have p1365_1 := h1365c.2.1
                                    have p1365_2 := h1365c.2.2.1
                                    have p1365_3 := h1365c.2.2.2
                                    linarith only [h1130, hlam, p1365_0]
                                  · have p1365_0 := h1365c.1
                                    have p1365_1 := h1365c.2.1
                                    have p1365_2 := h1365c.2.2.1
                                    have p1365_3 := h1365c.2.2.2
                                    linarith only [h0, h1117, h1130, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1365_1]
                                  · have p1365_0 := h1365c.1
                                    have p1365_1 := h1365c.2.1
                                    have p1365_2 := h1365c.2.2.1
                                    have p1365_3 := h1365c.2.2.2
                                    linarith only [hlam, p1365_0]
                                · linarith only [h1036, h1364, hlam]
                              · linarith only [h1363, h921, hlam]
                            · linarith only [h1362, h692, hlam]
                          · linarith only [h0, h1361, hlam]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [h1119, hlam, p1314_1]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [h1121, hlam, p1314_0]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [h1122, hlam, p1314_1]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [hlam, p1314_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1425 | h1425
                  · linarith only [h1121, h1123, h1129, h1130, h1425, h692, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1427 | h1427
                    · linarith only [h1425, h1427, hc34, hlam, hphi, ht23, u2ehi3]
                    · rcases h0bigk with h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c | h1429c
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [hlam, p1429_0]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [h0, hlam, p1429_1]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [h692, hlam, p1429_0]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [h921, hlam, p1429_1]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [h1036, hlam, p1429_1]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        rcases p1429_3 (m.d 0 1) (by simp) with h1435 | h1435
                        · linarith only [h0, h1435, hlam]
                        · rcases p1429_3 (m.d 0 2) (by simp) with h1437 | h1437
                          · rcases p1429_3 (m.d 0 3) (by simp) with h1438 | h1438
                            · linarith only [h1117, h1438, hlam]
                            · linarith only [h1438, h692, hlam]
                          · linarith only [h0, h1437, hlam]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [hlam, p1429_0]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [h0, h1120, h1122, h1130, h1427, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1429_1]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [h0, h1122, h1130, h1427, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1429_1, u2ehi2]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [h0, h1121, h1130, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1429_1, u2ehi2]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        rcases p1429_3 (m.d 0 1) (by simp) with h1446 | h1446
                        · linarith only [h1446, h692, hlam]
                        · rcases p1429_3 (m.d 0 2) (by simp) with h1448 | h1448
                          · rcases p1429_3 (m.d 0 3) (by simp) with h1449 | h1449
                            · rcases p1429_3 (m.d 0 4) (by simp) with h1450 | h1450
                              · linarith only [h1120, h1450, hlam]
                              · linarith only [h1450, h921, hlam]
                            · linarith only [h1449, h692, hlam]
                          · linarith only [h0, h1448, hlam]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [h1117, hlam, p1429_1]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [hlam, p1429_0]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [h1122, h1129, h1130, h1427, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1429_1, u2ehi3]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [h0, h1117, h1122, h1129, h1130, h1427, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1429_1, u2ehi3]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        rcases p1429_3 (m.d 0 1) (by simp) with h1459 | h1459
                        · linarith only [h1459, h921, hlam]
                        · rcases p1429_3 (m.d 0 2) (by simp) with h1461 | h1461
                          · rcases p1429_3 (m.d 0 3) (by simp) with h1462 | h1462
                            · rcases p1429_3 (m.d 0 4) (by simp) with h1463 | h1463
                              · rcases p1429_3 (m.d 0 5) (by simp) with h1464 | h1464
                                · linarith only [h1122, h1464, hlam]
                                · linarith only [h1036, h1464, hlam]
                              · linarith only [h1463, h921, hlam]
                            · linarith only [h1462, h692, hlam]
                          · linarith only [h0, h1461, hlam]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [h1118, hlam, p1429_0]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [h1120, hlam, p1429_0]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [hlam, p1429_0]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [h1122, h1129, h1130, h1427, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1429_1, u2ehi3]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        rcases p1429_3 (m.d 0 1) (by simp) with h1474 | h1474
                        · linarith only [h1036, h1474, hlam]
                        · rcases p1429_3 (m.d 0 2) (by simp) with h1476 | h1476
                          · rcases p1429_3 (m.d 0 3) (by simp) with h1477 | h1477
                            · rcases p1429_3 (m.d 0 4) (by simp) with h1478 | h1478
                              · rcases p1429_3 (m.d 0 5) (by simp) with h1479 | h1479
                                · rcases h3bigk with h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c
                                  · have p1480_0 := h1480c.1
                                    have p1480_1 := h1480c.2.1
                                    have p1480_2 := h1480c.2.2.1
                                    have p1480_3 := h1480c.2.2.2
                                    linarith only [hlam, p1480_0]
                                  · have p1480_0 := h1480c.1
                                    have p1480_1 := h1480c.2.1
                                    have p1480_2 := h1480c.2.2.1
                                    have p1480_3 := h1480c.2.2.2
                                    linarith only [h692, hlam, p1480_1]
                                  · have p1480_0 := h1480c.1
                                    have p1480_1 := h1480c.2.1
                                    have p1480_2 := h1480c.2.2.1
                                    have p1480_3 := h1480c.2.2.2
                                    rcases p1480_3 (m.d 0 3) (by simp) with h1483 | h1483
                                    · rcases p1480_3 (m.d 1 3) (by simp) with h1484 | h1484
                                      · rcases p1480_3 (m.d 2 3) (by simp) with h1485 | h1485
                                        · linarith only [h1117, h1485, hlam]
                                        · rcases p1480_3 (m.d 3 4) (by simp) with h1487 | h1487
                                          · linarith only [h1120, h1487, hlam]
                                          · rcases p1480_3 (m.d 3 5) (by simp) with h1489 | h1489
                                            · linarith only [h1121, h1489, hlam]
                                            · linarith only [h1130, h1489, hlam]
                                      · linarith only [h1123, h1484, hlam]
                                    · linarith only [h1117, h1483, hlam]
                                  · have p1480_0 := h1480c.1
                                    have p1480_1 := h1480c.2.1
                                    have p1480_2 := h1480c.2.2.1
                                    have p1480_3 := h1480c.2.2.2
                                    linarith only [h1121, h1129, h1130, hlam, p1480_2]
                                  · have p1480_0 := h1480c.1
                                    have p1480_1 := h1480c.2.1
                                    have p1480_2 := h1480c.2.2.1
                                    have p1480_3 := h1480c.2.2.2
                                    linarith only [h1129, h1130, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1480_1, u2ehi3]
                                  · have p1480_0 := h1480c.1
                                    have p1480_1 := h1480c.2.1
                                    have p1480_2 := h1480c.2.2.1
                                    have p1480_3 := h1480c.2.2.2
                                    linarith only [h1121, h1123, h1129, h1130, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1480_1, u2ehi3]
                                  · have p1480_0 := h1480c.1
                                    have p1480_1 := h1480c.2.1
                                    have p1480_2 := h1480c.2.2.1
                                    have p1480_3 := h1480c.2.2.2
                                    linarith only [hlam, p1480_0]
                                  · have p1480_0 := h1480c.1
                                    have p1480_1 := h1480c.2.1
                                    have p1480_2 := h1480c.2.2.1
                                    have p1480_3 := h1480c.2.2.2
                                    rcases p1480_3 (m.d 0 3) (by simp) with h1498 | h1498
                                    · linarith only [h1498, h692, hlam]
                                    · linarith only [h1117, h1498, hlam]
                                  · have p1480_0 := h1480c.1
                                    have p1480_1 := h1480c.2.1
                                    have p1480_2 := h1480c.2.2.1
                                    have p1480_3 := h1480c.2.2.2
                                    linarith only [h1120, h1122, h1129, h1130, h1427, h692, hlam, p1480_2]
                                  · have p1480_0 := h1480c.1
                                    have p1480_1 := h1480c.2.1
                                    have p1480_2 := h1480c.2.2.1
                                    have p1480_3 := h1480c.2.2.2
                                    linarith only [h1129, h1130, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1480_1, u2ehi3]
                                  · have p1480_0 := h1480c.1
                                    have p1480_1 := h1480c.2.1
                                    have p1480_2 := h1480c.2.2.1
                                    have p1480_3 := h1480c.2.2.2
                                    linarith only [h1117, hlam, p1480_0]
                                  · have p1480_0 := h1480c.1
                                    have p1480_1 := h1480c.2.1
                                    have p1480_2 := h1480c.2.2.1
                                    have p1480_3 := h1480c.2.2.2
                                    linarith only [h1123, hlam, p1480_0]
                                  · have p1480_0 := h1480c.1
                                    have p1480_1 := h1480c.2.1
                                    have p1480_2 := h1480c.2.2.1
                                    have p1480_3 := h1480c.2.2.2
                                    linarith only [hlam, p1480_0]
                                  · have p1480_0 := h1480c.1
                                    have p1480_1 := h1480c.2.1
                                    have p1480_2 := h1480c.2.2.1
                                    have p1480_3 := h1480c.2.2.2
                                    linarith only [h1120, h1122, h1130, h1427, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1480_1]
                                  · have p1480_0 := h1480c.1
                                    have p1480_1 := h1480c.2.1
                                    have p1480_2 := h1480c.2.2.1
                                    have p1480_3 := h1480c.2.2.2
                                    linarith only [h1130, hlam, p1480_0]
                                  · have p1480_0 := h1480c.1
                                    have p1480_1 := h1480c.2.1
                                    have p1480_2 := h1480c.2.2.1
                                    have p1480_3 := h1480c.2.2.2
                                    linarith only [h1120, hlam, p1480_0]
                                  · have p1480_0 := h1480c.1
                                    have p1480_1 := h1480c.2.1
                                    have p1480_2 := h1480c.2.2.1
                                    have p1480_3 := h1480c.2.2.2
                                    linarith only [h1126, hlam, p1480_0]
                                  · have p1480_0 := h1480c.1
                                    have p1480_1 := h1480c.2.1
                                    have p1480_2 := h1480c.2.2.1
                                    have p1480_3 := h1480c.2.2.2
                                    linarith only [h1129, hlam, p1480_0]
                                  · have p1480_0 := h1480c.1
                                    have p1480_1 := h1480c.2.1
                                    have p1480_2 := h1480c.2.2.1
                                    have p1480_3 := h1480c.2.2.2
                                    linarith only [hlam, p1480_0]
                                  · have p1480_0 := h1480c.1
                                    have p1480_1 := h1480c.2.1
                                    have p1480_2 := h1480c.2.2.1
                                    have p1480_3 := h1480c.2.2.2
                                    linarith only [h1427, hlam, p1480_1]
                                  · have p1480_0 := h1480c.1
                                    have p1480_1 := h1480c.2.1
                                    have p1480_2 := h1480c.2.2.1
                                    have p1480_3 := h1480c.2.2.2
                                    linarith only [h1121, hlam, p1480_0]
                                  · have p1480_0 := h1480c.1
                                    have p1480_1 := h1480c.2.1
                                    have p1480_2 := h1480c.2.2.1
                                    have p1480_3 := h1480c.2.2.2
                                    linarith only [h1127, hlam, p1480_0]
                                  · have p1480_0 := h1480c.1
                                    have p1480_1 := h1480c.2.1
                                    have p1480_2 := h1480c.2.2.1
                                    have p1480_3 := h1480c.2.2.2
                                    linarith only [h1120, h1122, h1427, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1480_1, u2ehi2]
                                  · have p1480_0 := h1480c.1
                                    have p1480_1 := h1480c.2.1
                                    have p1480_2 := h1480c.2.2.1
                                    have p1480_3 := h1480c.2.2.2
                                    rcases p1480_3 (m.d 0 3) (by simp) with h1516 | h1516
                                    · rcases p1480_3 (m.d 1 3) (by simp) with h1517 | h1517
                                      · rcases p1480_3 (m.d 2 3) (by simp) with h1518 | h1518
                                        · linarith only [h1130, h1518, hlam]
                                        · linarith only [h1129, h1518, hlam]
                                      · linarith only [h1126, h1517, hlam]
                                    · linarith only [h1120, h1516, hlam]
                                  · have p1480_0 := h1480c.1
                                    have p1480_1 := h1480c.2.1
                                    have p1480_2 := h1480c.2.2.1
                                    have p1480_3 := h1480c.2.2.2
                                    linarith only [hlam, p1480_0]
                                · linarith only [h1036, h1479, hlam]
                              · linarith only [h1478, h921, hlam]
                            · linarith only [h1477, h692, hlam]
                          · linarith only [h0, h1476, hlam]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [h1119, hlam, p1429_1]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [h1121, hlam, p1429_0]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [h1122, hlam, p1429_1]
                      · have p1429_0 := h1429c.1
                        have p1429_1 := h1429c.2.1
                        have p1429_2 := h1429c.2.2.1
                        have p1429_3 := h1429c.2.2.2
                        linarith only [hlam, p1429_0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1532 | h1532
                · linarith only [h0, h1117, h1120, h1129, h1532, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1534 | h1534
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1535 | h1535
                    · rcases h0bigk with h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c
                      · have p1536_0 := h1536c.1
                        have p1536_1 := h1536c.2.1
                        have p1536_2 := h1536c.2.2.1
                        have p1536_3 := h1536c.2.2.2
                        linarith only [hlam, p1536_0]
                      · have p1536_0 := h1536c.1
                        have p1536_1 := h1536c.2.1
                        have p1536_2 := h1536c.2.2.1
                        have p1536_3 := h1536c.2.2.2
                        linarith only [h0, hlam, p1536_1]
                      · have p1536_0 := h1536c.1
                        have p1536_1 := h1536c.2.1
                        have p1536_2 := h1536c.2.2.1
                        have p1536_3 := h1536c.2.2.2
                        linarith only [h692, hlam, p1536_0]
                      · have p1536_0 := h1536c.1
                        have p1536_1 := h1536c.2.1
                        have p1536_2 := h1536c.2.2.1
                        have p1536_3 := h1536c.2.2.2
                        linarith only [h921, hlam, p1536_1]
                      · have p1536_0 := h1536c.1
                        have p1536_1 := h1536c.2.1
                        have p1536_2 := h1536c.2.2.1
                        have p1536_3 := h1536c.2.2.2
                        linarith only [h1036, hlam, p1536_1]
                      · have p1536_0 := h1536c.1
                        have p1536_1 := h1536c.2.1
                        have p1536_2 := h1536c.2.2.1
                        have p1536_3 := h1536c.2.2.2
                        rcases p1536_3 (m.d 0 1) (by simp) with h1542 | h1542
                        · linarith only [h0, h1542, hlam]
                        · rcases p1536_3 (m.d 0 2) (by simp) with h1544 | h1544
                          · rcases p1536_3 (m.d 0 3) (by simp) with h1545 | h1545
                            · linarith only [h1117, h1545, hlam]
                            · linarith only [h1545, h692, hlam]
                          · linarith only [h0, h1544, hlam]
                      · have p1536_0 := h1536c.1
                        have p1536_1 := h1536c.2.1
                        have p1536_2 := h1536c.2.2.1
                        have p1536_3 := h1536c.2.2.2
                        linarith only [hlam, p1536_0]
                      · have p1536_0 := h1536c.1
                        have p1536_1 := h1536c.2.1
                        have p1536_2 := h1536c.2.2.1
                        have p1536_3 := h1536c.2.2.2
                        linarith only [h0, h1120, h1532, h1535, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1536_1]
                      · have p1536_0 := h1536c.1
                        have p1536_1 := h1536c.2.1
                        have p1536_2 := h1536c.2.2.1
                        have p1536_3 := h1536c.2.2.2
                        linarith only [h0, h1118, h1534, hc12, hlam, hphi, ht01, ht0b, ht5b, p1536_1, u5ehi4]
                      · have p1536_0 := h1536c.1
                        have p1536_1 := h1536c.2.1
                        have p1536_2 := h1536c.2.2.1
                        have p1536_3 := h1536c.2.2.2
                        linarith only [h0, h1121, h1532, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1536_1, u2ehi2]
                      · have p1536_0 := h1536c.1
                        have p1536_1 := h1536c.2.1
                        have p1536_2 := h1536c.2.2.1
                        have p1536_3 := h1536c.2.2.2
                        rcases p1536_3 (m.d 0 1) (by simp) with h1553 | h1553
                        · linarith only [h1553, h692, hlam]
                        · rcases p1536_3 (m.d 0 2) (by simp) with h1555 | h1555
                          · rcases p1536_3 (m.d 0 3) (by simp) with h1556 | h1556
                            · rcases p1536_3 (m.d 0 4) (by simp) with h1557 | h1557
                              · linarith only [h1120, h1557, hlam]
                              · linarith only [h1557, h921, hlam]
                            · linarith only [h1556, h692, hlam]
                          · linarith only [h0, h1555, hlam]
                      · have p1536_0 := h1536c.1
                        have p1536_1 := h1536c.2.1
                        have p1536_2 := h1536c.2.2.1
                        have p1536_3 := h1536c.2.2.2
                        linarith only [h1117, hlam, p1536_1]
                      · have p1536_0 := h1536c.1
                        have p1536_1 := h1536c.2.1
                        have p1536_2 := h1536c.2.2.1
                        have p1536_3 := h1536c.2.2.2
                        linarith only [hlam, p1536_0]
                      · have p1536_0 := h1536c.1
                        have p1536_1 := h1536c.2.1
                        have p1536_2 := h1536c.2.2.1
                        have p1536_3 := h1536c.2.2.2
                        linarith only [h1120, h1532, h1535, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1536_1, u2ehi2]
                      · have p1536_0 := h1536c.1
                        have p1536_1 := h1536c.2.1
                        have p1536_2 := h1536c.2.2.1
                        have p1536_3 := h1536c.2.2.2
                        linarith only [h1121, h1123, h1532, h692, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1536_1, u2ehi2]
                      · have p1536_0 := h1536c.1
                        have p1536_1 := h1536c.2.1
                        have p1536_2 := h1536c.2.2.1
                        have p1536_3 := h1536c.2.2.2
                        rcases p1536_3 (m.d 0 1) (by simp) with h1566 | h1566
                        · linarith only [h1566, h921, hlam]
                        · rcases p1536_3 (m.d 0 2) (by simp) with h1568 | h1568
                          · rcases p1536_3 (m.d 0 3) (by simp) with h1569 | h1569
                            · rcases p1536_3 (m.d 0 4) (by simp) with h1570 | h1570
                              · rcases p1536_3 (m.d 0 5) (by simp) with h1571 | h1571
                                · linarith only [h1122, h1571, hlam]
                                · linarith only [h1036, h1571, hlam]
                              · linarith only [h1570, h921, hlam]
                            · linarith only [h1569, h692, hlam]
                          · linarith only [h0, h1568, hlam]
                      · have p1536_0 := h1536c.1
                        have p1536_1 := h1536c.2.1
                        have p1536_2 := h1536c.2.2.1
                        have p1536_3 := h1536c.2.2.2
                        linarith only [h1118, hlam, p1536_0]
                      · have p1536_0 := h1536c.1
                        have p1536_1 := h1536c.2.1
                        have p1536_2 := h1536c.2.2.1
                        have p1536_3 := h1536c.2.2.2
                        linarith only [h1120, hlam, p1536_0]
                      · have p1536_0 := h1536c.1
                        have p1536_1 := h1536c.2.1
                        have p1536_2 := h1536c.2.2.1
                        have p1536_3 := h1536c.2.2.2
                        linarith only [hlam, p1536_0]
                      · have p1536_0 := h1536c.1
                        have p1536_1 := h1536c.2.1
                        have p1536_2 := h1536c.2.2.1
                        have p1536_3 := h1536c.2.2.2
                        linarith only [h1121, h1532, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1536_1, u2ehi2]
                      · have p1536_0 := h1536c.1
                        have p1536_1 := h1536c.2.1
                        have p1536_2 := h1536c.2.2.1
                        have p1536_3 := h1536c.2.2.2
                        rcases p1536_3 (m.d 0 1) (by simp) with h1581 | h1581
                        · linarith only [h1036, h1581, hlam]
                        · rcases p1536_3 (m.d 0 2) (by simp) with h1583 | h1583
                          · rcases p1536_3 (m.d 0 3) (by simp) with h1584 | h1584
                            · rcases p1536_3 (m.d 0 4) (by simp) with h1585 | h1585
                              · rcases p1536_3 (m.d 0 5) (by simp) with h1586 | h1586
                                · rcases h3bigk with h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c
                                  · have p1587_0 := h1587c.1
                                    have p1587_1 := h1587c.2.1
                                    have p1587_2 := h1587c.2.2.1
                                    have p1587_3 := h1587c.2.2.2
                                    linarith only [hlam, p1587_0]
                                  · have p1587_0 := h1587c.1
                                    have p1587_1 := h1587c.2.1
                                    have p1587_2 := h1587c.2.2.1
                                    have p1587_3 := h1587c.2.2.2
                                    linarith only [h692, hlam, p1587_1]
                                  · have p1587_0 := h1587c.1
                                    have p1587_1 := h1587c.2.1
                                    have p1587_2 := h1587c.2.2.1
                                    have p1587_3 := h1587c.2.2.2
                                    rcases p1587_3 (m.d 0 3) (by simp) with h1590 | h1590
                                    · rcases p1587_3 (m.d 1 3) (by simp) with h1591 | h1591
                                      · rcases p1587_3 (m.d 2 3) (by simp) with h1592 | h1592
                                        · linarith only [h1117, h1592, hlam]
                                        · rcases p1587_3 (m.d 3 4) (by simp) with h1594 | h1594
                                          · linarith only [h1120, h1594, hlam]
                                          · linarith only [h1129, h1594, hlam]
                                      · linarith only [h1123, h1591, hlam]
                                    · linarith only [h1117, h1590, hlam]
                                  · have p1587_0 := h1587c.1
                                    have p1587_1 := h1587c.2.1
                                    have p1587_2 := h1587c.2.2.1
                                    have p1587_3 := h1587c.2.2.2
                                    linarith only [h1123, h1532, h1535, h692, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1587_1, u2ehi2]
                                  · have p1587_0 := h1587c.1
                                    have p1587_1 := h1587c.2.1
                                    have p1587_2 := h1587c.2.2.1
                                    have p1587_3 := h1587c.2.2.2
                                    linarith only [h1123, h1532, h692, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1587_1, u2ehi2]
                                  · have p1587_0 := h1587c.1
                                    have p1587_1 := h1587c.2.1
                                    have p1587_2 := h1587c.2.2.1
                                    have p1587_3 := h1587c.2.2.2
                                    linarith only [h1120, h1123, h1532, h1535, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1587_1, u2ehi2]
                                  · have p1587_0 := h1587c.1
                                    have p1587_1 := h1587c.2.1
                                    have p1587_2 := h1587c.2.2.1
                                    have p1587_3 := h1587c.2.2.2
                                    linarith only [hlam, p1587_0]
                                  · have p1587_0 := h1587c.1
                                    have p1587_1 := h1587c.2.1
                                    have p1587_2 := h1587c.2.2.1
                                    have p1587_3 := h1587c.2.2.2
                                    rcases p1587_3 (m.d 0 3) (by simp) with h1603 | h1603
                                    · linarith only [h1603, h692, hlam]
                                    · linarith only [h1117, h1603, hlam]
                                  · have p1587_0 := h1587c.1
                                    have p1587_1 := h1587c.2.1
                                    have p1587_2 := h1587c.2.2.1
                                    have p1587_3 := h1587c.2.2.2
                                    linarith only [h1123, h1532, h1535, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1587_1, u2ehi2]
                                  · have p1587_0 := h1587c.1
                                    have p1587_1 := h1587c.2.1
                                    have p1587_2 := h1587c.2.2.1
                                    have p1587_3 := h1587c.2.2.2
                                    linarith only [h1123, h1532, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1587_1, u2ehi2]
                                  · have p1587_0 := h1587c.1
                                    have p1587_1 := h1587c.2.1
                                    have p1587_2 := h1587c.2.2.1
                                    have p1587_3 := h1587c.2.2.2
                                    linarith only [h1117, hlam, p1587_0]
                                  · have p1587_0 := h1587c.1
                                    have p1587_1 := h1587c.2.1
                                    have p1587_2 := h1587c.2.2.1
                                    have p1587_3 := h1587c.2.2.2
                                    linarith only [h1123, hlam, p1587_0]
                                  · have p1587_0 := h1587c.1
                                    have p1587_1 := h1587c.2.1
                                    have p1587_2 := h1587c.2.2.1
                                    have p1587_3 := h1587c.2.2.2
                                    linarith only [hlam, p1587_0]
                                  · have p1587_0 := h1587c.1
                                    have p1587_1 := h1587c.2.1
                                    have p1587_2 := h1587c.2.2.1
                                    have p1587_3 := h1587c.2.2.2
                                    linarith only [h1129, hlam, p1587_0]
                                  · have p1587_0 := h1587c.1
                                    have p1587_1 := h1587c.2.1
                                    have p1587_2 := h1587c.2.2.1
                                    have p1587_3 := h1587c.2.2.2
                                    linarith only [h1532, hlam, p1587_0]
                                  · have p1587_0 := h1587c.1
                                    have p1587_1 := h1587c.2.1
                                    have p1587_2 := h1587c.2.2.1
                                    have p1587_3 := h1587c.2.2.2
                                    linarith only [h1120, hlam, p1587_0]
                                  · have p1587_0 := h1587c.1
                                    have p1587_1 := h1587c.2.1
                                    have p1587_2 := h1587c.2.2.1
                                    have p1587_3 := h1587c.2.2.2
                                    linarith only [h1126, hlam, p1587_0]
                                  · have p1587_0 := h1587c.1
                                    have p1587_1 := h1587c.2.1
                                    have p1587_2 := h1587c.2.2.1
                                    have p1587_3 := h1587c.2.2.2
                                    linarith only [hc34, hlam, hphi, ht23, p1587_1, u2ehi2]
                                  · have p1587_0 := h1587c.1
                                    have p1587_1 := h1587c.2.1
                                    have p1587_2 := h1587c.2.2.1
                                    have p1587_3 := h1587c.2.2.2
                                    linarith only [hlam, p1587_0]
                                  · have p1587_0 := h1587c.1
                                    have p1587_1 := h1587c.2.1
                                    have p1587_2 := h1587c.2.2.1
                                    have p1587_3 := h1587c.2.2.2
                                    linarith only [h1120, h1123, h1532, h692, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1587_1, u2ehi2]
                                  · have p1587_0 := h1587c.1
                                    have p1587_1 := h1587c.2.1
                                    have p1587_2 := h1587c.2.2.1
                                    have p1587_3 := h1587c.2.2.2
                                    linarith only [h1121, hlam, p1587_0]
                                  · have p1587_0 := h1587c.1
                                    have p1587_1 := h1587c.2.1
                                    have p1587_2 := h1587c.2.2.1
                                    have p1587_3 := h1587c.2.2.2
                                    linarith only [h1127, hlam, p1587_0]
                                  · have p1587_0 := h1587c.1
                                    have p1587_1 := h1587c.2.1
                                    have p1587_2 := h1587c.2.2.1
                                    have p1587_3 := h1587c.2.2.2
                                    linarith only [hc35, hlam, hphi, ht23, p1587_1, u2ehi2]
                                  · have p1587_0 := h1587c.1
                                    have p1587_1 := h1587c.2.1
                                    have p1587_2 := h1587c.2.2.1
                                    have p1587_3 := h1587c.2.2.2
                                    linarith only [h1535, hlam, p1587_0]
                                  · have p1587_0 := h1587c.1
                                    have p1587_1 := h1587c.2.1
                                    have p1587_2 := h1587c.2.2.1
                                    have p1587_3 := h1587c.2.2.2
                                    linarith only [hlam, p1587_0]
                                · linarith only [h1036, h1586, hlam]
                              · linarith only [h1585, h921, hlam]
                            · linarith only [h1584, h692, hlam]
                          · linarith only [h0, h1583, hlam]
                      · have p1536_0 := h1536c.1
                        have p1536_1 := h1536c.2.1
                        have p1536_2 := h1536c.2.2.1
                        have p1536_3 := h1536c.2.2.2
                        linarith only [h1119, hlam, p1536_1]
                      · have p1536_0 := h1536c.1
                        have p1536_1 := h1536c.2.1
                        have p1536_2 := h1536c.2.2.1
                        have p1536_3 := h1536c.2.2.2
                        linarith only [h1121, hlam, p1536_0]
                      · have p1536_0 := h1536c.1
                        have p1536_1 := h1536c.2.1
                        have p1536_2 := h1536c.2.2.1
                        have p1536_3 := h1536c.2.2.2
                        linarith only [h1122, hlam, p1536_1]
                      · have p1536_0 := h1536c.1
                        have p1536_1 := h1536c.2.1
                        have p1536_2 := h1536c.2.2.1
                        have p1536_3 := h1536c.2.2.2
                        linarith only [hlam, p1536_0]
                    · linarith only [h1129, h1534, h1535, hc24, hlam, hphi, u2ehi2]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1632 | h1632
                    · linarith only [h1120, h1123, h1534, h1632, h692, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · linarith only [h1129, h1632, hc45, hlam, hphi, ht23, ht34, u2ehi2]
            · linarith only [h1122, h1128, h921, hlam]
          · linarith only [h1121, h1127, h692, hlam]
        · linarith only [h1120, h1126, h692, hlam]
      · linarith only [h0, h1117, h1125, hc25, hlam, hphi, u2ehi2]
    · linarith only [h0, h1118, h1124, hlam]
  · linarith only [h0, h1117, h1123, hlam]

end R2N4
