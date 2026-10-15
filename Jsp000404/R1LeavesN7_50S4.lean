import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5426000 in
set_option maxHeartbeats 5426000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h655 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h884 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h999 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1080 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1081 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1082 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1083 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1084 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h2ehi := hb2.1
  have h4bigk := hb4.1
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
  rcases m.htr 0 4 5 (by decide) (by decide) with h1085 | h1085
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1086 | h1086
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1087 | h1087
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1088 | h1088
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1089 | h1089
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1090 | h1090
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1091 | h1091
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1092 | h1092
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1093 | h1093
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1094 | h1094
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1095 | h1095
                      · linarith only [h1080, h1092, h1095, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases h1bigk with h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c | h1097c
                        · have p1097_0 := h1097c.1
                          have p1097_1 := h1097c.2.1
                          have p1097_2 := h1097c.2.2.1
                          have p1097_3 := h1097c.2.2.2
                          linarith only [hlam, p1097_0]
                        · have p1097_0 := h1097c.1
                          have p1097_1 := h1097c.2.1
                          have p1097_2 := h1097c.2.2.1
                          have p1097_3 := h1097c.2.2.2
                          linarith only [h0, hlam, p1097_0]
                        · have p1097_0 := h1097c.1
                          have p1097_1 := h1097c.2.1
                          have p1097_2 := h1097c.2.2.1
                          have p1097_3 := h1097c.2.2.2
                          linarith only [h655, hlam, p1097_0]
                        · have p1097_0 := h1097c.1
                          have p1097_1 := h1097c.2.1
                          have p1097_2 := h1097c.2.2.1
                          have p1097_3 := h1097c.2.2.2
                          linarith only [h884, hlam, p1097_0]
                        · have p1097_0 := h1097c.1
                          have p1097_1 := h1097c.2.1
                          have p1097_2 := h1097c.2.2.1
                          have p1097_3 := h1097c.2.2.2
                          linarith only [h999, hlam, p1097_0]
                        · have p1097_0 := h1097c.1
                          have p1097_1 := h1097c.2.1
                          have p1097_2 := h1097c.2.2.1
                          have p1097_3 := h1097c.2.2.2
                          rcases p1097_3 (m.d 0 1) (by simp) with h1103 | h1103
                          · linarith only [h1103, hlam, p1097_0]
                          · rcases p1097_3 (m.d 1 2) (by simp) with h1105 | h1105
                            · rcases p1097_3 (m.d 1 3) (by simp) with h1106 | h1106
                              · linarith only [h1086, h1106, hlam]
                              · linarith only [h1106, h655, hlam]
                            · linarith only [h1105, hlam, p1097_0]
                        · have p1097_0 := h1097c.1
                          have p1097_1 := h1097c.2.1
                          have p1097_2 := h1097c.2.2.1
                          have p1097_3 := h1097c.2.2.2
                          linarith only [hlam, p1097_0]
                        · have p1097_0 := h1097c.1
                          have p1097_1 := h1097c.2.1
                          have p1097_2 := h1097c.2.2.1
                          have p1097_3 := h1097c.2.2.2
                          linarith only [h655, hc01, hc12, hlam, hphi, p1097_1]
                        · have p1097_0 := h1097c.1
                          have p1097_1 := h1097c.2.1
                          have p1097_2 := h1097c.2.2.1
                          have p1097_3 := h1097c.2.2.2
                          linarith only [h1081, h1094, h1095, h884, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1097_1]
                        · have p1097_0 := h1097c.1
                          have p1097_1 := h1097c.2.1
                          have p1097_2 := h1097c.2.2.1
                          have p1097_3 := h1097c.2.2.2
                          linarith only [h999, hc01, hc12, hlam, hphi, p1097_1]
                        · have p1097_0 := h1097c.1
                          have p1097_1 := h1097c.2.1
                          have p1097_2 := h1097c.2.2.1
                          have p1097_3 := h1097c.2.2.2
                          rcases p1097_3 (m.d 0 1) (by simp) with h1114 | h1114
                          · linarith only [h1114, hlam, p1097_0]
                          · rcases p1097_3 (m.d 1 2) (by simp) with h1116 | h1116
                            · rcases p1097_3 (m.d 1 3) (by simp) with h1117 | h1117
                              · rcases p1097_3 (m.d 1 4) (by simp) with h1118 | h1118
                                · linarith only [h1089, h1118, hlam]
                                · linarith only [h1118, h884, hlam]
                              · linarith only [h1117, hlam, p1097_0]
                            · linarith only [h0, h1116, hlam]
                        · have p1097_0 := h1097c.1
                          have p1097_1 := h1097c.2.1
                          have p1097_2 := h1097c.2.2.1
                          have p1097_3 := h1097c.2.2.2
                          linarith only [h1086, hlam, p1097_0]
                        · have p1097_0 := h1097c.1
                          have p1097_1 := h1097c.2.1
                          have p1097_2 := h1097c.2.2.1
                          have p1097_3 := h1097c.2.2.2
                          linarith only [hlam, p1097_0]
                        · have p1097_0 := h1097c.1
                          have p1097_1 := h1097c.2.1
                          have p1097_2 := h1097c.2.2.1
                          have p1097_3 := h1097c.2.2.2
                          linarith only [h1081, h1094, h1095, h884, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1097_1]
                        · have p1097_0 := h1097c.1
                          have p1097_1 := h1097c.2.1
                          have p1097_2 := h1097c.2.2.1
                          have p1097_3 := h1097c.2.2.2
                          linarith only [h1086, h999, hc01, hc12, hlam, hphi, p1097_1]
                        · have p1097_0 := h1097c.1
                          have p1097_1 := h1097c.2.1
                          have p1097_2 := h1097c.2.2.1
                          have p1097_3 := h1097c.2.2.2
                          rcases p1097_3 (m.d 0 1) (by simp) with h1127 | h1127
                          · linarith only [h1127, hlam, p1097_0]
                          · rcases p1097_3 (m.d 1 2) (by simp) with h1129 | h1129
                            · rcases p1097_3 (m.d 1 3) (by simp) with h1130 | h1130
                              · rcases p1097_3 (m.d 1 4) (by simp) with h1131 | h1131
                                · rcases p1097_3 (m.d 1 5) (by simp) with h1132 | h1132
                                  · linarith only [h1091, h1132, hlam]
                                  · linarith only [h1132, h999, hlam]
                                · linarith only [h1131, hlam, p1097_0]
                              · linarith only [h1130, h655, hlam]
                            · linarith only [h0, h1129, hlam]
                        · have p1097_0 := h1097c.1
                          have p1097_1 := h1097c.2.1
                          have p1097_2 := h1097c.2.2.1
                          have p1097_3 := h1097c.2.2.2
                          linarith only [h1087, hlam, p1097_0]
                        · have p1097_0 := h1097c.1
                          have p1097_1 := h1097c.2.1
                          have p1097_2 := h1097c.2.2.1
                          have p1097_3 := h1097c.2.2.2
                          linarith only [h1089, hlam, p1097_1]
                        · have p1097_0 := h1097c.1
                          have p1097_1 := h1097c.2.1
                          have p1097_2 := h1097c.2.2.1
                          have p1097_3 := h1097c.2.2.2
                          linarith only [hlam, p1097_0]
                        · have p1097_0 := h1097c.1
                          have p1097_1 := h1097c.2.1
                          have p1097_2 := h1097c.2.2.1
                          have p1097_3 := h1097c.2.2.2
                          linarith only [h999, hc01, hc14, hlam, hphi, p1097_1]
                        · have p1097_0 := h1097c.1
                          have p1097_1 := h1097c.2.1
                          have p1097_2 := h1097c.2.2.1
                          have p1097_3 := h1097c.2.2.2
                          rcases p1097_3 (m.d 0 1) (by simp) with h1142 | h1142
                          · linarith only [h1142, hlam, p1097_0]
                          · rcases p1097_3 (m.d 1 2) (by simp) with h1144 | h1144
                            · rcases p1097_3 (m.d 1 3) (by simp) with h1145 | h1145
                              · rcases p1097_3 (m.d 1 4) (by simp) with h1146 | h1146
                                · rcases p1097_3 (m.d 1 5) (by simp) with h1147 | h1147
                                  · rcases h4bigk with h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c
                                    · have p1148_0 := h1148c.1
                                      have p1148_1 := h1148c.2.1
                                      have p1148_2 := h1148c.2.2.1
                                      have p1148_3 := h1148c.2.2.2
                                      linarith only [hlam, p1148_0]
                                    · have p1148_0 := h1148c.1
                                      have p1148_1 := h1148c.2.1
                                      have p1148_2 := h1148c.2.2.1
                                      have p1148_3 := h1148c.2.2.2
                                      linarith only [h884, hlam, p1148_1]
                                    · have p1148_0 := h1148c.1
                                      have p1148_1 := h1148c.2.1
                                      have p1148_2 := h1148c.2.2.1
                                      have p1148_3 := h1148c.2.2.2
                                      linarith only [h1083, h1094, h1095, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1148_1]
                                    · have p1148_0 := h1148c.1
                                      have p1148_1 := h1148c.2.1
                                      have p1148_2 := h1148c.2.2.1
                                      have p1148_3 := h1148c.2.2.2
                                      rcases p1148_3 (m.d 0 4) (by simp) with h1152 | h1152
                                      · rcases p1148_3 (m.d 1 4) (by simp) with h1153 | h1153
                                        · rcases p1148_3 (m.d 2 4) (by simp) with h1154 | h1154
                                          · linarith only [h1081, h1154, hlam]
                                          · linarith only [h1092, h1154, hlam]
                                        · linarith only [h1089, h1153, hlam]
                                      · linarith only [h1083, h1152, hlam]
                                    · have p1148_0 := h1148c.1
                                      have p1148_1 := h1148c.2.1
                                      have p1148_2 := h1148c.2.2.1
                                      have p1148_3 := h1148c.2.2.2
                                      rcases p1148_3 (m.d 0 4) (by simp) with h1159 | h1159
                                      · rcases p1148_3 (m.d 1 4) (by simp) with h1160 | h1160
                                        · rcases p1148_3 (m.d 2 4) (by simp) with h1161 | h1161
                                          · linarith only [h1081, h1161, hlam]
                                          · linarith only [h1094, h1161, hlam]
                                        · linarith only [h1091, h1160, hlam]
                                      · linarith only [h1159, hlam, p1148_0]
                                    · have p1148_0 := h1148c.1
                                      have p1148_1 := h1148c.2.1
                                      have p1148_2 := h1148c.2.2.1
                                      have p1148_3 := h1148c.2.2.2
                                      linarith only [h1081, h1086, h1089, h1094, h1095, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1148_1]
                                    · have p1148_0 := h1148c.1
                                      have p1148_1 := h1148c.2.1
                                      have p1148_2 := h1148c.2.2.1
                                      have p1148_3 := h1148c.2.2.2
                                      linarith only [hlam, p1148_0]
                                    · have p1148_0 := h1148c.1
                                      have p1148_1 := h1148c.2.1
                                      have p1148_2 := h1148c.2.2.1
                                      have p1148_3 := h1148c.2.2.2
                                      linarith only [h1086, h1089, h1094, h1095, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1148_1]
                                    · have p1148_0 := h1148c.1
                                      have p1148_1 := h1148c.2.1
                                      have p1148_2 := h1148c.2.2.1
                                      have p1148_3 := h1148c.2.2.2
                                      rcases p1148_3 (m.d 0 4) (by simp) with h1169 | h1169
                                      · linarith only [h1169, h884, hlam]
                                      · linarith only [h1083, h1169, hlam]
                                    · have p1148_0 := h1148c.1
                                      have p1148_1 := h1148c.2.1
                                      have p1148_2 := h1148c.2.2.1
                                      have p1148_3 := h1148c.2.2.2
                                      rcases p1148_3 (m.d 0 4) (by simp) with h1172 | h1172
                                      · linarith only [h1172, h884, hlam]
                                      · linarith only [h1085, h1172, hlam]
                                    · have p1148_0 := h1148c.1
                                      have p1148_1 := h1148c.2.1
                                      have p1148_2 := h1148c.2.2.1
                                      have p1148_3 := h1148c.2.2.2
                                      linarith only [h1081, hlam, p1148_0]
                                    · have p1148_0 := h1148c.1
                                      have p1148_1 := h1148c.2.1
                                      have p1148_2 := h1148c.2.2.1
                                      have p1148_3 := h1148c.2.2.2
                                      linarith only [h1087, hlam, p1148_0]
                                    · have p1148_0 := h1148c.1
                                      have p1148_1 := h1148c.2.1
                                      have p1148_2 := h1148c.2.2.1
                                      have p1148_3 := h1148c.2.2.2
                                      linarith only [hlam, p1148_0]
                                    · have p1148_0 := h1148c.1
                                      have p1148_1 := h1148c.2.1
                                      have p1148_2 := h1148c.2.2.1
                                      have p1148_3 := h1148c.2.2.2
                                      rcases p1148_3 (m.d 0 4) (by simp) with h1178 | h1178
                                      · rcases p1148_3 (m.d 1 4) (by simp) with h1179 | h1179
                                        · rcases p1148_3 (m.d 2 4) (by simp) with h1180 | h1180
                                          · rcases p1148_3 (m.d 3 4) (by simp) with h1181 | h1181
                                            · linarith only [h1092, h1181, hlam]
                                            · rcases p1148_3 (m.d 4 5) (by simp) with h1183 | h1183
                                              · linarith only [h1094, h1183, hlam]
                                              · linarith only [h1095, h1183, hlam]
                                          · linarith only [h1092, h1180, hlam]
                                        · linarith only [h1089, h1179, hlam]
                                      · linarith only [h1083, h1178, hlam]
                                    · have p1148_0 := h1148c.1
                                      have p1148_1 := h1148c.2.1
                                      have p1148_2 := h1148c.2.2.1
                                      have p1148_3 := h1148c.2.2.2
                                      linarith only [h0, h1081, h1095, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1148_1]
                                    · have p1148_0 := h1148c.1
                                      have p1148_1 := h1148c.2.1
                                      have p1148_2 := h1148c.2.2.1
                                      have p1148_3 := h1148c.2.2.2
                                      linarith only [h1083, hlam, p1148_0]
                                    · have p1148_0 := h1148c.1
                                      have p1148_1 := h1148c.2.1
                                      have p1148_2 := h1148c.2.2.1
                                      have p1148_3 := h1148c.2.2.2
                                      linarith only [h1089, hlam, p1148_0]
                                    · have p1148_0 := h1148c.1
                                      have p1148_1 := h1148c.2.1
                                      have p1148_2 := h1148c.2.2.1
                                      have p1148_3 := h1148c.2.2.2
                                      linarith only [h1092, hlam, p1148_0]
                                    · have p1148_0 := h1148c.1
                                      have p1148_1 := h1148c.2.1
                                      have p1148_2 := h1148c.2.2.1
                                      have p1148_3 := h1148c.2.2.2
                                      linarith only [hlam, p1148_0]
                                    · have p1148_0 := h1148c.1
                                      have p1148_1 := h1148c.2.1
                                      have p1148_2 := h1148c.2.2.1
                                      have p1148_3 := h1148c.2.2.2
                                      linarith only [h1095, hlam, p1148_0]
                                    · have p1148_0 := h1148c.1
                                      have p1148_1 := h1148c.2.1
                                      have p1148_2 := h1148c.2.2.1
                                      have p1148_3 := h1148c.2.2.2
                                      linarith only [h1085, hlam, p1148_0]
                                    · have p1148_0 := h1148c.1
                                      have p1148_1 := h1148c.2.1
                                      have p1148_2 := h1148c.2.2.1
                                      have p1148_3 := h1148c.2.2.2
                                      linarith only [h1091, hlam, p1148_0]
                                    · have p1148_0 := h1148c.1
                                      have p1148_1 := h1148c.2.1
                                      have p1148_2 := h1148c.2.2.1
                                      have p1148_3 := h1148c.2.2.2
                                      linarith only [h1094, hlam, p1148_0]
                                    · have p1148_0 := h1148c.1
                                      have p1148_1 := h1148c.2.1
                                      have p1148_2 := h1148c.2.2.1
                                      have p1148_3 := h1148c.2.2.2
                                      linarith only [h0, h1080, h1092, h1094, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1148_1]
                                    · have p1148_0 := h1148c.1
                                      have p1148_1 := h1148c.2.1
                                      have p1148_2 := h1148c.2.2.1
                                      have p1148_3 := h1148c.2.2.2
                                      linarith only [hlam, p1148_0]
                                  · linarith only [h1147, hlam, p1097_0]
                                · linarith only [h1146, h884, hlam]
                              · linarith only [h1145, h655, hlam]
                            · linarith only [h0, h1144, hlam]
                        · have p1097_0 := h1097c.1
                          have p1097_1 := h1097c.2.1
                          have p1097_2 := h1097c.2.2.1
                          have p1097_3 := h1097c.2.2.2
                          linarith only [h1088, hlam, p1097_0]
                        · have p1097_0 := h1097c.1
                          have p1097_1 := h1097c.2.1
                          have p1097_2 := h1097c.2.2.1
                          have p1097_3 := h1097c.2.2.2
                          linarith only [h1090, hlam, p1097_0]
                        · have p1097_0 := h1097c.1
                          have p1097_1 := h1097c.2.1
                          have p1097_2 := h1097c.2.2.1
                          have p1097_3 := h1097c.2.2.2
                          linarith only [h1091, hlam, p1097_0]
                        · have p1097_0 := h1097c.1
                          have p1097_1 := h1097c.2.1
                          have p1097_2 := h1097c.2.2.1
                          have p1097_3 := h1097c.2.2.2
                          linarith only [hlam, p1097_0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1208 | h1208
                      · linarith only [h1094, h1208, hc34, hlam, hphi, ht23, u2ehi3]
                      · rcases h1bigk with h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c
                        · have p1210_0 := h1210c.1
                          have p1210_1 := h1210c.2.1
                          have p1210_2 := h1210c.2.2.1
                          have p1210_3 := h1210c.2.2.2
                          linarith only [hlam, p1210_0]
                        · have p1210_0 := h1210c.1
                          have p1210_1 := h1210c.2.1
                          have p1210_2 := h1210c.2.2.1
                          have p1210_3 := h1210c.2.2.2
                          linarith only [h0, hlam, p1210_0]
                        · have p1210_0 := h1210c.1
                          have p1210_1 := h1210c.2.1
                          have p1210_2 := h1210c.2.2.1
                          have p1210_3 := h1210c.2.2.2
                          linarith only [h655, hlam, p1210_0]
                        · have p1210_0 := h1210c.1
                          have p1210_1 := h1210c.2.1
                          have p1210_2 := h1210c.2.2.1
                          have p1210_3 := h1210c.2.2.2
                          linarith only [h884, hlam, p1210_0]
                        · have p1210_0 := h1210c.1
                          have p1210_1 := h1210c.2.1
                          have p1210_2 := h1210c.2.2.1
                          have p1210_3 := h1210c.2.2.2
                          linarith only [h999, hlam, p1210_0]
                        · have p1210_0 := h1210c.1
                          have p1210_1 := h1210c.2.1
                          have p1210_2 := h1210c.2.2.1
                          have p1210_3 := h1210c.2.2.2
                          rcases p1210_3 (m.d 0 1) (by simp) with h1216 | h1216
                          · linarith only [h1216, hlam, p1210_0]
                          · rcases p1210_3 (m.d 1 2) (by simp) with h1218 | h1218
                            · rcases p1210_3 (m.d 1 3) (by simp) with h1219 | h1219
                              · linarith only [h1086, h1219, hlam]
                              · linarith only [h1219, h655, hlam]
                            · linarith only [h1218, hlam, p1210_0]
                        · have p1210_0 := h1210c.1
                          have p1210_1 := h1210c.2.1
                          have p1210_2 := h1210c.2.2.1
                          have p1210_3 := h1210c.2.2.2
                          linarith only [hlam, p1210_0]
                        · have p1210_0 := h1210c.1
                          have p1210_1 := h1210c.2.1
                          have p1210_2 := h1210c.2.2.1
                          have p1210_3 := h1210c.2.2.2
                          linarith only [h655, hc01, hc12, hlam, hphi, p1210_1]
                        · have p1210_0 := h1210c.1
                          have p1210_1 := h1210c.2.1
                          have p1210_2 := h1210c.2.2.1
                          have p1210_3 := h1210c.2.2.2
                          linarith only [h1085, h1094, h884, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1210_1, u2ehi3]
                        · have p1210_0 := h1210c.1
                          have p1210_1 := h1210c.2.1
                          have p1210_2 := h1210c.2.2.1
                          have p1210_3 := h1210c.2.2.2
                          linarith only [h999, hc01, hc12, hlam, hphi, p1210_1]
                        · have p1210_0 := h1210c.1
                          have p1210_1 := h1210c.2.1
                          have p1210_2 := h1210c.2.2.1
                          have p1210_3 := h1210c.2.2.2
                          rcases p1210_3 (m.d 0 1) (by simp) with h1227 | h1227
                          · linarith only [h1227, hlam, p1210_0]
                          · rcases p1210_3 (m.d 1 2) (by simp) with h1229 | h1229
                            · rcases p1210_3 (m.d 1 3) (by simp) with h1230 | h1230
                              · rcases p1210_3 (m.d 1 4) (by simp) with h1231 | h1231
                                · linarith only [h1089, h1231, hlam]
                                · linarith only [h1231, h884, hlam]
                              · linarith only [h1230, hlam, p1210_0]
                            · linarith only [h0, h1229, hlam]
                        · have p1210_0 := h1210c.1
                          have p1210_1 := h1210c.2.1
                          have p1210_2 := h1210c.2.2.1
                          have p1210_3 := h1210c.2.2.2
                          linarith only [h1086, hlam, p1210_0]
                        · have p1210_0 := h1210c.1
                          have p1210_1 := h1210c.2.1
                          have p1210_2 := h1210c.2.2.1
                          have p1210_3 := h1210c.2.2.2
                          linarith only [hlam, p1210_0]
                        · have p1210_0 := h1210c.1
                          have p1210_1 := h1210c.2.1
                          have p1210_2 := h1210c.2.2.1
                          have p1210_3 := h1210c.2.2.2
                          linarith only [h1085, h1094, h884, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1210_1, u2ehi3]
                        · have p1210_0 := h1210c.1
                          have p1210_1 := h1210c.2.1
                          have p1210_2 := h1210c.2.2.1
                          have p1210_3 := h1210c.2.2.2
                          linarith only [h1085, h1086, h1094, h999, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1210_1, u2ehi3]
                        · have p1210_0 := h1210c.1
                          have p1210_1 := h1210c.2.1
                          have p1210_2 := h1210c.2.2.1
                          have p1210_3 := h1210c.2.2.2
                          rcases p1210_3 (m.d 0 1) (by simp) with h1240 | h1240
                          · linarith only [h1240, hlam, p1210_0]
                          · rcases p1210_3 (m.d 1 2) (by simp) with h1242 | h1242
                            · rcases p1210_3 (m.d 1 3) (by simp) with h1243 | h1243
                              · rcases p1210_3 (m.d 1 4) (by simp) with h1244 | h1244
                                · rcases p1210_3 (m.d 1 5) (by simp) with h1245 | h1245
                                  · linarith only [h1091, h1245, hlam]
                                  · linarith only [h1245, h999, hlam]
                                · linarith only [h1244, hlam, p1210_0]
                              · linarith only [h1243, h655, hlam]
                            · linarith only [h0, h1242, hlam]
                        · have p1210_0 := h1210c.1
                          have p1210_1 := h1210c.2.1
                          have p1210_2 := h1210c.2.2.1
                          have p1210_3 := h1210c.2.2.2
                          linarith only [h1087, hlam, p1210_0]
                        · have p1210_0 := h1210c.1
                          have p1210_1 := h1210c.2.1
                          have p1210_2 := h1210c.2.2.1
                          have p1210_3 := h1210c.2.2.2
                          linarith only [h1089, hlam, p1210_1]
                        · have p1210_0 := h1210c.1
                          have p1210_1 := h1210c.2.1
                          have p1210_2 := h1210c.2.2.1
                          have p1210_3 := h1210c.2.2.2
                          linarith only [hlam, p1210_0]
                        · have p1210_0 := h1210c.1
                          have p1210_1 := h1210c.2.1
                          have p1210_2 := h1210c.2.2.1
                          have p1210_3 := h1210c.2.2.2
                          linarith only [h1085, h1094, h999, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1210_1, u2ehi3]
                        · have p1210_0 := h1210c.1
                          have p1210_1 := h1210c.2.1
                          have p1210_2 := h1210c.2.2.1
                          have p1210_3 := h1210c.2.2.2
                          rcases p1210_3 (m.d 0 1) (by simp) with h1255 | h1255
                          · linarith only [h1255, hlam, p1210_0]
                          · rcases p1210_3 (m.d 1 2) (by simp) with h1257 | h1257
                            · rcases p1210_3 (m.d 1 3) (by simp) with h1258 | h1258
                              · rcases p1210_3 (m.d 1 4) (by simp) with h1259 | h1259
                                · rcases p1210_3 (m.d 1 5) (by simp) with h1260 | h1260
                                  · rcases h4bigk with h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c | h1261c
                                    · have p1261_0 := h1261c.1
                                      have p1261_1 := h1261c.2.1
                                      have p1261_2 := h1261c.2.2.1
                                      have p1261_3 := h1261c.2.2.2
                                      linarith only [hlam, p1261_0]
                                    · have p1261_0 := h1261c.1
                                      have p1261_1 := h1261c.2.1
                                      have p1261_2 := h1261c.2.2.1
                                      have p1261_3 := h1261c.2.2.2
                                      linarith only [h884, hlam, p1261_1]
                                    · have p1261_0 := h1261c.1
                                      have p1261_1 := h1261c.2.1
                                      have p1261_2 := h1261c.2.2.1
                                      have p1261_3 := h1261c.2.2.2
                                      rcases p1261_3 (m.d 0 4) (by simp) with h1264 | h1264
                                      · rcases p1261_3 (m.d 1 4) (by simp) with h1265 | h1265
                                        · rcases p1261_3 (m.d 2 4) (by simp) with h1266 | h1266
                                          · linarith only [h1081, h1266, hlam]
                                          · rcases p1261_3 (m.d 3 4) (by simp) with h1268 | h1268
                                            · linarith only [h1083, h1268, hlam]
                                            · rcases p1261_3 (m.d 4 5) (by simp) with h1270 | h1270
                                              · linarith only [h1085, h1270, hlam]
                                              · linarith only [h1094, h1270, hlam]
                                        · linarith only [h1087, h1265, hlam]
                                      · linarith only [h1081, h1264, hlam]
                                    · have p1261_0 := h1261c.1
                                      have p1261_1 := h1261c.2.1
                                      have p1261_2 := h1261c.2.2.1
                                      have p1261_3 := h1261c.2.2.2
                                      rcases p1261_3 (m.d 0 4) (by simp) with h1275 | h1275
                                      · rcases p1261_3 (m.d 1 4) (by simp) with h1276 | h1276
                                        · rcases p1261_3 (m.d 2 4) (by simp) with h1277 | h1277
                                          · linarith only [h1081, h1277, hlam]
                                          · linarith only [h1092, h1277, hlam]
                                        · linarith only [h1089, h1276, hlam]
                                      · linarith only [h1083, h1275, hlam]
                                    · have p1261_0 := h1261c.1
                                      have p1261_1 := h1261c.2.1
                                      have p1261_2 := h1261c.2.2.1
                                      have p1261_3 := h1261c.2.2.2
                                      linarith only [h1094, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1261_1, u2ehi3]
                                    · have p1261_0 := h1261c.1
                                      have p1261_1 := h1261c.2.1
                                      have p1261_2 := h1261c.2.2.1
                                      have p1261_3 := h1261c.2.2.2
                                      linarith only [h1085, h1086, h1089, h1094, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1261_1, u2ehi3]
                                    · have p1261_0 := h1261c.1
                                      have p1261_1 := h1261c.2.1
                                      have p1261_2 := h1261c.2.2.1
                                      have p1261_3 := h1261c.2.2.2
                                      linarith only [hlam, p1261_0]
                                    · have p1261_0 := h1261c.1
                                      have p1261_1 := h1261c.2.1
                                      have p1261_2 := h1261c.2.2.1
                                      have p1261_3 := h1261c.2.2.2
                                      rcases p1261_3 (m.d 0 4) (by simp) with h1285 | h1285
                                      · linarith only [h1285, h884, hlam]
                                      · linarith only [h1081, h1285, hlam]
                                    · have p1261_0 := h1261c.1
                                      have p1261_1 := h1261c.2.1
                                      have p1261_2 := h1261c.2.2.1
                                      have p1261_3 := h1261c.2.2.2
                                      rcases p1261_3 (m.d 0 4) (by simp) with h1288 | h1288
                                      · linarith only [h1288, h884, hlam]
                                      · linarith only [h1083, h1288, hlam]
                                    · have p1261_0 := h1261c.1
                                      have p1261_1 := h1261c.2.1
                                      have p1261_2 := h1261c.2.2.1
                                      have p1261_3 := h1261c.2.2.2
                                      linarith only [h1086, h1089, h1094, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1261_1, u2ehi3]
                                    · have p1261_0 := h1261c.1
                                      have p1261_1 := h1261c.2.1
                                      have p1261_2 := h1261c.2.2.1
                                      have p1261_3 := h1261c.2.2.2
                                      linarith only [h1081, hlam, p1261_0]
                                    · have p1261_0 := h1261c.1
                                      have p1261_1 := h1261c.2.1
                                      have p1261_2 := h1261c.2.2.1
                                      have p1261_3 := h1261c.2.2.2
                                      linarith only [h1087, hlam, p1261_0]
                                    · have p1261_0 := h1261c.1
                                      have p1261_1 := h1261c.2.1
                                      have p1261_2 := h1261c.2.2.1
                                      have p1261_3 := h1261c.2.2.2
                                      linarith only [hlam, p1261_0]
                                    · have p1261_0 := h1261c.1
                                      have p1261_1 := h1261c.2.1
                                      have p1261_2 := h1261c.2.2.1
                                      have p1261_3 := h1261c.2.2.2
                                      linarith only [h1085, h1094, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p1261_1]
                                    · have p1261_0 := h1261c.1
                                      have p1261_1 := h1261c.2.1
                                      have p1261_2 := h1261c.2.2.1
                                      have p1261_3 := h1261c.2.2.2
                                      linarith only [h1094, hlam, p1261_0]
                                    · have p1261_0 := h1261c.1
                                      have p1261_1 := h1261c.2.1
                                      have p1261_2 := h1261c.2.2.1
                                      have p1261_3 := h1261c.2.2.2
                                      linarith only [h1083, hlam, p1261_0]
                                    · have p1261_0 := h1261c.1
                                      have p1261_1 := h1261c.2.1
                                      have p1261_2 := h1261c.2.2.1
                                      have p1261_3 := h1261c.2.2.2
                                      linarith only [h1089, hlam, p1261_0]
                                    · have p1261_0 := h1261c.1
                                      have p1261_1 := h1261c.2.1
                                      have p1261_2 := h1261c.2.2.1
                                      have p1261_3 := h1261c.2.2.2
                                      linarith only [h1092, hlam, p1261_0]
                                    · have p1261_0 := h1261c.1
                                      have p1261_1 := h1261c.2.1
                                      have p1261_2 := h1261c.2.2.1
                                      have p1261_3 := h1261c.2.2.2
                                      linarith only [hlam, p1261_0]
                                    · have p1261_0 := h1261c.1
                                      have p1261_1 := h1261c.2.1
                                      have p1261_2 := h1261c.2.2.1
                                      have p1261_3 := h1261c.2.2.2
                                      linarith only [h1208, hlam, p1261_0]
                                    · have p1261_0 := h1261c.1
                                      have p1261_1 := h1261c.2.1
                                      have p1261_2 := h1261c.2.2.1
                                      have p1261_3 := h1261c.2.2.2
                                      linarith only [h1085, hlam, p1261_0]
                                    · have p1261_0 := h1261c.1
                                      have p1261_1 := h1261c.2.1
                                      have p1261_2 := h1261c.2.2.1
                                      have p1261_3 := h1261c.2.2.2
                                      linarith only [h1091, hlam, p1261_0]
                                    · have p1261_0 := h1261c.1
                                      have p1261_1 := h1261c.2.1
                                      have p1261_2 := h1261c.2.2.1
                                      have p1261_3 := h1261c.2.2.2
                                      linarith only [h1085, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1261_1, u2ehi3]
                                    · have p1261_0 := h1261c.1
                                      have p1261_1 := h1261c.2.1
                                      have p1261_2 := h1261c.2.2.1
                                      have p1261_3 := h1261c.2.2.2
                                      rcases p1261_3 (m.d 0 4) (by simp) with h1305 | h1305
                                      · rcases p1261_3 (m.d 1 4) (by simp) with h1306 | h1306
                                        · rcases p1261_3 (m.d 2 4) (by simp) with h1307 | h1307
                                          · linarith only [h1094, h1307, hlam]
                                          · linarith only [h1092, h1307, hlam]
                                        · linarith only [h1089, h1306, hlam]
                                      · linarith only [h1083, h1305, hlam]
                                    · have p1261_0 := h1261c.1
                                      have p1261_1 := h1261c.2.1
                                      have p1261_2 := h1261c.2.2.1
                                      have p1261_3 := h1261c.2.2.2
                                      linarith only [hlam, p1261_0]
                                  · linarith only [h1260, hlam, p1210_0]
                                · linarith only [h1259, h884, hlam]
                              · linarith only [h1258, h655, hlam]
                            · linarith only [h0, h1257, hlam]
                        · have p1210_0 := h1210c.1
                          have p1210_1 := h1210c.2.1
                          have p1210_2 := h1210c.2.2.1
                          have p1210_3 := h1210c.2.2.2
                          linarith only [h1088, hlam, p1210_0]
                        · have p1210_0 := h1210c.1
                          have p1210_1 := h1210c.2.1
                          have p1210_2 := h1210c.2.2.1
                          have p1210_3 := h1210c.2.2.2
                          linarith only [h1090, hlam, p1210_0]
                        · have p1210_0 := h1210c.1
                          have p1210_1 := h1210c.2.1
                          have p1210_2 := h1210c.2.2.1
                          have p1210_3 := h1210c.2.2.2
                          linarith only [h1091, hlam, p1210_0]
                        · have p1210_0 := h1210c.1
                          have p1210_1 := h1210c.2.1
                          have p1210_2 := h1210c.2.2.1
                          have p1210_3 := h1210c.2.2.2
                          linarith only [hlam, p1210_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1321 | h1321
                    · linarith only [h0, h1080, h1084, h1092, h1093, h1321, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1323 | h1323
                      · linarith only [h0, h1080, h1084, h1092, h1093, h1321, h1323, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                      · rcases h1bigk with h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c
                        · have p1325_0 := h1325c.1
                          have p1325_1 := h1325c.2.1
                          have p1325_2 := h1325c.2.2.1
                          have p1325_3 := h1325c.2.2.2
                          linarith only [hlam, p1325_0]
                        · have p1325_0 := h1325c.1
                          have p1325_1 := h1325c.2.1
                          have p1325_2 := h1325c.2.2.1
                          have p1325_3 := h1325c.2.2.2
                          linarith only [h0, hlam, p1325_0]
                        · have p1325_0 := h1325c.1
                          have p1325_1 := h1325c.2.1
                          have p1325_2 := h1325c.2.2.1
                          have p1325_3 := h1325c.2.2.2
                          linarith only [h655, hlam, p1325_0]
                        · have p1325_0 := h1325c.1
                          have p1325_1 := h1325c.2.1
                          have p1325_2 := h1325c.2.2.1
                          have p1325_3 := h1325c.2.2.2
                          linarith only [h884, hlam, p1325_0]
                        · have p1325_0 := h1325c.1
                          have p1325_1 := h1325c.2.1
                          have p1325_2 := h1325c.2.2.1
                          have p1325_3 := h1325c.2.2.2
                          linarith only [h999, hlam, p1325_0]
                        · have p1325_0 := h1325c.1
                          have p1325_1 := h1325c.2.1
                          have p1325_2 := h1325c.2.2.1
                          have p1325_3 := h1325c.2.2.2
                          rcases p1325_3 (m.d 0 1) (by simp) with h1331 | h1331
                          · linarith only [h1331, hlam, p1325_0]
                          · rcases p1325_3 (m.d 1 2) (by simp) with h1333 | h1333
                            · rcases p1325_3 (m.d 1 3) (by simp) with h1334 | h1334
                              · linarith only [h1086, h1334, hlam]
                              · linarith only [h1334, h655, hlam]
                            · linarith only [h1333, hlam, p1325_0]
                        · have p1325_0 := h1325c.1
                          have p1325_1 := h1325c.2.1
                          have p1325_2 := h1325c.2.2.1
                          have p1325_3 := h1325c.2.2.2
                          linarith only [hlam, p1325_0]
                        · have p1325_0 := h1325c.1
                          have p1325_1 := h1325c.2.1
                          have p1325_2 := h1325c.2.2.1
                          have p1325_3 := h1325c.2.2.2
                          linarith only [h1085, h1089, h1093, h1323, h884, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1325_1]
                        · have p1325_0 := h1325c.1
                          have p1325_1 := h1325c.2.1
                          have p1325_2 := h1325c.2.2.1
                          have p1325_3 := h1325c.2.2.2
                          linarith only [h1085, h1092, h1093, h1323, h884, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1325_1, u2ehi3]
                        · have p1325_0 := h1325c.1
                          have p1325_1 := h1325c.2.1
                          have p1325_2 := h1325c.2.2.1
                          have p1325_3 := h1325c.2.2.2
                          linarith only [h1085, h1092, h1093, h1323, h999, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1325_1, u2ehi3]
                        · have p1325_0 := h1325c.1
                          have p1325_1 := h1325c.2.1
                          have p1325_2 := h1325c.2.2.1
                          have p1325_3 := h1325c.2.2.2
                          rcases p1325_3 (m.d 0 1) (by simp) with h1342 | h1342
                          · linarith only [h1342, hlam, p1325_0]
                          · rcases p1325_3 (m.d 1 2) (by simp) with h1344 | h1344
                            · rcases p1325_3 (m.d 1 3) (by simp) with h1345 | h1345
                              · rcases p1325_3 (m.d 1 4) (by simp) with h1346 | h1346
                                · linarith only [h1089, h1346, hlam]
                                · linarith only [h1346, h884, hlam]
                              · linarith only [h1345, hlam, p1325_0]
                            · linarith only [h0, h1344, hlam]
                        · have p1325_0 := h1325c.1
                          have p1325_1 := h1325c.2.1
                          have p1325_2 := h1325c.2.2.1
                          have p1325_3 := h1325c.2.2.2
                          linarith only [h1086, hlam, p1325_0]
                        · have p1325_0 := h1325c.1
                          have p1325_1 := h1325c.2.1
                          have p1325_2 := h1325c.2.2.1
                          have p1325_3 := h1325c.2.2.2
                          linarith only [hlam, p1325_0]
                        · have p1325_0 := h1325c.1
                          have p1325_1 := h1325c.2.1
                          have p1325_2 := h1325c.2.2.1
                          have p1325_3 := h1325c.2.2.2
                          linarith only [h1085, h1092, h1093, h1323, h884, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1325_1, u2ehi3]
                        · have p1325_0 := h1325c.1
                          have p1325_1 := h1325c.2.1
                          have p1325_2 := h1325c.2.2.1
                          have p1325_3 := h1325c.2.2.2
                          linarith only [h1085, h1086, h1092, h1093, h1323, h999, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1325_1, u2ehi3]
                        · have p1325_0 := h1325c.1
                          have p1325_1 := h1325c.2.1
                          have p1325_2 := h1325c.2.2.1
                          have p1325_3 := h1325c.2.2.2
                          rcases p1325_3 (m.d 0 1) (by simp) with h1355 | h1355
                          · linarith only [h1355, hlam, p1325_0]
                          · rcases p1325_3 (m.d 1 2) (by simp) with h1357 | h1357
                            · rcases p1325_3 (m.d 1 3) (by simp) with h1358 | h1358
                              · rcases p1325_3 (m.d 1 4) (by simp) with h1359 | h1359
                                · rcases p1325_3 (m.d 1 5) (by simp) with h1360 | h1360
                                  · linarith only [h1091, h1360, hlam]
                                  · linarith only [h1360, h999, hlam]
                                · linarith only [h1359, hlam, p1325_0]
                              · linarith only [h1358, h655, hlam]
                            · linarith only [h0, h1357, hlam]
                        · have p1325_0 := h1325c.1
                          have p1325_1 := h1325c.2.1
                          have p1325_2 := h1325c.2.2.1
                          have p1325_3 := h1325c.2.2.2
                          linarith only [h1087, hlam, p1325_0]
                        · have p1325_0 := h1325c.1
                          have p1325_1 := h1325c.2.1
                          have p1325_2 := h1325c.2.2.1
                          have p1325_3 := h1325c.2.2.2
                          linarith only [h1089, hlam, p1325_1]
                        · have p1325_0 := h1325c.1
                          have p1325_1 := h1325c.2.1
                          have p1325_2 := h1325c.2.2.1
                          have p1325_3 := h1325c.2.2.2
                          linarith only [hlam, p1325_0]
                        · have p1325_0 := h1325c.1
                          have p1325_1 := h1325c.2.1
                          have p1325_2 := h1325c.2.2.1
                          have p1325_3 := h1325c.2.2.2
                          linarith only [h1085, h1092, h1093, h1323, h999, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1325_1, u2ehi3]
                        · have p1325_0 := h1325c.1
                          have p1325_1 := h1325c.2.1
                          have p1325_2 := h1325c.2.2.1
                          have p1325_3 := h1325c.2.2.2
                          rcases p1325_3 (m.d 0 1) (by simp) with h1370 | h1370
                          · linarith only [h1370, hlam, p1325_0]
                          · rcases p1325_3 (m.d 1 2) (by simp) with h1372 | h1372
                            · rcases p1325_3 (m.d 1 3) (by simp) with h1373 | h1373
                              · rcases p1325_3 (m.d 1 4) (by simp) with h1374 | h1374
                                · rcases p1325_3 (m.d 1 5) (by simp) with h1375 | h1375
                                  · rcases h4bigk with h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c | h1376c
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [hlam, p1376_0]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h884, hlam, p1376_1]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      rcases p1376_3 (m.d 0 4) (by simp) with h1379 | h1379
                                      · rcases p1376_3 (m.d 1 4) (by simp) with h1380 | h1380
                                        · rcases p1376_3 (m.d 2 4) (by simp) with h1381 | h1381
                                          · linarith only [h1081, h1381, hlam]
                                          · rcases p1376_3 (m.d 3 4) (by simp) with h1383 | h1383
                                            · linarith only [h1083, h1383, hlam]
                                            · rcases p1376_3 (m.d 4 5) (by simp) with h1385 | h1385
                                              · linarith only [h1085, h1385, hlam]
                                              · linarith only [h1321, h1385, hlam]
                                        · linarith only [h1087, h1380, hlam]
                                      · linarith only [h1081, h1379, hlam]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h1085, h1092, h1093, h1323, hlam, p1376_2]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h1092, h1093, h1323, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1376_1, u2ehi3]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h1085, h1086, h1089, h1092, h1093, h1323, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1376_1, u2ehi3]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [hlam, p1376_0]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      rcases p1376_3 (m.d 0 4) (by simp) with h1394 | h1394
                                      · linarith only [h1394, h884, hlam]
                                      · linarith only [h1081, h1394, hlam]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h1085, h1092, h1093, h1323, h884, hlam, p1376_2]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h1092, h1093, h1323, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1376_1, u2ehi3]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h1081, hlam, p1376_0]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h1087, hlam, p1376_0]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [hlam, p1376_0]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h1085, h1092, h1093, h1323, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p1376_1]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h1321, hlam, p1376_0]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h1083, hlam, p1376_0]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h1089, hlam, p1376_0]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h1092, hlam, p1376_0]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [hlam, p1376_0]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h1323, hlam, p1376_0]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h1085, hlam, p1376_0]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h1091, hlam, p1376_0]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [h1085, h1086, h1089, h884, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1376_1, u2ehi3]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      rcases p1376_3 (m.d 0 4) (by simp) with h1412 | h1412
                                      · rcases p1376_3 (m.d 1 4) (by simp) with h1413 | h1413
                                        · rcases p1376_3 (m.d 2 4) (by simp) with h1414 | h1414
                                          · linarith only [h1321, h1414, hlam]
                                          · linarith only [h1092, h1414, hlam]
                                        · linarith only [h1089, h1413, hlam]
                                      · linarith only [h1083, h1412, hlam]
                                    · have p1376_0 := h1376c.1
                                      have p1376_1 := h1376c.2.1
                                      have p1376_2 := h1376c.2.2.1
                                      have p1376_3 := h1376c.2.2.2
                                      linarith only [hlam, p1376_0]
                                  · linarith only [h1375, hlam, p1325_0]
                                · linarith only [h1374, h884, hlam]
                              · linarith only [h1373, h655, hlam]
                            · linarith only [h0, h1372, hlam]
                        · have p1325_0 := h1325c.1
                          have p1325_1 := h1325c.2.1
                          have p1325_2 := h1325c.2.2.1
                          have p1325_3 := h1325c.2.2.2
                          linarith only [h1088, hlam, p1325_0]
                        · have p1325_0 := h1325c.1
                          have p1325_1 := h1325c.2.1
                          have p1325_2 := h1325c.2.2.1
                          have p1325_3 := h1325c.2.2.2
                          linarith only [h1090, hlam, p1325_0]
                        · have p1325_0 := h1325c.1
                          have p1325_1 := h1325c.2.1
                          have p1325_2 := h1325c.2.2.1
                          have p1325_3 := h1325c.2.2.2
                          linarith only [h1091, hlam, p1325_0]
                        · have p1325_0 := h1325c.1
                          have p1325_1 := h1325c.2.1
                          have p1325_2 := h1325c.2.2.1
                          have p1325_3 := h1325c.2.2.2
                          linarith only [hlam, p1325_0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1428 | h1428
                  · linarith only [h0, h1080, h1083, h1092, h1428, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1430 | h1430
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1431 | h1431
                      · rcases h1bigk with h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c | h1432c
                        · have p1432_0 := h1432c.1
                          have p1432_1 := h1432c.2.1
                          have p1432_2 := h1432c.2.2.1
                          have p1432_3 := h1432c.2.2.2
                          linarith only [hlam, p1432_0]
                        · have p1432_0 := h1432c.1
                          have p1432_1 := h1432c.2.1
                          have p1432_2 := h1432c.2.2.1
                          have p1432_3 := h1432c.2.2.2
                          linarith only [h0, hlam, p1432_0]
                        · have p1432_0 := h1432c.1
                          have p1432_1 := h1432c.2.1
                          have p1432_2 := h1432c.2.2.1
                          have p1432_3 := h1432c.2.2.2
                          linarith only [h655, hlam, p1432_0]
                        · have p1432_0 := h1432c.1
                          have p1432_1 := h1432c.2.1
                          have p1432_2 := h1432c.2.2.1
                          have p1432_3 := h1432c.2.2.2
                          linarith only [h884, hlam, p1432_0]
                        · have p1432_0 := h1432c.1
                          have p1432_1 := h1432c.2.1
                          have p1432_2 := h1432c.2.2.1
                          have p1432_3 := h1432c.2.2.2
                          linarith only [h999, hlam, p1432_0]
                        · have p1432_0 := h1432c.1
                          have p1432_1 := h1432c.2.1
                          have p1432_2 := h1432c.2.2.1
                          have p1432_3 := h1432c.2.2.2
                          rcases p1432_3 (m.d 0 1) (by simp) with h1438 | h1438
                          · linarith only [h1438, hlam, p1432_0]
                          · rcases p1432_3 (m.d 1 2) (by simp) with h1440 | h1440
                            · rcases p1432_3 (m.d 1 3) (by simp) with h1441 | h1441
                              · linarith only [h1086, h1441, hlam]
                              · linarith only [h1441, h655, hlam]
                            · linarith only [h1440, hlam, p1432_0]
                        · have p1432_0 := h1432c.1
                          have p1432_1 := h1432c.2.1
                          have p1432_2 := h1432c.2.2.1
                          have p1432_3 := h1432c.2.2.2
                          linarith only [hlam, p1432_0]
                        · have p1432_0 := h1432c.1
                          have p1432_1 := h1432c.2.1
                          have p1432_2 := h1432c.2.2.1
                          have p1432_3 := h1432c.2.2.2
                          linarith only [h655, hc01, hc12, hlam, hphi, p1432_1]
                        · have p1432_0 := h1432c.1
                          have p1432_1 := h1432c.2.1
                          have p1432_2 := h1432c.2.2.1
                          have p1432_3 := h1432c.2.2.2
                          linarith only [h884, hc01, hc12, hlam, hphi, p1432_1]
                        · have p1432_0 := h1432c.1
                          have p1432_1 := h1432c.2.1
                          have p1432_2 := h1432c.2.2.1
                          have p1432_3 := h1432c.2.2.2
                          linarith only [h999, hc01, hc12, hlam, hphi, p1432_1]
                        · have p1432_0 := h1432c.1
                          have p1432_1 := h1432c.2.1
                          have p1432_2 := h1432c.2.2.1
                          have p1432_3 := h1432c.2.2.2
                          rcases p1432_3 (m.d 0 1) (by simp) with h1449 | h1449
                          · linarith only [h1449, hlam, p1432_0]
                          · rcases p1432_3 (m.d 1 2) (by simp) with h1451 | h1451
                            · rcases p1432_3 (m.d 1 3) (by simp) with h1452 | h1452
                              · rcases p1432_3 (m.d 1 4) (by simp) with h1453 | h1453
                                · linarith only [h1089, h1453, hlam]
                                · linarith only [h1453, h884, hlam]
                              · linarith only [h1452, hlam, p1432_0]
                            · linarith only [h0, h1451, hlam]
                        · have p1432_0 := h1432c.1
                          have p1432_1 := h1432c.2.1
                          have p1432_2 := h1432c.2.2.1
                          have p1432_3 := h1432c.2.2.2
                          linarith only [h1086, hlam, p1432_0]
                        · have p1432_0 := h1432c.1
                          have p1432_1 := h1432c.2.1
                          have p1432_2 := h1432c.2.2.1
                          have p1432_3 := h1432c.2.2.2
                          linarith only [hlam, p1432_0]
                        · have p1432_0 := h1432c.1
                          have p1432_1 := h1432c.2.1
                          have p1432_2 := h1432c.2.2.1
                          have p1432_3 := h1432c.2.2.2
                          linarith only [h1083, h1428, h1431, h884, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1432_1, u2ehi2]
                        · have p1432_0 := h1432c.1
                          have p1432_1 := h1432c.2.1
                          have p1432_2 := h1432c.2.2.1
                          have p1432_3 := h1432c.2.2.2
                          linarith only [h1084, h1086, h1428, h999, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1432_1, u2ehi2]
                        · have p1432_0 := h1432c.1
                          have p1432_1 := h1432c.2.1
                          have p1432_2 := h1432c.2.2.1
                          have p1432_3 := h1432c.2.2.2
                          rcases p1432_3 (m.d 0 1) (by simp) with h1462 | h1462
                          · linarith only [h1462, hlam, p1432_0]
                          · rcases p1432_3 (m.d 1 2) (by simp) with h1464 | h1464
                            · rcases p1432_3 (m.d 1 3) (by simp) with h1465 | h1465
                              · rcases p1432_3 (m.d 1 4) (by simp) with h1466 | h1466
                                · rcases p1432_3 (m.d 1 5) (by simp) with h1467 | h1467
                                  · linarith only [h1091, h1467, hlam]
                                  · linarith only [h1467, h999, hlam]
                                · linarith only [h1466, hlam, p1432_0]
                              · linarith only [h1465, h655, hlam]
                            · linarith only [h0, h1464, hlam]
                        · have p1432_0 := h1432c.1
                          have p1432_1 := h1432c.2.1
                          have p1432_2 := h1432c.2.2.1
                          have p1432_3 := h1432c.2.2.2
                          linarith only [h1087, hlam, p1432_0]
                        · have p1432_0 := h1432c.1
                          have p1432_1 := h1432c.2.1
                          have p1432_2 := h1432c.2.2.1
                          have p1432_3 := h1432c.2.2.2
                          linarith only [h1089, hlam, p1432_1]
                        · have p1432_0 := h1432c.1
                          have p1432_1 := h1432c.2.1
                          have p1432_2 := h1432c.2.2.1
                          have p1432_3 := h1432c.2.2.2
                          linarith only [hlam, p1432_0]
                        · have p1432_0 := h1432c.1
                          have p1432_1 := h1432c.2.1
                          have p1432_2 := h1432c.2.2.1
                          have p1432_3 := h1432c.2.2.2
                          linarith only [h1084, h1428, h999, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1432_1, u2ehi2]
                        · have p1432_0 := h1432c.1
                          have p1432_1 := h1432c.2.1
                          have p1432_2 := h1432c.2.2.1
                          have p1432_3 := h1432c.2.2.2
                          rcases p1432_3 (m.d 0 1) (by simp) with h1477 | h1477
                          · linarith only [h1477, hlam, p1432_0]
                          · rcases p1432_3 (m.d 1 2) (by simp) with h1479 | h1479
                            · rcases p1432_3 (m.d 1 3) (by simp) with h1480 | h1480
                              · rcases p1432_3 (m.d 1 4) (by simp) with h1481 | h1481
                                · rcases p1432_3 (m.d 1 5) (by simp) with h1482 | h1482
                                  · rcases h4bigk with h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c
                                    · have p1483_0 := h1483c.1
                                      have p1483_1 := h1483c.2.1
                                      have p1483_2 := h1483c.2.2.1
                                      have p1483_3 := h1483c.2.2.2
                                      linarith only [hlam, p1483_0]
                                    · have p1483_0 := h1483c.1
                                      have p1483_1 := h1483c.2.1
                                      have p1483_2 := h1483c.2.2.1
                                      have p1483_3 := h1483c.2.2.2
                                      linarith only [h884, hlam, p1483_1]
                                    · have p1483_0 := h1483c.1
                                      have p1483_1 := h1483c.2.1
                                      have p1483_2 := h1483c.2.2.1
                                      have p1483_3 := h1483c.2.2.2
                                      linarith only [h1430, hc04, hlam, hphi, ht0b, ht5b, p1483_1, u5ehi4]
                                    · have p1483_0 := h1483c.1
                                      have p1483_1 := h1483c.2.1
                                      have p1483_2 := h1483c.2.2.1
                                      have p1483_3 := h1483c.2.2.2
                                      linarith only [h1086, h1089, h1428, h1431, h884, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1483_1, u2ehi2]
                                    · have p1483_0 := h1483c.1
                                      have p1483_1 := h1483c.2.1
                                      have p1483_2 := h1483c.2.2.1
                                      have p1483_3 := h1483c.2.2.2
                                      rcases p1483_3 (m.d 0 4) (by simp) with h1488 | h1488
                                      · rcases p1483_3 (m.d 1 4) (by simp) with h1489 | h1489
                                        · rcases p1483_3 (m.d 2 4) (by simp) with h1490 | h1490
                                          · linarith only [h1081, h1490, hlam]
                                          · linarith only [h1430, h1490, hlam]
                                        · linarith only [h1091, h1489, hlam]
                                      · linarith only [h1488, hlam, p1483_0]
                                    · have p1483_0 := h1483c.1
                                      have p1483_1 := h1483c.2.1
                                      have p1483_2 := h1483c.2.2.1
                                      have p1483_3 := h1483c.2.2.2
                                      linarith only [h1081, h1086, h1089, h1430, hc12, hlam, hphi, ht01, ht0b, ht5b, p1483_1, u5ehi4]
                                    · have p1483_0 := h1483c.1
                                      have p1483_1 := h1483c.2.1
                                      have p1483_2 := h1483c.2.2.1
                                      have p1483_3 := h1483c.2.2.2
                                      linarith only [hlam, p1483_0]
                                    · have p1483_0 := h1483c.1
                                      have p1483_1 := h1483c.2.1
                                      have p1483_2 := h1483c.2.2.1
                                      have p1483_3 := h1483c.2.2.2
                                      linarith only [h1086, h1089, h1430, hc12, hlam, hphi, ht01, ht0b, ht5b, p1483_1, u5ehi4]
                                    · have p1483_0 := h1483c.1
                                      have p1483_1 := h1483c.2.1
                                      have p1483_2 := h1483c.2.2.1
                                      have p1483_3 := h1483c.2.2.2
                                      linarith only [h1086, h1089, h1428, h1431, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1483_1, u2ehi2]
                                    · have p1483_0 := h1483c.1
                                      have p1483_1 := h1483c.2.1
                                      have p1483_2 := h1483c.2.2.1
                                      have p1483_3 := h1483c.2.2.2
                                      rcases p1483_3 (m.d 0 4) (by simp) with h1499 | h1499
                                      · linarith only [h1499, h884, hlam]
                                      · linarith only [h1085, h1499, hlam]
                                    · have p1483_0 := h1483c.1
                                      have p1483_1 := h1483c.2.1
                                      have p1483_2 := h1483c.2.2.1
                                      have p1483_3 := h1483c.2.2.2
                                      linarith only [h1081, hlam, p1483_0]
                                    · have p1483_0 := h1483c.1
                                      have p1483_1 := h1483c.2.1
                                      have p1483_2 := h1483c.2.2.1
                                      have p1483_3 := h1483c.2.2.2
                                      linarith only [h1087, hlam, p1483_0]
                                    · have p1483_0 := h1483c.1
                                      have p1483_1 := h1483c.2.1
                                      have p1483_2 := h1483c.2.2.1
                                      have p1483_3 := h1483c.2.2.2
                                      linarith only [hlam, p1483_0]
                                    · have p1483_0 := h1483c.1
                                      have p1483_1 := h1483c.2.1
                                      have p1483_2 := h1483c.2.2.1
                                      have p1483_3 := h1483c.2.2.2
                                      linarith only [h1092, hlam, p1483_1]
                                    · have p1483_0 := h1483c.1
                                      have p1483_1 := h1483c.2.1
                                      have p1483_2 := h1483c.2.2.1
                                      have p1483_3 := h1483c.2.2.2
                                      linarith only [h1081, hc02, hlam, hphi, ht0b, ht5b, p1483_1, u5ehi4]
                                    · have p1483_0 := h1483c.1
                                      have p1483_1 := h1483c.2.1
                                      have p1483_2 := h1483c.2.2.1
                                      have p1483_3 := h1483c.2.2.2
                                      linarith only [h1083, hlam, p1483_0]
                                    · have p1483_0 := h1483c.1
                                      have p1483_1 := h1483c.2.1
                                      have p1483_2 := h1483c.2.2.1
                                      have p1483_3 := h1483c.2.2.2
                                      linarith only [h1089, hlam, p1483_0]
                                    · have p1483_0 := h1483c.1
                                      have p1483_1 := h1483c.2.1
                                      have p1483_2 := h1483c.2.2.1
                                      have p1483_3 := h1483c.2.2.2
                                      linarith only [h1083, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1483_1, u2ehi3]
                                    · have p1483_0 := h1483c.1
                                      have p1483_1 := h1483c.2.1
                                      have p1483_2 := h1483c.2.2.1
                                      have p1483_3 := h1483c.2.2.2
                                      linarith only [hlam, p1483_0]
                                    · have p1483_0 := h1483c.1
                                      have p1483_1 := h1483c.2.1
                                      have p1483_2 := h1483c.2.2.1
                                      have p1483_3 := h1483c.2.2.2
                                      linarith only [h1083, h1086, h655, hc12, hlam, hphi, ht01, ht0b, ht5b, p1483_1, u5ehi4]
                                    · have p1483_0 := h1483c.1
                                      have p1483_1 := h1483c.2.1
                                      have p1483_2 := h1483c.2.2.1
                                      have p1483_3 := h1483c.2.2.2
                                      linarith only [h1085, hlam, p1483_0]
                                    · have p1483_0 := h1483c.1
                                      have p1483_1 := h1483c.2.1
                                      have p1483_2 := h1483c.2.2.1
                                      have p1483_3 := h1483c.2.2.2
                                      linarith only [h1091, hlam, p1483_0]
                                    · have p1483_0 := h1483c.1
                                      have p1483_1 := h1483c.2.1
                                      have p1483_2 := h1483c.2.2.1
                                      have p1483_3 := h1483c.2.2.2
                                      linarith only [h1430, hlam, p1483_0]
                                    · have p1483_0 := h1483c.1
                                      have p1483_1 := h1483c.2.1
                                      have p1483_2 := h1483c.2.2.1
                                      have p1483_3 := h1483c.2.2.2
                                      linarith only [h1431, hlam, p1483_0]
                                    · have p1483_0 := h1483c.1
                                      have p1483_1 := h1483c.2.1
                                      have p1483_2 := h1483c.2.2.1
                                      have p1483_3 := h1483c.2.2.2
                                      linarith only [hlam, p1483_0]
                                  · linarith only [h1482, hlam, p1432_0]
                                · linarith only [h1481, h884, hlam]
                              · linarith only [h1480, h655, hlam]
                            · linarith only [h0, h1479, hlam]
                        · have p1432_0 := h1432c.1
                          have p1432_1 := h1432c.2.1
                          have p1432_2 := h1432c.2.2.1
                          have p1432_3 := h1432c.2.2.2
                          linarith only [h1088, hlam, p1432_0]
                        · have p1432_0 := h1432c.1
                          have p1432_1 := h1432c.2.1
                          have p1432_2 := h1432c.2.2.1
                          have p1432_3 := h1432c.2.2.2
                          linarith only [h1090, hlam, p1432_0]
                        · have p1432_0 := h1432c.1
                          have p1432_1 := h1432c.2.1
                          have p1432_2 := h1432c.2.2.1
                          have p1432_3 := h1432c.2.2.2
                          linarith only [h1091, hlam, p1432_0]
                        · have p1432_0 := h1432c.1
                          have p1432_1 := h1432c.2.1
                          have p1432_2 := h1432c.2.2.1
                          have p1432_3 := h1432c.2.2.2
                          linarith only [hlam, p1432_0]
                      · linarith only [h1092, h1430, h1431, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1526 | h1526
                      · linarith only [h1083, h1086, h1092, h1430, h1526, h655, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h1085, h1092, h1526, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
              · linarith only [h1085, h1091, h884, hlam]
            · linarith only [h1084, h1090, h655, hlam]
          · linarith only [h1083, h1089, h655, hlam]
        · linarith only [h0, h1080, h1088, hc25, hlam, hphi, u2ehi2]
      · linarith only [h0, h1080, h1087, hc24, hlam, hphi, u2ehi2]
    · linarith only [h0, h1080, h1086, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1535 | h1535
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1536 | h1536
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1537 | h1537
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1538 | h1538
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1539 | h1539
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1540 | h1540
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1541 | h1541
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1542 | h1542
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1543 | h1543
                    · linarith only [h1081, h1085, h1543, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1545 | h1545
                      · linarith only [h1081, h1085, h1541, h1545, hc23, hlam, hphi, u2ehi3]
                      · rcases h1bigk with h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c
                        · have p1547_0 := h1547c.1
                          have p1547_1 := h1547c.2.1
                          have p1547_2 := h1547c.2.2.1
                          have p1547_3 := h1547c.2.2.2
                          linarith only [hlam, p1547_0]
                        · have p1547_0 := h1547c.1
                          have p1547_1 := h1547c.2.1
                          have p1547_2 := h1547c.2.2.1
                          have p1547_3 := h1547c.2.2.2
                          linarith only [h0, hlam, p1547_0]
                        · have p1547_0 := h1547c.1
                          have p1547_1 := h1547c.2.1
                          have p1547_2 := h1547c.2.2.1
                          have p1547_3 := h1547c.2.2.2
                          linarith only [h655, hlam, p1547_0]
                        · have p1547_0 := h1547c.1
                          have p1547_1 := h1547c.2.1
                          have p1547_2 := h1547c.2.2.1
                          have p1547_3 := h1547c.2.2.2
                          linarith only [h884, hlam, p1547_0]
                        · have p1547_0 := h1547c.1
                          have p1547_1 := h1547c.2.1
                          have p1547_2 := h1547c.2.2.1
                          have p1547_3 := h1547c.2.2.2
                          linarith only [h999, hlam, p1547_0]
                        · have p1547_0 := h1547c.1
                          have p1547_1 := h1547c.2.1
                          have p1547_2 := h1547c.2.2.1
                          have p1547_3 := h1547c.2.2.2
                          rcases p1547_3 (m.d 0 1) (by simp) with h1553 | h1553
                          · linarith only [h1553, hlam, p1547_0]
                          · rcases p1547_3 (m.d 1 2) (by simp) with h1555 | h1555
                            · rcases p1547_3 (m.d 1 3) (by simp) with h1556 | h1556
                              · linarith only [h1535, h1556, hlam]
                              · linarith only [h1556, h655, hlam]
                            · linarith only [h1555, hlam, p1547_0]
                        · have p1547_0 := h1547c.1
                          have p1547_1 := h1547c.2.1
                          have p1547_2 := h1547c.2.2.1
                          have p1547_3 := h1547c.2.2.2
                          linarith only [hlam, p1547_0]
                        · have p1547_0 := h1547c.1
                          have p1547_1 := h1547c.2.1
                          have p1547_2 := h1547c.2.2.1
                          have p1547_3 := h1547c.2.2.2
                          linarith only [h1081, h1085, h1538, h1540, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1547_1, u2ehi3]
                        · have p1547_0 := h1547c.1
                          have p1547_1 := h1547c.2.1
                          have p1547_2 := h1547c.2.2.1
                          have p1547_3 := h1547c.2.2.2
                          linarith only [h1081, h1085, h1540, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1547_1, u2ehi3]
                        · have p1547_0 := h1547c.1
                          have p1547_1 := h1547c.2.1
                          have p1547_2 := h1547c.2.2.1
                          have p1547_3 := h1547c.2.2.2
                          linarith only [h999, hc01, hc12, hlam, hphi, p1547_1]
                        · have p1547_0 := h1547c.1
                          have p1547_1 := h1547c.2.1
                          have p1547_2 := h1547c.2.2.1
                          have p1547_3 := h1547c.2.2.2
                          rcases p1547_3 (m.d 0 1) (by simp) with h1564 | h1564
                          · linarith only [h1564, hlam, p1547_0]
                          · rcases p1547_3 (m.d 1 2) (by simp) with h1566 | h1566
                            · rcases p1547_3 (m.d 1 3) (by simp) with h1567 | h1567
                              · rcases p1547_3 (m.d 1 4) (by simp) with h1568 | h1568
                                · linarith only [h1538, h1568, hlam]
                                · linarith only [h1568, h884, hlam]
                              · linarith only [h1567, hlam, p1547_0]
                            · linarith only [h0, h1566, hlam]
                        · have p1547_0 := h1547c.1
                          have p1547_1 := h1547c.2.1
                          have p1547_2 := h1547c.2.2.1
                          have p1547_3 := h1547c.2.2.2
                          linarith only [h1535, hlam, p1547_0]
                        · have p1547_0 := h1547c.1
                          have p1547_1 := h1547c.2.1
                          have p1547_2 := h1547c.2.2.1
                          have p1547_3 := h1547c.2.2.2
                          linarith only [hlam, p1547_0]
                        · have p1547_0 := h1547c.1
                          have p1547_1 := h1547c.2.1
                          have p1547_2 := h1547c.2.2.1
                          have p1547_3 := h1547c.2.2.2
                          linarith only [h1081, h1085, h1540, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1547_1, u2ehi3]
                        · have p1547_0 := h1547c.1
                          have p1547_1 := h1547c.2.1
                          have p1547_2 := h1547c.2.2.1
                          have p1547_3 := h1547c.2.2.2
                          linarith only [h1081, h1085, h1535, h1540, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1547_1, u2ehi3]
                        · have p1547_0 := h1547c.1
                          have p1547_1 := h1547c.2.1
                          have p1547_2 := h1547c.2.2.1
                          have p1547_3 := h1547c.2.2.2
                          rcases p1547_3 (m.d 0 1) (by simp) with h1577 | h1577
                          · linarith only [h1577, hlam, p1547_0]
                          · rcases p1547_3 (m.d 1 2) (by simp) with h1579 | h1579
                            · rcases p1547_3 (m.d 1 3) (by simp) with h1580 | h1580
                              · rcases p1547_3 (m.d 1 4) (by simp) with h1581 | h1581
                                · rcases p1547_3 (m.d 1 5) (by simp) with h1582 | h1582
                                  · linarith only [h1540, h1582, hlam]
                                  · linarith only [h1582, h999, hlam]
                                · linarith only [h1581, hlam, p1547_0]
                              · linarith only [h1580, h655, hlam]
                            · linarith only [h0, h1579, hlam]
                        · have p1547_0 := h1547c.1
                          have p1547_1 := h1547c.2.1
                          have p1547_2 := h1547c.2.2.1
                          have p1547_3 := h1547c.2.2.2
                          linarith only [h1536, hlam, p1547_0]
                        · have p1547_0 := h1547c.1
                          have p1547_1 := h1547c.2.1
                          have p1547_2 := h1547c.2.2.1
                          have p1547_3 := h1547c.2.2.2
                          linarith only [h1538, hlam, p1547_1]
                        · have p1547_0 := h1547c.1
                          have p1547_1 := h1547c.2.1
                          have p1547_2 := h1547c.2.2.1
                          have p1547_3 := h1547c.2.2.2
                          linarith only [hlam, p1547_0]
                        · have p1547_0 := h1547c.1
                          have p1547_1 := h1547c.2.1
                          have p1547_2 := h1547c.2.2.1
                          have p1547_3 := h1547c.2.2.2
                          linarith only [h1081, h1085, h1540, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1547_1, u2ehi3]
                        · have p1547_0 := h1547c.1
                          have p1547_1 := h1547c.2.1
                          have p1547_2 := h1547c.2.2.1
                          have p1547_3 := h1547c.2.2.2
                          rcases p1547_3 (m.d 0 1) (by simp) with h1592 | h1592
                          · linarith only [h1592, hlam, p1547_0]
                          · rcases p1547_3 (m.d 1 2) (by simp) with h1594 | h1594
                            · rcases p1547_3 (m.d 1 3) (by simp) with h1595 | h1595
                              · rcases p1547_3 (m.d 1 4) (by simp) with h1596 | h1596
                                · rcases p1547_3 (m.d 1 5) (by simp) with h1597 | h1597
                                  · rcases h4bigk with h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c | h1598c
                                    · have p1598_0 := h1598c.1
                                      have p1598_1 := h1598c.2.1
                                      have p1598_2 := h1598c.2.2.1
                                      have p1598_3 := h1598c.2.2.2
                                      linarith only [hlam, p1598_0]
                                    · have p1598_0 := h1598c.1
                                      have p1598_1 := h1598c.2.1
                                      have p1598_2 := h1598c.2.2.1
                                      have p1598_3 := h1598c.2.2.2
                                      linarith only [h884, hlam, p1598_1]
                                    · have p1598_0 := h1598c.1
                                      have p1598_1 := h1598c.2.1
                                      have p1598_2 := h1598c.2.2.1
                                      have p1598_3 := h1598c.2.2.2
                                      linarith only [h1085, hc45, hlam, hphi, ht23, ht34, p1598_1, u2ehi3]
                                    · have p1598_0 := h1598c.1
                                      have p1598_1 := h1598c.2.1
                                      have p1598_2 := h1598c.2.2.1
                                      have p1598_3 := h1598c.2.2.2
                                      linarith only [h1085, hc34, hc45, hlam, hphi, p1598_1]
                                    · have p1598_0 := h1598c.1
                                      have p1598_1 := h1598c.2.1
                                      have p1598_2 := h1598c.2.2.1
                                      have p1598_3 := h1598c.2.2.2
                                      linarith only [h1085, hlam, p1598_0]
                                    · have p1598_0 := h1598c.1
                                      have p1598_1 := h1598c.2.1
                                      have p1598_2 := h1598c.2.2.1
                                      have p1598_3 := h1598c.2.2.2
                                      rcases p1598_3 (m.d 0 4) (by simp) with h1604 | h1604
                                      · linarith only [h1604, h884, hlam]
                                      · rcases p1598_3 (m.d 1 4) (by simp) with h1606 | h1606
                                        · rcases p1598_3 (m.d 2 4) (by simp) with h1607 | h1607
                                          · linarith only [h1536, h1607, hlam]
                                          · rcases p1598_3 (m.d 3 4) (by simp) with h1609 | h1609
                                            · linarith only [h1538, h1609, hlam]
                                            · rcases p1598_3 (m.d 4 5) (by simp) with h1611 | h1611
                                              · linarith only [h1540, h1611, hlam]
                                              · linarith only [h1085, h1611, hlam]
                                        · linarith only [h1606, h884, hlam]
                                    · have p1598_0 := h1598c.1
                                      have p1598_1 := h1598c.2.1
                                      have p1598_2 := h1598c.2.2.1
                                      have p1598_3 := h1598c.2.2.2
                                      linarith only [hlam, p1598_0]
                                    · have p1598_0 := h1598c.1
                                      have p1598_1 := h1598c.2.1
                                      have p1598_2 := h1598c.2.2.1
                                      have p1598_3 := h1598c.2.2.2
                                      rcases p1598_3 (m.d 0 4) (by simp) with h1616 | h1616
                                      · linarith only [h1616, h884, hlam]
                                      · linarith only [h1081, h1616, hlam]
                                    · have p1598_0 := h1598c.1
                                      have p1598_1 := h1598c.2.1
                                      have p1598_2 := h1598c.2.2.1
                                      have p1598_3 := h1598c.2.2.2
                                      rcases p1598_3 (m.d 0 4) (by simp) with h1619 | h1619
                                      · linarith only [h1619, h884, hlam]
                                      · linarith only [h1083, h1619, hlam]
                                    · have p1598_0 := h1598c.1
                                      have p1598_1 := h1598c.2.1
                                      have p1598_2 := h1598c.2.2.1
                                      have p1598_3 := h1598c.2.2.2
                                      linarith only [h1085, h1535, h1538, h884, hc01, hc12, hlam, hphi, p1598_1]
                                    · have p1598_0 := h1598c.1
                                      have p1598_1 := h1598c.2.1
                                      have p1598_2 := h1598c.2.2.1
                                      have p1598_3 := h1598c.2.2.2
                                      linarith only [h1081, hlam, p1598_0]
                                    · have p1598_0 := h1598c.1
                                      have p1598_1 := h1598c.2.1
                                      have p1598_2 := h1598c.2.2.1
                                      have p1598_3 := h1598c.2.2.2
                                      linarith only [h1536, hlam, p1598_0]
                                    · have p1598_0 := h1598c.1
                                      have p1598_1 := h1598c.2.1
                                      have p1598_2 := h1598c.2.2.1
                                      have p1598_3 := h1598c.2.2.2
                                      linarith only [hlam, p1598_0]
                                    · have p1598_0 := h1598c.1
                                      have p1598_1 := h1598c.2.1
                                      have p1598_2 := h1598c.2.2.1
                                      have p1598_3 := h1598c.2.2.2
                                      linarith only [h1081, h1085, hc34, hc45, hlam, hphi, p1598_1]
                                    · have p1598_0 := h1598c.1
                                      have p1598_1 := h1598c.2.1
                                      have p1598_2 := h1598c.2.2.1
                                      have p1598_3 := h1598c.2.2.2
                                      linarith only [h1543, hlam, p1598_0]
                                    · have p1598_0 := h1598c.1
                                      have p1598_1 := h1598c.2.1
                                      have p1598_2 := h1598c.2.2.1
                                      have p1598_3 := h1598c.2.2.2
                                      linarith only [h1083, hlam, p1598_0]
                                    · have p1598_0 := h1598c.1
                                      have p1598_1 := h1598c.2.1
                                      have p1598_2 := h1598c.2.2.1
                                      have p1598_3 := h1598c.2.2.2
                                      linarith only [h1538, hlam, p1598_0]
                                    · have p1598_0 := h1598c.1
                                      have p1598_1 := h1598c.2.1
                                      have p1598_2 := h1598c.2.2.1
                                      have p1598_3 := h1598c.2.2.2
                                      linarith only [h1541, hlam, p1598_0]
                                    · have p1598_0 := h1598c.1
                                      have p1598_1 := h1598c.2.1
                                      have p1598_2 := h1598c.2.2.1
                                      have p1598_3 := h1598c.2.2.2
                                      linarith only [hlam, p1598_0]
                                    · have p1598_0 := h1598c.1
                                      have p1598_1 := h1598c.2.1
                                      have p1598_2 := h1598c.2.2.1
                                      have p1598_3 := h1598c.2.2.2
                                      linarith only [h1545, hlam, p1598_0]
                                    · have p1598_0 := h1598c.1
                                      have p1598_1 := h1598c.2.1
                                      have p1598_2 := h1598c.2.2.1
                                      have p1598_3 := h1598c.2.2.2
                                      linarith only [h1081, hc45, hlam, hphi, ht23, ht34, p1598_1, u2ehi3]
                                    · have p1598_0 := h1598c.1
                                      have p1598_1 := h1598c.2.1
                                      have p1598_2 := h1598c.2.2.1
                                      have p1598_3 := h1598c.2.2.2
                                      linarith only [h1540, hlam, p1598_0]
                                    · have p1598_0 := h1598c.1
                                      have p1598_1 := h1598c.2.1
                                      have p1598_2 := h1598c.2.2.1
                                      have p1598_3 := h1598c.2.2.2
                                      linarith only [h1535, h1538, h1540, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1598_1, u2ehi3]
                                    · have p1598_0 := h1598c.1
                                      have p1598_1 := h1598c.2.1
                                      have p1598_2 := h1598c.2.2.1
                                      have p1598_3 := h1598c.2.2.2
                                      rcases p1598_3 (m.d 0 4) (by simp) with h1636 | h1636
                                      · linarith only [h1085, h1636, hlam]
                                      · linarith only [h1083, h1636, hlam]
                                    · have p1598_0 := h1598c.1
                                      have p1598_1 := h1598c.2.1
                                      have p1598_2 := h1598c.2.2.1
                                      have p1598_3 := h1598c.2.2.2
                                      linarith only [hlam, p1598_0]
                                  · linarith only [h1597, hlam, p1547_0]
                                · linarith only [h1596, h884, hlam]
                              · linarith only [h1595, h655, hlam]
                            · linarith only [h0, h1594, hlam]
                        · have p1547_0 := h1547c.1
                          have p1547_1 := h1547c.2.1
                          have p1547_2 := h1547c.2.2.1
                          have p1547_3 := h1547c.2.2.2
                          linarith only [h1537, hlam, p1547_0]
                        · have p1547_0 := h1547c.1
                          have p1547_1 := h1547c.2.1
                          have p1547_2 := h1547c.2.2.1
                          have p1547_3 := h1547c.2.2.2
                          linarith only [h1539, hlam, p1547_0]
                        · have p1547_0 := h1547c.1
                          have p1547_1 := h1547c.2.1
                          have p1547_2 := h1547c.2.2.1
                          have p1547_3 := h1547c.2.2.2
                          linarith only [h1540, hlam, p1547_0]
                        · have p1547_0 := h1547c.1
                          have p1547_1 := h1547c.2.1
                          have p1547_2 := h1547c.2.2.1
                          have p1547_3 := h1547c.2.2.2
                          linarith only [hlam, p1547_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1648 | h1648
                    · linarith only [h1084, h1085, h1542, h1648, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1650 | h1650
                      · linarith only [h1084, h1085, h1542, h1650, hc34, hlam, hphi, ht23, u2ehi2]
                      · rcases h1bigk with h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c
                        · have p1652_0 := h1652c.1
                          have p1652_1 := h1652c.2.1
                          have p1652_2 := h1652c.2.2.1
                          have p1652_3 := h1652c.2.2.2
                          linarith only [hlam, p1652_0]
                        · have p1652_0 := h1652c.1
                          have p1652_1 := h1652c.2.1
                          have p1652_2 := h1652c.2.2.1
                          have p1652_3 := h1652c.2.2.2
                          linarith only [h0, hlam, p1652_0]
                        · have p1652_0 := h1652c.1
                          have p1652_1 := h1652c.2.1
                          have p1652_2 := h1652c.2.2.1
                          have p1652_3 := h1652c.2.2.2
                          linarith only [h655, hlam, p1652_0]
                        · have p1652_0 := h1652c.1
                          have p1652_1 := h1652c.2.1
                          have p1652_2 := h1652c.2.2.1
                          have p1652_3 := h1652c.2.2.2
                          linarith only [h884, hlam, p1652_0]
                        · have p1652_0 := h1652c.1
                          have p1652_1 := h1652c.2.1
                          have p1652_2 := h1652c.2.2.1
                          have p1652_3 := h1652c.2.2.2
                          linarith only [h999, hlam, p1652_0]
                        · have p1652_0 := h1652c.1
                          have p1652_1 := h1652c.2.1
                          have p1652_2 := h1652c.2.2.1
                          have p1652_3 := h1652c.2.2.2
                          rcases p1652_3 (m.d 0 1) (by simp) with h1658 | h1658
                          · linarith only [h1658, hlam, p1652_0]
                          · rcases p1652_3 (m.d 1 2) (by simp) with h1660 | h1660
                            · rcases p1652_3 (m.d 1 3) (by simp) with h1661 | h1661
                              · linarith only [h1535, h1661, hlam]
                              · linarith only [h1661, h655, hlam]
                            · linarith only [h1660, hlam, p1652_0]
                        · have p1652_0 := h1652c.1
                          have p1652_1 := h1652c.2.1
                          have p1652_2 := h1652c.2.2.1
                          have p1652_3 := h1652c.2.2.2
                          linarith only [hlam, p1652_0]
                        · have p1652_0 := h1652c.1
                          have p1652_1 := h1652c.2.1
                          have p1652_2 := h1652c.2.2.1
                          have p1652_3 := h1652c.2.2.2
                          linarith only [h1084, h1085, h1538, h1540, h1541, h1542, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1652_1, u2ehi3]
                        · have p1652_0 := h1652c.1
                          have p1652_1 := h1652c.2.1
                          have p1652_2 := h1652c.2.2.1
                          have p1652_3 := h1652c.2.2.2
                          linarith only [h1084, h1085, h1540, h1541, h1542, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1652_1, u2ehi3]
                        · have p1652_0 := h1652c.1
                          have p1652_1 := h1652c.2.1
                          have p1652_2 := h1652c.2.2.1
                          have p1652_3 := h1652c.2.2.2
                          linarith only [h999, hc01, hc12, hlam, hphi, p1652_1]
                        · have p1652_0 := h1652c.1
                          have p1652_1 := h1652c.2.1
                          have p1652_2 := h1652c.2.2.1
                          have p1652_3 := h1652c.2.2.2
                          rcases p1652_3 (m.d 0 1) (by simp) with h1669 | h1669
                          · linarith only [h1669, hlam, p1652_0]
                          · rcases p1652_3 (m.d 1 2) (by simp) with h1671 | h1671
                            · rcases p1652_3 (m.d 1 3) (by simp) with h1672 | h1672
                              · rcases p1652_3 (m.d 1 4) (by simp) with h1673 | h1673
                                · linarith only [h1538, h1673, hlam]
                                · linarith only [h1673, h884, hlam]
                              · linarith only [h1672, hlam, p1652_0]
                            · linarith only [h0, h1671, hlam]
                        · have p1652_0 := h1652c.1
                          have p1652_1 := h1652c.2.1
                          have p1652_2 := h1652c.2.2.1
                          have p1652_3 := h1652c.2.2.2
                          linarith only [h1535, hlam, p1652_0]
                        · have p1652_0 := h1652c.1
                          have p1652_1 := h1652c.2.1
                          have p1652_2 := h1652c.2.2.1
                          have p1652_3 := h1652c.2.2.2
                          linarith only [hlam, p1652_0]
                        · have p1652_0 := h1652c.1
                          have p1652_1 := h1652c.2.1
                          have p1652_2 := h1652c.2.2.1
                          have p1652_3 := h1652c.2.2.2
                          linarith only [h1084, h1085, h1540, h1541, h1542, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1652_1, u2ehi3]
                        · have p1652_0 := h1652c.1
                          have p1652_1 := h1652c.2.1
                          have p1652_2 := h1652c.2.2.1
                          have p1652_3 := h1652c.2.2.2
                          linarith only [h1084, h1085, h1535, h1540, h1541, h1542, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1652_1, u2ehi3]
                        · have p1652_0 := h1652c.1
                          have p1652_1 := h1652c.2.1
                          have p1652_2 := h1652c.2.2.1
                          have p1652_3 := h1652c.2.2.2
                          rcases p1652_3 (m.d 0 1) (by simp) with h1682 | h1682
                          · linarith only [h1682, hlam, p1652_0]
                          · rcases p1652_3 (m.d 1 2) (by simp) with h1684 | h1684
                            · rcases p1652_3 (m.d 1 3) (by simp) with h1685 | h1685
                              · rcases p1652_3 (m.d 1 4) (by simp) with h1686 | h1686
                                · rcases p1652_3 (m.d 1 5) (by simp) with h1687 | h1687
                                  · linarith only [h1540, h1687, hlam]
                                  · linarith only [h1687, h999, hlam]
                                · linarith only [h1686, hlam, p1652_0]
                              · linarith only [h1685, h655, hlam]
                            · linarith only [h0, h1684, hlam]
                        · have p1652_0 := h1652c.1
                          have p1652_1 := h1652c.2.1
                          have p1652_2 := h1652c.2.2.1
                          have p1652_3 := h1652c.2.2.2
                          linarith only [h1536, hlam, p1652_0]
                        · have p1652_0 := h1652c.1
                          have p1652_1 := h1652c.2.1
                          have p1652_2 := h1652c.2.2.1
                          have p1652_3 := h1652c.2.2.2
                          linarith only [h1538, hlam, p1652_1]
                        · have p1652_0 := h1652c.1
                          have p1652_1 := h1652c.2.1
                          have p1652_2 := h1652c.2.2.1
                          have p1652_3 := h1652c.2.2.2
                          linarith only [hlam, p1652_0]
                        · have p1652_0 := h1652c.1
                          have p1652_1 := h1652c.2.1
                          have p1652_2 := h1652c.2.2.1
                          have p1652_3 := h1652c.2.2.2
                          linarith only [h1084, h1085, h1540, h1541, h1542, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1652_1, u2ehi3]
                        · have p1652_0 := h1652c.1
                          have p1652_1 := h1652c.2.1
                          have p1652_2 := h1652c.2.2.1
                          have p1652_3 := h1652c.2.2.2
                          rcases p1652_3 (m.d 0 1) (by simp) with h1697 | h1697
                          · linarith only [h1697, hlam, p1652_0]
                          · rcases p1652_3 (m.d 1 2) (by simp) with h1699 | h1699
                            · rcases p1652_3 (m.d 1 3) (by simp) with h1700 | h1700
                              · rcases p1652_3 (m.d 1 4) (by simp) with h1701 | h1701
                                · rcases p1652_3 (m.d 1 5) (by simp) with h1702 | h1702
                                  · rcases h4bigk with h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c | h1703c
                                    · have p1703_0 := h1703c.1
                                      have p1703_1 := h1703c.2.1
                                      have p1703_2 := h1703c.2.2.1
                                      have p1703_3 := h1703c.2.2.2
                                      linarith only [hlam, p1703_0]
                                    · have p1703_0 := h1703c.1
                                      have p1703_1 := h1703c.2.1
                                      have p1703_2 := h1703c.2.2.1
                                      have p1703_3 := h1703c.2.2.2
                                      linarith only [h884, hlam, p1703_1]
                                    · have p1703_0 := h1703c.1
                                      have p1703_1 := h1703c.2.1
                                      have p1703_2 := h1703c.2.2.1
                                      have p1703_3 := h1703c.2.2.2
                                      linarith only [h1085, hc45, hlam, hphi, ht23, ht34, p1703_1, u2ehi3]
                                    · have p1703_0 := h1703c.1
                                      have p1703_1 := h1703c.2.1
                                      have p1703_2 := h1703c.2.2.1
                                      have p1703_3 := h1703c.2.2.2
                                      linarith only [h1085, hc34, hc45, hlam, hphi, p1703_1]
                                    · have p1703_0 := h1703c.1
                                      have p1703_1 := h1703c.2.1
                                      have p1703_2 := h1703c.2.2.1
                                      have p1703_3 := h1703c.2.2.2
                                      linarith only [h1085, hlam, p1703_0]
                                    · have p1703_0 := h1703c.1
                                      have p1703_1 := h1703c.2.1
                                      have p1703_2 := h1703c.2.2.1
                                      have p1703_3 := h1703c.2.2.2
                                      rcases p1703_3 (m.d 0 4) (by simp) with h1709 | h1709
                                      · linarith only [h1709, h884, hlam]
                                      · rcases p1703_3 (m.d 1 4) (by simp) with h1711 | h1711
                                        · rcases p1703_3 (m.d 2 4) (by simp) with h1712 | h1712
                                          · linarith only [h1536, h1712, hlam]
                                          · rcases p1703_3 (m.d 3 4) (by simp) with h1714 | h1714
                                            · linarith only [h1538, h1714, hlam]
                                            · rcases p1703_3 (m.d 4 5) (by simp) with h1716 | h1716
                                              · linarith only [h1540, h1716, hlam]
                                              · linarith only [h1085, h1716, hlam]
                                        · linarith only [h1711, h884, hlam]
                                    · have p1703_0 := h1703c.1
                                      have p1703_1 := h1703c.2.1
                                      have p1703_2 := h1703c.2.2.1
                                      have p1703_3 := h1703c.2.2.2
                                      linarith only [hlam, p1703_0]
                                    · have p1703_0 := h1703c.1
                                      have p1703_1 := h1703c.2.1
                                      have p1703_2 := h1703c.2.2.1
                                      have p1703_3 := h1703c.2.2.2
                                      rcases p1703_3 (m.d 0 4) (by simp) with h1721 | h1721
                                      · linarith only [h1721, h884, hlam]
                                      · linarith only [h1081, h1721, hlam]
                                    · have p1703_0 := h1703c.1
                                      have p1703_1 := h1703c.2.1
                                      have p1703_2 := h1703c.2.2.1
                                      have p1703_3 := h1703c.2.2.2
                                      linarith only [h1084, h1085, h1540, h1541, h1542, hlam, p1703_2]
                                    · have p1703_0 := h1703c.1
                                      have p1703_1 := h1703c.2.1
                                      have p1703_2 := h1703c.2.2.1
                                      have p1703_3 := h1703c.2.2.2
                                      linarith only [h1081, h1085, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1703_1, u2ehi3]
                                    · have p1703_0 := h1703c.1
                                      have p1703_1 := h1703c.2.1
                                      have p1703_2 := h1703c.2.2.1
                                      have p1703_3 := h1703c.2.2.2
                                      linarith only [h1081, hlam, p1703_0]
                                    · have p1703_0 := h1703c.1
                                      have p1703_1 := h1703c.2.1
                                      have p1703_2 := h1703c.2.2.1
                                      have p1703_3 := h1703c.2.2.2
                                      linarith only [h1536, hlam, p1703_0]
                                    · have p1703_0 := h1703c.1
                                      have p1703_1 := h1703c.2.1
                                      have p1703_2 := h1703c.2.2.1
                                      have p1703_3 := h1703c.2.2.2
                                      linarith only [hlam, p1703_0]
                                    · have p1703_0 := h1703c.1
                                      have p1703_1 := h1703c.2.1
                                      have p1703_2 := h1703c.2.2.1
                                      have p1703_3 := h1703c.2.2.2
                                      linarith only [h1081, h1085, h1535, h1538, h1540, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1703_1]
                                    · have p1703_0 := h1703c.1
                                      have p1703_1 := h1703c.2.1
                                      have p1703_2 := h1703c.2.2.1
                                      have p1703_3 := h1703c.2.2.2
                                      linarith only [h1648, hlam, p1703_0]
                                    · have p1703_0 := h1703c.1
                                      have p1703_1 := h1703c.2.1
                                      have p1703_2 := h1703c.2.2.1
                                      have p1703_3 := h1703c.2.2.2
                                      linarith only [h1083, hlam, p1703_0]
                                    · have p1703_0 := h1703c.1
                                      have p1703_1 := h1703c.2.1
                                      have p1703_2 := h1703c.2.2.1
                                      have p1703_3 := h1703c.2.2.2
                                      linarith only [h1538, hlam, p1703_0]
                                    · have p1703_0 := h1703c.1
                                      have p1703_1 := h1703c.2.1
                                      have p1703_2 := h1703c.2.2.1
                                      have p1703_3 := h1703c.2.2.2
                                      linarith only [h1541, hlam, p1703_0]
                                    · have p1703_0 := h1703c.1
                                      have p1703_1 := h1703c.2.1
                                      have p1703_2 := h1703c.2.2.1
                                      have p1703_3 := h1703c.2.2.2
                                      linarith only [hlam, p1703_0]
                                    · have p1703_0 := h1703c.1
                                      have p1703_1 := h1703c.2.1
                                      have p1703_2 := h1703c.2.2.1
                                      have p1703_3 := h1703c.2.2.2
                                      linarith only [h1650, hlam, p1703_0]
                                    · have p1703_0 := h1703c.1
                                      have p1703_1 := h1703c.2.1
                                      have p1703_2 := h1703c.2.2.1
                                      have p1703_3 := h1703c.2.2.2
                                      linarith only [h1081, h1535, h1538, h1540, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1703_1, u2ehi3]
                                    · have p1703_0 := h1703c.1
                                      have p1703_1 := h1703c.2.1
                                      have p1703_2 := h1703c.2.2.1
                                      have p1703_3 := h1703c.2.2.2
                                      linarith only [h1540, hlam, p1703_0]
                                    · have p1703_0 := h1703c.1
                                      have p1703_1 := h1703c.2.1
                                      have p1703_2 := h1703c.2.2.1
                                      have p1703_3 := h1703c.2.2.2
                                      linarith only [h1535, h1538, h1540, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1703_1, u2ehi3]
                                    · have p1703_0 := h1703c.1
                                      have p1703_1 := h1703c.2.1
                                      have p1703_2 := h1703c.2.2.1
                                      have p1703_3 := h1703c.2.2.2
                                      rcases p1703_3 (m.d 0 4) (by simp) with h1739 | h1739
                                      · linarith only [h1085, h1739, hlam]
                                      · linarith only [h1083, h1739, hlam]
                                    · have p1703_0 := h1703c.1
                                      have p1703_1 := h1703c.2.1
                                      have p1703_2 := h1703c.2.2.1
                                      have p1703_3 := h1703c.2.2.2
                                      linarith only [hlam, p1703_0]
                                  · linarith only [h1702, hlam, p1652_0]
                                · linarith only [h1701, h884, hlam]
                              · linarith only [h1700, h655, hlam]
                            · linarith only [h0, h1699, hlam]
                        · have p1652_0 := h1652c.1
                          have p1652_1 := h1652c.2.1
                          have p1652_2 := h1652c.2.2.1
                          have p1652_3 := h1652c.2.2.2
                          linarith only [h1537, hlam, p1652_0]
                        · have p1652_0 := h1652c.1
                          have p1652_1 := h1652c.2.1
                          have p1652_2 := h1652c.2.2.1
                          have p1652_3 := h1652c.2.2.2
                          linarith only [h1539, hlam, p1652_0]
                        · have p1652_0 := h1652c.1
                          have p1652_1 := h1652c.2.1
                          have p1652_2 := h1652c.2.2.1
                          have p1652_3 := h1652c.2.2.2
                          linarith only [h1540, hlam, p1652_0]
                        · have p1652_0 := h1652c.1
                          have p1652_1 := h1652c.2.1
                          have p1652_2 := h1652c.2.2.1
                          have p1652_3 := h1652c.2.2.2
                          linarith only [hlam, p1652_0]
                · linarith only [h1083, h1085, h1535, h1538, h1540, h1541, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1752 | h1752
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1753 | h1753
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1754 | h1754
                    · linarith only [h1540, h1754, h884, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1756 | h1756
                      · linarith only [h1081, h1540, h1752, h1756, h884, hc23, hlam, hphi, u2ehi3]
                      · rcases h1bigk with h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c | h1758c
                        · have p1758_0 := h1758c.1
                          have p1758_1 := h1758c.2.1
                          have p1758_2 := h1758c.2.2.1
                          have p1758_3 := h1758c.2.2.2
                          linarith only [hlam, p1758_0]
                        · have p1758_0 := h1758c.1
                          have p1758_1 := h1758c.2.1
                          have p1758_2 := h1758c.2.2.1
                          have p1758_3 := h1758c.2.2.2
                          linarith only [h0, hlam, p1758_0]
                        · have p1758_0 := h1758c.1
                          have p1758_1 := h1758c.2.1
                          have p1758_2 := h1758c.2.2.1
                          have p1758_3 := h1758c.2.2.2
                          linarith only [h655, hlam, p1758_0]
                        · have p1758_0 := h1758c.1
                          have p1758_1 := h1758c.2.1
                          have p1758_2 := h1758c.2.2.1
                          have p1758_3 := h1758c.2.2.2
                          linarith only [h884, hlam, p1758_0]
                        · have p1758_0 := h1758c.1
                          have p1758_1 := h1758c.2.1
                          have p1758_2 := h1758c.2.2.1
                          have p1758_3 := h1758c.2.2.2
                          linarith only [h999, hlam, p1758_0]
                        · have p1758_0 := h1758c.1
                          have p1758_1 := h1758c.2.1
                          have p1758_2 := h1758c.2.2.1
                          have p1758_3 := h1758c.2.2.2
                          rcases p1758_3 (m.d 0 1) (by simp) with h1764 | h1764
                          · linarith only [h1764, hlam, p1758_0]
                          · rcases p1758_3 (m.d 1 2) (by simp) with h1766 | h1766
                            · rcases p1758_3 (m.d 1 3) (by simp) with h1767 | h1767
                              · linarith only [h1535, h1767, hlam]
                              · linarith only [h1767, h655, hlam]
                            · linarith only [h1766, hlam, p1758_0]
                        · have p1758_0 := h1758c.1
                          have p1758_1 := h1758c.2.1
                          have p1758_2 := h1758c.2.2.1
                          have p1758_3 := h1758c.2.2.2
                          linarith only [hlam, p1758_0]
                        · have p1758_0 := h1758c.1
                          have p1758_1 := h1758c.2.1
                          have p1758_2 := h1758c.2.2.1
                          have p1758_3 := h1758c.2.2.2
                          linarith only [h655, hc01, hc12, hlam, hphi, p1758_1]
                        · have p1758_0 := h1758c.1
                          have p1758_1 := h1758c.2.1
                          have p1758_2 := h1758c.2.2.1
                          have p1758_3 := h1758c.2.2.2
                          linarith only [h884, hc01, hc12, hlam, hphi, p1758_1]
                        · have p1758_0 := h1758c.1
                          have p1758_1 := h1758c.2.1
                          have p1758_2 := h1758c.2.2.1
                          have p1758_3 := h1758c.2.2.2
                          linarith only [h999, hc01, hc12, hlam, hphi, p1758_1]
                        · have p1758_0 := h1758c.1
                          have p1758_1 := h1758c.2.1
                          have p1758_2 := h1758c.2.2.1
                          have p1758_3 := h1758c.2.2.2
                          rcases p1758_3 (m.d 0 1) (by simp) with h1775 | h1775
                          · linarith only [h1775, hlam, p1758_0]
                          · rcases p1758_3 (m.d 1 2) (by simp) with h1777 | h1777
                            · rcases p1758_3 (m.d 1 3) (by simp) with h1778 | h1778
                              · rcases p1758_3 (m.d 1 4) (by simp) with h1779 | h1779
                                · linarith only [h1538, h1779, hlam]
                                · linarith only [h1779, h884, hlam]
                              · linarith only [h1778, hlam, p1758_0]
                            · linarith only [h0, h1777, hlam]
                        · have p1758_0 := h1758c.1
                          have p1758_1 := h1758c.2.1
                          have p1758_2 := h1758c.2.2.1
                          have p1758_3 := h1758c.2.2.2
                          linarith only [h1535, hlam, p1758_0]
                        · have p1758_0 := h1758c.1
                          have p1758_1 := h1758c.2.1
                          have p1758_2 := h1758c.2.2.1
                          have p1758_3 := h1758c.2.2.2
                          linarith only [hlam, p1758_0]
                        · have p1758_0 := h1758c.1
                          have p1758_1 := h1758c.2.1
                          have p1758_2 := h1758c.2.2.1
                          have p1758_3 := h1758c.2.2.2
                          linarith only [h884, hc01, hc13, hlam, hphi, p1758_1]
                        · have p1758_0 := h1758c.1
                          have p1758_1 := h1758c.2.1
                          have p1758_2 := h1758c.2.2.1
                          have p1758_3 := h1758c.2.2.2
                          linarith only [h1535, h1540, h884, hc01, hc12, hlam, hphi, p1758_1]
                        · have p1758_0 := h1758c.1
                          have p1758_1 := h1758c.2.1
                          have p1758_2 := h1758c.2.2.1
                          have p1758_3 := h1758c.2.2.2
                          linarith only [h1540, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1758_1]
                        · have p1758_0 := h1758c.1
                          have p1758_1 := h1758c.2.1
                          have p1758_2 := h1758c.2.2.1
                          have p1758_3 := h1758c.2.2.2
                          linarith only [h1536, hlam, p1758_0]
                        · have p1758_0 := h1758c.1
                          have p1758_1 := h1758c.2.1
                          have p1758_2 := h1758c.2.2.1
                          have p1758_3 := h1758c.2.2.2
                          linarith only [h1538, hlam, p1758_1]
                        · have p1758_0 := h1758c.1
                          have p1758_1 := h1758c.2.1
                          have p1758_2 := h1758c.2.2.1
                          have p1758_3 := h1758c.2.2.2
                          linarith only [hlam, p1758_0]
                        · have p1758_0 := h1758c.1
                          have p1758_1 := h1758c.2.1
                          have p1758_2 := h1758c.2.2.1
                          have p1758_3 := h1758c.2.2.2
                          linarith only [h1540, hlam, p1758_1]
                        · have p1758_0 := h1758c.1
                          have p1758_1 := h1758c.2.1
                          have p1758_2 := h1758c.2.2.1
                          have p1758_3 := h1758c.2.2.2
                          rcases p1758_3 (m.d 0 1) (by simp) with h1793 | h1793
                          · linarith only [h1793, hlam, p1758_0]
                          · rcases p1758_3 (m.d 1 2) (by simp) with h1795 | h1795
                            · rcases p1758_3 (m.d 1 3) (by simp) with h1796 | h1796
                              · rcases p1758_3 (m.d 1 4) (by simp) with h1797 | h1797
                                · linarith only [h1540, h1797, hlam]
                                · linarith only [h1797, h884, hlam]
                              · linarith only [h1796, h655, hlam]
                            · linarith only [h0, h1795, hlam]
                        · have p1758_0 := h1758c.1
                          have p1758_1 := h1758c.2.1
                          have p1758_2 := h1758c.2.2.1
                          have p1758_3 := h1758c.2.2.2
                          linarith only [h1537, hlam, p1758_0]
                        · have p1758_0 := h1758c.1
                          have p1758_1 := h1758c.2.1
                          have p1758_2 := h1758c.2.2.1
                          have p1758_3 := h1758c.2.2.2
                          linarith only [h1539, hlam, p1758_0]
                        · have p1758_0 := h1758c.1
                          have p1758_1 := h1758c.2.1
                          have p1758_2 := h1758c.2.2.1
                          have p1758_3 := h1758c.2.2.2
                          linarith only [h884, hc01, hc15, hlam, hphi, p1758_1]
                        · have p1758_0 := h1758c.1
                          have p1758_1 := h1758c.2.1
                          have p1758_2 := h1758c.2.2.1
                          have p1758_3 := h1758c.2.2.2
                          linarith only [hlam, p1758_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1806 | h1806
                    · linarith only [h0, h1080, h1084, h1540, h1752, h1753, h1806, h999, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1808 | h1808
                      · linarith only [h1084, h1540, h1752, h1753, h1808, h999, hlam]
                      · rcases h1bigk with h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c | h1810c
                        · have p1810_0 := h1810c.1
                          have p1810_1 := h1810c.2.1
                          have p1810_2 := h1810c.2.2.1
                          have p1810_3 := h1810c.2.2.2
                          linarith only [hlam, p1810_0]
                        · have p1810_0 := h1810c.1
                          have p1810_1 := h1810c.2.1
                          have p1810_2 := h1810c.2.2.1
                          have p1810_3 := h1810c.2.2.2
                          linarith only [h0, hlam, p1810_0]
                        · have p1810_0 := h1810c.1
                          have p1810_1 := h1810c.2.1
                          have p1810_2 := h1810c.2.2.1
                          have p1810_3 := h1810c.2.2.2
                          linarith only [h655, hlam, p1810_0]
                        · have p1810_0 := h1810c.1
                          have p1810_1 := h1810c.2.1
                          have p1810_2 := h1810c.2.2.1
                          have p1810_3 := h1810c.2.2.2
                          linarith only [h884, hlam, p1810_0]
                        · have p1810_0 := h1810c.1
                          have p1810_1 := h1810c.2.1
                          have p1810_2 := h1810c.2.2.1
                          have p1810_3 := h1810c.2.2.2
                          linarith only [h999, hlam, p1810_0]
                        · have p1810_0 := h1810c.1
                          have p1810_1 := h1810c.2.1
                          have p1810_2 := h1810c.2.2.1
                          have p1810_3 := h1810c.2.2.2
                          rcases p1810_3 (m.d 0 1) (by simp) with h1816 | h1816
                          · linarith only [h1816, hlam, p1810_0]
                          · rcases p1810_3 (m.d 1 2) (by simp) with h1818 | h1818
                            · rcases p1810_3 (m.d 1 3) (by simp) with h1819 | h1819
                              · linarith only [h1535, h1819, hlam]
                              · linarith only [h1819, h655, hlam]
                            · linarith only [h1818, hlam, p1810_0]
                        · have p1810_0 := h1810c.1
                          have p1810_1 := h1810c.2.1
                          have p1810_2 := h1810c.2.2.1
                          have p1810_3 := h1810c.2.2.2
                          linarith only [hlam, p1810_0]
                        · have p1810_0 := h1810c.1
                          have p1810_1 := h1810c.2.1
                          have p1810_2 := h1810c.2.2.1
                          have p1810_3 := h1810c.2.2.2
                          linarith only [h655, hc01, hc12, hlam, hphi, p1810_1]
                        · have p1810_0 := h1810c.1
                          have p1810_1 := h1810c.2.1
                          have p1810_2 := h1810c.2.2.1
                          have p1810_3 := h1810c.2.2.2
                          linarith only [h884, hc01, hc12, hlam, hphi, p1810_1]
                        · have p1810_0 := h1810c.1
                          have p1810_1 := h1810c.2.1
                          have p1810_2 := h1810c.2.2.1
                          have p1810_3 := h1810c.2.2.2
                          linarith only [h1084, h1752, h1753, h999, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1810_1, u2ehi3]
                        · have p1810_0 := h1810c.1
                          have p1810_1 := h1810c.2.1
                          have p1810_2 := h1810c.2.2.1
                          have p1810_3 := h1810c.2.2.2
                          rcases p1810_3 (m.d 0 1) (by simp) with h1827 | h1827
                          · linarith only [h1827, hlam, p1810_0]
                          · rcases p1810_3 (m.d 1 2) (by simp) with h1829 | h1829
                            · rcases p1810_3 (m.d 1 3) (by simp) with h1830 | h1830
                              · rcases p1810_3 (m.d 1 4) (by simp) with h1831 | h1831
                                · linarith only [h1538, h1831, hlam]
                                · linarith only [h1831, h884, hlam]
                              · linarith only [h1830, hlam, p1810_0]
                            · linarith only [h0, h1829, hlam]
                        · have p1810_0 := h1810c.1
                          have p1810_1 := h1810c.2.1
                          have p1810_2 := h1810c.2.2.1
                          have p1810_3 := h1810c.2.2.2
                          linarith only [h1535, hlam, p1810_0]
                        · have p1810_0 := h1810c.1
                          have p1810_1 := h1810c.2.1
                          have p1810_2 := h1810c.2.2.1
                          have p1810_3 := h1810c.2.2.2
                          linarith only [hlam, p1810_0]
                        · have p1810_0 := h1810c.1
                          have p1810_1 := h1810c.2.1
                          have p1810_2 := h1810c.2.2.1
                          have p1810_3 := h1810c.2.2.2
                          linarith only [h884, hc01, hc13, hlam, hphi, p1810_1]
                        · have p1810_0 := h1810c.1
                          have p1810_1 := h1810c.2.1
                          have p1810_2 := h1810c.2.2.1
                          have p1810_3 := h1810c.2.2.2
                          linarith only [h1084, h1535, h1752, h1753, h999, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1810_1, u2ehi3]
                        · have p1810_0 := h1810c.1
                          have p1810_1 := h1810c.2.1
                          have p1810_2 := h1810c.2.2.1
                          have p1810_3 := h1810c.2.2.2
                          linarith only [h1540, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1810_1]
                        · have p1810_0 := h1810c.1
                          have p1810_1 := h1810c.2.1
                          have p1810_2 := h1810c.2.2.1
                          have p1810_3 := h1810c.2.2.2
                          linarith only [h1536, hlam, p1810_0]
                        · have p1810_0 := h1810c.1
                          have p1810_1 := h1810c.2.1
                          have p1810_2 := h1810c.2.2.1
                          have p1810_3 := h1810c.2.2.2
                          linarith only [h1538, hlam, p1810_1]
                        · have p1810_0 := h1810c.1
                          have p1810_1 := h1810c.2.1
                          have p1810_2 := h1810c.2.2.1
                          have p1810_3 := h1810c.2.2.2
                          linarith only [hlam, p1810_0]
                        · have p1810_0 := h1810c.1
                          have p1810_1 := h1810c.2.1
                          have p1810_2 := h1810c.2.2.1
                          have p1810_3 := h1810c.2.2.2
                          linarith only [h1540, hlam, p1810_1]
                        · have p1810_0 := h1810c.1
                          have p1810_1 := h1810c.2.1
                          have p1810_2 := h1810c.2.2.1
                          have p1810_3 := h1810c.2.2.2
                          rcases p1810_3 (m.d 0 1) (by simp) with h1845 | h1845
                          · linarith only [h1845, hlam, p1810_0]
                          · rcases p1810_3 (m.d 1 2) (by simp) with h1847 | h1847
                            · rcases p1810_3 (m.d 1 3) (by simp) with h1848 | h1848
                              · rcases p1810_3 (m.d 1 4) (by simp) with h1849 | h1849
                                · linarith only [h1540, h1849, hlam]
                                · linarith only [h1849, h884, hlam]
                              · linarith only [h1848, h655, hlam]
                            · linarith only [h0, h1847, hlam]
                        · have p1810_0 := h1810c.1
                          have p1810_1 := h1810c.2.1
                          have p1810_2 := h1810c.2.2.1
                          have p1810_3 := h1810c.2.2.2
                          linarith only [h1537, hlam, p1810_0]
                        · have p1810_0 := h1810c.1
                          have p1810_1 := h1810c.2.1
                          have p1810_2 := h1810c.2.2.1
                          have p1810_3 := h1810c.2.2.2
                          linarith only [h1539, hlam, p1810_0]
                        · have p1810_0 := h1810c.1
                          have p1810_1 := h1810c.2.1
                          have p1810_2 := h1810c.2.2.1
                          have p1810_3 := h1810c.2.2.2
                          linarith only [h884, hc01, hc15, hlam, hphi, p1810_1]
                        · have p1810_0 := h1810c.1
                          have p1810_1 := h1810c.2.1
                          have p1810_2 := h1810c.2.2.1
                          have p1810_3 := h1810c.2.2.2
                          linarith only [hlam, p1810_0]
                · linarith only [h1083, h1085, h1752, hc45, hlam, hphi, ht23, ht34, u2ehi2]
            · linarith only [h0, h1080, h1084, h1539, h655, hc01, hc12, hlam, hphi]
          · linarith only [h1083, h1084, h1085, h1538, h655, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
        · linarith only [h0, h1080, h1537, hc25, hlam, hphi, u2ehi2]
      · linarith only [h0, h1080, h1536, hc24, hlam, hphi, u2ehi2]
    · linarith only [h0, h1080, h1535, hlam]

end R2N4
