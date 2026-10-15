import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_22S14

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5114000 in
set_option maxHeartbeats 5114000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s4_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 1 2 3 (by decide) (by decide) with h1099 | h1099
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1100 | h1100
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1101 | h1101
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1102 | h1102
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1103 | h1103
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1104 | h1104
            · linarith only [h1104, h9, hc14, hlam, hphi, ht01, u0ehi3]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1106 | h1106
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1107 | h1107
                · linarith only [h0, h1099, h1107, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                · linarith only [h1, h1103, h1106, h1107, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1110 | h1110
                · linarith only [h0, h1099, h1110, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1112 | h1112
                  · linarith only [h0, h1099, h1102, h1106, h1112, h9, hc01, hlam, hphi, u0ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1114 | h1114
                    · linarith only [h0, h1099, h1102, h1114, h9, hc01, hlam, hphi, u0ehi3]
                    · rcases h2bigk with h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c | h1116c
                      · have p1116_0 := h1116c.1
                        have p1116_1 := h1116c.2.1
                        have p1116_2 := h1116c.2.2.1
                        have p1116_3 := h1116c.2.2.2
                        linarith only [hlam, p1116_0]
                      · have p1116_0 := h1116c.1
                        have p1116_1 := h1116c.2.1
                        have p1116_2 := h1116c.2.2.1
                        have p1116_3 := h1116c.2.2.2
                        linarith only [h0, h1099, h1103, h1106, h1114, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1116_1]
                      · have p1116_0 := h1116c.1
                        have p1116_1 := h1116c.2.1
                        have p1116_2 := h1116c.2.2.1
                        have p1116_3 := h1116c.2.2.2
                        rcases p1116_3 (m.d 0 2) (by simp) with h1119 | h1119
                        · rcases p1116_3 (m.d 1 2) (by simp) with h1120 | h1120
                          · linarith only [h0, h1120, hlam]
                          · linarith only [h1099, h1120, hlam]
                        · linarith only [h1119, hlam, p1116_0]
                      · have p1116_0 := h1116c.1
                        have p1116_1 := h1116c.2.1
                        have p1116_2 := h1116c.2.2.1
                        have p1116_3 := h1116c.2.2.2
                        rcases p1116_3 (m.d 0 2) (by simp) with h1124 | h1124
                        · rcases p1116_3 (m.d 1 2) (by simp) with h1125 | h1125
                          · linarith only [h0, h1125, hlam]
                          · linarith only [h1100, h1125, hlam]
                        · linarith only [h1124, hlam, p1116_0]
                      · have p1116_0 := h1116c.1
                        have p1116_1 := h1116c.2.1
                        have p1116_2 := h1116c.2.2.1
                        have p1116_3 := h1116c.2.2.2
                        rcases p1116_3 (m.d 0 2) (by simp) with h1129 | h1129
                        · rcases p1116_3 (m.d 1 2) (by simp) with h1130 | h1130
                          · linarith only [h0, h1130, hlam]
                          · linarith only [h1101, h1130, hlam]
                        · linarith only [h1129, hlam, p1116_0]
                      · have p1116_0 := h1116c.1
                        have p1116_1 := h1116c.2.1
                        have p1116_2 := h1116c.2.2.1
                        have p1116_3 := h1116c.2.2.2
                        linarith only [h0, hlam, p1116_0]
                      · have p1116_0 := h1116c.1
                        have p1116_1 := h1116c.2.1
                        have p1116_2 := h1116c.2.2.1
                        have p1116_3 := h1116c.2.2.2
                        linarith only [hlam, p1116_0]
                      · have p1116_0 := h1116c.1
                        have p1116_1 := h1116c.2.1
                        have p1116_2 := h1116c.2.2.1
                        have p1116_3 := h1116c.2.2.2
                        rcases p1116_3 (m.d 0 2) (by simp) with h1136 | h1136
                        · rcases p1116_3 (m.d 1 2) (by simp) with h1137 | h1137
                          · rcases p1116_3 (m.d 2 3) (by simp) with h1138 | h1138
                            · linarith only [h1138, hlam, p1116_0]
                            · rcases p1116_3 (m.d 2 4) (by simp) with h1140 | h1140
                              · linarith only [h1100, h1140, hlam]
                              · linarith only [h1106, h1140, hlam]
                          · linarith only [h1137, hlam, p1116_0]
                        · linarith only [h1136, h4, hlam]
                      · have p1116_0 := h1116c.1
                        have p1116_1 := h1116c.2.1
                        have p1116_2 := h1116c.2.2.1
                        have p1116_3 := h1116c.2.2.2
                        rcases p1116_3 (m.d 0 2) (by simp) with h1145 | h1145
                        · rcases p1116_3 (m.d 1 2) (by simp) with h1146 | h1146
                          · rcases p1116_3 (m.d 2 3) (by simp) with h1147 | h1147
                            · linarith only [h1099, h1147, hlam]
                            · rcases p1116_3 (m.d 2 4) (by simp) with h1149 | h1149
                              · linarith only [h1149, hlam, p1116_0]
                              · rcases p1116_3 (m.d 2 5) (by simp) with h1151 | h1151
                                · linarith only [h1101, h1151, hlam]
                                · linarith only [h1112, h1151, hlam]
                          · linarith only [h1146, hlam, p1116_0]
                        · linarith only [h1145, h5, hlam]
                      · have p1116_0 := h1116c.1
                        have p1116_1 := h1116c.2.1
                        have p1116_2 := h1116c.2.2.1
                        have p1116_3 := h1116c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p1116_1, u5ehi2]
                      · have p1116_0 := h1116c.1
                        have p1116_1 := h1116c.2.1
                        have p1116_2 := h1116c.2.2.1
                        have p1116_3 := h1116c.2.2.2
                        linarith only [h4, hlam, p1116_0]
                      · have p1116_0 := h1116c.1
                        have p1116_1 := h1116c.2.1
                        have p1116_2 := h1116c.2.2.1
                        have p1116_3 := h1116c.2.2.2
                        linarith only [h1099, hlam, p1116_0]
                      · have p1116_0 := h1116c.1
                        have p1116_1 := h1116c.2.1
                        have p1116_2 := h1116c.2.2.1
                        have p1116_3 := h1116c.2.2.2
                        linarith only [hlam, p1116_0]
                      · have p1116_0 := h1116c.1
                        have p1116_1 := h1116c.2.1
                        have p1116_2 := h1116c.2.2.1
                        have p1116_3 := h1116c.2.2.2
                        linarith only [h1106, hlam, p1116_0]
                      · have p1116_0 := h1116c.1
                        have p1116_1 := h1116c.2.1
                        have p1116_2 := h1116c.2.2.1
                        have p1116_3 := h1116c.2.2.2
                        linarith only [h1110, hlam, p1116_0]
                      · have p1116_0 := h1116c.1
                        have p1116_1 := h1116c.2.1
                        have p1116_2 := h1116c.2.2.1
                        have p1116_3 := h1116c.2.2.2
                        linarith only [h5, hlam, p1116_0]
                      · have p1116_0 := h1116c.1
                        have p1116_1 := h1116c.2.1
                        have p1116_2 := h1116c.2.2.1
                        have p1116_3 := h1116c.2.2.2
                        linarith only [h1100, hlam, p1116_0]
                      · have p1116_0 := h1116c.1
                        have p1116_1 := h1116c.2.1
                        have p1116_2 := h1116c.2.2.1
                        have p1116_3 := h1116c.2.2.2
                        linarith only [h5, h9, hc23, hc45, hlam, hphi, ht34, p1116_1]
                      · have p1116_0 := h1116c.1
                        have p1116_1 := h1116c.2.1
                        have p1116_2 := h1116c.2.2.1
                        have p1116_3 := h1116c.2.2.2
                        linarith only [hlam, p1116_0]
                      · have p1116_0 := h1116c.1
                        have p1116_1 := h1116c.2.1
                        have p1116_2 := h1116c.2.2.1
                        have p1116_3 := h1116c.2.2.2
                        linarith only [h1112, hlam, p1116_1]
                      · have p1116_0 := h1116c.1
                        have p1116_1 := h1116c.2.1
                        have p1116_2 := h1116c.2.2.1
                        have p1116_3 := h1116c.2.2.2
                        linarith only [h6, hlam, p1116_0]
                      · have p1116_0 := h1116c.1
                        have p1116_1 := h1116c.2.1
                        have p1116_2 := h1116c.2.2.1
                        have p1116_3 := h1116c.2.2.2
                        linarith only [h1101, hlam, p1116_0]
                      · have p1116_0 := h1116c.1
                        have p1116_1 := h1116c.2.1
                        have p1116_2 := h1116c.2.2.1
                        have p1116_3 := h1116c.2.2.2
                        linarith only [h0, h1101, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1116_1]
                      · have p1116_0 := h1116c.1
                        have p1116_1 := h1116c.2.1
                        have p1116_2 := h1116c.2.2.1
                        have p1116_3 := h1116c.2.2.2
                        linarith only [h1, h1103, h1110, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1116_1]
                      · have p1116_0 := h1116c.1
                        have p1116_1 := h1116c.2.1
                        have p1116_2 := h1116c.2.2.1
                        have p1116_3 := h1116c.2.2.2
                        linarith only [hlam, p1116_0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1172 | h1172
            · linarith only [h1102, h1103, h1172, h4, h8, h9, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1174 | h1174
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1175 | h1175
                · linarith only [h1099, h1103, h1175, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1177 | h1177
                  · linarith only [h1177, h9, hc24, hlam, hphi, ht01, ht12, u0ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1179 | h1179
                    · linarith only [h1179, h9, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                    · rcases h2bigk with h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c
                      · have p1181_0 := h1181c.1
                        have p1181_1 := h1181c.2.1
                        have p1181_2 := h1181c.2.2.1
                        have p1181_3 := h1181c.2.2.2
                        linarith only [hlam, p1181_0]
                      · have p1181_0 := h1181c.1
                        have p1181_1 := h1181c.2.1
                        have p1181_2 := h1181c.2.2.1
                        have p1181_3 := h1181c.2.2.2
                        linarith only [h0, h1101, hc01, hlam, hphi, ht0b, ht5b, p1181_1, u5ehi2]
                      · have p1181_0 := h1181c.1
                        have p1181_1 := h1181c.2.1
                        have p1181_2 := h1181c.2.2.1
                        have p1181_3 := h1181c.2.2.2
                        rcases p1181_3 (m.d 0 2) (by simp) with h1184 | h1184
                        · rcases p1181_3 (m.d 1 2) (by simp) with h1185 | h1185
                          · linarith only [h0, h1185, hlam]
                          · linarith only [h1099, h1185, hlam]
                        · linarith only [h1184, hlam, p1181_0]
                      · have p1181_0 := h1181c.1
                        have p1181_1 := h1181c.2.1
                        have p1181_2 := h1181c.2.2.1
                        have p1181_3 := h1181c.2.2.2
                        rcases p1181_3 (m.d 0 2) (by simp) with h1189 | h1189
                        · rcases p1181_3 (m.d 1 2) (by simp) with h1190 | h1190
                          · linarith only [h0, h1190, hlam]
                          · linarith only [h1100, h1190, hlam]
                        · linarith only [h1189, hlam, p1181_0]
                      · have p1181_0 := h1181c.1
                        have p1181_1 := h1181c.2.1
                        have p1181_2 := h1181c.2.2.1
                        have p1181_3 := h1181c.2.2.2
                        rcases p1181_3 (m.d 0 2) (by simp) with h1194 | h1194
                        · rcases p1181_3 (m.d 1 2) (by simp) with h1195 | h1195
                          · linarith only [h0, h1195, hlam]
                          · linarith only [h1101, h1195, hlam]
                        · linarith only [h1194, hlam, p1181_0]
                      · have p1181_0 := h1181c.1
                        have p1181_1 := h1181c.2.1
                        have p1181_2 := h1181c.2.2.1
                        have p1181_3 := h1181c.2.2.2
                        linarith only [h0, hlam, p1181_0]
                      · have p1181_0 := h1181c.1
                        have p1181_1 := h1181c.2.1
                        have p1181_2 := h1181c.2.2.1
                        have p1181_3 := h1181c.2.2.2
                        linarith only [hlam, p1181_0]
                      · have p1181_0 := h1181c.1
                        have p1181_1 := h1181c.2.1
                        have p1181_2 := h1181c.2.2.1
                        have p1181_3 := h1181c.2.2.2
                        linarith only [h0, h1174, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1181_1]
                      · have p1181_0 := h1181c.1
                        have p1181_1 := h1181c.2.1
                        have p1181_2 := h1181c.2.2.1
                        have p1181_3 := h1181c.2.2.2
                        rcases p1181_3 (m.d 0 2) (by simp) with h1202 | h1202
                        · rcases p1181_3 (m.d 1 2) (by simp) with h1203 | h1203
                          · rcases p1181_3 (m.d 2 3) (by simp) with h1204 | h1204
                            · linarith only [h1099, h1204, hlam]
                            · linarith only [h1174, h1204, hlam]
                          · linarith only [h1203, hlam, p1181_0]
                        · linarith only [h1202, h5, hlam]
                      · have p1181_0 := h1181c.1
                        have p1181_1 := h1181c.2.1
                        have p1181_2 := h1181c.2.2.1
                        have p1181_3 := h1181c.2.2.2
                        linarith only [h0, h1174, h1175, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1181_1]
                      · have p1181_0 := h1181c.1
                        have p1181_1 := h1181c.2.1
                        have p1181_2 := h1181c.2.2.1
                        have p1181_3 := h1181c.2.2.2
                        linarith only [h4, hlam, p1181_0]
                      · have p1181_0 := h1181c.1
                        have p1181_1 := h1181c.2.1
                        have p1181_2 := h1181c.2.2.1
                        have p1181_3 := h1181c.2.2.2
                        linarith only [h1099, hlam, p1181_0]
                      · have p1181_0 := h1181c.1
                        have p1181_1 := h1181c.2.1
                        have p1181_2 := h1181c.2.2.1
                        have p1181_3 := h1181c.2.2.2
                        linarith only [hlam, p1181_0]
                      · have p1181_0 := h1181c.1
                        have p1181_1 := h1181c.2.1
                        have p1181_2 := h1181c.2.2.1
                        have p1181_3 := h1181c.2.2.2
                        linarith only [h0, h1099, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1181_1]
                      · have p1181_0 := h1181c.1
                        have p1181_1 := h1181c.2.1
                        have p1181_2 := h1181c.2.2.1
                        have p1181_3 := h1181c.2.2.2
                        linarith only [h1175, hlam, p1181_0]
                      · have p1181_0 := h1181c.1
                        have p1181_1 := h1181c.2.1
                        have p1181_2 := h1181c.2.2.1
                        have p1181_3 := h1181c.2.2.2
                        linarith only [h5, hlam, p1181_0]
                      · have p1181_0 := h1181c.1
                        have p1181_1 := h1181c.2.1
                        have p1181_2 := h1181c.2.2.1
                        have p1181_3 := h1181c.2.2.2
                        linarith only [h1100, hlam, p1181_0]
                      · have p1181_0 := h1181c.1
                        have p1181_1 := h1181c.2.1
                        have p1181_2 := h1181c.2.2.1
                        have p1181_3 := h1181c.2.2.2
                        linarith only [h1174, hlam, p1181_1]
                      · have p1181_0 := h1181c.1
                        have p1181_1 := h1181c.2.1
                        have p1181_2 := h1181c.2.2.1
                        have p1181_3 := h1181c.2.2.2
                        linarith only [hlam, p1181_0]
                      · have p1181_0 := h1181c.1
                        have p1181_1 := h1181c.2.1
                        have p1181_2 := h1181c.2.2.1
                        have p1181_3 := h1181c.2.2.2
                        linarith only [h1177, hlam, p1181_1]
                      · have p1181_0 := h1181c.1
                        have p1181_1 := h1181c.2.1
                        have p1181_2 := h1181c.2.2.1
                        have p1181_3 := h1181c.2.2.2
                        linarith only [h6, hlam, p1181_0]
                      · have p1181_0 := h1181c.1
                        have p1181_1 := h1181c.2.1
                        have p1181_2 := h1181c.2.2.1
                        have p1181_3 := h1181c.2.2.2
                        linarith only [h1101, hlam, p1181_0]
                      · have p1181_0 := h1181c.1
                        have p1181_1 := h1181c.2.1
                        have p1181_2 := h1181c.2.2.1
                        have p1181_3 := h1181c.2.2.2
                        linarith only [h0, h1101, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1181_1]
                      · have p1181_0 := h1181c.1
                        have p1181_1 := h1181c.2.1
                        have p1181_2 := h1181c.2.2.1
                        have p1181_3 := h1181c.2.2.2
                        linarith only [h0, h1101, h1174, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1181_1]
                      · have p1181_0 := h1181c.1
                        have p1181_1 := h1181c.2.1
                        have p1181_2 := h1181c.2.2.1
                        have p1181_3 := h1181c.2.2.2
                        linarith only [hlam, p1181_0]
              · linarith only [h0, h1102, h1103, h1174, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1226 | h1226
          · linarith only [h1102, h1226, h7, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1228 | h1228
            · linarith only [h1228, h9, hc14, hlam, hphi, ht01, u0ehi3]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1230 | h1230
              · linarith only [h0, h1099, h1102, h1230, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1232 | h1232
                · linarith only [h0, h1099, h1101, h1102, h1226, h1232, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1234 | h1234
                  · linarith only [h1234, h9, hc24, hlam, hphi, ht01, ht12, u0ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1236 | h1236
                    · linarith only [h1236, h7, h9, hlam]
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
                        linarith only [h0, h1101, hc01, hlam, hphi, ht0b, ht5b, p1238_1, u5ehi2]
                      · have p1238_0 := h1238c.1
                        have p1238_1 := h1238c.2.1
                        have p1238_2 := h1238c.2.2.1
                        have p1238_3 := h1238c.2.2.2
                        rcases p1238_3 (m.d 0 2) (by simp) with h1241 | h1241
                        · rcases p1238_3 (m.d 1 2) (by simp) with h1242 | h1242
                          · linarith only [h0, h1242, hlam]
                          · linarith only [h1099, h1242, hlam]
                        · linarith only [h1241, hlam, p1238_0]
                      · have p1238_0 := h1238c.1
                        have p1238_1 := h1238c.2.1
                        have p1238_2 := h1238c.2.2.1
                        have p1238_3 := h1238c.2.2.2
                        rcases p1238_3 (m.d 0 2) (by simp) with h1246 | h1246
                        · rcases p1238_3 (m.d 1 2) (by simp) with h1247 | h1247
                          · linarith only [h0, h1247, hlam]
                          · linarith only [h1100, h1247, hlam]
                        · linarith only [h1246, hlam, p1238_0]
                      · have p1238_0 := h1238c.1
                        have p1238_1 := h1238c.2.1
                        have p1238_2 := h1238c.2.2.1
                        have p1238_3 := h1238c.2.2.2
                        rcases p1238_3 (m.d 0 2) (by simp) with h1251 | h1251
                        · rcases p1238_3 (m.d 1 2) (by simp) with h1252 | h1252
                          · linarith only [h0, h1252, hlam]
                          · linarith only [h1101, h1252, hlam]
                        · linarith only [h1251, hlam, p1238_0]
                      · have p1238_0 := h1238c.1
                        have p1238_1 := h1238c.2.1
                        have p1238_2 := h1238c.2.2.1
                        have p1238_3 := h1238c.2.2.2
                        linarith only [h0, hlam, p1238_0]
                      · have p1238_0 := h1238c.1
                        have p1238_1 := h1238c.2.1
                        have p1238_2 := h1238c.2.2.1
                        have p1238_3 := h1238c.2.2.2
                        linarith only [hlam, p1238_0]
                      · have p1238_0 := h1238c.1
                        have p1238_1 := h1238c.2.1
                        have p1238_2 := h1238c.2.2.1
                        have p1238_3 := h1238c.2.2.2
                        rcases p1238_3 (m.d 0 2) (by simp) with h1258 | h1258
                        · rcases p1238_3 (m.d 1 2) (by simp) with h1259 | h1259
                          · rcases p1238_3 (m.d 2 3) (by simp) with h1260 | h1260
                            · linarith only [h1260, hlam, p1238_0]
                            · rcases p1238_3 (m.d 2 4) (by simp) with h1262 | h1262
                              · linarith only [h1100, h1262, hlam]
                              · linarith only [h1230, h1262, hlam]
                          · linarith only [h1259, hlam, p1238_0]
                        · linarith only [h1258, h4, hlam]
                      · have p1238_0 := h1238c.1
                        have p1238_1 := h1238c.2.1
                        have p1238_2 := h1238c.2.2.1
                        have p1238_3 := h1238c.2.2.2
                        rcases p1238_3 (m.d 0 2) (by simp) with h1267 | h1267
                        · rcases p1238_3 (m.d 1 2) (by simp) with h1268 | h1268
                          · rcases p1238_3 (m.d 2 3) (by simp) with h1269 | h1269
                            · linarith only [h1099, h1269, hlam]
                            · rcases p1238_3 (m.d 2 4) (by simp) with h1271 | h1271
                              · linarith only [h1271, hlam, p1238_0]
                              · rcases p1238_3 (m.d 2 5) (by simp) with h1273 | h1273
                                · linarith only [h1101, h1273, hlam]
                                · linarith only [h1234, h1273, hlam]
                          · linarith only [h1268, hlam, p1238_0]
                        · linarith only [h1267, h5, hlam]
                      · have p1238_0 := h1238c.1
                        have p1238_1 := h1238c.2.1
                        have p1238_2 := h1238c.2.2.1
                        have p1238_3 := h1238c.2.2.2
                        linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p1238_1, u5ehi2]
                      · have p1238_0 := h1238c.1
                        have p1238_1 := h1238c.2.1
                        have p1238_2 := h1238c.2.2.1
                        have p1238_3 := h1238c.2.2.2
                        linarith only [h4, hlam, p1238_0]
                      · have p1238_0 := h1238c.1
                        have p1238_1 := h1238c.2.1
                        have p1238_2 := h1238c.2.2.1
                        have p1238_3 := h1238c.2.2.2
                        linarith only [h1099, hlam, p1238_0]
                      · have p1238_0 := h1238c.1
                        have p1238_1 := h1238c.2.1
                        have p1238_2 := h1238c.2.2.1
                        have p1238_3 := h1238c.2.2.2
                        linarith only [hlam, p1238_0]
                      · have p1238_0 := h1238c.1
                        have p1238_1 := h1238c.2.1
                        have p1238_2 := h1238c.2.2.1
                        have p1238_3 := h1238c.2.2.2
                        linarith only [h1230, hlam, p1238_0]
                      · have p1238_0 := h1238c.1
                        have p1238_1 := h1238c.2.1
                        have p1238_2 := h1238c.2.2.1
                        have p1238_3 := h1238c.2.2.2
                        linarith only [h1232, hlam, p1238_0]
                      · have p1238_0 := h1238c.1
                        have p1238_1 := h1238c.2.1
                        have p1238_2 := h1238c.2.2.1
                        have p1238_3 := h1238c.2.2.2
                        linarith only [h5, hlam, p1238_0]
                      · have p1238_0 := h1238c.1
                        have p1238_1 := h1238c.2.1
                        have p1238_2 := h1238c.2.2.1
                        have p1238_3 := h1238c.2.2.2
                        linarith only [h1100, hlam, p1238_0]
                      · have p1238_0 := h1238c.1
                        have p1238_1 := h1238c.2.1
                        have p1238_2 := h1238c.2.2.1
                        have p1238_3 := h1238c.2.2.2
                        linarith only [h5, h9, hc23, hc45, hlam, hphi, ht34, p1238_1]
                      · have p1238_0 := h1238c.1
                        have p1238_1 := h1238c.2.1
                        have p1238_2 := h1238c.2.2.1
                        have p1238_3 := h1238c.2.2.2
                        linarith only [hlam, p1238_0]
                      · have p1238_0 := h1238c.1
                        have p1238_1 := h1238c.2.1
                        have p1238_2 := h1238c.2.2.1
                        have p1238_3 := h1238c.2.2.2
                        linarith only [h1234, hlam, p1238_1]
                      · have p1238_0 := h1238c.1
                        have p1238_1 := h1238c.2.1
                        have p1238_2 := h1238c.2.2.1
                        have p1238_3 := h1238c.2.2.2
                        linarith only [h6, hlam, p1238_0]
                      · have p1238_0 := h1238c.1
                        have p1238_1 := h1238c.2.1
                        have p1238_2 := h1238c.2.2.1
                        have p1238_3 := h1238c.2.2.2
                        linarith only [h1101, hlam, p1238_0]
                      · have p1238_0 := h1238c.1
                        have p1238_1 := h1238c.2.1
                        have p1238_2 := h1238c.2.2.1
                        have p1238_3 := h1238c.2.2.2
                        linarith only [h0, h1101, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1238_1]
                      · have p1238_0 := h1238c.1
                        have p1238_1 := h1238c.2.1
                        have p1238_2 := h1238c.2.2.1
                        have p1238_3 := h1238c.2.2.2
                        linarith only [h0, h1101, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1238_1]
                      · have p1238_0 := h1238c.1
                        have p1238_1 := h1238c.2.1
                        have p1238_2 := h1238c.2.2.1
                        have p1238_3 := h1238c.2.2.2
                        linarith only [hlam, p1238_0]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1294 | h1294
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1295 | h1295
          · linarith only [h0, h1099, h1101, h1295, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1297 | h1297
            · linarith only [h0, h1099, h1101, h1294, h1297, h6, h9, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1299 | h1299
              · linarith only [h0, h1099, h1101, h1299, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h1099, h1101, h1294, h1299, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1302 | h1302
          · linarith only [h1294, h1302, h7, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1304 | h1304
            · linarith only [h1304, h9, hc14, hlam, hphi, ht01, u0ehi3]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1306 | h1306
              · linarith only [h1099, h1101, h1294, h1306, h6, h8, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1308 | h1308
                · linarith only [h1099, h1101, h1302, h1308, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1310 | h1310
                  · linarith only [h0, h1100, h1101, h1308, h1310, h4, h8, h9, hc01, hlam, hphi, u0ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1312 | h1312
                    · linarith only [h1312, h9, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                    · rcases h2bigk with h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [hlam, p1314_0]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        rcases p1314_3 (m.d 0 2) (by simp) with h1316 | h1316
                        · rcases p1314_3 (m.d 1 2) (by simp) with h1317 | h1317
                          · linarith only [h0, h1317, hlam]
                          · rcases p1314_3 (m.d 2 3) (by simp) with h1319 | h1319
                            · linarith only [h1319, h4, hlam]
                            · rcases p1314_3 (m.d 2 4) (by simp) with h1321 | h1321
                              · linarith only [h1321, h5, hlam]
                              · rcases p1314_3 (m.d 2 5) (by simp) with h1323 | h1323
                                · linarith only [h1323, h6, hlam]
                                · linarith only [h1101, h1323, hlam]
                        · linarith only [h0, h1316, hlam]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [h1100, h1101, h1306, h1308, h4, h8, hlam, p1314_2]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [h1100, h1101, h1308, h4, h8, hlam, p1314_2]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [h0, h1100, h1101, h1306, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1314_1]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [h0, hlam, p1314_0]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [hlam, p1314_0]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [h0, h1101, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1314_1]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [h0, h1101, h1306, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1314_1]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [h1101, hlam, p1314_0]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [h4, hlam, p1314_0]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [h1099, hlam, p1314_0]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [hlam, p1314_0]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [h1306, hlam, p1314_0]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [h1308, hlam, p1314_0]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [h5, hlam, p1314_0]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [h1100, hlam, p1314_0]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [h5, h9, hc23, hc45, hlam, hphi, ht34, p1314_1]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [hlam, p1314_0]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [h1310, hlam, p1314_1]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [h6, hlam, p1314_0]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [h0, h1099, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1314_1]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        rcases p1314_3 (m.d 0 2) (by simp) with h1347 | h1347
                        · rcases p1314_3 (m.d 1 2) (by simp) with h1348 | h1348
                          · linarith only [h1101, h1348, hlam]
                          · linarith only [h1099, h1348, hlam]
                        · linarith only [h1347, h4, hlam]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        rcases p1314_3 (m.d 0 2) (by simp) with h1352 | h1352
                        · rcases p1314_3 (m.d 1 2) (by simp) with h1353 | h1353
                          · linarith only [h1101, h1353, hlam]
                          · linarith only [h1100, h1353, hlam]
                        · linarith only [h1352, h5, hlam]
                      · have p1314_0 := h1314c.1
                        have p1314_1 := h1314c.2.1
                        have p1314_2 := h1314c.2.2.1
                        have p1314_3 := h1314c.2.2.2
                        linarith only [hlam, p1314_0]
    · linarith only [h1099, h1100, h5, h9, hc23, hc45, hlam, hphi, ht34]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1359 | h1359
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1360 | h1360
      · linarith only [h0, h1099, h1360, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1362 | h1362
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1363 | h1363
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1364 | h1364
            · linarith only [h0, h1099, h1359, h1364, h4, h9, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1366 | h1366
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1367 | h1367
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1368 | h1368
                  · linarith only [h0, h1359, h1360, h1367, h1368, h4, h9, hc01, hlam, hphi, u0ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1370 | h1370
                    · linarith only [h0, h1359, h1360, h1366, h1367, h1370, h4, h9, hc01, hlam, hphi, u0ehi3]
                    · rcases h2bigk with h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c
                      · have p1372_0 := h1372c.1
                        have p1372_1 := h1372c.2.1
                        have p1372_2 := h1372c.2.2.1
                        have p1372_3 := h1372c.2.2.2
                        linarith only [hlam, p1372_0]
                      · have p1372_0 := h1372c.1
                        have p1372_1 := h1372c.2.1
                        have p1372_2 := h1372c.2.2.1
                        have p1372_3 := h1372c.2.2.2
                        rcases p1372_3 (m.d 0 2) (by simp) with h1374 | h1374
                        · rcases p1372_3 (m.d 1 2) (by simp) with h1375 | h1375
                          · linarith only [h0, h1375, hlam]
                          · rcases p1372_3 (m.d 2 3) (by simp) with h1377 | h1377
                            · linarith only [h1377, h4, hlam]
                            · linarith only [h1099, h1377, hlam]
                        · linarith only [h0, h1374, hlam]
                      · have p1372_0 := h1372c.1
                        have p1372_1 := h1372c.2.1
                        have p1372_2 := h1372c.2.2.1
                        have p1372_3 := h1372c.2.2.2
                        linarith only [h0, h1359, h1360, h1367, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1372_1]
                      · have p1372_0 := h1372c.1
                        have p1372_1 := h1372c.2.1
                        have p1372_2 := h1372c.2.2.1
                        have p1372_3 := h1372c.2.2.2
                        linarith only [h1359, h1360, h1367, h4, hlam, p1372_2]
                      · have p1372_0 := h1372c.1
                        have p1372_1 := h1372c.2.1
                        have p1372_2 := h1372c.2.2.1
                        have p1372_3 := h1372c.2.2.2
                        linarith only [h1359, h1360, h1366, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1372_1]
                      · have p1372_0 := h1372c.1
                        have p1372_1 := h1372c.2.1
                        have p1372_2 := h1372c.2.2.1
                        have p1372_3 := h1372c.2.2.2
                        linarith only [h0, hlam, p1372_0]
                      · have p1372_0 := h1372c.1
                        have p1372_1 := h1372c.2.1
                        have p1372_2 := h1372c.2.2.1
                        have p1372_3 := h1372c.2.2.2
                        linarith only [hlam, p1372_0]
                      · have p1372_0 := h1372c.1
                        have p1372_1 := h1372c.2.1
                        have p1372_2 := h1372c.2.2.1
                        have p1372_3 := h1372c.2.2.2
                        linarith only [h1099, hlam, p1372_0]
                      · have p1372_0 := h1372c.1
                        have p1372_1 := h1372c.2.1
                        have p1372_2 := h1372c.2.2.1
                        have p1372_3 := h1372c.2.2.2
                        linarith only [h0, h1360, h1366, h1367, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1372_1]
                      · have p1372_0 := h1372c.1
                        have p1372_1 := h1372c.2.1
                        have p1372_2 := h1372c.2.2.1
                        have p1372_3 := h1372c.2.2.2
                        linarith only [h1360, hlam, p1372_0]
                      · have p1372_0 := h1372c.1
                        have p1372_1 := h1372c.2.1
                        have p1372_2 := h1372c.2.2.1
                        have p1372_3 := h1372c.2.2.2
                        linarith only [h4, hlam, p1372_0]
                      · have p1372_0 := h1372c.1
                        have p1372_1 := h1372c.2.1
                        have p1372_2 := h1372c.2.2.1
                        have p1372_3 := h1372c.2.2.2
                        linarith only [h0, h1359, h1366, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1372_1]
                      · have p1372_0 := h1372c.1
                        have p1372_1 := h1372c.2.1
                        have p1372_2 := h1372c.2.2.1
                        have p1372_3 := h1372c.2.2.2
                        linarith only [hlam, p1372_0]
                      · have p1372_0 := h1372c.1
                        have p1372_1 := h1372c.2.1
                        have p1372_2 := h1372c.2.2.1
                        have p1372_3 := h1372c.2.2.2
                        rcases p1372_3 (m.d 0 2) (by simp) with h1392 | h1392
                        · rcases p1372_3 (m.d 1 2) (by simp) with h1393 | h1393
                          · linarith only [h1099, h1393, hlam]
                          · linarith only [h1359, h1393, hlam]
                        · linarith only [h1392, h5, hlam]
                      · have p1372_0 := h1372c.1
                        have p1372_1 := h1372c.2.1
                        have p1372_2 := h1372c.2.2.1
                        have p1372_3 := h1372c.2.2.2
                        linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, p1372_1, u5ehi2]
                      · have p1372_0 := h1372c.1
                        have p1372_1 := h1372c.2.1
                        have p1372_2 := h1372c.2.2.1
                        have p1372_3 := h1372c.2.2.2
                        linarith only [h5, hlam, p1372_0]
                      · have p1372_0 := h1372c.1
                        have p1372_1 := h1372c.2.1
                        have p1372_2 := h1372c.2.2.1
                        have p1372_3 := h1372c.2.2.2
                        linarith only [h1359, hlam, p1372_0]
                      · have p1372_0 := h1372c.1
                        have p1372_1 := h1372c.2.1
                        have p1372_2 := h1372c.2.2.1
                        have p1372_3 := h1372c.2.2.2
                        linarith only [h1366, hlam, p1372_1]
                      · have p1372_0 := h1372c.1
                        have p1372_1 := h1372c.2.1
                        have p1372_2 := h1372c.2.2.1
                        have p1372_3 := h1372c.2.2.2
                        linarith only [hlam, p1372_0]
                      · have p1372_0 := h1372c.1
                        have p1372_1 := h1372c.2.1
                        have p1372_2 := h1372c.2.2.1
                        have p1372_3 := h1372c.2.2.2
                        linarith only [h1368, hlam, p1372_1]
                      · have p1372_0 := h1372c.1
                        have p1372_1 := h1372c.2.1
                        have p1372_2 := h1372c.2.2.1
                        have p1372_3 := h1372c.2.2.2
                        linarith only [h6, hlam, p1372_0]
                      · have p1372_0 := h1372c.1
                        have p1372_1 := h1372c.2.1
                        have p1372_2 := h1372c.2.2.1
                        have p1372_3 := h1372c.2.2.2
                        linarith only [h0, h1359, h1366, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1372_1]
                      · have p1372_0 := h1372c.1
                        have p1372_1 := h1372c.2.1
                        have p1372_2 := h1372c.2.2.1
                        have p1372_3 := h1372c.2.2.2
                        linarith only [h1367, hlam, p1372_1]
                      · have p1372_0 := h1372c.1
                        have p1372_1 := h1372c.2.1
                        have p1372_2 := h1372c.2.2.1
                        have p1372_3 := h1372c.2.2.2
                        rcases p1372_3 (m.d 0 2) (by simp) with h1406 | h1406
                        · rcases p1372_3 (m.d 1 2) (by simp) with h1407 | h1407
                          · linarith only [h1360, h1407, hlam]
                          · linarith only [h1359, h1407, hlam]
                        · linarith only [h1406, h5, hlam]
                      · have p1372_0 := h1372c.1
                        have p1372_1 := h1372c.2.1
                        have p1372_2 := h1372c.2.2.1
                        have p1372_3 := h1372c.2.2.2
                        linarith only [hlam, p1372_0]
                · linarith only [h0, h1099, h1359, h1366, h1367, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h1099, h1363, h1366, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1414 | h1414
            · linarith only [h1359, h1414, h9, hc12, hlam, hphi, ht01, u0ehi3]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1416 | h1416
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1417 | h1417
                · linarith only [h0, h1099, h1359, h1363, h1417, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h1099, h1359, h1416, h1417, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h1099, h1359, h1416, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h1099, h1359, h1362, h7, h9, hc24, hc45, hlam, hphi]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1422 | h1422
      · linarith only [h0, h1359, h1422, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1424 | h1424
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1425 | h1425
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1426 | h1426
            · linarith only [h1426, h9, hc14, hlam, hphi, ht01, u0ehi3]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1428 | h1428
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1429 | h1429
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1430 | h1430
                  · linarith only [h1430, h5, h9, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1432 | h1432
                    · linarith only [h1424, h1432, h9, hc14, hlam, hphi, ht01, u0ehi3]
                    · rcases h2bigk with h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c | h1434c
                      · have p1434_0 := h1434c.1
                        have p1434_1 := h1434c.2.1
                        have p1434_2 := h1434c.2.2.1
                        have p1434_3 := h1434c.2.2.2
                        linarith only [hlam, p1434_0]
                      · have p1434_0 := h1434c.1
                        have p1434_1 := h1434c.2.1
                        have p1434_2 := h1434c.2.2.1
                        have p1434_3 := h1434c.2.2.2
                        rcases p1434_3 (m.d 0 2) (by simp) with h1436 | h1436
                        · rcases p1434_3 (m.d 1 2) (by simp) with h1437 | h1437
                          · linarith only [h0, h1437, hlam]
                          · rcases p1434_3 (m.d 2 3) (by simp) with h1439 | h1439
                            · linarith only [h1439, h4, hlam]
                            · linarith only [h1099, h1439, hlam]
                        · linarith only [h0, h1436, hlam]
                      · have p1434_0 := h1434c.1
                        have p1434_1 := h1434c.2.1
                        have p1434_2 := h1434c.2.2.1
                        have p1434_3 := h1434c.2.2.2
                        linarith only [h0, h1099, h1425, hc01, hlam, hphi, ht0b, ht5b, p1434_1, u5ehi3]
                      · have p1434_0 := h1434c.1
                        have p1434_1 := h1434c.2.1
                        have p1434_2 := h1434c.2.2.1
                        have p1434_3 := h1434c.2.2.2
                        rcases p1434_3 (m.d 0 2) (by simp) with h1444 | h1444
                        · rcases p1434_3 (m.d 1 2) (by simp) with h1445 | h1445
                          · linarith only [h0, h1445, hlam]
                          · rcases p1434_3 (m.d 2 3) (by simp) with h1447 | h1447
                            · linarith only [h1447, h4, hlam]
                            · linarith only [h1428, h1447, hlam]
                        · linarith only [h1444, hlam, p1434_0]
                      · have p1434_0 := h1434c.1
                        have p1434_1 := h1434c.2.1
                        have p1434_2 := h1434c.2.2.1
                        have p1434_3 := h1434c.2.2.2
                        rcases p1434_3 (m.d 0 2) (by simp) with h1451 | h1451
                        · rcases p1434_3 (m.d 1 2) (by simp) with h1452 | h1452
                          · linarith only [h0, h1452, hlam]
                          · rcases p1434_3 (m.d 2 3) (by simp) with h1454 | h1454
                            · linarith only [h1454, h4, hlam]
                            · linarith only [h1429, h1454, hlam]
                        · linarith only [h1451, hlam, p1434_0]
                      · have p1434_0 := h1434c.1
                        have p1434_1 := h1434c.2.1
                        have p1434_2 := h1434c.2.2.1
                        have p1434_3 := h1434c.2.2.2
                        linarith only [h0, hlam, p1434_0]
                      · have p1434_0 := h1434c.1
                        have p1434_1 := h1434c.2.1
                        have p1434_2 := h1434c.2.2.1
                        have p1434_3 := h1434c.2.2.2
                        linarith only [hlam, p1434_0]
                      · have p1434_0 := h1434c.1
                        have p1434_1 := h1434c.2.1
                        have p1434_2 := h1434c.2.2.1
                        have p1434_3 := h1434c.2.2.2
                        linarith only [h1099, hlam, p1434_0]
                      · have p1434_0 := h1434c.1
                        have p1434_1 := h1434c.2.1
                        have p1434_2 := h1434c.2.2.1
                        have p1434_3 := h1434c.2.2.2
                        linarith only [h1359, hlam, p1434_0]
                      · have p1434_0 := h1434c.1
                        have p1434_1 := h1434c.2.1
                        have p1434_2 := h1434c.2.2.1
                        have p1434_3 := h1434c.2.2.2
                        linarith only [h1422, hlam, p1434_0]
                      · have p1434_0 := h1434c.1
                        have p1434_1 := h1434c.2.1
                        have p1434_2 := h1434c.2.2.1
                        have p1434_3 := h1434c.2.2.2
                        linarith only [h4, hlam, p1434_0]
                      · have p1434_0 := h1434c.1
                        have p1434_1 := h1434c.2.1
                        have p1434_2 := h1434c.2.2.1
                        have p1434_3 := h1434c.2.2.2
                        rcases p1434_3 (m.d 0 2) (by simp) with h1464 | h1464
                        · rcases p1434_3 (m.d 1 2) (by simp) with h1465 | h1465
                          · linarith only [h1465, hlam, p1434_0]
                          · rcases p1434_3 (m.d 2 3) (by simp) with h1467 | h1467
                            · rcases p1434_3 (m.d 2 4) (by simp) with h1468 | h1468
                              · linarith only [h1428, h1468, hlam]
                              · linarith only [h1359, h1468, hlam]
                            · linarith only [h1467, hlam, p1434_0]
                        · linarith only [h0, h1464, hlam]
                      · have p1434_0 := h1434c.1
                        have p1434_1 := h1434c.2.1
                        have p1434_2 := h1434c.2.2.1
                        have p1434_3 := h1434c.2.2.2
                        linarith only [hlam, p1434_0]
                      · have p1434_0 := h1434c.1
                        have p1434_1 := h1434c.2.1
                        have p1434_2 := h1434c.2.2.1
                        have p1434_3 := h1434c.2.2.2
                        linarith only [h1359, hc12, hc23, hlam, hphi, p1434_1]
                      · have p1434_0 := h1434c.1
                        have p1434_1 := h1434c.2.1
                        have p1434_2 := h1434c.2.2.1
                        have p1434_3 := h1434c.2.2.2
                        linarith only [h0, h1359, h1430, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1434_1]
                      · have p1434_0 := h1434c.1
                        have p1434_1 := h1434c.2.1
                        have p1434_2 := h1434c.2.2.1
                        have p1434_3 := h1434c.2.2.2
                        linarith only [h5, hlam, p1434_0]
                      · have p1434_0 := h1434c.1
                        have p1434_1 := h1434c.2.1
                        have p1434_2 := h1434c.2.2.1
                        have p1434_3 := h1434c.2.2.2
                        linarith only [h5, h9, hc12, hc45, hlam, hphi, ht23, ht34, p1434_1]
                      · have p1434_0 := h1434c.1
                        have p1434_1 := h1434c.2.1
                        have p1434_2 := h1434c.2.2.1
                        have p1434_3 := h1434c.2.2.2
                        linarith only [h1428, hlam, p1434_1]
                      · have p1434_0 := h1434c.1
                        have p1434_1 := h1434c.2.1
                        have p1434_2 := h1434c.2.2.1
                        have p1434_3 := h1434c.2.2.2
                        linarith only [hlam, p1434_0]
                      · have p1434_0 := h1434c.1
                        have p1434_1 := h1434c.2.1
                        have p1434_2 := h1434c.2.2.1
                        have p1434_3 := h1434c.2.2.2
                        linarith only [h1430, hlam, p1434_1]
                      · have p1434_0 := h1434c.1
                        have p1434_1 := h1434c.2.1
                        have p1434_2 := h1434c.2.2.1
                        have p1434_3 := h1434c.2.2.2
                        linarith only [h6, hlam, p1434_0]
                      · have p1434_0 := h1434c.1
                        have p1434_1 := h1434c.2.1
                        have p1434_2 := h1434c.2.2.1
                        have p1434_3 := h1434c.2.2.2
                        rcases p1434_3 (m.d 0 2) (by simp) with h1482 | h1482
                        · rcases p1434_3 (m.d 1 2) (by simp) with h1483 | h1483
                          · linarith only [h1483, hlam, p1434_0]
                          · rcases p1434_3 (m.d 2 3) (by simp) with h1485 | h1485
                            · rcases p1434_3 (m.d 2 4) (by simp) with h1486 | h1486
                              · linarith only [h1430, h1486, hlam]
                              · linarith only [h1359, h1486, hlam]
                            · linarith only [h1099, h1485, hlam]
                        · linarith only [h0, h1482, hlam]
                      · have p1434_0 := h1434c.1
                        have p1434_1 := h1434c.2.1
                        have p1434_2 := h1434c.2.2.1
                        have p1434_3 := h1434c.2.2.2
                        linarith only [h1429, hlam, p1434_1]
                      · have p1434_0 := h1434c.1
                        have p1434_1 := h1434c.2.1
                        have p1434_2 := h1434c.2.2.1
                        have p1434_3 := h1434c.2.2.2
                        linarith only [h1359, hc12, hc25, hlam, hphi, p1434_1]
                      · have p1434_0 := h1434c.1
                        have p1434_1 := h1434c.2.1
                        have p1434_2 := h1434c.2.2.1
                        have p1434_3 := h1434c.2.2.2
                        linarith only [hlam, p1434_0]
                · linarith only [h1099, h1425, h1429, hlam]
              · linarith only [h1099, h1424, h1428, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1496 | h1496
            · linarith only [h1359, h1496, h9, hc24, hlam, hphi, ht01, ht12, u0ehi3]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1498 | h1498
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1499 | h1499
                · linarith only [h0, h1424, h1425, h1499, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1501 | h1501
                  · linarith only [h0, h1498, h1499, h1501, h4, h8, h9, hc01, hlam, hphi, u0ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1503 | h1503
                    · linarith only [h1424, h1503, h9, hc13, hlam, hphi, ht01, u0ehi3]
                    · rcases h2bigk with h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c
                      · have p1505_0 := h1505c.1
                        have p1505_1 := h1505c.2.1
                        have p1505_2 := h1505c.2.2.1
                        have p1505_3 := h1505c.2.2.2
                        linarith only [hlam, p1505_0]
                      · have p1505_0 := h1505c.1
                        have p1505_1 := h1505c.2.1
                        have p1505_2 := h1505c.2.2.1
                        have p1505_3 := h1505c.2.2.2
                        linarith only [h1359, h1498, h1499, h4, h8, hlam, p1505_2]
                      · have p1505_0 := h1505c.1
                        have p1505_1 := h1505c.2.1
                        have p1505_2 := h1505c.2.2.1
                        have p1505_3 := h1505c.2.2.2
                        rcases p1505_3 (m.d 0 2) (by simp) with h1508 | h1508
                        · rcases p1505_3 (m.d 1 2) (by simp) with h1509 | h1509
                          · linarith only [h0, h1509, hlam]
                          · rcases p1505_3 (m.d 2 3) (by simp) with h1511 | h1511
                            · linarith only [h1511, hlam, p1505_0]
                            · rcases p1505_3 (m.d 2 4) (by simp) with h1513 | h1513
                              · linarith only [h1513, h5, hlam]
                              · rcases p1505_3 (m.d 2 5) (by simp) with h1515 | h1515
                                · linarith only [h1515, h6, hlam]
                                · linarith only [h1499, h1515, hlam]
                        · linarith only [h1508, hlam, p1505_0]
                      · have p1505_0 := h1505c.1
                        have p1505_1 := h1505c.2.1
                        have p1505_2 := h1505c.2.2.1
                        have p1505_3 := h1505c.2.2.2
                        rcases p1505_3 (m.d 0 2) (by simp) with h1519 | h1519
                        · rcases p1505_3 (m.d 1 2) (by simp) with h1520 | h1520
                          · linarith only [h0, h1520, hlam]
                          · rcases p1505_3 (m.d 2 3) (by simp) with h1522 | h1522
                            · linarith only [h1522, h4, hlam]
                            · linarith only [h1498, h1522, hlam]
                        · linarith only [h1519, hlam, p1505_0]
                      · have p1505_0 := h1505c.1
                        have p1505_1 := h1505c.2.1
                        have p1505_2 := h1505c.2.2.1
                        have p1505_3 := h1505c.2.2.2
                        rcases p1505_3 (m.d 0 2) (by simp) with h1526 | h1526
                        · rcases p1505_3 (m.d 1 2) (by simp) with h1527 | h1527
                          · linarith only [h0, h1527, hlam]
                          · rcases p1505_3 (m.d 2 3) (by simp) with h1529 | h1529
                            · linarith only [h1529, h4, hlam]
                            · rcases p1505_3 (m.d 2 4) (by simp) with h1531 | h1531
                              · linarith only [h1531, h5, hlam]
                              · rcases p1505_3 (m.d 2 5) (by simp) with h1533 | h1533
                                · linarith only [h1533, hlam, p1505_0]
                                · rcases h3bigk with h1535c | h1535c | h1535c | h1535c | h1535c | h1535c | h1535c | h1535c | h1535c | h1535c | h1535c | h1535c | h1535c | h1535c | h1535c | h1535c | h1535c | h1535c | h1535c | h1535c | h1535c | h1535c | h1535c | h1535c | h1535c
                                  · have p1535_0 := h1535c.1
                                    have p1535_1 := h1535c.2.1
                                    have p1535_2 := h1535c.2.2.1
                                    have p1535_3 := h1535c.2.2.2
                                    linarith only [hlam, p1535_0]
                                  · have p1535_0 := h1535c.1
                                    have p1535_1 := h1535c.2.1
                                    have p1535_2 := h1535c.2.2.1
                                    have p1535_3 := h1535c.2.2.2
                                    rcases p1535_3 (m.d 0 3) (by simp) with h1537 | h1537
                                    · rcases p1535_3 (m.d 1 3) (by simp) with h1538 | h1538
                                      · linarith only [h1, h1538, hlam]
                                      · rcases p1535_3 (m.d 2 3) (by simp) with h1540 | h1540
                                        · linarith only [h1540, h4, hlam]
                                        · linarith only [h1099, h1540, hlam]
                                    · linarith only [h1, h1537, hlam]
                                  · have p1535_0 := h1535c.1
                                    have p1535_1 := h1535c.2.1
                                    have p1535_2 := h1535c.2.2.1
                                    have p1535_3 := h1535c.2.2.2
                                    rcases p1535_3 (m.d 0 3) (by simp) with h1544 | h1544
                                    · rcases p1535_3 (m.d 1 3) (by simp) with h1545 | h1545
                                      · linarith only [h1, h1545, hlam]
                                      · rcases p1535_3 (m.d 2 3) (by simp) with h1547 | h1547
                                        · linarith only [h1547, h4, hlam]
                                        · rcases p1535_3 (m.d 3 4) (by simp) with h1549 | h1549
                                          · linarith only [h1549, h7, hlam]
                                          · rcases p1535_3 (m.d 3 5) (by simp) with h1551 | h1551
                                            · linarith only [h1551, h8, hlam]
                                            · linarith only [h1499, h1551, hlam]
                                    · linarith only [h1544, h4, hlam]
                                  · have p1535_0 := h1535c.1
                                    have p1535_1 := h1535c.2.1
                                    have p1535_2 := h1535c.2.2.1
                                    have p1535_3 := h1535c.2.2.2
                                    linarith only [h1099, h1424, h1499, h8, hlam, p1535_2]
                                  · have p1535_0 := h1535c.1
                                    have p1535_1 := h1535c.2.1
                                    have p1535_2 := h1535c.2.2.1
                                    have p1535_3 := h1535c.2.2.2
                                    linarith only [h0, h1359, h1498, h1499, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1535_1]
                                  · have p1535_0 := h1535c.1
                                    have p1535_1 := h1535c.2.1
                                    have p1535_2 := h1535c.2.2.1
                                    have p1535_3 := h1535c.2.2.2
                                    linarith only [h1, hlam, p1535_0]
                                  · have p1535_0 := h1535c.1
                                    have p1535_1 := h1535c.2.1
                                    have p1535_2 := h1535c.2.2.1
                                    have p1535_3 := h1535c.2.2.2
                                    linarith only [hlam, p1535_0]
                                  · have p1535_0 := h1535c.1
                                    have p1535_1 := h1535c.2.1
                                    have p1535_2 := h1535c.2.2.1
                                    have p1535_3 := h1535c.2.2.2
                                    linarith only [h1099, hlam, p1535_1]
                                  · have p1535_0 := h1535c.1
                                    have p1535_1 := h1535c.2.1
                                    have p1535_2 := h1535c.2.2.1
                                    have p1535_3 := h1535c.2.2.2
                                    linarith only [h0, h1099, h1499, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1535_1]
                                  · have p1535_0 := h1535c.1
                                    have p1535_1 := h1535c.2.1
                                    have p1535_2 := h1535c.2.2.1
                                    have p1535_3 := h1535c.2.2.2
                                    linarith only [h1425, hlam, p1535_0]
                                  · have p1535_0 := h1535c.1
                                    have p1535_1 := h1535c.2.1
                                    have p1535_2 := h1535c.2.2.1
                                    have p1535_3 := h1535c.2.2.2
                                    linarith only [h4, hlam, p1535_0]
                                  · have p1535_0 := h1535c.1
                                    have p1535_1 := h1535c.2.1
                                    have p1535_2 := h1535c.2.2.1
                                    have p1535_3 := h1535c.2.2.2
                                    linarith only [h1499, hc13, hc35, hlam, hphi, p1535_1]
                                  · have p1535_0 := h1535c.1
                                    have p1535_1 := h1535c.2.1
                                    have p1535_2 := h1535c.2.2.1
                                    have p1535_3 := h1535c.2.2.2
                                    linarith only [hlam, p1535_0]
                                  · have p1535_0 := h1535c.1
                                    have p1535_1 := h1535c.2.1
                                    have p1535_2 := h1535c.2.2.1
                                    have p1535_3 := h1535c.2.2.2
                                    linarith only [h0, h1499, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1535_1]
                                  · have p1535_0 := h1535c.1
                                    have p1535_1 := h1535c.2.1
                                    have p1535_2 := h1535c.2.2.1
                                    have p1535_3 := h1535c.2.2.2
                                    linarith only [h1499, hlam, p1535_0]
                                  · have p1535_0 := h1535c.1
                                    have p1535_1 := h1535c.2.1
                                    have p1535_2 := h1535c.2.2.1
                                    have p1535_3 := h1535c.2.2.2
                                    linarith only [h7, hlam, p1535_0]
                                  · have p1535_0 := h1535c.1
                                    have p1535_1 := h1535c.2.1
                                    have p1535_2 := h1535c.2.2.1
                                    have p1535_3 := h1535c.2.2.2
                                    linarith only [h1424, hlam, p1535_0]
                                  · have p1535_0 := h1535c.1
                                    have p1535_1 := h1535c.2.1
                                    have p1535_2 := h1535c.2.2.1
                                    have p1535_3 := h1535c.2.2.2
                                    linarith only [h1498, hlam, p1535_0]
                                  · have p1535_0 := h1535c.1
                                    have p1535_1 := h1535c.2.1
                                    have p1535_2 := h1535c.2.2.1
                                    have p1535_3 := h1535c.2.2.2
                                    linarith only [hlam, p1535_0]
                                  · have p1535_0 := h1535c.1
                                    have p1535_1 := h1535c.2.1
                                    have p1535_2 := h1535c.2.2.1
                                    have p1535_3 := h1535c.2.2.2
                                    linarith only [h1503, hlam, p1535_1]
                                  · have p1535_0 := h1535c.1
                                    have p1535_1 := h1535c.2.1
                                    have p1535_2 := h1535c.2.2.1
                                    have p1535_3 := h1535c.2.2.2
                                    linarith only [h8, hlam, p1535_0]
                                  · have p1535_0 := h1535c.1
                                    have p1535_1 := h1535c.2.1
                                    have p1535_2 := h1535c.2.2.1
                                    have p1535_3 := h1535c.2.2.2
                                    linarith only [h0, h1424, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1535_1]
                                  · have p1535_0 := h1535c.1
                                    have p1535_1 := h1535c.2.1
                                    have p1535_2 := h1535c.2.2.1
                                    have p1535_3 := h1535c.2.2.2
                                    linarith only [h0, h1099, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1535_1]
                                  · have p1535_0 := h1535c.1
                                    have p1535_1 := h1535c.2.1
                                    have p1535_2 := h1535c.2.2.1
                                    have p1535_3 := h1535c.2.2.2
                                    rcases p1535_3 (m.d 0 3) (by simp) with h1575 | h1575
                                    · rcases p1535_3 (m.d 1 3) (by simp) with h1576 | h1576
                                      · linarith only [h1425, h1576, hlam]
                                      · linarith only [h1424, h1576, hlam]
                                    · linarith only [h1575, h7, hlam]
                                  · have p1535_0 := h1535c.1
                                    have p1535_1 := h1535c.2.1
                                    have p1535_2 := h1535c.2.2.1
                                    have p1535_3 := h1535c.2.2.2
                                    linarith only [hlam, p1535_0]
                        · linarith only [h1526, hlam, p1505_0]
                      · have p1505_0 := h1505c.1
                        have p1505_1 := h1505c.2.1
                        have p1505_2 := h1505c.2.2.1
                        have p1505_3 := h1505c.2.2.2
                        linarith only [h0, hlam, p1505_0]
                      · have p1505_0 := h1505c.1
                        have p1505_1 := h1505c.2.1
                        have p1505_2 := h1505c.2.2.1
                        have p1505_3 := h1505c.2.2.2
                        linarith only [hlam, p1505_0]
                      · have p1505_0 := h1505c.1
                        have p1505_1 := h1505c.2.1
                        have p1505_2 := h1505c.2.2.1
                        have p1505_3 := h1505c.2.2.2
                        linarith only [h1099, hlam, p1505_0]
                      · have p1505_0 := h1505c.1
                        have p1505_1 := h1505c.2.1
                        have p1505_2 := h1505c.2.2.1
                        have p1505_3 := h1505c.2.2.2
                        linarith only [h1359, hlam, p1505_0]
                      · have p1505_0 := h1505c.1
                        have p1505_1 := h1505c.2.1
                        have p1505_2 := h1505c.2.2.1
                        have p1505_3 := h1505c.2.2.2
                        linarith only [h1422, hlam, p1505_0]
                      · have p1505_0 := h1505c.1
                        have p1505_1 := h1505c.2.1
                        have p1505_2 := h1505c.2.2.1
                        have p1505_3 := h1505c.2.2.2
                        linarith only [h4, hlam, p1505_0]
                      · have p1505_0 := h1505c.1
                        have p1505_1 := h1505c.2.1
                        have p1505_2 := h1505c.2.2.1
                        have p1505_3 := h1505c.2.2.2
                        linarith only [h0, h1499, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1505_1]
                      · have p1505_0 := h1505c.1
                        have p1505_1 := h1505c.2.1
                        have p1505_2 := h1505c.2.2.1
                        have p1505_3 := h1505c.2.2.2
                        linarith only [hlam, p1505_0]
                      · have p1505_0 := h1505c.1
                        have p1505_1 := h1505c.2.1
                        have p1505_2 := h1505c.2.2.1
                        have p1505_3 := h1505c.2.2.2
                        linarith only [h1359, hc12, hc23, hlam, hphi, p1505_1]
                      · have p1505_0 := h1505c.1
                        have p1505_1 := h1505c.2.1
                        have p1505_2 := h1505c.2.2.1
                        have p1505_3 := h1505c.2.2.2
                        linarith only [h1499, hlam, p1505_0]
                      · have p1505_0 := h1505c.1
                        have p1505_1 := h1505c.2.1
                        have p1505_2 := h1505c.2.2.1
                        have p1505_3 := h1505c.2.2.2
                        linarith only [h5, hlam, p1505_0]
                      · have p1505_0 := h1505c.1
                        have p1505_1 := h1505c.2.1
                        have p1505_2 := h1505c.2.2.1
                        have p1505_3 := h1505c.2.2.2
                        linarith only [h5, h9, hc12, hc45, hlam, hphi, ht23, ht34, p1505_1]
                      · have p1505_0 := h1505c.1
                        have p1505_1 := h1505c.2.1
                        have p1505_2 := h1505c.2.2.1
                        have p1505_3 := h1505c.2.2.2
                        linarith only [h1498, hlam, p1505_1]
                      · have p1505_0 := h1505c.1
                        have p1505_1 := h1505c.2.1
                        have p1505_2 := h1505c.2.2.1
                        have p1505_3 := h1505c.2.2.2
                        linarith only [hlam, p1505_0]
                      · have p1505_0 := h1505c.1
                        have p1505_1 := h1505c.2.1
                        have p1505_2 := h1505c.2.2.1
                        have p1505_3 := h1505c.2.2.2
                        linarith only [h1501, hlam, p1505_1]
                      · have p1505_0 := h1505c.1
                        have p1505_1 := h1505c.2.1
                        have p1505_2 := h1505c.2.2.1
                        have p1505_3 := h1505c.2.2.2
                        linarith only [h6, hlam, p1505_0]
                      · have p1505_0 := h1505c.1
                        have p1505_1 := h1505c.2.1
                        have p1505_2 := h1505c.2.2.1
                        have p1505_3 := h1505c.2.2.2
                        rcases p1505_3 (m.d 0 2) (by simp) with h1598 | h1598
                        · rcases p1505_3 (m.d 1 2) (by simp) with h1599 | h1599
                          · linarith only [h1599, hlam, p1505_0]
                          · rcases p1505_3 (m.d 2 3) (by simp) with h1601 | h1601
                            · linarith only [h1499, h1601, hlam]
                            · linarith only [h1099, h1601, hlam]
                        · linarith only [h0, h1598, hlam]
                      · have p1505_0 := h1505c.1
                        have p1505_1 := h1505c.2.1
                        have p1505_2 := h1505c.2.2.1
                        have p1505_3 := h1505c.2.2.2
                        linarith only [h0, h1099, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1505_1]
                      · have p1505_0 := h1505c.1
                        have p1505_1 := h1505c.2.1
                        have p1505_2 := h1505c.2.2.1
                        have p1505_3 := h1505c.2.2.2
                        linarith only [h0, h1359, h1499, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1505_1]
                      · have p1505_0 := h1505c.1
                        have p1505_1 := h1505c.2.1
                        have p1505_2 := h1505c.2.2.1
                        have p1505_3 := h1505c.2.2.2
                        linarith only [hlam, p1505_0]
              · linarith only [h1, h1099, h1424, h1498, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1609 | h1609
          · linarith only [h1424, h1609, h7, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1611 | h1611
            · linarith only [h0, h1424, h1611, h4, h7, h9, hc01, hlam, hphi, u0ehi3]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1613 | h1613
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1614 | h1614
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1615 | h1615
                  · linarith only [h1615, h5, h9, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1617 | h1617
                    · linarith only [h0, h1613, h1617, h4, h9, hc01, hlam, hphi, u0ehi3]
                    · rcases h2bigk with h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c
                      · have p1619_0 := h1619c.1
                        have p1619_1 := h1619c.2.1
                        have p1619_2 := h1619c.2.2.1
                        have p1619_3 := h1619c.2.2.2
                        linarith only [hlam, p1619_0]
                      · have p1619_0 := h1619c.1
                        have p1619_1 := h1619c.2.1
                        have p1619_2 := h1619c.2.2.1
                        have p1619_3 := h1619c.2.2.2
                        linarith only [h1099, h1424, h1614, h1617, h4, hlam, p1619_2]
                      · have p1619_0 := h1619c.1
                        have p1619_1 := h1619c.2.1
                        have p1619_2 := h1619c.2.2.1
                        have p1619_3 := h1619c.2.2.2
                        linarith only [h0, h1424, h1614, h1617, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1619_1]
                      · have p1619_0 := h1619c.1
                        have p1619_1 := h1619c.2.1
                        have p1619_2 := h1619c.2.2.1
                        have p1619_3 := h1619c.2.2.2
                        rcases p1619_3 (m.d 0 2) (by simp) with h1623 | h1623
                        · rcases p1619_3 (m.d 1 2) (by simp) with h1624 | h1624
                          · linarith only [h0, h1624, hlam]
                          · rcases p1619_3 (m.d 2 3) (by simp) with h1626 | h1626
                            · linarith only [h1626, h4, hlam]
                            · linarith only [h1613, h1626, hlam]
                        · linarith only [h1623, hlam, p1619_0]
                      · have p1619_0 := h1619c.1
                        have p1619_1 := h1619c.2.1
                        have p1619_2 := h1619c.2.2.1
                        have p1619_3 := h1619c.2.2.2
                        rcases p1619_3 (m.d 0 2) (by simp) with h1630 | h1630
                        · rcases p1619_3 (m.d 1 2) (by simp) with h1631 | h1631
                          · linarith only [h0, h1631, hlam]
                          · rcases p1619_3 (m.d 2 3) (by simp) with h1633 | h1633
                            · linarith only [h1633, h4, hlam]
                            · linarith only [h1614, h1633, hlam]
                        · linarith only [h1630, hlam, p1619_0]
                      · have p1619_0 := h1619c.1
                        have p1619_1 := h1619c.2.1
                        have p1619_2 := h1619c.2.2.1
                        have p1619_3 := h1619c.2.2.2
                        linarith only [h0, hlam, p1619_0]
                      · have p1619_0 := h1619c.1
                        have p1619_1 := h1619c.2.1
                        have p1619_2 := h1619c.2.2.1
                        have p1619_3 := h1619c.2.2.2
                        linarith only [hlam, p1619_0]
                      · have p1619_0 := h1619c.1
                        have p1619_1 := h1619c.2.1
                        have p1619_2 := h1619c.2.2.1
                        have p1619_3 := h1619c.2.2.2
                        linarith only [h1099, hlam, p1619_0]
                      · have p1619_0 := h1619c.1
                        have p1619_1 := h1619c.2.1
                        have p1619_2 := h1619c.2.2.1
                        have p1619_3 := h1619c.2.2.2
                        linarith only [h1359, hlam, p1619_0]
                      · have p1619_0 := h1619c.1
                        have p1619_1 := h1619c.2.1
                        have p1619_2 := h1619c.2.2.1
                        have p1619_3 := h1619c.2.2.2
                        linarith only [h1422, hlam, p1619_0]
                      · have p1619_0 := h1619c.1
                        have p1619_1 := h1619c.2.1
                        have p1619_2 := h1619c.2.2.1
                        have p1619_3 := h1619c.2.2.2
                        linarith only [h4, hlam, p1619_0]
                      · have p1619_0 := h1619c.1
                        have p1619_1 := h1619c.2.1
                        have p1619_2 := h1619c.2.2.1
                        have p1619_3 := h1619c.2.2.2
                        rcases p1619_3 (m.d 0 2) (by simp) with h1643 | h1643
                        · rcases p1619_3 (m.d 1 2) (by simp) with h1644 | h1644
                          · linarith only [h1644, hlam, p1619_0]
                          · rcases p1619_3 (m.d 2 3) (by simp) with h1646 | h1646
                            · rcases p1619_3 (m.d 2 4) (by simp) with h1647 | h1647
                              · linarith only [h1613, h1647, hlam]
                              · linarith only [h1359, h1647, hlam]
                            · linarith only [h1646, hlam, p1619_0]
                        · linarith only [h0, h1643, hlam]
                      · have p1619_0 := h1619c.1
                        have p1619_1 := h1619c.2.1
                        have p1619_2 := h1619c.2.2.1
                        have p1619_3 := h1619c.2.2.2
                        linarith only [hlam, p1619_0]
                      · have p1619_0 := h1619c.1
                        have p1619_1 := h1619c.2.1
                        have p1619_2 := h1619c.2.2.1
                        have p1619_3 := h1619c.2.2.2
                        linarith only [h1359, hc12, hc23, hlam, hphi, p1619_1]
                      · have p1619_0 := h1619c.1
                        have p1619_1 := h1619c.2.1
                        have p1619_2 := h1619c.2.2.1
                        have p1619_3 := h1619c.2.2.2
                        linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, p1619_1, u5ehi2]
                      · have p1619_0 := h1619c.1
                        have p1619_1 := h1619c.2.1
                        have p1619_2 := h1619c.2.2.1
                        have p1619_3 := h1619c.2.2.2
                        linarith only [h5, hlam, p1619_0]
                      · have p1619_0 := h1619c.1
                        have p1619_1 := h1619c.2.1
                        have p1619_2 := h1619c.2.2.1
                        have p1619_3 := h1619c.2.2.2
                        linarith only [h5, h9, hc12, hc45, hlam, hphi, ht23, ht34, p1619_1]
                      · have p1619_0 := h1619c.1
                        have p1619_1 := h1619c.2.1
                        have p1619_2 := h1619c.2.2.1
                        have p1619_3 := h1619c.2.2.2
                        linarith only [h1613, hlam, p1619_1]
                      · have p1619_0 := h1619c.1
                        have p1619_1 := h1619c.2.1
                        have p1619_2 := h1619c.2.2.1
                        have p1619_3 := h1619c.2.2.2
                        linarith only [hlam, p1619_0]
                      · have p1619_0 := h1619c.1
                        have p1619_1 := h1619c.2.1
                        have p1619_2 := h1619c.2.2.1
                        have p1619_3 := h1619c.2.2.2
                        linarith only [h1615, hlam, p1619_1]
                      · have p1619_0 := h1619c.1
                        have p1619_1 := h1619c.2.1
                        have p1619_2 := h1619c.2.2.1
                        have p1619_3 := h1619c.2.2.2
                        linarith only [h6, hlam, p1619_0]
                      · have p1619_0 := h1619c.1
                        have p1619_1 := h1619c.2.1
                        have p1619_2 := h1619c.2.2.1
                        have p1619_3 := h1619c.2.2.2
                        rcases p1619_3 (m.d 0 2) (by simp) with h1661 | h1661
                        · rcases p1619_3 (m.d 1 2) (by simp) with h1662 | h1662
                          · linarith only [h1662, hlam, p1619_0]
                          · rcases p1619_3 (m.d 2 3) (by simp) with h1664 | h1664
                            · rcases p1619_3 (m.d 2 4) (by simp) with h1665 | h1665
                              · linarith only [h1615, h1665, hlam]
                              · linarith only [h1359, h1665, hlam]
                            · linarith only [h1099, h1664, hlam]
                        · linarith only [h0, h1661, hlam]
                      · have p1619_0 := h1619c.1
                        have p1619_1 := h1619c.2.1
                        have p1619_2 := h1619c.2.2.1
                        have p1619_3 := h1619c.2.2.2
                        linarith only [h1614, hlam, p1619_1]
                      · have p1619_0 := h1619c.1
                        have p1619_1 := h1619c.2.1
                        have p1619_2 := h1619c.2.2.1
                        have p1619_3 := h1619c.2.2.2
                        linarith only [h1359, hc12, hc25, hlam, hphi, p1619_1]
                      · have p1619_0 := h1619c.1
                        have p1619_1 := h1619c.2.1
                        have p1619_2 := h1619c.2.2.1
                        have p1619_3 := h1619c.2.2.2
                        linarith only [hlam, p1619_0]
                · linarith only [h0, h1099, h1424, h1613, h1614, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h1099, h1613, h7, h9, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5114000 in
set_option maxHeartbeats 5114000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s4_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s4_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h5 h6 h7 h8 h9
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s4_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h5 h6 h7 h8 h9

set_option maxHeartbeats 5114000 in
set_option maxHeartbeats 5114000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s4_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 4 5 (by decide) (by decide) with h1675 | h1675
  · linarith only [h1675, h7, h8, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1677 | h1677
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1678 | h1678
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1679 | h1679
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1680 | h1680
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1681 | h1681
            · linarith only [h1681, h8, hc13, hlam, hphi, ht01, u0ehi2]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1683 | h1683
              · linarith only [h1675, h1683, hc14, hlam, hphi, ht01, u0ehi3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1685 | h1685
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1686 | h1686
                  · linarith only [h1677, h1686, h7, h8, hc12, hlam, hphi, ht01, u0ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1688 | h1688
                    · linarith only [h0, h1675, h1679, h1685, h1686, h1688, hc01, hlam, hphi, u0ehi3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1690 | h1690
                      · linarith only [h0, h1675, h1679, h1685, h1686, h1690, hc01, hlam, hphi, u0ehi3]
                      · rcases h2bigk with h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c
                        · have p1692_0 := h1692c.1
                          have p1692_1 := h1692c.2.1
                          have p1692_2 := h1692c.2.2.1
                          have p1692_3 := h1692c.2.2.2
                          linarith only [hlam, p1692_0]
                        · have p1692_0 := h1692c.1
                          have p1692_1 := h1692c.2.1
                          have p1692_2 := h1692c.2.2.1
                          have p1692_3 := h1692c.2.2.2
                          linarith only [h0, h1679, hc01, hlam, hphi, ht0b, ht5b, p1692_1, u5ehi2]
                        · have p1692_0 := h1692c.1
                          have p1692_1 := h1692c.2.1
                          have p1692_2 := h1692c.2.2.1
                          have p1692_3 := h1692c.2.2.2
                          rcases p1692_3 (m.d 0 2) (by simp) with h1695 | h1695
                          · rcases p1692_3 (m.d 1 2) (by simp) with h1696 | h1696
                            · linarith only [h0, h1696, hlam]
                            · linarith only [h1677, h1696, hlam]
                          · linarith only [h1695, hlam, p1692_0]
                        · have p1692_0 := h1692c.1
                          have p1692_1 := h1692c.2.1
                          have p1692_2 := h1692c.2.2.1
                          have p1692_3 := h1692c.2.2.2
                          rcases p1692_3 (m.d 0 2) (by simp) with h1700 | h1700
                          · rcases p1692_3 (m.d 1 2) (by simp) with h1701 | h1701
                            · linarith only [h0, h1701, hlam]
                            · linarith only [h1678, h1701, hlam]
                          · linarith only [h1700, hlam, p1692_0]
                        · have p1692_0 := h1692c.1
                          have p1692_1 := h1692c.2.1
                          have p1692_2 := h1692c.2.2.1
                          have p1692_3 := h1692c.2.2.2
                          rcases p1692_3 (m.d 0 2) (by simp) with h1705 | h1705
                          · rcases p1692_3 (m.d 1 2) (by simp) with h1706 | h1706
                            · linarith only [h0, h1706, hlam]
                            · linarith only [h1679, h1706, hlam]
                          · linarith only [h1705, hlam, p1692_0]
                        · have p1692_0 := h1692c.1
                          have p1692_1 := h1692c.2.1
                          have p1692_2 := h1692c.2.2.1
                          have p1692_3 := h1692c.2.2.2
                          linarith only [h0, hlam, p1692_0]
                        · have p1692_0 := h1692c.1
                          have p1692_1 := h1692c.2.1
                          have p1692_2 := h1692c.2.2.1
                          have p1692_3 := h1692c.2.2.2
                          linarith only [hlam, p1692_0]
                        · have p1692_0 := h1692c.1
                          have p1692_1 := h1692c.2.1
                          have p1692_2 := h1692c.2.2.1
                          have p1692_3 := h1692c.2.2.2
                          linarith only [h0, h1685, h1690, h7, h8, hc01, hc34, hc45, hlam, hphi, p1692_1, u0ehi3]
                        · have p1692_0 := h1692c.1
                          have p1692_1 := h1692c.2.1
                          have p1692_2 := h1692c.2.2.1
                          have p1692_3 := h1692c.2.2.2
                          rcases p1692_3 (m.d 0 2) (by simp) with h1713 | h1713
                          · rcases p1692_3 (m.d 1 2) (by simp) with h1714 | h1714
                            · rcases p1692_3 (m.d 2 3) (by simp) with h1715 | h1715
                              · linarith only [h1677, h1715, hlam]
                              · linarith only [h1685, h1715, hlam]
                            · linarith only [h1714, hlam, p1692_0]
                          · linarith only [h1713, h5, hlam]
                        · have p1692_0 := h1692c.1
                          have p1692_1 := h1692c.2.1
                          have p1692_2 := h1692c.2.2.1
                          have p1692_3 := h1692c.2.2.2
                          linarith only [h0, h1685, h1686, h1690, h7, h8, hc01, hc34, hc45, hlam, hphi, p1692_1, u0ehi3]
                        · have p1692_0 := h1692c.1
                          have p1692_1 := h1692c.2.1
                          have p1692_2 := h1692c.2.2.1
                          have p1692_3 := h1692c.2.2.2
                          linarith only [h4, hlam, p1692_0]
                        · have p1692_0 := h1692c.1
                          have p1692_1 := h1692c.2.1
                          have p1692_2 := h1692c.2.2.1
                          have p1692_3 := h1692c.2.2.2
                          linarith only [h1677, hlam, p1692_0]
                        · have p1692_0 := h1692c.1
                          have p1692_1 := h1692c.2.1
                          have p1692_2 := h1692c.2.2.1
                          have p1692_3 := h1692c.2.2.2
                          linarith only [hlam, p1692_0]
                        · have p1692_0 := h1692c.1
                          have p1692_1 := h1692c.2.1
                          have p1692_2 := h1692c.2.2.1
                          have p1692_3 := h1692c.2.2.2
                          linarith only [h1690, h4, h8, hc24, hc45, hlam, hphi, p1692_1]
                        · have p1692_0 := h1692c.1
                          have p1692_1 := h1692c.2.1
                          have p1692_2 := h1692c.2.2.1
                          have p1692_3 := h1692c.2.2.2
                          linarith only [h1686, hlam, p1692_0]
                        · have p1692_0 := h1692c.1
                          have p1692_1 := h1692c.2.1
                          have p1692_2 := h1692c.2.2.1
                          have p1692_3 := h1692c.2.2.2
                          linarith only [h5, hlam, p1692_0]
                        · have p1692_0 := h1692c.1
                          have p1692_1 := h1692c.2.1
                          have p1692_2 := h1692c.2.2.1
                          have p1692_3 := h1692c.2.2.2
                          linarith only [h1678, hlam, p1692_0]
                        · have p1692_0 := h1692c.1
                          have p1692_1 := h1692c.2.1
                          have p1692_2 := h1692c.2.2.1
                          have p1692_3 := h1692c.2.2.2
                          linarith only [h1685, hlam, p1692_1]
                        · have p1692_0 := h1692c.1
                          have p1692_1 := h1692c.2.1
                          have p1692_2 := h1692c.2.2.1
                          have p1692_3 := h1692c.2.2.2
                          linarith only [hlam, p1692_0]
                        · have p1692_0 := h1692c.1
                          have p1692_1 := h1692c.2.1
                          have p1692_2 := h1692c.2.2.1
                          have p1692_3 := h1692c.2.2.2
                          linarith only [h1688, hlam, p1692_1]
                        · have p1692_0 := h1692c.1
                          have p1692_1 := h1692c.2.1
                          have p1692_2 := h1692c.2.2.1
                          have p1692_3 := h1692c.2.2.2
                          linarith only [h6, hlam, p1692_0]
                        · have p1692_0 := h1692c.1
                          have p1692_1 := h1692c.2.1
                          have p1692_2 := h1692c.2.2.1
                          have p1692_3 := h1692c.2.2.2
                          linarith only [h1679, hlam, p1692_0]
                        · have p1692_0 := h1692c.1
                          have p1692_1 := h1692c.2.1
                          have p1692_2 := h1692c.2.2.1
                          have p1692_3 := h1692c.2.2.2
                          linarith only [h0, h1679, h1690, h7, h8, hc01, hc23, hc45, hlam, hphi, ht34, p1692_1, u0ehi3]
                        · have p1692_0 := h1692c.1
                          have p1692_1 := h1692c.2.1
                          have p1692_2 := h1692c.2.2.1
                          have p1692_3 := h1692c.2.2.2
                          linarith only [h0, h1679, h1685, h1690, h7, h8, hc01, hc34, hc45, hlam, hphi, p1692_1, u0ehi3]
                        · have p1692_0 := h1692c.1
                          have p1692_1 := h1692c.2.1
                          have p1692_2 := h1692c.2.2.1
                          have p1692_3 := h1692c.2.2.2
                          linarith only [hlam, p1692_0]
                · linarith only [h1685, h7, h8, hc23, hc35, hlam, hphi]
          · linarith only [h1680, h7, h8, hc13, hc35, hlam, hphi]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1738 | h1738
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1739 | h1739
            · linarith only [h1677, h1679, h1739, h8, hc25, hlam, hphi, ht01, ht12, u0ehi2]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1741 | h1741
              · linarith only [h0, h1675, h1677, h1679, h1738, h1741, h6, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1743 | h1743
                · linarith only [h0, h1677, h1679, h1743, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h1743, h7, h8, hc23, hc35, hlam, hphi]
          · linarith only [h1738, h7, h8, hc13, hc35, hlam, hphi]
      · linarith only [h1675, h1677, h1678, h5, hc23, hc45, hlam, hphi, ht34]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1748 | h1748
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1749 | h1749
        · linarith only [h1677, h1749, h4, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1751 | h1751
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1752 | h1752
            · linarith only [h1752, h8, hc13, hlam, hphi, ht01, u0ehi2]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1754 | h1754
              · linarith only [h1677, h1748, h1754, h4, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1756 | h1756
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1757 | h1757
                  · linarith only [h1757, h4, h8, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1759 | h1759
                    · linarith only [h1675, h1677, h1748, h1759, h4, h8, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1761 | h1761
                      · linarith only [h1675, h1677, h1748, h1756, h1761, h4, h8, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                      · linarith only [h1677, h1748, h1756, h1761, h4, h8, hc34, hc45, hlam, hphi]
                · linarith only [h1677, h1748, h1756, h7, h8, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
          · linarith only [h1751, h7, h8, hc13, hc35, hlam, hphi]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1766 | h1766
        · linarith only [h0, h1748, h1766, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1768 | h1768
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1769 | h1769
            · linarith only [h1769, h8, hc13, hlam, hphi, ht01, u0ehi2]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1771 | h1771
              · linarith only [h1675, h1771, hc14, hlam, hphi, ht01, u0ehi3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1773 | h1773
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1774 | h1774
                  · linarith only [h1774, h4, h8, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1776 | h1776
                    · linarith only [h1675, h1776, h5, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1778 | h1778
                      · linarith only [h1675, h1778, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                      · rcases h2bigk with h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c
                        · have p1780_0 := h1780c.1
                          have p1780_1 := h1780c.2.1
                          have p1780_2 := h1780c.2.2.1
                          have p1780_3 := h1780c.2.2.2
                          linarith only [hlam, p1780_0]
                        · have p1780_0 := h1780c.1
                          have p1780_1 := h1780c.2.1
                          have p1780_2 := h1780c.2.2.1
                          have p1780_3 := h1780c.2.2.2
                          rcases p1780_3 (m.d 0 2) (by simp) with h1782 | h1782
                          · rcases p1780_3 (m.d 1 2) (by simp) with h1783 | h1783
                            · linarith only [h0, h1783, hlam]
                            · rcases p1780_3 (m.d 2 3) (by simp) with h1785 | h1785
                              · linarith only [h1785, h4, hlam]
                              · linarith only [h1677, h1785, hlam]
                          · linarith only [h0, h1782, hlam]
                        · have p1780_0 := h1780c.1
                          have p1780_1 := h1780c.2.1
                          have p1780_2 := h1780c.2.2.1
                          have p1780_3 := h1780c.2.2.2
                          rcases p1780_3 (m.d 0 2) (by simp) with h1789 | h1789
                          · rcases p1780_3 (m.d 1 2) (by simp) with h1790 | h1790
                            · linarith only [h0, h1790, hlam]
                            · rcases p1780_3 (m.d 2 3) (by simp) with h1792 | h1792
                              · linarith only [h1792, hlam, p1780_0]
                              · rcases p1780_3 (m.d 2 4) (by simp) with h1794 | h1794
                                · linarith only [h1794, h5, hlam]
                                · rcases p1780_3 (m.d 2 5) (by simp) with h1796 | h1796
                                  · linarith only [h1796, h6, hlam]
                                  · linarith only [h1774, h1796, hlam]
                          · linarith only [h1789, hlam, p1780_0]
                        · have p1780_0 := h1780c.1
                          have p1780_1 := h1780c.2.1
                          have p1780_2 := h1780c.2.2.1
                          have p1780_3 := h1780c.2.2.2
                          rcases p1780_3 (m.d 0 2) (by simp) with h1800 | h1800
                          · rcases p1780_3 (m.d 1 2) (by simp) with h1801 | h1801
                            · linarith only [h0, h1801, hlam]
                            · rcases p1780_3 (m.d 2 3) (by simp) with h1803 | h1803
                              · linarith only [h1803, h4, hlam]
                              · linarith only [h1773, h1803, hlam]
                          · linarith only [h1800, hlam, p1780_0]
                        · have p1780_0 := h1780c.1
                          have p1780_1 := h1780c.2.1
                          have p1780_2 := h1780c.2.2.1
                          have p1780_3 := h1780c.2.2.2
                          rcases p1780_3 (m.d 0 2) (by simp) with h1807 | h1807
                          · rcases p1780_3 (m.d 1 2) (by simp) with h1808 | h1808
                            · linarith only [h0, h1808, hlam]
                            · rcases p1780_3 (m.d 2 3) (by simp) with h1810 | h1810
                              · linarith only [h1810, h4, hlam]
                              · rcases p1780_3 (m.d 2 4) (by simp) with h1812 | h1812
                                · linarith only [h1812, h5, hlam]
                                · rcases p1780_3 (m.d 2 5) (by simp) with h1814 | h1814
                                  · linarith only [h1814, hlam, p1780_0]
                                  · rcases h3bigk with h1816c | h1816c | h1816c | h1816c | h1816c | h1816c | h1816c | h1816c | h1816c | h1816c | h1816c | h1816c | h1816c | h1816c | h1816c | h1816c | h1816c | h1816c | h1816c | h1816c | h1816c | h1816c | h1816c | h1816c | h1816c
                                    · have p1816_0 := h1816c.1
                                      have p1816_1 := h1816c.2.1
                                      have p1816_2 := h1816c.2.2.1
                                      have p1816_3 := h1816c.2.2.2
                                      linarith only [hlam, p1816_0]
                                    · have p1816_0 := h1816c.1
                                      have p1816_1 := h1816c.2.1
                                      have p1816_2 := h1816c.2.2.1
                                      have p1816_3 := h1816c.2.2.2
                                      linarith only [h0, h1748, h1768, h1773, h1774, h8, hc01, hc12, hc34, hc35, hlam, hphi, ht0b, ht23, ht45, ht5b, p1780_1, p1816_1]
                                    · have p1816_0 := h1816c.1
                                      have p1816_1 := h1816c.2.1
                                      have p1816_2 := h1816c.2.2.1
                                      have p1816_3 := h1816c.2.2.2
                                      linarith only [h1748, h1773, h1778, h8, hc12, hc45, hlam, hphi, ht23, ht34, p1816_1]
                                    · have p1816_0 := h1816c.1
                                      have p1816_1 := h1816c.2.1
                                      have p1816_2 := h1816c.2.2.1
                                      have p1816_3 := h1816c.2.2.2
                                      linarith only [h1778, h8, hc34, hc45, hlam, hphi, p1816_1]
                                    · have p1816_0 := h1816c.1
                                      have p1816_1 := h1816c.2.1
                                      have p1816_2 := h1816c.2.2.1
                                      have p1816_3 := h1816c.2.2.2
                                      linarith only [h8, hlam, p1816_0]
                                    · have p1816_0 := h1816c.1
                                      have p1816_1 := h1816c.2.1
                                      have p1816_2 := h1816c.2.2.1
                                      have p1816_3 := h1816c.2.2.2
                                      linarith only [h1, hlam, p1816_0]
                                    · have p1816_0 := h1816c.1
                                      have p1816_1 := h1816c.2.1
                                      have p1816_2 := h1816c.2.2.1
                                      have p1816_3 := h1816c.2.2.2
                                      linarith only [hlam, p1816_0]
                                    · have p1816_0 := h1816c.1
                                      have p1816_1 := h1816c.2.1
                                      have p1816_2 := h1816c.2.2.1
                                      have p1816_3 := h1816c.2.2.2
                                      linarith only [h1677, hlam, p1816_1]
                                    · have p1816_0 := h1816c.1
                                      have p1816_1 := h1816c.2.1
                                      have p1816_2 := h1816c.2.2.1
                                      have p1816_3 := h1816c.2.2.2
                                      linarith only [h1, h1778, h8, hc34, hc45, hlam, hphi, p1816_1]
                                    · have p1816_0 := h1816c.1
                                      have p1816_1 := h1816c.2.1
                                      have p1816_2 := h1816c.2.2.1
                                      have p1816_3 := h1816c.2.2.2
                                      linarith only [h1769, hlam, p1816_0]
                                    · have p1816_0 := h1816c.1
                                      have p1816_1 := h1816c.2.1
                                      have p1816_2 := h1816c.2.2.1
                                      have p1816_3 := h1816c.2.2.2
                                      linarith only [h4, hlam, p1816_0]
                                    · have p1816_0 := h1816c.1
                                      have p1816_1 := h1816c.2.1
                                      have p1816_2 := h1816c.2.2.1
                                      have p1816_3 := h1816c.2.2.2
                                      linarith only [h0, h1774, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1780_1, p1816_1]
                                    · have p1816_0 := h1816c.1
                                      have p1816_1 := h1816c.2.1
                                      have p1816_2 := h1816c.2.2.1
                                      have p1816_3 := h1816c.2.2.2
                                      linarith only [hlam, p1816_0]
                                    · have p1816_0 := h1816c.1
                                      have p1816_1 := h1816c.2.1
                                      have p1816_2 := h1816c.2.2.1
                                      have p1816_3 := h1816c.2.2.2
                                      linarith only [h0, h1774, h1778, h7, h8, hc01, hc34, hc45, hlam, hphi, p1780_1, p1816_1, u0ehi3]
                                    · have p1816_0 := h1816c.1
                                      have p1816_1 := h1816c.2.1
                                      have p1816_2 := h1816c.2.2.1
                                      have p1816_3 := h1816c.2.2.2
                                      linarith only [h1774, hlam, p1816_0]
                                    · have p1816_0 := h1816c.1
                                      have p1816_1 := h1816c.2.1
                                      have p1816_2 := h1816c.2.2.1
                                      have p1816_3 := h1816c.2.2.2
                                      linarith only [h7, hlam, p1816_0]
                                    · have p1816_0 := h1816c.1
                                      have p1816_1 := h1816c.2.1
                                      have p1816_2 := h1816c.2.2.1
                                      have p1816_3 := h1816c.2.2.2
                                      linarith only [h1768, hlam, p1816_0]
                                    · have p1816_0 := h1816c.1
                                      have p1816_1 := h1816c.2.1
                                      have p1816_2 := h1816c.2.2.1
                                      have p1816_3 := h1816c.2.2.2
                                      linarith only [h1773, hlam, p1816_0]
                                    · have p1816_0 := h1816c.1
                                      have p1816_1 := h1816c.2.1
                                      have p1816_2 := h1816c.2.2.1
                                      have p1816_3 := h1816c.2.2.2
                                      linarith only [hlam, p1816_0]
                                    · have p1816_0 := h1816c.1
                                      have p1816_1 := h1816c.2.1
                                      have p1816_2 := h1816c.2.2.1
                                      have p1816_3 := h1816c.2.2.2
                                      linarith only [h1778, hlam, p1816_1]
                                    · have p1816_0 := h1816c.1
                                      have p1816_1 := h1816c.2.1
                                      have p1816_2 := h1816c.2.2.1
                                      have p1816_3 := h1816c.2.2.2
                                      linarith only [h1778, h7, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1816_1, u0ehi3]
                                    · have p1816_0 := h1816c.1
                                      have p1816_1 := h1816c.2.1
                                      have p1816_2 := h1816c.2.2.1
                                      have p1816_3 := h1816c.2.2.2
                                      linarith only [h1768, h1778, hc34, hc45, hlam, hphi, p1816_1]
                                    · have p1816_0 := h1816c.1
                                      have p1816_1 := h1816c.2.1
                                      have p1816_2 := h1816c.2.2.1
                                      have p1816_3 := h1816c.2.2.2
                                      linarith only [h1748, h1773, h1778, hc12, hc45, hlam, hphi, ht23, ht34, p1816_1]
                                    · have p1816_0 := h1816c.1
                                      have p1816_1 := h1816c.2.1
                                      have p1816_2 := h1816c.2.2.1
                                      have p1816_3 := h1816c.2.2.2
                                      rcases p1816_3 (m.d 0 3) (by simp) with h1840 | h1840
                                      · linarith only [h1840, h8, hlam]
                                      · linarith only [h1840, h7, hlam]
                                    · have p1816_0 := h1816c.1
                                      have p1816_1 := h1816c.2.1
                                      have p1816_2 := h1816c.2.2.1
                                      have p1816_3 := h1816c.2.2.2
                                      linarith only [hlam, p1816_0]
                          · linarith only [h1807, hlam, p1780_0]
                        · have p1780_0 := h1780c.1
                          have p1780_1 := h1780c.2.1
                          have p1780_2 := h1780c.2.2.1
                          have p1780_3 := h1780c.2.2.2
                          linarith only [h0, hlam, p1780_0]
                        · have p1780_0 := h1780c.1
                          have p1780_1 := h1780c.2.1
                          have p1780_2 := h1780c.2.2.1
                          have p1780_3 := h1780c.2.2.2
                          linarith only [hlam, p1780_0]
                        · have p1780_0 := h1780c.1
                          have p1780_1 := h1780c.2.1
                          have p1780_2 := h1780c.2.2.1
                          have p1780_3 := h1780c.2.2.2
                          linarith only [h1677, hlam, p1780_0]
                        · have p1780_0 := h1780c.1
                          have p1780_1 := h1780c.2.1
                          have p1780_2 := h1780c.2.2.1
                          have p1780_3 := h1780c.2.2.2
                          linarith only [h1748, hlam, p1780_0]
                        · have p1780_0 := h1780c.1
                          have p1780_1 := h1780c.2.1
                          have p1780_2 := h1780c.2.2.1
                          have p1780_3 := h1780c.2.2.2
                          linarith only [h1766, hlam, p1780_0]
                        · have p1780_0 := h1780c.1
                          have p1780_1 := h1780c.2.1
                          have p1780_2 := h1780c.2.2.1
                          have p1780_3 := h1780c.2.2.2
                          linarith only [h4, hlam, p1780_0]
                        · have p1780_0 := h1780c.1
                          have p1780_1 := h1780c.2.1
                          have p1780_2 := h1780c.2.2.1
                          have p1780_3 := h1780c.2.2.2
                          linarith only [h1778, h4, h8, hc12, hc45, hlam, hphi, ht23, ht34, p1780_1]
                        · have p1780_0 := h1780c.1
                          have p1780_1 := h1780c.2.1
                          have p1780_2 := h1780c.2.2.1
                          have p1780_3 := h1780c.2.2.2
                          linarith only [hlam, p1780_0]
                        · have p1780_0 := h1780c.1
                          have p1780_1 := h1780c.2.1
                          have p1780_2 := h1780c.2.2.1
                          have p1780_3 := h1780c.2.2.2
                          linarith only [h1748, h1778, h4, h8, hc12, hc45, hlam, hphi, ht23, ht34, p1780_1]
                        · have p1780_0 := h1780c.1
                          have p1780_1 := h1780c.2.1
                          have p1780_2 := h1780c.2.2.1
                          have p1780_3 := h1780c.2.2.2
                          linarith only [h1774, hlam, p1780_0]
                        · have p1780_0 := h1780c.1
                          have p1780_1 := h1780c.2.1
                          have p1780_2 := h1780c.2.2.1
                          have p1780_3 := h1780c.2.2.2
                          linarith only [h5, hlam, p1780_0]
                        · have p1780_0 := h1780c.1
                          have p1780_1 := h1780c.2.1
                          have p1780_2 := h1780c.2.2.1
                          have p1780_3 := h1780c.2.2.2
                          linarith only [h1778, h5, h7, h8, hc12, hc45, hlam, hphi, ht23, ht34, p1780_1]
                        · have p1780_0 := h1780c.1
                          have p1780_1 := h1780c.2.1
                          have p1780_2 := h1780c.2.2.1
                          have p1780_3 := h1780c.2.2.2
                          linarith only [h1773, hlam, p1780_1]
                        · have p1780_0 := h1780c.1
                          have p1780_1 := h1780c.2.1
                          have p1780_2 := h1780c.2.2.1
                          have p1780_3 := h1780c.2.2.2
                          linarith only [hlam, p1780_0]
                        · have p1780_0 := h1780c.1
                          have p1780_1 := h1780c.2.1
                          have p1780_2 := h1780c.2.2.1
                          have p1780_3 := h1780c.2.2.2
                          linarith only [h1776, hlam, p1780_1]
                        · have p1780_0 := h1780c.1
                          have p1780_1 := h1780c.2.1
                          have p1780_2 := h1780c.2.2.1
                          have p1780_3 := h1780c.2.2.2
                          linarith only [h6, hlam, p1780_0]
                        · have p1780_0 := h1780c.1
                          have p1780_1 := h1780c.2.1
                          have p1780_2 := h1780c.2.2.1
                          have p1780_3 := h1780c.2.2.2
                          rcases p1780_3 (m.d 0 2) (by simp) with h1861 | h1861
                          · rcases p1780_3 (m.d 1 2) (by simp) with h1862 | h1862
                            · linarith only [h1862, hlam, p1780_0]
                            · rcases p1780_3 (m.d 2 3) (by simp) with h1864 | h1864
                              · linarith only [h1774, h1864, hlam]
                              · linarith only [h1677, h1864, hlam]
                          · linarith only [h0, h1861, hlam]
                        · have p1780_0 := h1780c.1
                          have p1780_1 := h1780c.2.1
                          have p1780_2 := h1780c.2.2.1
                          have p1780_3 := h1780c.2.2.2
                          linarith only [h1677, hc12, hc25, hlam, hphi, p1780_1]
                        · have p1780_0 := h1780c.1
                          have p1780_1 := h1780c.2.1
                          have p1780_2 := h1780c.2.2.1
                          have p1780_3 := h1780c.2.2.2
                          linarith only [h0, h1748, h1778, h6, h7, h8, hc01, hc12, hc45, hlam, hphi, ht23, ht34, p1780_1, u0ehi3]
                        · have p1780_0 := h1780c.1
                          have p1780_1 := h1780c.2.1
                          have p1780_2 := h1780c.2.2.1
                          have p1780_3 := h1780c.2.2.2
                          linarith only [hlam, p1780_0]
                · linarith only [h1, h1677, h1768, h1773, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · linarith only [h1768, h7, h8, hc13, hc35, hlam, hphi]

set_option maxHeartbeats 5114000 in
set_option maxHeartbeats 5114000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s4_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s4_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h5 h6 h7 h8
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s4_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 h5 h6 h7 h8

end R2N4
