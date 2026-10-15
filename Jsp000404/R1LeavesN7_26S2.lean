import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5008000 in
theorem r1l7_10_12_23_L_I_L_I_M_IR_s2_x0_x1_x1_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h883 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1033 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1100 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1101 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1102 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h2bigk := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 1 2 3 (by decide) (by decide) with h1103 | h1103
  · linarith only [h0, h1103, h4, hlam]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1105 | h1105
    · linarith only [h0, h1105, h883, hlam]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1107 | h1107
      · linarith only [h0, h1033, h1107, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1109 | h1109
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1110 | h1110
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1111 | h1111
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1112 | h1112
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1113 | h1113
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1114 | h1114
                  · rcases h0bigk with h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c
                    · have p1115_0 := h1115c.1
                      have p1115_1 := h1115c.2.1
                      have p1115_2 := h1115c.2.2.1
                      have p1115_3 := h1115c.2.2.2
                      linarith only [hlam, p1115_0]
                    · have p1115_0 := h1115c.1
                      have p1115_1 := h1115c.2.1
                      have p1115_2 := h1115c.2.2.1
                      have p1115_3 := h1115c.2.2.2
                      rcases p1115_3 (m.d 0 1) (by simp) with h1117 | h1117
                      · rcases p1115_3 (m.d 0 2) (by simp) with h1118 | h1118
                        · linarith only [h0, h1118, hlam]
                        · rcases p1115_3 (m.d 0 3) (by simp) with h1120 | h1120
                          · linarith only [h1, h1120, hlam]
                          · linarith only [h1120, h4, hlam]
                      · linarith only [h0, h1117, hlam]
                    · have p1115_0 := h1115c.1
                      have p1115_1 := h1115c.2.1
                      have p1115_2 := h1115c.2.2.1
                      have p1115_3 := h1115c.2.2.2
                      linarith only [h1, h1109, h1114, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1115_1, u3ehi4]
                    · have p1115_0 := h1115c.1
                      have p1115_1 := h1115c.2.1
                      have p1115_2 := h1115c.2.2.1
                      have p1115_3 := h1115c.2.2.2
                      rcases p1115_3 (m.d 0 1) (by simp) with h1125 | h1125
                      · rcases p1115_3 (m.d 0 2) (by simp) with h1126 | h1126
                        · linarith only [h0, h1126, hlam]
                        · rcases p1115_3 (m.d 0 3) (by simp) with h1128 | h1128
                          · linarith only [h1, h1128, hlam]
                          · linarith only [h1100, h1128, hlam]
                      · linarith only [h1125, h2, hlam]
                    · have p1115_0 := h1115c.1
                      have p1115_1 := h1115c.2.1
                      have p1115_2 := h1115c.2.2.1
                      have p1115_3 := h1115c.2.2.2
                      rcases p1115_3 (m.d 0 1) (by simp) with h1132 | h1132
                      · rcases p1115_3 (m.d 0 2) (by simp) with h1133 | h1133
                        · linarith only [h0, h1133, hlam]
                        · rcases p1115_3 (m.d 0 3) (by simp) with h1135 | h1135
                          · linarith only [h1, h1135, hlam]
                          · linarith only [h1101, h1135, hlam]
                      · linarith only [h1132, h3, hlam]
                    · have p1115_0 := h1115c.1
                      have p1115_1 := h1115c.2.1
                      have p1115_2 := h1115c.2.2.1
                      have p1115_3 := h1115c.2.2.2
                      linarith only [h0, hlam, p1115_0]
                    · have p1115_0 := h1115c.1
                      have p1115_1 := h1115c.2.1
                      have p1115_2 := h1115c.2.2.1
                      have p1115_3 := h1115c.2.2.2
                      linarith only [hlam, p1115_0]
                    · have p1115_0 := h1115c.1
                      have p1115_1 := h1115c.2.1
                      have p1115_2 := h1115c.2.2.1
                      have p1115_3 := h1115c.2.2.2
                      linarith only [h4, hlam, p1115_0]
                    · have p1115_0 := h1115c.1
                      have p1115_1 := h1115c.2.1
                      have p1115_2 := h1115c.2.2.1
                      have p1115_3 := h1115c.2.2.2
                      linarith only [h883, hlam, p1115_1]
                    · have p1115_0 := h1115c.1
                      have p1115_1 := h1115c.2.1
                      have p1115_2 := h1115c.2.2.1
                      have p1115_3 := h1115c.2.2.2
                      linarith only [h1033, hlam, p1115_0]
                    · have p1115_0 := h1115c.1
                      have p1115_1 := h1115c.2.1
                      have p1115_2 := h1115c.2.2.1
                      have p1115_3 := h1115c.2.2.2
                      linarith only [h1, hlam, p1115_1]
                    · have p1115_0 := h1115c.1
                      have p1115_1 := h1115c.2.1
                      have p1115_2 := h1115c.2.2.1
                      have p1115_3 := h1115c.2.2.2
                      rcases p1115_3 (m.d 0 1) (by simp) with h1145 | h1145
                      · rcases p1115_3 (m.d 0 2) (by simp) with h1146 | h1146
                        · linarith only [h1146, h4, hlam]
                        · rcases p1115_3 (m.d 0 3) (by simp) with h1148 | h1148
                          · rcases p1115_3 (m.d 0 4) (by simp) with h1149 | h1149
                            · linarith only [h1100, h1149, hlam]
                            · linarith only [h1149, h883, hlam]
                          · linarith only [h1148, h4, hlam]
                      · linarith only [h0, h1145, hlam]
                    · have p1115_0 := h1115c.1
                      have p1115_1 := h1115c.2.1
                      have p1115_2 := h1115c.2.2.1
                      have p1115_3 := h1115c.2.2.2
                      linarith only [hlam, p1115_0]
                    · have p1115_0 := h1115c.1
                      have p1115_1 := h1115c.2.1
                      have p1115_2 := h1115c.2.2.1
                      have p1115_3 := h1115c.2.2.2
                      rcases p1115_3 (m.d 0 1) (by simp) with h1155 | h1155
                      · rcases p1115_3 (m.d 0 2) (by simp) with h1156 | h1156
                        · linarith only [h1156, h4, hlam]
                        · rcases p1115_3 (m.d 0 3) (by simp) with h1158 | h1158
                          · rcases p1115_3 (m.d 0 4) (by simp) with h1159 | h1159
                            · linarith only [h1100, h1159, hlam]
                            · rcases p1115_3 (m.d 0 5) (by simp) with h1161 | h1161
                              · linarith only [h1101, h1161, hlam]
                              · rcases h2bigk with h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c
                                · have p1163_0 := h1163c.1
                                  have p1163_1 := h1163c.2.1
                                  have p1163_2 := h1163c.2.2.1
                                  have p1163_3 := h1163c.2.2.2
                                  linarith only [hlam, p1163_0]
                                · have p1163_0 := h1163c.1
                                  have p1163_1 := h1163c.2.1
                                  have p1163_2 := h1163c.2.2.1
                                  have p1163_3 := h1163c.2.2.2
                                  linarith only [h1033, h1102, h4, hc12, hc23, hlam, hphi, p1115_1, p1163_1]
                                · have p1163_0 := h1163c.1
                                  have p1163_1 := h1163c.2.1
                                  have p1163_2 := h1163c.2.2.1
                                  have p1163_3 := h1163c.2.2.2
                                  linarith only [h4, hlam, p1163_0]
                                · have p1163_0 := h1163c.1
                                  have p1163_1 := h1163c.2.1
                                  have p1163_2 := h1163c.2.2.1
                                  have p1163_3 := h1163c.2.2.2
                                  linarith only [h883, hlam, p1163_0]
                                · have p1163_0 := h1163c.1
                                  have p1163_1 := h1163c.2.1
                                  have p1163_2 := h1163c.2.2.1
                                  have p1163_3 := h1163c.2.2.2
                                  linarith only [h1033, hlam, p1163_0]
                                · have p1163_0 := h1163c.1
                                  have p1163_1 := h1163c.2.1
                                  have p1163_2 := h1163c.2.2.1
                                  have p1163_3 := h1163c.2.2.2
                                  linarith only [h0, hlam, p1163_0]
                                · have p1163_0 := h1163c.1
                                  have p1163_1 := h1163c.2.1
                                  have p1163_2 := h1163c.2.2.1
                                  have p1163_3 := h1163c.2.2.2
                                  linarith only [hlam, p1163_0]
                                · have p1163_0 := h1163c.1
                                  have p1163_1 := h1163c.2.1
                                  have p1163_2 := h1163c.2.2.1
                                  have p1163_3 := h1163c.2.2.2
                                  linarith only [h1103, hlam, p1163_0]
                                · have p1163_0 := h1163c.1
                                  have p1163_1 := h1163c.2.1
                                  have p1163_2 := h1163c.2.2.1
                                  have p1163_3 := h1163c.2.2.2
                                  linarith only [h1105, hlam, p1163_0]
                                · have p1163_0 := h1163c.1
                                  have p1163_1 := h1163c.2.1
                                  have p1163_2 := h1163c.2.2.1
                                  have p1163_3 := h1163c.2.2.2
                                  linarith only [h1107, hlam, p1163_0]
                                · have p1163_0 := h1163c.1
                                  have p1163_1 := h1163c.2.1
                                  have p1163_2 := h1163c.2.2.1
                                  have p1163_3 := h1163c.2.2.2
                                  rcases p1163_3 (m.d 0 2) (by simp) with h1174 | h1174
                                  · linarith only [h1174, hlam, p1163_0]
                                  · rcases p1163_3 (m.d 1 2) (by simp) with h1176 | h1176
                                    · linarith only [h1103, h1176, hlam]
                                    · rcases p1163_3 (m.d 2 3) (by simp) with h1178 | h1178
                                      · rcases p1163_3 (m.d 2 4) (by simp) with h1179 | h1179
                                        · linarith only [h1111, h1179, hlam]
                                        · linarith only [h1179, h883, hlam]
                                      · linarith only [h1178, hlam, p1163_0]
                                · have p1163_0 := h1163c.1
                                  have p1163_1 := h1163c.2.1
                                  have p1163_2 := h1163c.2.2.1
                                  have p1163_3 := h1163c.2.2.2
                                  rcases p1163_3 (m.d 0 2) (by simp) with h1183 | h1183
                                  · linarith only [h1183, h4, hlam]
                                  · linarith only [h0, h1183, hlam]
                                · have p1163_0 := h1163c.1
                                  have p1163_1 := h1163c.2.1
                                  have p1163_2 := h1163c.2.2.1
                                  have p1163_3 := h1163c.2.2.2
                                  linarith only [hlam, p1163_0]
                                · have p1163_0 := h1163c.1
                                  have p1163_1 := h1163c.2.1
                                  have p1163_2 := h1163c.2.2.1
                                  have p1163_3 := h1163c.2.2.2
                                  linarith only [h1033, h1113, hc02, hc23, hlam, hphi, p1163_1]
                                · have p1163_0 := h1163c.1
                                  have p1163_1 := h1163c.2.1
                                  have p1163_2 := h1163c.2.2.1
                                  have p1163_3 := h1163c.2.2.2
                                  linarith only [h0, h1033, hc12, hc23, hlam, hphi, p1163_1]
                                · have p1163_0 := h1163c.1
                                  have p1163_1 := h1163c.2.1
                                  have p1163_2 := h1163c.2.2.1
                                  have p1163_3 := h1163c.2.2.2
                                  rcases p1163_3 (m.d 0 2) (by simp) with h1189 | h1189
                                  · linarith only [h1189, hlam, p1163_0]
                                  · rcases p1163_3 (m.d 1 2) (by simp) with h1191 | h1191
                                    · linarith only [h1105, h1191, hlam]
                                    · rcases p1163_3 (m.d 2 3) (by simp) with h1193 | h1193
                                      · rcases p1163_3 (m.d 2 4) (by simp) with h1194 | h1194
                                        · rcases p1163_3 (m.d 2 5) (by simp) with h1195 | h1195
                                          · linarith only [h1113, h1195, hlam]
                                          · linarith only [h1033, h1195, hlam]
                                        · linarith only [h1194, hlam, p1163_0]
                                      · linarith only [h1193, h4, hlam]
                                · have p1163_0 := h1163c.1
                                  have p1163_1 := h1163c.2.1
                                  have p1163_2 := h1163c.2.2.1
                                  have p1163_3 := h1163c.2.2.2
                                  rcases p1163_3 (m.d 0 2) (by simp) with h1200 | h1200
                                  · linarith only [h1200, h883, hlam]
                                  · linarith only [h0, h1200, hlam]
                                · have p1163_0 := h1163c.1
                                  have p1163_1 := h1163c.2.1
                                  have p1163_2 := h1163c.2.2.1
                                  have p1163_3 := h1163c.2.2.2
                                  linarith only [h1111, hlam, p1163_1]
                                · have p1163_0 := h1163c.1
                                  have p1163_1 := h1163c.2.1
                                  have p1163_2 := h1163c.2.2.1
                                  have p1163_3 := h1163c.2.2.2
                                  linarith only [hlam, p1163_0]
                                · have p1163_0 := h1163c.1
                                  have p1163_1 := h1163c.2.1
                                  have p1163_2 := h1163c.2.2.1
                                  have p1163_3 := h1163c.2.2.2
                                  linarith only [h0, h1033, hc12, hc24, hlam, hphi, p1163_1]
                                · have p1163_0 := h1163c.1
                                  have p1163_1 := h1163c.2.1
                                  have p1163_2 := h1163c.2.2.1
                                  have p1163_3 := h1163c.2.2.2
                                  rcases p1163_3 (m.d 0 2) (by simp) with h1206 | h1206
                                  · linarith only [h1206, hlam, p1163_0]
                                  · rcases p1163_3 (m.d 1 2) (by simp) with h1208 | h1208
                                    · linarith only [h1107, h1208, hlam]
                                    · rcases p1163_3 (m.d 2 3) (by simp) with h1210 | h1210
                                      · rcases p1163_3 (m.d 2 4) (by simp) with h1211 | h1211
                                        · rcases p1163_3 (m.d 2 5) (by simp) with h1212 | h1212
                                          · rcases h3bigk with h1213c | h1213c | h1213c | h1213c | h1213c | h1213c | h1213c | h1213c | h1213c | h1213c | h1213c | h1213c | h1213c | h1213c | h1213c | h1213c | h1213c | h1213c | h1213c | h1213c | h1213c | h1213c | h1213c | h1213c | h1213c
                                            · have p1213_0 := h1213c.1
                                              have p1213_1 := h1213c.2.1
                                              have p1213_2 := h1213c.2.2.1
                                              have p1213_3 := h1213c.2.2.2
                                              linarith only [hlam, p1213_0]
                                            · have p1213_0 := h1213c.1
                                              have p1213_1 := h1213c.2.1
                                              have p1213_2 := h1213c.2.2.1
                                              have p1213_3 := h1213c.2.2.2
                                              linarith only [h1109, h1114, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1213_1, u3ehi4]
                                            · have p1213_0 := h1213c.1
                                              have p1213_1 := h1213c.2.1
                                              have p1213_2 := h1213c.2.2.1
                                              have p1213_3 := h1213c.2.2.2
                                              linarith only [h4, hlam, p1213_1]
                                            · have p1213_0 := h1213c.1
                                              have p1213_1 := h1213c.2.1
                                              have p1213_2 := h1213c.2.2.1
                                              have p1213_3 := h1213c.2.2.2
                                              rcases p1213_3 (m.d 0 3) (by simp) with h1217 | h1217
                                              · rcases p1213_3 (m.d 1 3) (by simp) with h1218 | h1218
                                                · linarith only [h1, h1218, hlam]
                                                · linarith only [h1109, h1218, hlam]
                                              · linarith only [h1217, hlam, p1213_0]
                                            · have p1213_0 := h1213c.1
                                              have p1213_1 := h1213c.2.1
                                              have p1213_2 := h1213c.2.2.1
                                              have p1213_3 := h1213c.2.2.2
                                              rcases p1213_3 (m.d 0 3) (by simp) with h1222 | h1222
                                              · rcases p1213_3 (m.d 1 3) (by simp) with h1223 | h1223
                                                · linarith only [h1, h1223, hlam]
                                                · linarith only [h1110, h1223, hlam]
                                              · linarith only [h1222, hlam, p1213_0]
                                            · have p1213_0 := h1213c.1
                                              have p1213_1 := h1213c.2.1
                                              have p1213_2 := h1213c.2.2.1
                                              have p1213_3 := h1213c.2.2.2
                                              linarith only [h1, hlam, p1213_0]
                                            · have p1213_0 := h1213c.1
                                              have p1213_1 := h1213c.2.1
                                              have p1213_2 := h1213c.2.2.1
                                              have p1213_3 := h1213c.2.2.2
                                              linarith only [hlam, p1213_0]
                                            · have p1213_0 := h1213c.1
                                              have p1213_1 := h1213c.2.1
                                              have p1213_2 := h1213c.2.2.1
                                              have p1213_3 := h1213c.2.2.2
                                              linarith only [h1103, hlam, p1213_1]
                                            · have p1213_0 := h1213c.1
                                              have p1213_1 := h1213c.2.1
                                              have p1213_2 := h1213c.2.2.1
                                              have p1213_3 := h1213c.2.2.2
                                              linarith only [h1, h1114, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1213_1, u3ehi4]
                                            · have p1213_0 := h1213c.1
                                              have p1213_1 := h1213c.2.1
                                              have p1213_2 := h1213c.2.2.1
                                              have p1213_3 := h1213c.2.2.2
                                              linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1213_1, u3ehi4]
                                            · have p1213_0 := h1213c.1
                                              have p1213_1 := h1213c.2.1
                                              have p1213_2 := h1213c.2.2.1
                                              have p1213_3 := h1213c.2.2.2
                                              linarith only [hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1115_1, p1213_1]
                                            · have p1213_0 := h1213c.1
                                              have p1213_1 := h1213c.2.1
                                              have p1213_2 := h1213c.2.2.1
                                              have p1213_3 := h1213c.2.2.2
                                              linarith only [h1109, h1114, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1213_1, u3ehi4]
                                            · have p1213_0 := h1213c.1
                                              have p1213_1 := h1213c.2.1
                                              have p1213_2 := h1213c.2.2.1
                                              have p1213_3 := h1213c.2.2.2
                                              linarith only [hlam, p1213_0]
                                            · have p1213_0 := h1213c.1
                                              have p1213_1 := h1213c.2.1
                                              have p1213_2 := h1213c.2.2.1
                                              have p1213_3 := h1213c.2.2.2
                                              rcases p1213_3 (m.d 0 3) (by simp) with h1235 | h1235
                                              · linarith only [h1235, h4, hlam]
                                              · linarith only [h1100, h1235, hlam]
                                            · have p1213_0 := h1213c.1
                                              have p1213_1 := h1213c.2.1
                                              have p1213_2 := h1213c.2.2.1
                                              have p1213_3 := h1213c.2.2.2
                                              rcases p1213_3 (m.d 0 3) (by simp) with h1238 | h1238
                                              · linarith only [h1238, h4, hlam]
                                              · linarith only [h1101, h1238, hlam]
                                            · have p1213_0 := h1213c.1
                                              have p1213_1 := h1213c.2.1
                                              have p1213_2 := h1213c.2.2.1
                                              have p1213_3 := h1213c.2.2.2
                                              linarith only [h1100, hlam, p1213_0]
                                            · have p1213_0 := h1213c.1
                                              have p1213_1 := h1213c.2.1
                                              have p1213_2 := h1213c.2.2.1
                                              have p1213_3 := h1213c.2.2.2
                                              linarith only [h1109, hlam, p1213_0]
                                            · have p1213_0 := h1213c.1
                                              have p1213_1 := h1213c.2.1
                                              have p1213_2 := h1213c.2.2.1
                                              have p1213_3 := h1213c.2.2.2
                                              linarith only [h1111, hlam, p1213_0]
                                            · have p1213_0 := h1213c.1
                                              have p1213_1 := h1213c.2.1
                                              have p1213_2 := h1213c.2.2.1
                                              have p1213_3 := h1213c.2.2.2
                                              linarith only [hlam, p1213_0]
                                            · have p1213_0 := h1213c.1
                                              have p1213_1 := h1213c.2.1
                                              have p1213_2 := h1213c.2.2.1
                                              have p1213_3 := h1213c.2.2.2
                                              linarith only [h1109, h2, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1115_1, p1213_1, u3ehi4]
                                            · have p1213_0 := h1213c.1
                                              have p1213_1 := h1213c.2.1
                                              have p1213_2 := h1213c.2.2.1
                                              have p1213_3 := h1213c.2.2.2
                                              linarith only [h1101, hlam, p1213_0]
                                            · have p1213_0 := h1213c.1
                                              have p1213_1 := h1213c.2.1
                                              have p1213_2 := h1213c.2.2.1
                                              have p1213_3 := h1213c.2.2.2
                                              linarith only [h1110, hlam, p1213_0]
                                            · have p1213_0 := h1213c.1
                                              have p1213_1 := h1213c.2.1
                                              have p1213_2 := h1213c.2.2.1
                                              have p1213_3 := h1213c.2.2.2
                                              linarith only [h1112, hlam, p1213_0]
                                            · have p1213_0 := h1213c.1
                                              have p1213_1 := h1213c.2.1
                                              have p1213_2 := h1213c.2.2.1
                                              have p1213_3 := h1213c.2.2.2
                                              linarith only [h1114, hlam, p1213_0]
                                            · have p1213_0 := h1213c.1
                                              have p1213_1 := h1213c.2.1
                                              have p1213_2 := h1213c.2.2.1
                                              have p1213_3 := h1213c.2.2.2
                                              linarith only [hlam, p1213_0]
                                          · linarith only [h1212, hlam, p1163_0]
                                        · linarith only [h1211, h883, hlam]
                                      · linarith only [h1210, h4, hlam]
                                · have p1163_0 := h1163c.1
                                  have p1163_1 := h1163c.2.1
                                  have p1163_2 := h1163c.2.2.1
                                  have p1163_3 := h1163c.2.2.2
                                  rcases p1163_3 (m.d 0 2) (by simp) with h1254 | h1254
                                  · linarith only [h1033, h1254, hlam]
                                  · linarith only [h0, h1254, hlam]
                                · have p1163_0 := h1163c.1
                                  have p1163_1 := h1163c.2.1
                                  have p1163_2 := h1163c.2.2.1
                                  have p1163_3 := h1163c.2.2.2
                                  linarith only [h1112, hlam, p1163_1]
                                · have p1163_0 := h1163c.1
                                  have p1163_1 := h1163c.2.1
                                  have p1163_2 := h1163c.2.2.1
                                  have p1163_3 := h1163c.2.2.2
                                  linarith only [h1113, hlam, p1163_0]
                                · have p1163_0 := h1163c.1
                                  have p1163_1 := h1163c.2.1
                                  have p1163_2 := h1163c.2.2.1
                                  have p1163_3 := h1163c.2.2.2
                                  linarith only [hlam, p1163_0]
                          · linarith only [h1100, h1158, hlam]
                      · linarith only [h1155, h2, hlam]
                    · have p1115_0 := h1115c.1
                      have p1115_1 := h1115c.2.1
                      have p1115_2 := h1115c.2.2.1
                      have p1115_3 := h1115c.2.2.2
                      rcases p1115_3 (m.d 0 1) (by simp) with h1262 | h1262
                      · rcases p1115_3 (m.d 0 2) (by simp) with h1263 | h1263
                        · linarith only [h1263, h4, hlam]
                        · rcases p1115_3 (m.d 0 3) (by simp) with h1265 | h1265
                          · rcases p1115_3 (m.d 0 4) (by simp) with h1266 | h1266
                            · linarith only [h1100, h1266, hlam]
                            · linarith only [h1102, h1266, hlam]
                          · linarith only [h1101, h1265, hlam]
                      · linarith only [h1262, h3, hlam]
                    · have p1115_0 := h1115c.1
                      have p1115_1 := h1115c.2.1
                      have p1115_2 := h1115c.2.2.1
                      have p1115_3 := h1115c.2.2.2
                      linarith only [h2, hlam, p1115_0]
                    · have p1115_0 := h1115c.1
                      have p1115_1 := h1115c.2.1
                      have p1115_2 := h1115c.2.2.1
                      have p1115_3 := h1115c.2.2.2
                      rcases p1115_3 (m.d 0 1) (by simp) with h1272 | h1272
                      · rcases p1115_3 (m.d 0 2) (by simp) with h1273 | h1273
                        · linarith only [h1273, h883, hlam]
                        · rcases p1115_3 (m.d 0 3) (by simp) with h1275 | h1275
                          · rcases p1115_3 (m.d 0 4) (by simp) with h1276 | h1276
                            · rcases p1115_3 (m.d 0 5) (by simp) with h1277 | h1277
                              · linarith only [h1102, h1277, hlam]
                              · linarith only [h1033, h1277, hlam]
                            · linarith only [h1276, h883, hlam]
                          · linarith only [h1275, h4, hlam]
                      · linarith only [h0, h1272, hlam]
                    · have p1115_0 := h1115c.1
                      have p1115_1 := h1115c.2.1
                      have p1115_2 := h1115c.2.2.1
                      have p1115_3 := h1115c.2.2.2
                      linarith only [h1100, hlam, p1115_0]
                    · have p1115_0 := h1115c.1
                      have p1115_1 := h1115c.2.1
                      have p1115_2 := h1115c.2.2.1
                      have p1115_3 := h1115c.2.2.2
                      linarith only [hlam, p1115_0]
                    · have p1115_0 := h1115c.1
                      have p1115_1 := h1115c.2.1
                      have p1115_2 := h1115c.2.2.1
                      have p1115_3 := h1115c.2.2.2
                      rcases p1115_3 (m.d 0 1) (by simp) with h1285 | h1285
                      · rcases p1115_3 (m.d 0 2) (by simp) with h1286 | h1286
                        · linarith only [h1286, h883, hlam]
                        · rcases p1115_3 (m.d 0 3) (by simp) with h1288 | h1288
                          · rcases p1115_3 (m.d 0 4) (by simp) with h1289 | h1289
                            · rcases p1115_3 (m.d 0 5) (by simp) with h1290 | h1290
                              · linarith only [h1102, h1290, hlam]
                              · rcases h2bigk with h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c
                                · have p1292_0 := h1292c.1
                                  have p1292_1 := h1292c.2.1
                                  have p1292_2 := h1292c.2.2.1
                                  have p1292_3 := h1292c.2.2.2
                                  linarith only [hlam, p1292_0]
                                · have p1292_0 := h1292c.1
                                  have p1292_1 := h1292c.2.1
                                  have p1292_2 := h1292c.2.2.1
                                  have p1292_3 := h1292c.2.2.2
                                  linarith only [h4, hc12, hc23, hlam, hphi, p1292_1]
                                · have p1292_0 := h1292c.1
                                  have p1292_1 := h1292c.2.1
                                  have p1292_2 := h1292c.2.2.1
                                  have p1292_3 := h1292c.2.2.2
                                  linarith only [h4, hlam, p1292_0]
                                · have p1292_0 := h1292c.1
                                  have p1292_1 := h1292c.2.1
                                  have p1292_2 := h1292c.2.2.1
                                  have p1292_3 := h1292c.2.2.2
                                  linarith only [h883, hlam, p1292_0]
                                · have p1292_0 := h1292c.1
                                  have p1292_1 := h1292c.2.1
                                  have p1292_2 := h1292c.2.2.1
                                  have p1292_3 := h1292c.2.2.2
                                  linarith only [h1033, hlam, p1292_0]
                                · have p1292_0 := h1292c.1
                                  have p1292_1 := h1292c.2.1
                                  have p1292_2 := h1292c.2.2.1
                                  have p1292_3 := h1292c.2.2.2
                                  linarith only [h0, hlam, p1292_0]
                                · have p1292_0 := h1292c.1
                                  have p1292_1 := h1292c.2.1
                                  have p1292_2 := h1292c.2.2.1
                                  have p1292_3 := h1292c.2.2.2
                                  linarith only [hlam, p1292_0]
                                · have p1292_0 := h1292c.1
                                  have p1292_1 := h1292c.2.1
                                  have p1292_2 := h1292c.2.2.1
                                  have p1292_3 := h1292c.2.2.2
                                  linarith only [h1103, hlam, p1292_0]
                                · have p1292_0 := h1292c.1
                                  have p1292_1 := h1292c.2.1
                                  have p1292_2 := h1292c.2.2.1
                                  have p1292_3 := h1292c.2.2.2
                                  linarith only [h1105, hlam, p1292_0]
                                · have p1292_0 := h1292c.1
                                  have p1292_1 := h1292c.2.1
                                  have p1292_2 := h1292c.2.2.1
                                  have p1292_3 := h1292c.2.2.2
                                  linarith only [h1107, hlam, p1292_0]
                                · have p1292_0 := h1292c.1
                                  have p1292_1 := h1292c.2.1
                                  have p1292_2 := h1292c.2.2.1
                                  have p1292_3 := h1292c.2.2.2
                                  rcases p1292_3 (m.d 0 2) (by simp) with h1303 | h1303
                                  · linarith only [h1303, hlam, p1292_0]
                                  · rcases p1292_3 (m.d 1 2) (by simp) with h1305 | h1305
                                    · linarith only [h1103, h1305, hlam]
                                    · rcases p1292_3 (m.d 2 3) (by simp) with h1307 | h1307
                                      · rcases p1292_3 (m.d 2 4) (by simp) with h1308 | h1308
                                        · linarith only [h1111, h1308, hlam]
                                        · linarith only [h1308, h883, hlam]
                                      · linarith only [h1307, hlam, p1292_0]
                                · have p1292_0 := h1292c.1
                                  have p1292_1 := h1292c.2.1
                                  have p1292_2 := h1292c.2.2.1
                                  have p1292_3 := h1292c.2.2.2
                                  rcases p1292_3 (m.d 0 2) (by simp) with h1312 | h1312
                                  · linarith only [h1312, h4, hlam]
                                  · linarith only [h0, h1312, hlam]
                                · have p1292_0 := h1292c.1
                                  have p1292_1 := h1292c.2.1
                                  have p1292_2 := h1292c.2.2.1
                                  have p1292_3 := h1292c.2.2.2
                                  linarith only [hlam, p1292_0]
                                · have p1292_0 := h1292c.1
                                  have p1292_1 := h1292c.2.1
                                  have p1292_2 := h1292c.2.2.1
                                  have p1292_3 := h1292c.2.2.2
                                  linarith only [h883, hc02, hc23, hlam, hphi, p1292_1]
                                · have p1292_0 := h1292c.1
                                  have p1292_1 := h1292c.2.1
                                  have p1292_2 := h1292c.2.2.1
                                  have p1292_3 := h1292c.2.2.2
                                  linarith only [h0, h1033, hc12, hc23, hlam, hphi, p1292_1]
                                · have p1292_0 := h1292c.1
                                  have p1292_1 := h1292c.2.1
                                  have p1292_2 := h1292c.2.2.1
                                  have p1292_3 := h1292c.2.2.2
                                  rcases p1292_3 (m.d 0 2) (by simp) with h1318 | h1318
                                  · linarith only [h1318, hlam, p1292_0]
                                  · rcases p1292_3 (m.d 1 2) (by simp) with h1320 | h1320
                                    · linarith only [h1105, h1320, hlam]
                                    · rcases p1292_3 (m.d 2 3) (by simp) with h1322 | h1322
                                      · rcases p1292_3 (m.d 2 4) (by simp) with h1323 | h1323
                                        · rcases p1292_3 (m.d 2 5) (by simp) with h1324 | h1324
                                          · linarith only [h1113, h1324, hlam]
                                          · linarith only [h1033, h1324, hlam]
                                        · linarith only [h1323, hlam, p1292_0]
                                      · linarith only [h1322, h4, hlam]
                                · have p1292_0 := h1292c.1
                                  have p1292_1 := h1292c.2.1
                                  have p1292_2 := h1292c.2.2.1
                                  have p1292_3 := h1292c.2.2.2
                                  rcases p1292_3 (m.d 0 2) (by simp) with h1329 | h1329
                                  · linarith only [h1329, h883, hlam]
                                  · linarith only [h0, h1329, hlam]
                                · have p1292_0 := h1292c.1
                                  have p1292_1 := h1292c.2.1
                                  have p1292_2 := h1292c.2.2.1
                                  have p1292_3 := h1292c.2.2.2
                                  linarith only [h1111, hlam, p1292_1]
                                · have p1292_0 := h1292c.1
                                  have p1292_1 := h1292c.2.1
                                  have p1292_2 := h1292c.2.2.1
                                  have p1292_3 := h1292c.2.2.2
                                  linarith only [hlam, p1292_0]
                                · have p1292_0 := h1292c.1
                                  have p1292_1 := h1292c.2.1
                                  have p1292_2 := h1292c.2.2.1
                                  have p1292_3 := h1292c.2.2.2
                                  linarith only [h0, h1033, hc12, hc24, hlam, hphi, p1292_1]
                                · have p1292_0 := h1292c.1
                                  have p1292_1 := h1292c.2.1
                                  have p1292_2 := h1292c.2.2.1
                                  have p1292_3 := h1292c.2.2.2
                                  rcases p1292_3 (m.d 0 2) (by simp) with h1335 | h1335
                                  · linarith only [h1335, hlam, p1292_0]
                                  · rcases p1292_3 (m.d 1 2) (by simp) with h1337 | h1337
                                    · linarith only [h1107, h1337, hlam]
                                    · rcases p1292_3 (m.d 2 3) (by simp) with h1339 | h1339
                                      · rcases p1292_3 (m.d 2 4) (by simp) with h1340 | h1340
                                        · rcases p1292_3 (m.d 2 5) (by simp) with h1341 | h1341
                                          · rcases h3bigk with h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c
                                            · have p1342_0 := h1342c.1
                                              have p1342_1 := h1342c.2.1
                                              have p1342_2 := h1342c.2.2.1
                                              have p1342_3 := h1342c.2.2.2
                                              linarith only [hlam, p1342_0]
                                            · have p1342_0 := h1342c.1
                                              have p1342_1 := h1342c.2.1
                                              have p1342_2 := h1342c.2.2.1
                                              have p1342_3 := h1342c.2.2.2
                                              linarith only [h1109, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1342_1, u3ehi3]
                                            · have p1342_0 := h1342c.1
                                              have p1342_1 := h1342c.2.1
                                              have p1342_2 := h1342c.2.2.1
                                              have p1342_3 := h1342c.2.2.2
                                              linarith only [h4, hlam, p1342_1]
                                            · have p1342_0 := h1342c.1
                                              have p1342_1 := h1342c.2.1
                                              have p1342_2 := h1342c.2.2.1
                                              have p1342_3 := h1342c.2.2.2
                                              rcases p1342_3 (m.d 0 3) (by simp) with h1346 | h1346
                                              · rcases p1342_3 (m.d 1 3) (by simp) with h1347 | h1347
                                                · linarith only [h1, h1347, hlam]
                                                · linarith only [h1109, h1347, hlam]
                                              · linarith only [h1346, hlam, p1342_0]
                                            · have p1342_0 := h1342c.1
                                              have p1342_1 := h1342c.2.1
                                              have p1342_2 := h1342c.2.2.1
                                              have p1342_3 := h1342c.2.2.2
                                              rcases p1342_3 (m.d 0 3) (by simp) with h1351 | h1351
                                              · rcases p1342_3 (m.d 1 3) (by simp) with h1352 | h1352
                                                · linarith only [h1, h1352, hlam]
                                                · linarith only [h1110, h1352, hlam]
                                              · linarith only [h1351, hlam, p1342_0]
                                            · have p1342_0 := h1342c.1
                                              have p1342_1 := h1342c.2.1
                                              have p1342_2 := h1342c.2.2.1
                                              have p1342_3 := h1342c.2.2.2
                                              linarith only [h1, hlam, p1342_0]
                                            · have p1342_0 := h1342c.1
                                              have p1342_1 := h1342c.2.1
                                              have p1342_2 := h1342c.2.2.1
                                              have p1342_3 := h1342c.2.2.2
                                              linarith only [hlam, p1342_0]
                                            · have p1342_0 := h1342c.1
                                              have p1342_1 := h1342c.2.1
                                              have p1342_2 := h1342c.2.2.1
                                              have p1342_3 := h1342c.2.2.2
                                              linarith only [h1103, hlam, p1342_1]
                                            · have p1342_0 := h1342c.1
                                              have p1342_1 := h1342c.2.1
                                              have p1342_2 := h1342c.2.2.1
                                              have p1342_3 := h1342c.2.2.2
                                              linarith only [h1, h1114, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1342_1, u3ehi4]
                                            · have p1342_0 := h1342c.1
                                              have p1342_1 := h1342c.2.1
                                              have p1342_2 := h1342c.2.2.1
                                              have p1342_3 := h1342c.2.2.2
                                              linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1342_1, u3ehi4]
                                            · have p1342_0 := h1342c.1
                                              have p1342_1 := h1342c.2.1
                                              have p1342_2 := h1342c.2.2.1
                                              have p1342_3 := h1342c.2.2.2
                                              linarith only [h1100, h1114, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1342_1, u3ehi4]
                                            · have p1342_0 := h1342c.1
                                              have p1342_1 := h1342c.2.1
                                              have p1342_2 := h1342c.2.2.1
                                              have p1342_3 := h1342c.2.2.2
                                              linarith only [h1109, h1114, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1342_1, u3ehi4]
                                            · have p1342_0 := h1342c.1
                                              have p1342_1 := h1342c.2.1
                                              have p1342_2 := h1342c.2.2.1
                                              have p1342_3 := h1342c.2.2.2
                                              linarith only [hlam, p1342_0]
                                            · have p1342_0 := h1342c.1
                                              have p1342_1 := h1342c.2.1
                                              have p1342_2 := h1342c.2.2.1
                                              have p1342_3 := h1342c.2.2.2
                                              rcases p1342_3 (m.d 0 3) (by simp) with h1364 | h1364
                                              · linarith only [h1364, h4, hlam]
                                              · linarith only [h1100, h1364, hlam]
                                            · have p1342_0 := h1342c.1
                                              have p1342_1 := h1342c.2.1
                                              have p1342_2 := h1342c.2.2.1
                                              have p1342_3 := h1342c.2.2.2
                                              rcases p1342_3 (m.d 0 3) (by simp) with h1367 | h1367
                                              · linarith only [h1367, h4, hlam]
                                              · linarith only [h1101, h1367, hlam]
                                            · have p1342_0 := h1342c.1
                                              have p1342_1 := h1342c.2.1
                                              have p1342_2 := h1342c.2.2.1
                                              have p1342_3 := h1342c.2.2.2
                                              linarith only [h1100, hlam, p1342_0]
                                            · have p1342_0 := h1342c.1
                                              have p1342_1 := h1342c.2.1
                                              have p1342_2 := h1342c.2.2.1
                                              have p1342_3 := h1342c.2.2.2
                                              linarith only [h1109, hlam, p1342_0]
                                            · have p1342_0 := h1342c.1
                                              have p1342_1 := h1342c.2.1
                                              have p1342_2 := h1342c.2.2.1
                                              have p1342_3 := h1342c.2.2.2
                                              linarith only [h1111, hlam, p1342_0]
                                            · have p1342_0 := h1342c.1
                                              have p1342_1 := h1342c.2.1
                                              have p1342_2 := h1342c.2.2.1
                                              have p1342_3 := h1342c.2.2.2
                                              linarith only [hlam, p1342_0]
                                            · have p1342_0 := h1342c.1
                                              have p1342_1 := h1342c.2.1
                                              have p1342_2 := h1342c.2.2.1
                                              have p1342_3 := h1342c.2.2.2
                                              linarith only [h1109, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1342_1, u3ehi4]
                                            · have p1342_0 := h1342c.1
                                              have p1342_1 := h1342c.2.1
                                              have p1342_2 := h1342c.2.2.1
                                              have p1342_3 := h1342c.2.2.2
                                              linarith only [h1101, hlam, p1342_0]
                                            · have p1342_0 := h1342c.1
                                              have p1342_1 := h1342c.2.1
                                              have p1342_2 := h1342c.2.2.1
                                              have p1342_3 := h1342c.2.2.2
                                              linarith only [h1110, hlam, p1342_0]
                                            · have p1342_0 := h1342c.1
                                              have p1342_1 := h1342c.2.1
                                              have p1342_2 := h1342c.2.2.1
                                              have p1342_3 := h1342c.2.2.2
                                              linarith only [h1112, hlam, p1342_0]
                                            · have p1342_0 := h1342c.1
                                              have p1342_1 := h1342c.2.1
                                              have p1342_2 := h1342c.2.2.1
                                              have p1342_3 := h1342c.2.2.2
                                              linarith only [h1114, hlam, p1342_0]
                                            · have p1342_0 := h1342c.1
                                              have p1342_1 := h1342c.2.1
                                              have p1342_2 := h1342c.2.2.1
                                              have p1342_3 := h1342c.2.2.2
                                              linarith only [hlam, p1342_0]
                                          · linarith only [h1341, hlam, p1292_0]
                                        · linarith only [h1340, h883, hlam]
                                      · linarith only [h1339, h4, hlam]
                                · have p1292_0 := h1292c.1
                                  have p1292_1 := h1292c.2.1
                                  have p1292_2 := h1292c.2.2.1
                                  have p1292_3 := h1292c.2.2.2
                                  rcases p1292_3 (m.d 0 2) (by simp) with h1383 | h1383
                                  · linarith only [h1033, h1383, hlam]
                                  · linarith only [h0, h1383, hlam]
                                · have p1292_0 := h1292c.1
                                  have p1292_1 := h1292c.2.1
                                  have p1292_2 := h1292c.2.2.1
                                  have p1292_3 := h1292c.2.2.2
                                  linarith only [h1112, hlam, p1292_1]
                                · have p1292_0 := h1292c.1
                                  have p1292_1 := h1292c.2.1
                                  have p1292_2 := h1292c.2.2.1
                                  have p1292_3 := h1292c.2.2.2
                                  linarith only [h1113, hlam, p1292_0]
                                · have p1292_0 := h1292c.1
                                  have p1292_1 := h1292c.2.1
                                  have p1292_2 := h1292c.2.2.1
                                  have p1292_3 := h1292c.2.2.2
                                  linarith only [hlam, p1292_0]
                            · linarith only [h1102, h1289, hlam]
                          · linarith only [h1101, h1288, hlam]
                      · linarith only [h1285, h3, hlam]
                    · have p1115_0 := h1115c.1
                      have p1115_1 := h1115c.2.1
                      have p1115_2 := h1115c.2.2.1
                      have p1115_3 := h1115c.2.2.2
                      linarith only [h3, hlam, p1115_0]
                    · have p1115_0 := h1115c.1
                      have p1115_1 := h1115c.2.1
                      have p1115_2 := h1115c.2.2.1
                      have p1115_3 := h1115c.2.2.2
                      rcases p1115_3 (m.d 0 1) (by simp) with h1393 | h1393
                      · rcases p1115_3 (m.d 0 2) (by simp) with h1394 | h1394
                        · linarith only [h1033, h1394, hlam]
                        · rcases p1115_3 (m.d 0 3) (by simp) with h1396 | h1396
                          · rcases p1115_3 (m.d 0 4) (by simp) with h1397 | h1397
                            · rcases p1115_3 (m.d 0 5) (by simp) with h1398 | h1398
                              · rcases h2bigk with h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c
                                · have p1399_0 := h1399c.1
                                  have p1399_1 := h1399c.2.1
                                  have p1399_2 := h1399c.2.2.1
                                  have p1399_3 := h1399c.2.2.2
                                  linarith only [hlam, p1399_0]
                                · have p1399_0 := h1399c.1
                                  have p1399_1 := h1399c.2.1
                                  have p1399_2 := h1399c.2.2.1
                                  have p1399_3 := h1399c.2.2.2
                                  linarith only [hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1115_1, p1399_1]
                                · have p1399_0 := h1399c.1
                                  have p1399_1 := h1399c.2.1
                                  have p1399_2 := h1399c.2.2.1
                                  have p1399_3 := h1399c.2.2.2
                                  linarith only [h4, hlam, p1399_0]
                                · have p1399_0 := h1399c.1
                                  have p1399_1 := h1399c.2.1
                                  have p1399_2 := h1399c.2.2.1
                                  have p1399_3 := h1399c.2.2.2
                                  linarith only [h883, hlam, p1399_0]
                                · have p1399_0 := h1399c.1
                                  have p1399_1 := h1399c.2.1
                                  have p1399_2 := h1399c.2.2.1
                                  have p1399_3 := h1399c.2.2.2
                                  linarith only [h1033, hlam, p1399_0]
                                · have p1399_0 := h1399c.1
                                  have p1399_1 := h1399c.2.1
                                  have p1399_2 := h1399c.2.2.1
                                  have p1399_3 := h1399c.2.2.2
                                  linarith only [h0, hlam, p1399_0]
                                · have p1399_0 := h1399c.1
                                  have p1399_1 := h1399c.2.1
                                  have p1399_2 := h1399c.2.2.1
                                  have p1399_3 := h1399c.2.2.2
                                  linarith only [hlam, p1399_0]
                                · have p1399_0 := h1399c.1
                                  have p1399_1 := h1399c.2.1
                                  have p1399_2 := h1399c.2.2.1
                                  have p1399_3 := h1399c.2.2.2
                                  linarith only [h1103, hlam, p1399_0]
                                · have p1399_0 := h1399c.1
                                  have p1399_1 := h1399c.2.1
                                  have p1399_2 := h1399c.2.2.1
                                  have p1399_3 := h1399c.2.2.2
                                  linarith only [h1105, hlam, p1399_0]
                                · have p1399_0 := h1399c.1
                                  have p1399_1 := h1399c.2.1
                                  have p1399_2 := h1399c.2.2.1
                                  have p1399_3 := h1399c.2.2.2
                                  linarith only [h1107, hlam, p1399_0]
                                · have p1399_0 := h1399c.1
                                  have p1399_1 := h1399c.2.1
                                  have p1399_2 := h1399c.2.2.1
                                  have p1399_3 := h1399c.2.2.2
                                  rcases p1399_3 (m.d 0 2) (by simp) with h1410 | h1410
                                  · linarith only [h1410, hlam, p1399_0]
                                  · rcases p1399_3 (m.d 1 2) (by simp) with h1412 | h1412
                                    · linarith only [h1103, h1412, hlam]
                                    · rcases p1399_3 (m.d 2 3) (by simp) with h1414 | h1414
                                      · rcases p1399_3 (m.d 2 4) (by simp) with h1415 | h1415
                                        · linarith only [h1111, h1415, hlam]
                                        · linarith only [h1415, h883, hlam]
                                      · linarith only [h1414, hlam, p1399_0]
                                · have p1399_0 := h1399c.1
                                  have p1399_1 := h1399c.2.1
                                  have p1399_2 := h1399c.2.2.1
                                  have p1399_3 := h1399c.2.2.2
                                  rcases p1399_3 (m.d 0 2) (by simp) with h1419 | h1419
                                  · linarith only [h1419, h4, hlam]
                                  · linarith only [h0, h1419, hlam]
                                · have p1399_0 := h1399c.1
                                  have p1399_1 := h1399c.2.1
                                  have p1399_2 := h1399c.2.2.1
                                  have p1399_3 := h1399c.2.2.2
                                  linarith only [hlam, p1399_0]
                                · have p1399_0 := h1399c.1
                                  have p1399_1 := h1399c.2.1
                                  have p1399_2 := h1399c.2.2.1
                                  have p1399_3 := h1399c.2.2.2
                                  linarith only [h883, hc02, hc23, hlam, hphi, p1399_1]
                                · have p1399_0 := h1399c.1
                                  have p1399_1 := h1399c.2.1
                                  have p1399_2 := h1399c.2.2.1
                                  have p1399_3 := h1399c.2.2.2
                                  linarith only [h0, h1033, hc12, hc23, hlam, hphi, p1399_1]
                                · have p1399_0 := h1399c.1
                                  have p1399_1 := h1399c.2.1
                                  have p1399_2 := h1399c.2.2.1
                                  have p1399_3 := h1399c.2.2.2
                                  rcases p1399_3 (m.d 0 2) (by simp) with h1425 | h1425
                                  · linarith only [h1425, hlam, p1399_0]
                                  · rcases p1399_3 (m.d 1 2) (by simp) with h1427 | h1427
                                    · linarith only [h1105, h1427, hlam]
                                    · rcases p1399_3 (m.d 2 3) (by simp) with h1429 | h1429
                                      · rcases p1399_3 (m.d 2 4) (by simp) with h1430 | h1430
                                        · rcases p1399_3 (m.d 2 5) (by simp) with h1431 | h1431
                                          · linarith only [h1113, h1431, hlam]
                                          · linarith only [h1033, h1431, hlam]
                                        · linarith only [h1430, hlam, p1399_0]
                                      · linarith only [h1429, h4, hlam]
                                · have p1399_0 := h1399c.1
                                  have p1399_1 := h1399c.2.1
                                  have p1399_2 := h1399c.2.2.1
                                  have p1399_3 := h1399c.2.2.2
                                  rcases p1399_3 (m.d 0 2) (by simp) with h1436 | h1436
                                  · linarith only [h1436, h883, hlam]
                                  · linarith only [h0, h1436, hlam]
                                · have p1399_0 := h1399c.1
                                  have p1399_1 := h1399c.2.1
                                  have p1399_2 := h1399c.2.2.1
                                  have p1399_3 := h1399c.2.2.2
                                  linarith only [h1111, hlam, p1399_1]
                                · have p1399_0 := h1399c.1
                                  have p1399_1 := h1399c.2.1
                                  have p1399_2 := h1399c.2.2.1
                                  have p1399_3 := h1399c.2.2.2
                                  linarith only [hlam, p1399_0]
                                · have p1399_0 := h1399c.1
                                  have p1399_1 := h1399c.2.1
                                  have p1399_2 := h1399c.2.2.1
                                  have p1399_3 := h1399c.2.2.2
                                  linarith only [h0, h1033, hc12, hc24, hlam, hphi, p1115_1, p1399_1]
                                · have p1399_0 := h1399c.1
                                  have p1399_1 := h1399c.2.1
                                  have p1399_2 := h1399c.2.2.1
                                  have p1399_3 := h1399c.2.2.2
                                  rcases p1399_3 (m.d 0 2) (by simp) with h1442 | h1442
                                  · linarith only [h1442, hlam, p1399_0]
                                  · rcases p1399_3 (m.d 1 2) (by simp) with h1444 | h1444
                                    · linarith only [h1107, h1444, hlam]
                                    · rcases p1399_3 (m.d 2 3) (by simp) with h1446 | h1446
                                      · rcases p1399_3 (m.d 2 4) (by simp) with h1447 | h1447
                                        · rcases p1399_3 (m.d 2 5) (by simp) with h1448 | h1448
                                          · rcases h3bigk with h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c
                                            · have p1449_0 := h1449c.1
                                              have p1449_1 := h1449c.2.1
                                              have p1449_2 := h1449c.2.2.1
                                              have p1449_3 := h1449c.2.2.2
                                              linarith only [hlam, p1449_0]
                                            · have p1449_0 := h1449c.1
                                              have p1449_1 := h1449c.2.1
                                              have p1449_2 := h1449c.2.2.1
                                              have p1449_3 := h1449c.2.2.2
                                              linarith only [h1109, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1449_1, u3ehi3]
                                            · have p1449_0 := h1449c.1
                                              have p1449_1 := h1449c.2.1
                                              have p1449_2 := h1449c.2.2.1
                                              have p1449_3 := h1449c.2.2.2
                                              linarith only [h4, hlam, p1449_1]
                                            · have p1449_0 := h1449c.1
                                              have p1449_1 := h1449c.2.1
                                              have p1449_2 := h1449c.2.2.1
                                              have p1449_3 := h1449c.2.2.2
                                              rcases p1449_3 (m.d 0 3) (by simp) with h1453 | h1453
                                              · rcases p1449_3 (m.d 1 3) (by simp) with h1454 | h1454
                                                · linarith only [h1, h1454, hlam]
                                                · linarith only [h1109, h1454, hlam]
                                              · linarith only [h1453, hlam, p1449_0]
                                            · have p1449_0 := h1449c.1
                                              have p1449_1 := h1449c.2.1
                                              have p1449_2 := h1449c.2.2.1
                                              have p1449_3 := h1449c.2.2.2
                                              rcases p1449_3 (m.d 0 3) (by simp) with h1458 | h1458
                                              · rcases p1449_3 (m.d 1 3) (by simp) with h1459 | h1459
                                                · linarith only [h1, h1459, hlam]
                                                · linarith only [h1110, h1459, hlam]
                                              · linarith only [h1458, hlam, p1449_0]
                                            · have p1449_0 := h1449c.1
                                              have p1449_1 := h1449c.2.1
                                              have p1449_2 := h1449c.2.2.1
                                              have p1449_3 := h1449c.2.2.2
                                              linarith only [h1, hlam, p1449_0]
                                            · have p1449_0 := h1449c.1
                                              have p1449_1 := h1449c.2.1
                                              have p1449_2 := h1449c.2.2.1
                                              have p1449_3 := h1449c.2.2.2
                                              linarith only [hlam, p1449_0]
                                            · have p1449_0 := h1449c.1
                                              have p1449_1 := h1449c.2.1
                                              have p1449_2 := h1449c.2.2.1
                                              have p1449_3 := h1449c.2.2.2
                                              linarith only [h1103, hlam, p1449_1]
                                            · have p1449_0 := h1449c.1
                                              have p1449_1 := h1449c.2.1
                                              have p1449_2 := h1449c.2.2.1
                                              have p1449_3 := h1449c.2.2.2
                                              linarith only [h1, h1114, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1449_1, u3ehi4]
                                            · have p1449_0 := h1449c.1
                                              have p1449_1 := h1449c.2.1
                                              have p1449_2 := h1449c.2.2.1
                                              have p1449_3 := h1449c.2.2.2
                                              linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1449_1, u3ehi4]
                                            · have p1449_0 := h1449c.1
                                              have p1449_1 := h1449c.2.1
                                              have p1449_2 := h1449c.2.2.1
                                              have p1449_3 := h1449c.2.2.2
                                              linarith only [h1100, h1114, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1449_1, u3ehi4]
                                            · have p1449_0 := h1449c.1
                                              have p1449_1 := h1449c.2.1
                                              have p1449_2 := h1449c.2.2.1
                                              have p1449_3 := h1449c.2.2.2
                                              linarith only [h1109, h1114, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1449_1, u3ehi4]
                                            · have p1449_0 := h1449c.1
                                              have p1449_1 := h1449c.2.1
                                              have p1449_2 := h1449c.2.2.1
                                              have p1449_3 := h1449c.2.2.2
                                              linarith only [hlam, p1449_0]
                                            · have p1449_0 := h1449c.1
                                              have p1449_1 := h1449c.2.1
                                              have p1449_2 := h1449c.2.2.1
                                              have p1449_3 := h1449c.2.2.2
                                              rcases p1449_3 (m.d 0 3) (by simp) with h1471 | h1471
                                              · linarith only [h1471, h4, hlam]
                                              · linarith only [h1100, h1471, hlam]
                                            · have p1449_0 := h1449c.1
                                              have p1449_1 := h1449c.2.1
                                              have p1449_2 := h1449c.2.2.1
                                              have p1449_3 := h1449c.2.2.2
                                              rcases p1449_3 (m.d 0 3) (by simp) with h1474 | h1474
                                              · linarith only [h1474, h4, hlam]
                                              · linarith only [h1101, h1474, hlam]
                                            · have p1449_0 := h1449c.1
                                              have p1449_1 := h1449c.2.1
                                              have p1449_2 := h1449c.2.2.1
                                              have p1449_3 := h1449c.2.2.2
                                              linarith only [h1100, hlam, p1449_0]
                                            · have p1449_0 := h1449c.1
                                              have p1449_1 := h1449c.2.1
                                              have p1449_2 := h1449c.2.2.1
                                              have p1449_3 := h1449c.2.2.2
                                              linarith only [h1109, hlam, p1449_0]
                                            · have p1449_0 := h1449c.1
                                              have p1449_1 := h1449c.2.1
                                              have p1449_2 := h1449c.2.2.1
                                              have p1449_3 := h1449c.2.2.2
                                              linarith only [h1111, hlam, p1449_0]
                                            · have p1449_0 := h1449c.1
                                              have p1449_1 := h1449c.2.1
                                              have p1449_2 := h1449c.2.2.1
                                              have p1449_3 := h1449c.2.2.2
                                              linarith only [hlam, p1449_0]
                                            · have p1449_0 := h1449c.1
                                              have p1449_1 := h1449c.2.1
                                              have p1449_2 := h1449c.2.2.1
                                              have p1449_3 := h1449c.2.2.2
                                              linarith only [h1109, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1449_1, u3ehi4]
                                            · have p1449_0 := h1449c.1
                                              have p1449_1 := h1449c.2.1
                                              have p1449_2 := h1449c.2.2.1
                                              have p1449_3 := h1449c.2.2.2
                                              linarith only [h1101, hlam, p1449_0]
                                            · have p1449_0 := h1449c.1
                                              have p1449_1 := h1449c.2.1
                                              have p1449_2 := h1449c.2.2.1
                                              have p1449_3 := h1449c.2.2.2
                                              linarith only [h1110, hlam, p1449_0]
                                            · have p1449_0 := h1449c.1
                                              have p1449_1 := h1449c.2.1
                                              have p1449_2 := h1449c.2.2.1
                                              have p1449_3 := h1449c.2.2.2
                                              linarith only [h1112, hlam, p1449_0]
                                            · have p1449_0 := h1449c.1
                                              have p1449_1 := h1449c.2.1
                                              have p1449_2 := h1449c.2.2.1
                                              have p1449_3 := h1449c.2.2.2
                                              linarith only [h1114, hlam, p1449_0]
                                            · have p1449_0 := h1449c.1
                                              have p1449_1 := h1449c.2.1
                                              have p1449_2 := h1449c.2.2.1
                                              have p1449_3 := h1449c.2.2.2
                                              linarith only [hlam, p1449_0]
                                          · linarith only [h1448, hlam, p1399_0]
                                        · linarith only [h1447, h883, hlam]
                                      · linarith only [h1446, h4, hlam]
                                · have p1399_0 := h1399c.1
                                  have p1399_1 := h1399c.2.1
                                  have p1399_2 := h1399c.2.2.1
                                  have p1399_3 := h1399c.2.2.2
                                  rcases p1399_3 (m.d 0 2) (by simp) with h1490 | h1490
                                  · linarith only [h1033, h1490, hlam]
                                  · linarith only [h0, h1490, hlam]
                                · have p1399_0 := h1399c.1
                                  have p1399_1 := h1399c.2.1
                                  have p1399_2 := h1399c.2.2.1
                                  have p1399_3 := h1399c.2.2.2
                                  linarith only [h1112, hlam, p1399_1]
                                · have p1399_0 := h1399c.1
                                  have p1399_1 := h1399c.2.1
                                  have p1399_2 := h1399c.2.2.1
                                  have p1399_3 := h1399c.2.2.2
                                  linarith only [h1113, hlam, p1399_0]
                                · have p1399_0 := h1399c.1
                                  have p1399_1 := h1399c.2.1
                                  have p1399_2 := h1399c.2.2.1
                                  have p1399_3 := h1399c.2.2.2
                                  linarith only [hlam, p1399_0]
                              · linarith only [h1033, h1398, hlam]
                            · linarith only [h1397, h883, hlam]
                          · linarith only [h1396, h4, hlam]
                      · linarith only [h0, h1393, hlam]
                    · have p1115_0 := h1115c.1
                      have p1115_1 := h1115c.2.1
                      have p1115_2 := h1115c.2.2.1
                      have p1115_3 := h1115c.2.2.2
                      linarith only [h1101, hlam, p1115_0]
                    · have p1115_0 := h1115c.1
                      have p1115_1 := h1115c.2.1
                      have p1115_2 := h1115c.2.2.1
                      have p1115_3 := h1115c.2.2.2
                      linarith only [h1102, hlam, p1115_1]
                    · have p1115_0 := h1115c.1
                      have p1115_1 := h1115c.2.1
                      have p1115_2 := h1115c.2.2.1
                      have p1115_3 := h1115c.2.2.2
                      linarith only [hlam, p1115_0]
                  · rcases h0bigk with h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c | h1503c
                    · have p1503_0 := h1503c.1
                      have p1503_1 := h1503c.2.1
                      have p1503_2 := h1503c.2.2.1
                      have p1503_3 := h1503c.2.2.2
                      linarith only [hlam, p1503_0]
                    · have p1503_0 := h1503c.1
                      have p1503_1 := h1503c.2.1
                      have p1503_2 := h1503c.2.2.1
                      have p1503_3 := h1503c.2.2.2
                      rcases p1503_3 (m.d 0 1) (by simp) with h1505 | h1505
                      · rcases p1503_3 (m.d 0 2) (by simp) with h1506 | h1506
                        · linarith only [h0, h1506, hlam]
                        · rcases p1503_3 (m.d 0 3) (by simp) with h1508 | h1508
                          · linarith only [h1, h1508, hlam]
                          · linarith only [h1508, h4, hlam]
                      · linarith only [h0, h1505, hlam]
                    · have p1503_0 := h1503c.1
                      have p1503_1 := h1503c.2.1
                      have p1503_2 := h1503c.2.2.1
                      have p1503_3 := h1503c.2.2.2
                      linarith only [h1100, h1102, h1114, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1503_1, u3ehi3]
                    · have p1503_0 := h1503c.1
                      have p1503_1 := h1503c.2.1
                      have p1503_2 := h1503c.2.2.1
                      have p1503_3 := h1503c.2.2.2
                      linarith only [h1102, h1114, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1503_1, u3ehi3]
                    · have p1503_0 := h1503c.1
                      have p1503_1 := h1503c.2.1
                      have p1503_2 := h1503c.2.2.1
                      have p1503_3 := h1503c.2.2.2
                      linarith only [h1102, h1114, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1503_1, u3ehi3]
                    · have p1503_0 := h1503c.1
                      have p1503_1 := h1503c.2.1
                      have p1503_2 := h1503c.2.2.1
                      have p1503_3 := h1503c.2.2.2
                      linarith only [h0, hlam, p1503_0]
                    · have p1503_0 := h1503c.1
                      have p1503_1 := h1503c.2.1
                      have p1503_2 := h1503c.2.2.1
                      have p1503_3 := h1503c.2.2.2
                      linarith only [hlam, p1503_0]
                    · have p1503_0 := h1503c.1
                      have p1503_1 := h1503c.2.1
                      have p1503_2 := h1503c.2.2.1
                      have p1503_3 := h1503c.2.2.2
                      linarith only [h4, hlam, p1503_0]
                    · have p1503_0 := h1503c.1
                      have p1503_1 := h1503c.2.1
                      have p1503_2 := h1503c.2.2.1
                      have p1503_3 := h1503c.2.2.2
                      linarith only [h883, hlam, p1503_1]
                    · have p1503_0 := h1503c.1
                      have p1503_1 := h1503c.2.1
                      have p1503_2 := h1503c.2.2.1
                      have p1503_3 := h1503c.2.2.2
                      linarith only [h1033, hlam, p1503_0]
                    · have p1503_0 := h1503c.1
                      have p1503_1 := h1503c.2.1
                      have p1503_2 := h1503c.2.2.1
                      have p1503_3 := h1503c.2.2.2
                      linarith only [h1, hlam, p1503_1]
                    · have p1503_0 := h1503c.1
                      have p1503_1 := h1503c.2.1
                      have p1503_2 := h1503c.2.2.1
                      have p1503_3 := h1503c.2.2.2
                      rcases p1503_3 (m.d 0 1) (by simp) with h1521 | h1521
                      · rcases p1503_3 (m.d 0 2) (by simp) with h1522 | h1522
                        · linarith only [h1522, h4, hlam]
                        · rcases p1503_3 (m.d 0 3) (by simp) with h1524 | h1524
                          · rcases p1503_3 (m.d 0 4) (by simp) with h1525 | h1525
                            · linarith only [h1100, h1525, hlam]
                            · linarith only [h1525, h883, hlam]
                          · linarith only [h1524, h4, hlam]
                      · linarith only [h0, h1521, hlam]
                    · have p1503_0 := h1503c.1
                      have p1503_1 := h1503c.2.1
                      have p1503_2 := h1503c.2.2.1
                      have p1503_3 := h1503c.2.2.2
                      linarith only [hlam, p1503_0]
                    · have p1503_0 := h1503c.1
                      have p1503_1 := h1503c.2.1
                      have p1503_2 := h1503c.2.2.1
                      have p1503_3 := h1503c.2.2.2
                      linarith only [h1102, h1114, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1503_1, u3ehi3]
                    · have p1503_0 := h1503c.1
                      have p1503_1 := h1503c.2.1
                      have p1503_2 := h1503c.2.2.1
                      have p1503_3 := h1503c.2.2.2
                      linarith only [h1102, h1114, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1503_1, u3ehi3]
                    · have p1503_0 := h1503c.1
                      have p1503_1 := h1503c.2.1
                      have p1503_2 := h1503c.2.2.1
                      have p1503_3 := h1503c.2.2.2
                      linarith only [h2, hlam, p1503_0]
                    · have p1503_0 := h1503c.1
                      have p1503_1 := h1503c.2.1
                      have p1503_2 := h1503c.2.2.1
                      have p1503_3 := h1503c.2.2.2
                      rcases p1503_3 (m.d 0 1) (by simp) with h1534 | h1534
                      · rcases p1503_3 (m.d 0 2) (by simp) with h1535 | h1535
                        · linarith only [h1535, h883, hlam]
                        · rcases p1503_3 (m.d 0 3) (by simp) with h1537 | h1537
                          · rcases p1503_3 (m.d 0 4) (by simp) with h1538 | h1538
                            · rcases p1503_3 (m.d 0 5) (by simp) with h1539 | h1539
                              · linarith only [h1102, h1539, hlam]
                              · linarith only [h1033, h1539, hlam]
                            · linarith only [h1538, h883, hlam]
                          · linarith only [h1537, h4, hlam]
                      · linarith only [h0, h1534, hlam]
                    · have p1503_0 := h1503c.1
                      have p1503_1 := h1503c.2.1
                      have p1503_2 := h1503c.2.2.1
                      have p1503_3 := h1503c.2.2.2
                      linarith only [h1100, hlam, p1503_0]
                    · have p1503_0 := h1503c.1
                      have p1503_1 := h1503c.2.1
                      have p1503_2 := h1503c.2.2.1
                      have p1503_3 := h1503c.2.2.2
                      linarith only [hlam, p1503_0]
                    · have p1503_0 := h1503c.1
                      have p1503_1 := h1503c.2.1
                      have p1503_2 := h1503c.2.2.1
                      have p1503_3 := h1503c.2.2.2
                      linarith only [h1102, h1114, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1503_1, u3ehi3]
                    · have p1503_0 := h1503c.1
                      have p1503_1 := h1503c.2.1
                      have p1503_2 := h1503c.2.2.1
                      have p1503_3 := h1503c.2.2.2
                      linarith only [h3, hlam, p1503_0]
                    · have p1503_0 := h1503c.1
                      have p1503_1 := h1503c.2.1
                      have p1503_2 := h1503c.2.2.1
                      have p1503_3 := h1503c.2.2.2
                      rcases p1503_3 (m.d 0 1) (by simp) with h1549 | h1549
                      · rcases p1503_3 (m.d 0 2) (by simp) with h1550 | h1550
                        · linarith only [h1033, h1550, hlam]
                        · rcases p1503_3 (m.d 0 3) (by simp) with h1552 | h1552
                          · rcases p1503_3 (m.d 0 4) (by simp) with h1553 | h1553
                            · rcases p1503_3 (m.d 0 5) (by simp) with h1554 | h1554
                              · rcases h2bigk with h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c
                                · have p1555_0 := h1555c.1
                                  have p1555_1 := h1555c.2.1
                                  have p1555_2 := h1555c.2.2.1
                                  have p1555_3 := h1555c.2.2.2
                                  linarith only [hlam, p1555_0]
                                · have p1555_0 := h1555c.1
                                  have p1555_1 := h1555c.2.1
                                  have p1555_2 := h1555c.2.2.1
                                  have p1555_3 := h1555c.2.2.2
                                  linarith only [hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1503_1, p1555_1]
                                · have p1555_0 := h1555c.1
                                  have p1555_1 := h1555c.2.1
                                  have p1555_2 := h1555c.2.2.1
                                  have p1555_3 := h1555c.2.2.2
                                  linarith only [h4, hlam, p1555_0]
                                · have p1555_0 := h1555c.1
                                  have p1555_1 := h1555c.2.1
                                  have p1555_2 := h1555c.2.2.1
                                  have p1555_3 := h1555c.2.2.2
                                  linarith only [h883, hlam, p1555_0]
                                · have p1555_0 := h1555c.1
                                  have p1555_1 := h1555c.2.1
                                  have p1555_2 := h1555c.2.2.1
                                  have p1555_3 := h1555c.2.2.2
                                  linarith only [h1033, hlam, p1555_0]
                                · have p1555_0 := h1555c.1
                                  have p1555_1 := h1555c.2.1
                                  have p1555_2 := h1555c.2.2.1
                                  have p1555_3 := h1555c.2.2.2
                                  linarith only [h0, hlam, p1555_0]
                                · have p1555_0 := h1555c.1
                                  have p1555_1 := h1555c.2.1
                                  have p1555_2 := h1555c.2.2.1
                                  have p1555_3 := h1555c.2.2.2
                                  linarith only [hlam, p1555_0]
                                · have p1555_0 := h1555c.1
                                  have p1555_1 := h1555c.2.1
                                  have p1555_2 := h1555c.2.2.1
                                  have p1555_3 := h1555c.2.2.2
                                  linarith only [h1103, hlam, p1555_0]
                                · have p1555_0 := h1555c.1
                                  have p1555_1 := h1555c.2.1
                                  have p1555_2 := h1555c.2.2.1
                                  have p1555_3 := h1555c.2.2.2
                                  linarith only [h1105, hlam, p1555_0]
                                · have p1555_0 := h1555c.1
                                  have p1555_1 := h1555c.2.1
                                  have p1555_2 := h1555c.2.2.1
                                  have p1555_3 := h1555c.2.2.2
                                  linarith only [h1107, hlam, p1555_0]
                                · have p1555_0 := h1555c.1
                                  have p1555_1 := h1555c.2.1
                                  have p1555_2 := h1555c.2.2.1
                                  have p1555_3 := h1555c.2.2.2
                                  rcases p1555_3 (m.d 0 2) (by simp) with h1566 | h1566
                                  · linarith only [h1566, hlam, p1555_0]
                                  · rcases p1555_3 (m.d 1 2) (by simp) with h1568 | h1568
                                    · linarith only [h1103, h1568, hlam]
                                    · rcases p1555_3 (m.d 2 3) (by simp) with h1570 | h1570
                                      · rcases p1555_3 (m.d 2 4) (by simp) with h1571 | h1571
                                        · linarith only [h1111, h1571, hlam]
                                        · linarith only [h1571, h883, hlam]
                                      · linarith only [h1570, hlam, p1555_0]
                                · have p1555_0 := h1555c.1
                                  have p1555_1 := h1555c.2.1
                                  have p1555_2 := h1555c.2.2.1
                                  have p1555_3 := h1555c.2.2.2
                                  rcases p1555_3 (m.d 0 2) (by simp) with h1575 | h1575
                                  · linarith only [h1575, h4, hlam]
                                  · linarith only [h0, h1575, hlam]
                                · have p1555_0 := h1555c.1
                                  have p1555_1 := h1555c.2.1
                                  have p1555_2 := h1555c.2.2.1
                                  have p1555_3 := h1555c.2.2.2
                                  linarith only [hlam, p1555_0]
                                · have p1555_0 := h1555c.1
                                  have p1555_1 := h1555c.2.1
                                  have p1555_2 := h1555c.2.2.1
                                  have p1555_3 := h1555c.2.2.2
                                  linarith only [h1102, h1114, h883, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1555_1, u3ehi3]
                                · have p1555_0 := h1555c.1
                                  have p1555_1 := h1555c.2.1
                                  have p1555_2 := h1555c.2.2.1
                                  have p1555_3 := h1555c.2.2.2
                                  linarith only [h1033, hc02, hc23, hlam, hphi, p1555_1]
                                · have p1555_0 := h1555c.1
                                  have p1555_1 := h1555c.2.1
                                  have p1555_2 := h1555c.2.2.1
                                  have p1555_3 := h1555c.2.2.2
                                  rcases p1555_3 (m.d 0 2) (by simp) with h1581 | h1581
                                  · linarith only [h1581, hlam, p1555_0]
                                  · rcases p1555_3 (m.d 1 2) (by simp) with h1583 | h1583
                                    · linarith only [h1105, h1583, hlam]
                                    · rcases p1555_3 (m.d 2 3) (by simp) with h1585 | h1585
                                      · rcases p1555_3 (m.d 2 4) (by simp) with h1586 | h1586
                                        · rcases p1555_3 (m.d 2 5) (by simp) with h1587 | h1587
                                          · linarith only [h1113, h1587, hlam]
                                          · linarith only [h1033, h1587, hlam]
                                        · linarith only [h1586, hlam, p1555_0]
                                      · linarith only [h1585, h4, hlam]
                                · have p1555_0 := h1555c.1
                                  have p1555_1 := h1555c.2.1
                                  have p1555_2 := h1555c.2.2.1
                                  have p1555_3 := h1555c.2.2.2
                                  rcases p1555_3 (m.d 0 2) (by simp) with h1592 | h1592
                                  · linarith only [h1592, h883, hlam]
                                  · linarith only [h0, h1592, hlam]
                                · have p1555_0 := h1555c.1
                                  have p1555_1 := h1555c.2.1
                                  have p1555_2 := h1555c.2.2.1
                                  have p1555_3 := h1555c.2.2.2
                                  linarith only [h1111, hlam, p1555_1]
                                · have p1555_0 := h1555c.1
                                  have p1555_1 := h1555c.2.1
                                  have p1555_2 := h1555c.2.2.1
                                  have p1555_3 := h1555c.2.2.2
                                  linarith only [hlam, p1555_0]
                                · have p1555_0 := h1555c.1
                                  have p1555_1 := h1555c.2.1
                                  have p1555_2 := h1555c.2.2.1
                                  have p1555_3 := h1555c.2.2.2
                                  linarith only [h0, h1033, hc12, hc24, hlam, hphi, p1555_1]
                                · have p1555_0 := h1555c.1
                                  have p1555_1 := h1555c.2.1
                                  have p1555_2 := h1555c.2.2.1
                                  have p1555_3 := h1555c.2.2.2
                                  rcases p1555_3 (m.d 0 2) (by simp) with h1598 | h1598
                                  · linarith only [h1598, hlam, p1555_0]
                                  · rcases p1555_3 (m.d 1 2) (by simp) with h1600 | h1600
                                    · linarith only [h1107, h1600, hlam]
                                    · rcases p1555_3 (m.d 2 3) (by simp) with h1602 | h1602
                                      · rcases p1555_3 (m.d 2 4) (by simp) with h1603 | h1603
                                        · rcases p1555_3 (m.d 2 5) (by simp) with h1604 | h1604
                                          · rcases h3bigk with h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c
                                            · have p1605_0 := h1605c.1
                                              have p1605_1 := h1605c.2.1
                                              have p1605_2 := h1605c.2.2.1
                                              have p1605_3 := h1605c.2.2.2
                                              linarith only [hlam, p1605_0]
                                            · have p1605_0 := h1605c.1
                                              have p1605_1 := h1605c.2.1
                                              have p1605_2 := h1605c.2.2.1
                                              have p1605_3 := h1605c.2.2.2
                                              linarith only [h1109, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1605_1, u3ehi3]
                                            · have p1605_0 := h1605c.1
                                              have p1605_1 := h1605c.2.1
                                              have p1605_2 := h1605c.2.2.1
                                              have p1605_3 := h1605c.2.2.2
                                              linarith only [h4, hlam, p1605_1]
                                            · have p1605_0 := h1605c.1
                                              have p1605_1 := h1605c.2.1
                                              have p1605_2 := h1605c.2.2.1
                                              have p1605_3 := h1605c.2.2.2
                                              rcases p1605_3 (m.d 0 3) (by simp) with h1609 | h1609
                                              · rcases p1605_3 (m.d 1 3) (by simp) with h1610 | h1610
                                                · linarith only [h1, h1610, hlam]
                                                · linarith only [h1109, h1610, hlam]
                                              · linarith only [h1609, hlam, p1605_0]
                                            · have p1605_0 := h1605c.1
                                              have p1605_1 := h1605c.2.1
                                              have p1605_2 := h1605c.2.2.1
                                              have p1605_3 := h1605c.2.2.2
                                              rcases p1605_3 (m.d 0 3) (by simp) with h1614 | h1614
                                              · rcases p1605_3 (m.d 1 3) (by simp) with h1615 | h1615
                                                · linarith only [h1, h1615, hlam]
                                                · linarith only [h1110, h1615, hlam]
                                              · linarith only [h1614, hlam, p1605_0]
                                            · have p1605_0 := h1605c.1
                                              have p1605_1 := h1605c.2.1
                                              have p1605_2 := h1605c.2.2.1
                                              have p1605_3 := h1605c.2.2.2
                                              linarith only [h1, hlam, p1605_0]
                                            · have p1605_0 := h1605c.1
                                              have p1605_1 := h1605c.2.1
                                              have p1605_2 := h1605c.2.2.1
                                              have p1605_3 := h1605c.2.2.2
                                              linarith only [hlam, p1605_0]
                                            · have p1605_0 := h1605c.1
                                              have p1605_1 := h1605c.2.1
                                              have p1605_2 := h1605c.2.2.1
                                              have p1605_3 := h1605c.2.2.2
                                              linarith only [h1103, hlam, p1605_1]
                                            · have p1605_0 := h1605c.1
                                              have p1605_1 := h1605c.2.1
                                              have p1605_2 := h1605c.2.2.1
                                              have p1605_3 := h1605c.2.2.2
                                              linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1605_1, u3ehi3]
                                            · have p1605_0 := h1605c.1
                                              have p1605_1 := h1605c.2.1
                                              have p1605_2 := h1605c.2.2.1
                                              have p1605_3 := h1605c.2.2.2
                                              linarith only [h1, h1114, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1605_1, u3ehi3]
                                            · have p1605_0 := h1605c.1
                                              have p1605_1 := h1605c.2.1
                                              have p1605_2 := h1605c.2.2.1
                                              have p1605_3 := h1605c.2.2.2
                                              linarith only [h1100, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1605_1, u3ehi3]
                                            · have p1605_0 := h1605c.1
                                              have p1605_1 := h1605c.2.1
                                              have p1605_2 := h1605c.2.2.1
                                              have p1605_3 := h1605c.2.2.2
                                              linarith only [h1109, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1605_1, u3ehi3]
                                            · have p1605_0 := h1605c.1
                                              have p1605_1 := h1605c.2.1
                                              have p1605_2 := h1605c.2.2.1
                                              have p1605_3 := h1605c.2.2.2
                                              linarith only [hlam, p1605_0]
                                            · have p1605_0 := h1605c.1
                                              have p1605_1 := h1605c.2.1
                                              have p1605_2 := h1605c.2.2.1
                                              have p1605_3 := h1605c.2.2.2
                                              rcases p1605_3 (m.d 0 3) (by simp) with h1627 | h1627
                                              · linarith only [h1627, h4, hlam]
                                              · linarith only [h1100, h1627, hlam]
                                            · have p1605_0 := h1605c.1
                                              have p1605_1 := h1605c.2.1
                                              have p1605_2 := h1605c.2.2.1
                                              have p1605_3 := h1605c.2.2.2
                                              rcases p1605_3 (m.d 0 3) (by simp) with h1630 | h1630
                                              · linarith only [h1630, h4, hlam]
                                              · linarith only [h1101, h1630, hlam]
                                            · have p1605_0 := h1605c.1
                                              have p1605_1 := h1605c.2.1
                                              have p1605_2 := h1605c.2.2.1
                                              have p1605_3 := h1605c.2.2.2
                                              linarith only [h1100, hlam, p1605_0]
                                            · have p1605_0 := h1605c.1
                                              have p1605_1 := h1605c.2.1
                                              have p1605_2 := h1605c.2.2.1
                                              have p1605_3 := h1605c.2.2.2
                                              linarith only [h1109, hlam, p1605_0]
                                            · have p1605_0 := h1605c.1
                                              have p1605_1 := h1605c.2.1
                                              have p1605_2 := h1605c.2.2.1
                                              have p1605_3 := h1605c.2.2.2
                                              linarith only [h1111, hlam, p1605_0]
                                            · have p1605_0 := h1605c.1
                                              have p1605_1 := h1605c.2.1
                                              have p1605_2 := h1605c.2.2.1
                                              have p1605_3 := h1605c.2.2.2
                                              linarith only [hlam, p1605_0]
                                            · have p1605_0 := h1605c.1
                                              have p1605_1 := h1605c.2.1
                                              have p1605_2 := h1605c.2.2.1
                                              have p1605_3 := h1605c.2.2.2
                                              linarith only [h1114, hlam, p1605_1]
                                            · have p1605_0 := h1605c.1
                                              have p1605_1 := h1605c.2.1
                                              have p1605_2 := h1605c.2.2.1
                                              have p1605_3 := h1605c.2.2.2
                                              linarith only [h1101, hlam, p1605_0]
                                            · have p1605_0 := h1605c.1
                                              have p1605_1 := h1605c.2.1
                                              have p1605_2 := h1605c.2.2.1
                                              have p1605_3 := h1605c.2.2.2
                                              linarith only [h1110, hlam, p1605_0]
                                            · have p1605_0 := h1605c.1
                                              have p1605_1 := h1605c.2.1
                                              have p1605_2 := h1605c.2.2.1
                                              have p1605_3 := h1605c.2.2.2
                                              linarith only [h1112, hlam, p1605_0]
                                            · have p1605_0 := h1605c.1
                                              have p1605_1 := h1605c.2.1
                                              have p1605_2 := h1605c.2.2.1
                                              have p1605_3 := h1605c.2.2.2
                                              linarith only [h1110, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1605_1, u3ehi3]
                                            · have p1605_0 := h1605c.1
                                              have p1605_1 := h1605c.2.1
                                              have p1605_2 := h1605c.2.2.1
                                              have p1605_3 := h1605c.2.2.2
                                              linarith only [hlam, p1605_0]
                                          · linarith only [h1604, hlam, p1555_0]
                                        · linarith only [h1603, h883, hlam]
                                      · linarith only [h1602, h4, hlam]
                                · have p1555_0 := h1555c.1
                                  have p1555_1 := h1555c.2.1
                                  have p1555_2 := h1555c.2.2.1
                                  have p1555_3 := h1555c.2.2.2
                                  rcases p1555_3 (m.d 0 2) (by simp) with h1646 | h1646
                                  · linarith only [h1033, h1646, hlam]
                                  · linarith only [h0, h1646, hlam]
                                · have p1555_0 := h1555c.1
                                  have p1555_1 := h1555c.2.1
                                  have p1555_2 := h1555c.2.2.1
                                  have p1555_3 := h1555c.2.2.2
                                  linarith only [h1112, hlam, p1555_1]
                                · have p1555_0 := h1555c.1
                                  have p1555_1 := h1555c.2.1
                                  have p1555_2 := h1555c.2.2.1
                                  have p1555_3 := h1555c.2.2.2
                                  linarith only [h1113, hlam, p1555_0]
                                · have p1555_0 := h1555c.1
                                  have p1555_1 := h1555c.2.1
                                  have p1555_2 := h1555c.2.2.1
                                  have p1555_3 := h1555c.2.2.2
                                  linarith only [hlam, p1555_0]
                              · linarith only [h1033, h1554, hlam]
                            · linarith only [h1553, h883, hlam]
                          · linarith only [h1552, h4, hlam]
                      · linarith only [h0, h1549, hlam]
                    · have p1503_0 := h1503c.1
                      have p1503_1 := h1503c.2.1
                      have p1503_2 := h1503c.2.2.1
                      have p1503_3 := h1503c.2.2.2
                      linarith only [h1101, hlam, p1503_0]
                    · have p1503_0 := h1503c.1
                      have p1503_1 := h1503c.2.1
                      have p1503_2 := h1503c.2.2.1
                      have p1503_3 := h1503c.2.2.2
                      linarith only [h1102, hlam, p1503_1]
                    · have p1503_0 := h1503c.1
                      have p1503_1 := h1503c.2.1
                      have p1503_2 := h1503c.2.2.1
                      have p1503_3 := h1503c.2.2.2
                      linarith only [hlam, p1503_0]
                · linarith only [h0, h1100, h1102, h1113, h4, h883, hc12, hc23, hlam, hphi]
              · linarith only [h1, h1110, h1112, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
            · linarith only [h1, h1110, h1111, h4, hc34, hlam, hphi, u3ehi4]
          · linarith only [h1109, h1110, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1663 | h1663
          · linarith only [h1100, h1109, h1663, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1665 | h1665
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1666 | h1666
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1667 | h1667
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1668 | h1668
                  · rcases h0bigk with h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c | h1669c
                    · have p1669_0 := h1669c.1
                      have p1669_1 := h1669c.2.1
                      have p1669_2 := h1669c.2.2.1
                      have p1669_3 := h1669c.2.2.2
                      linarith only [hlam, p1669_0]
                    · have p1669_0 := h1669c.1
                      have p1669_1 := h1669c.2.1
                      have p1669_2 := h1669c.2.2.1
                      have p1669_3 := h1669c.2.2.2
                      rcases p1669_3 (m.d 0 1) (by simp) with h1671 | h1671
                      · rcases p1669_3 (m.d 0 2) (by simp) with h1672 | h1672
                        · linarith only [h0, h1672, hlam]
                        · rcases p1669_3 (m.d 0 3) (by simp) with h1674 | h1674
                          · linarith only [h1, h1674, hlam]
                          · linarith only [h1674, h4, hlam]
                      · linarith only [h0, h1671, hlam]
                    · have p1669_0 := h1669c.1
                      have p1669_1 := h1669c.2.1
                      have p1669_2 := h1669c.2.2.1
                      have p1669_3 := h1669c.2.2.2
                      linarith only [h1100, h1663, h1668, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1669_1, u3ehi1]
                    · have p1669_0 := h1669c.1
                      have p1669_1 := h1669c.2.1
                      have p1669_2 := h1669c.2.2.1
                      have p1669_3 := h1669c.2.2.2
                      linarith only [h1100, h1663, h1668, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1669_1, u3ehi1]
                    · have p1669_0 := h1669c.1
                      have p1669_1 := h1669c.2.1
                      have p1669_2 := h1669c.2.2.1
                      have p1669_3 := h1669c.2.2.2
                      linarith only [h1101, h1663, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1669_1, u3ehi1]
                    · have p1669_0 := h1669c.1
                      have p1669_1 := h1669c.2.1
                      have p1669_2 := h1669c.2.2.1
                      have p1669_3 := h1669c.2.2.2
                      linarith only [h0, hlam, p1669_0]
                    · have p1669_0 := h1669c.1
                      have p1669_1 := h1669c.2.1
                      have p1669_2 := h1669c.2.2.1
                      have p1669_3 := h1669c.2.2.2
                      linarith only [hlam, p1669_0]
                    · have p1669_0 := h1669c.1
                      have p1669_1 := h1669c.2.1
                      have p1669_2 := h1669c.2.2.1
                      have p1669_3 := h1669c.2.2.2
                      linarith only [h4, hlam, p1669_0]
                    · have p1669_0 := h1669c.1
                      have p1669_1 := h1669c.2.1
                      have p1669_2 := h1669c.2.2.1
                      have p1669_3 := h1669c.2.2.2
                      linarith only [h883, hlam, p1669_1]
                    · have p1669_0 := h1669c.1
                      have p1669_1 := h1669c.2.1
                      have p1669_2 := h1669c.2.2.1
                      have p1669_3 := h1669c.2.2.2
                      linarith only [h1033, hlam, p1669_0]
                    · have p1669_0 := h1669c.1
                      have p1669_1 := h1669c.2.1
                      have p1669_2 := h1669c.2.2.1
                      have p1669_3 := h1669c.2.2.2
                      linarith only [h1, hlam, p1669_1]
                    · have p1669_0 := h1669c.1
                      have p1669_1 := h1669c.2.1
                      have p1669_2 := h1669c.2.2.1
                      have p1669_3 := h1669c.2.2.2
                      rcases p1669_3 (m.d 0 1) (by simp) with h1687 | h1687
                      · rcases p1669_3 (m.d 0 2) (by simp) with h1688 | h1688
                        · linarith only [h1688, h4, hlam]
                        · rcases p1669_3 (m.d 0 3) (by simp) with h1690 | h1690
                          · rcases p1669_3 (m.d 0 4) (by simp) with h1691 | h1691
                            · linarith only [h1100, h1691, hlam]
                            · linarith only [h1691, h883, hlam]
                          · linarith only [h1690, h4, hlam]
                      · linarith only [h0, h1687, hlam]
                    · have p1669_0 := h1669c.1
                      have p1669_1 := h1669c.2.1
                      have p1669_2 := h1669c.2.2.1
                      have p1669_3 := h1669c.2.2.2
                      linarith only [hlam, p1669_0]
                    · have p1669_0 := h1669c.1
                      have p1669_1 := h1669c.2.1
                      have p1669_2 := h1669c.2.2.1
                      have p1669_3 := h1669c.2.2.2
                      linarith only [h1100, h1663, h1668, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1669_1, u3ehi1]
                    · have p1669_0 := h1669c.1
                      have p1669_1 := h1669c.2.1
                      have p1669_2 := h1669c.2.2.1
                      have p1669_3 := h1669c.2.2.2
                      linarith only [h1101, h1663, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1669_1, u3ehi1]
                    · have p1669_0 := h1669c.1
                      have p1669_1 := h1669c.2.1
                      have p1669_2 := h1669c.2.2.1
                      have p1669_3 := h1669c.2.2.2
                      linarith only [h2, hlam, p1669_0]
                    · have p1669_0 := h1669c.1
                      have p1669_1 := h1669c.2.1
                      have p1669_2 := h1669c.2.2.1
                      have p1669_3 := h1669c.2.2.2
                      rcases p1669_3 (m.d 0 1) (by simp) with h1700 | h1700
                      · rcases p1669_3 (m.d 0 2) (by simp) with h1701 | h1701
                        · linarith only [h1701, h883, hlam]
                        · rcases p1669_3 (m.d 0 3) (by simp) with h1703 | h1703
                          · rcases p1669_3 (m.d 0 4) (by simp) with h1704 | h1704
                            · rcases p1669_3 (m.d 0 5) (by simp) with h1705 | h1705
                              · linarith only [h1102, h1705, hlam]
                              · linarith only [h1033, h1705, hlam]
                            · linarith only [h1704, h883, hlam]
                          · linarith only [h1703, h4, hlam]
                      · linarith only [h0, h1700, hlam]
                    · have p1669_0 := h1669c.1
                      have p1669_1 := h1669c.2.1
                      have p1669_2 := h1669c.2.2.1
                      have p1669_3 := h1669c.2.2.2
                      linarith only [h1100, hlam, p1669_0]
                    · have p1669_0 := h1669c.1
                      have p1669_1 := h1669c.2.1
                      have p1669_2 := h1669c.2.2.1
                      have p1669_3 := h1669c.2.2.2
                      linarith only [hlam, p1669_0]
                    · have p1669_0 := h1669c.1
                      have p1669_1 := h1669c.2.1
                      have p1669_2 := h1669c.2.2.1
                      have p1669_3 := h1669c.2.2.2
                      linarith only [h1101, h1663, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1669_1, u3ehi1]
                    · have p1669_0 := h1669c.1
                      have p1669_1 := h1669c.2.1
                      have p1669_2 := h1669c.2.2.1
                      have p1669_3 := h1669c.2.2.2
                      linarith only [h3, hlam, p1669_0]
                    · have p1669_0 := h1669c.1
                      have p1669_1 := h1669c.2.1
                      have p1669_2 := h1669c.2.2.1
                      have p1669_3 := h1669c.2.2.2
                      rcases p1669_3 (m.d 0 1) (by simp) with h1715 | h1715
                      · rcases p1669_3 (m.d 0 2) (by simp) with h1716 | h1716
                        · linarith only [h1033, h1716, hlam]
                        · rcases p1669_3 (m.d 0 3) (by simp) with h1718 | h1718
                          · rcases p1669_3 (m.d 0 4) (by simp) with h1719 | h1719
                            · rcases p1669_3 (m.d 0 5) (by simp) with h1720 | h1720
                              · rcases h2bigk with h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [hlam, p1721_0]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1669_1, p1721_1]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [h4, hlam, p1721_0]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [h883, hlam, p1721_0]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [h1033, hlam, p1721_0]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [h0, hlam, p1721_0]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [hlam, p1721_0]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [h1103, hlam, p1721_0]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [h1105, hlam, p1721_0]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [h1107, hlam, p1721_0]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  rcases p1721_3 (m.d 0 2) (by simp) with h1732 | h1732
                                  · linarith only [h1732, hlam, p1721_0]
                                  · rcases p1721_3 (m.d 1 2) (by simp) with h1734 | h1734
                                    · linarith only [h1103, h1734, hlam]
                                    · rcases p1721_3 (m.d 2 3) (by simp) with h1736 | h1736
                                      · rcases p1721_3 (m.d 2 4) (by simp) with h1737 | h1737
                                        · linarith only [h1665, h1737, hlam]
                                        · linarith only [h1737, h883, hlam]
                                      · linarith only [h1736, hlam, p1721_0]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  rcases p1721_3 (m.d 0 2) (by simp) with h1741 | h1741
                                  · linarith only [h1741, h4, hlam]
                                  · linarith only [h0, h1741, hlam]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [hlam, p1721_0]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [h883, hc02, hc23, hlam, hphi, p1721_1]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [h0, h1033, hc12, hc23, hlam, hphi, p1721_1]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  rcases p1721_3 (m.d 0 2) (by simp) with h1747 | h1747
                                  · linarith only [h1747, hlam, p1721_0]
                                  · rcases p1721_3 (m.d 1 2) (by simp) with h1749 | h1749
                                    · linarith only [h1105, h1749, hlam]
                                    · rcases p1721_3 (m.d 2 3) (by simp) with h1751 | h1751
                                      · rcases p1721_3 (m.d 2 4) (by simp) with h1752 | h1752
                                        · rcases p1721_3 (m.d 2 5) (by simp) with h1753 | h1753
                                          · linarith only [h1667, h1753, hlam]
                                          · linarith only [h1033, h1753, hlam]
                                        · linarith only [h1752, hlam, p1721_0]
                                      · linarith only [h1751, h4, hlam]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  rcases p1721_3 (m.d 0 2) (by simp) with h1758 | h1758
                                  · linarith only [h1758, h883, hlam]
                                  · linarith only [h0, h1758, hlam]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [h1665, hlam, p1721_1]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [hlam, p1721_0]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [h0, h1033, hc12, hc24, hlam, hphi, p1669_1, p1721_1]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  rcases p1721_3 (m.d 0 2) (by simp) with h1764 | h1764
                                  · linarith only [h1764, hlam, p1721_0]
                                  · rcases p1721_3 (m.d 1 2) (by simp) with h1766 | h1766
                                    · linarith only [h1107, h1766, hlam]
                                    · rcases p1721_3 (m.d 2 3) (by simp) with h1768 | h1768
                                      · rcases p1721_3 (m.d 2 4) (by simp) with h1769 | h1769
                                        · rcases p1721_3 (m.d 2 5) (by simp) with h1770 | h1770
                                          · rcases h3bigk with h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c
                                            · have p1771_0 := h1771c.1
                                              have p1771_1 := h1771c.2.1
                                              have p1771_2 := h1771c.2.2.1
                                              have p1771_3 := h1771c.2.2.2
                                              linarith only [hlam, p1771_0]
                                            · have p1771_0 := h1771c.1
                                              have p1771_1 := h1771c.2.1
                                              have p1771_2 := h1771c.2.2.1
                                              have p1771_3 := h1771c.2.2.2
                                              rcases p1771_3 (m.d 0 3) (by simp) with h1773 | h1773
                                              · rcases p1771_3 (m.d 1 3) (by simp) with h1774 | h1774
                                                · linarith only [h1, h1774, hlam]
                                                · rcases p1771_3 (m.d 2 3) (by simp) with h1776 | h1776
                                                  · rcases p1771_3 (m.d 3 4) (by simp) with h1777 | h1777
                                                    · linarith only [h1100, h1777, hlam]
                                                    · linarith only [h1109, h1777, hlam]
                                                  · linarith only [h1103, h1776, hlam]
                                              · linarith only [h1, h1773, hlam]
                                            · have p1771_0 := h1771c.1
                                              have p1771_1 := h1771c.2.1
                                              have p1771_2 := h1771c.2.2.1
                                              have p1771_3 := h1771c.2.2.2
                                              linarith only [h4, hlam, p1771_1]
                                            · have p1771_0 := h1771c.1
                                              have p1771_1 := h1771c.2.1
                                              have p1771_2 := h1771c.2.2.1
                                              have p1771_3 := h1771c.2.2.2
                                              linarith only [h1663, h1668, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1771_1, u3ehi1]
                                            · have p1771_0 := h1771c.1
                                              have p1771_1 := h1771c.2.1
                                              have p1771_2 := h1771c.2.2.1
                                              have p1771_3 := h1771c.2.2.2
                                              linarith only [h1663, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1771_1, u3ehi1]
                                            · have p1771_0 := h1771c.1
                                              have p1771_1 := h1771c.2.1
                                              have p1771_2 := h1771c.2.2.1
                                              have p1771_3 := h1771c.2.2.2
                                              linarith only [h1, hlam, p1771_0]
                                            · have p1771_0 := h1771c.1
                                              have p1771_1 := h1771c.2.1
                                              have p1771_2 := h1771c.2.2.1
                                              have p1771_3 := h1771c.2.2.2
                                              linarith only [hlam, p1771_0]
                                            · have p1771_0 := h1771c.1
                                              have p1771_1 := h1771c.2.1
                                              have p1771_2 := h1771c.2.2.1
                                              have p1771_3 := h1771c.2.2.2
                                              linarith only [h1103, hlam, p1771_1]
                                            · have p1771_0 := h1771c.1
                                              have p1771_1 := h1771c.2.1
                                              have p1771_2 := h1771c.2.2.1
                                              have p1771_3 := h1771c.2.2.2
                                              linarith only [h1109, hlam, p1771_0]
                                            · have p1771_0 := h1771c.1
                                              have p1771_1 := h1771c.2.1
                                              have p1771_2 := h1771c.2.2.1
                                              have p1771_3 := h1771c.2.2.2
                                              linarith only [h1663, hlam, p1771_0]
                                            · have p1771_0 := h1771c.1
                                              have p1771_1 := h1771c.2.1
                                              have p1771_2 := h1771c.2.2.1
                                              have p1771_3 := h1771c.2.2.2
                                              linarith only [h1100, h1663, h1668, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1771_1, u3ehi1]
                                            · have p1771_0 := h1771c.1
                                              have p1771_1 := h1771c.2.1
                                              have p1771_2 := h1771c.2.2.1
                                              have p1771_3 := h1771c.2.2.2
                                              rcases p1771_3 (m.d 0 3) (by simp) with h1791 | h1791
                                              · linarith only [h1791, h4, hlam]
                                              · linarith only [h1, h1791, hlam]
                                            · have p1771_0 := h1771c.1
                                              have p1771_1 := h1771c.2.1
                                              have p1771_2 := h1771c.2.2.1
                                              have p1771_3 := h1771c.2.2.2
                                              linarith only [hlam, p1771_0]
                                            · have p1771_0 := h1771c.1
                                              have p1771_1 := h1771c.2.1
                                              have p1771_2 := h1771c.2.2.1
                                              have p1771_3 := h1771c.2.2.2
                                              linarith only [h1663, h1668, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1771_1, u3ehi1]
                                            · have p1771_0 := h1771c.1
                                              have p1771_1 := h1771c.2.1
                                              have p1771_2 := h1771c.2.2.1
                                              have p1771_3 := h1771c.2.2.2
                                              linarith only [h1663, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1771_1, u3ehi1]
                                            · have p1771_0 := h1771c.1
                                              have p1771_1 := h1771c.2.1
                                              have p1771_2 := h1771c.2.2.1
                                              have p1771_3 := h1771c.2.2.2
                                              linarith only [h1100, hlam, p1771_0]
                                            · have p1771_0 := h1771c.1
                                              have p1771_1 := h1771c.2.1
                                              have p1771_2 := h1771c.2.2.1
                                              have p1771_3 := h1771c.2.2.2
                                              linarith only [h1100, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1771_1, u3ehi1]
                                            · have p1771_0 := h1771c.1
                                              have p1771_1 := h1771c.2.1
                                              have p1771_2 := h1771c.2.2.1
                                              have p1771_3 := h1771c.2.2.2
                                              linarith only [h1665, hlam, p1771_0]
                                            · have p1771_0 := h1771c.1
                                              have p1771_1 := h1771c.2.1
                                              have p1771_2 := h1771c.2.2.1
                                              have p1771_3 := h1771c.2.2.2
                                              linarith only [hlam, p1771_0]
                                            · have p1771_0 := h1771c.1
                                              have p1771_1 := h1771c.2.1
                                              have p1771_2 := h1771c.2.2.1
                                              have p1771_3 := h1771c.2.2.2
                                              linarith only [h1100, h1663, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1771_1, u3ehi1]
                                            · have p1771_0 := h1771c.1
                                              have p1771_1 := h1771c.2.1
                                              have p1771_2 := h1771c.2.2.1
                                              have p1771_3 := h1771c.2.2.2
                                              linarith only [h1101, hlam, p1771_0]
                                            · have p1771_0 := h1771c.1
                                              have p1771_1 := h1771c.2.1
                                              have p1771_2 := h1771c.2.2.1
                                              have p1771_3 := h1771c.2.2.2
                                              linarith only [hc35, hlam, hphi, p1771_1, u3ehi1]
                                            · have p1771_0 := h1771c.1
                                              have p1771_1 := h1771c.2.1
                                              have p1771_2 := h1771c.2.2.1
                                              have p1771_3 := h1771c.2.2.2
                                              linarith only [h1666, hlam, p1771_0]
                                            · have p1771_0 := h1771c.1
                                              have p1771_1 := h1771c.2.1
                                              have p1771_2 := h1771c.2.2.1
                                              have p1771_3 := h1771c.2.2.2
                                              linarith only [h1668, hlam, p1771_0]
                                            · have p1771_0 := h1771c.1
                                              have p1771_1 := h1771c.2.1
                                              have p1771_2 := h1771c.2.2.1
                                              have p1771_3 := h1771c.2.2.2
                                              linarith only [hlam, p1771_0]
                                          · linarith only [h1770, hlam, p1721_0]
                                        · linarith only [h1769, h883, hlam]
                                      · linarith only [h1768, h4, hlam]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  rcases p1721_3 (m.d 0 2) (by simp) with h1810 | h1810
                                  · linarith only [h1033, h1810, hlam]
                                  · linarith only [h0, h1810, hlam]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [h1666, hlam, p1721_1]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [h1667, hlam, p1721_0]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [hlam, p1721_0]
                              · linarith only [h1033, h1720, hlam]
                            · linarith only [h1719, h883, hlam]
                          · linarith only [h1718, h4, hlam]
                      · linarith only [h0, h1715, hlam]
                    · have p1669_0 := h1669c.1
                      have p1669_1 := h1669c.2.1
                      have p1669_2 := h1669c.2.2.1
                      have p1669_3 := h1669c.2.2.2
                      linarith only [h1101, hlam, p1669_0]
                    · have p1669_0 := h1669c.1
                      have p1669_1 := h1669c.2.1
                      have p1669_2 := h1669c.2.2.1
                      have p1669_3 := h1669c.2.2.2
                      linarith only [h1102, hlam, p1669_1]
                    · have p1669_0 := h1669c.1
                      have p1669_1 := h1669c.2.1
                      have p1669_2 := h1669c.2.2.1
                      have p1669_3 := h1669c.2.2.2
                      linarith only [hlam, p1669_0]
                  · linarith only [h1100, h1102, h1109, h1668, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h0, h1100, h1102, h1667, h4, h883, hc12, hc23, hlam, hphi]
              · linarith only [h1100, h1109, h1666, h4, hc35, hlam, hphi, u3ehi1]
            · linarith only [h1101, h1665, h4, hc34, hlam, hphi, u3ehi4]

end R2N4
