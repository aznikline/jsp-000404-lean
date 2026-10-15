import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_15S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6236000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s6_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 2 3 (by decide) (by decide) with h1101 | h1101
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1102 | h1102
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1103 | h1103
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1104 | h1104
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1105 | h1105
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1106 | h1106
            · linarith only [h1106, h2, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1108 | h1108
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1109 | h1109
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1110 | h1110
                  · linarith only [h0, h1101, h1108, h1110, h9, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1112 | h1112
                    · linarith only [h1102, h1108, h1112, h2, h9, hlam]
                    · rcases h0bigk with h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [hlam, p1114_0]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [h0, h1101, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1114_1]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1114_1]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        rcases p1114_3 (m.d 0 1) (by simp) with h1118 | h1118
                        · rcases p1114_3 (m.d 0 2) (by simp) with h1119 | h1119
                          · linarith only [h0, h1119, hlam]
                          · linarith only [h1119, h5, hlam]
                        · linarith only [h1118, h2, hlam]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        rcases p1114_3 (m.d 0 1) (by simp) with h1123 | h1123
                        · rcases p1114_3 (m.d 0 2) (by simp) with h1124 | h1124
                          · linarith only [h0, h1124, hlam]
                          · linarith only [h1124, h6, hlam]
                        · linarith only [h1123, h3, hlam]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [h0, hlam, p1114_0]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [hlam, p1114_0]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [h1, h1101, h1109, h1112, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1114_1]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        rcases p1114_3 (m.d 0 1) (by simp) with h1131 | h1131
                        · rcases p1114_3 (m.d 0 2) (by simp) with h1132 | h1132
                          · rcases p1114_3 (m.d 0 3) (by simp) with h1133 | h1133
                            · linarith only [h1133, h4, hlam]
                            · linarith only [h1133, h7, hlam]
                          · linarith only [h1132, h5, hlam]
                        · linarith only [h1131, h2, hlam]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        rcases p1114_3 (m.d 0 1) (by simp) with h1138 | h1138
                        · rcases p1114_3 (m.d 0 2) (by simp) with h1139 | h1139
                          · rcases p1114_3 (m.d 0 3) (by simp) with h1140 | h1140
                            · linarith only [h1140, h4, hlam]
                            · linarith only [h1140, h8, hlam]
                          · linarith only [h1139, h6, hlam]
                        · linarith only [h1138, h3, hlam]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [h1, hlam, p1114_1]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [h4, hlam, p1114_1]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [hlam, p1114_0]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        rcases p1114_3 (m.d 0 1) (by simp) with h1148 | h1148
                        · rcases p1114_3 (m.d 0 2) (by simp) with h1149 | h1149
                          · rcases p1114_3 (m.d 0 3) (by simp) with h1150 | h1150
                            · rcases p1114_3 (m.d 0 4) (by simp) with h1151 | h1151
                              · linarith only [h1151, h7, hlam]
                              · rcases p1114_3 (m.d 0 5) (by simp) with h1153 | h1153
                                · linarith only [h1153, h8, hlam]
                                · linarith only [h1153, h9, hlam]
                            · linarith only [h1150, h7, hlam]
                          · linarith only [h1149, h5, hlam]
                        · linarith only [h1148, h2, hlam]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        rcases p1114_3 (m.d 0 1) (by simp) with h1159 | h1159
                        · rcases p1114_3 (m.d 0 2) (by simp) with h1160 | h1160
                          · rcases p1114_3 (m.d 0 3) (by simp) with h1161 | h1161
                            · rcases p1114_3 (m.d 0 4) (by simp) with h1162 | h1162
                              · linarith only [h1162, h7, hlam]
                              · rcases p1114_3 (m.d 0 5) (by simp) with h1164 | h1164
                                · linarith only [h1164, h8, hlam]
                                · rcases h1bigk with h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c | h1166c
                                  · have p1166_0 := h1166c.1
                                    have p1166_1 := h1166c.2.1
                                    have p1166_2 := h1166c.2.2.1
                                    have p1166_3 := h1166c.2.2.2
                                    linarith only [hlam, p1166_0]
                                  · have p1166_0 := h1166c.1
                                    have p1166_1 := h1166c.2.1
                                    have p1166_2 := h1166c.2.2.1
                                    have p1166_3 := h1166c.2.2.2
                                    linarith only [h1101, h1109, h1112, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1166_1]
                                  · have p1166_0 := h1166c.1
                                    have p1166_1 := h1166c.2.1
                                    have p1166_2 := h1166c.2.2.1
                                    have p1166_3 := h1166c.2.2.2
                                    rcases p1166_3 (m.d 0 1) (by simp) with h1169 | h1169
                                    · rcases p1166_3 (m.d 1 2) (by simp) with h1170 | h1170
                                      · linarith only [h0, h1170, hlam]
                                      · linarith only [h1101, h1170, hlam]
                                    · linarith only [h1169, hlam, p1166_0]
                                  · have p1166_0 := h1166c.1
                                    have p1166_1 := h1166c.2.1
                                    have p1166_2 := h1166c.2.2.1
                                    have p1166_3 := h1166c.2.2.2
                                    linarith only [h1, h1106, h3, hlam, p1114_1, p1166_2]
                                  · have p1166_0 := h1166c.1
                                    have p1166_1 := h1166c.2.1
                                    have p1166_2 := h1166c.2.2.1
                                    have p1166_3 := h1166c.2.2.2
                                    linarith only [h1, h3, hlam, p1114_1, p1166_2]
                                  · have p1166_0 := h1166c.1
                                    have p1166_1 := h1166c.2.1
                                    have p1166_2 := h1166c.2.2.1
                                    have p1166_3 := h1166c.2.2.2
                                    linarith only [h0, hlam, p1166_0]
                                  · have p1166_0 := h1166c.1
                                    have p1166_1 := h1166c.2.1
                                    have p1166_2 := h1166c.2.2.1
                                    have p1166_3 := h1166c.2.2.2
                                    linarith only [hlam, p1166_0]
                                  · have p1166_0 := h1166c.1
                                    have p1166_1 := h1166c.2.1
                                    have p1166_2 := h1166c.2.2.1
                                    have p1166_3 := h1166c.2.2.2
                                    linarith only [h0, h1101, h1109, h1112, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1166_1]
                                  · have p1166_0 := h1166c.1
                                    have p1166_1 := h1166c.2.1
                                    have p1166_2 := h1166c.2.2.1
                                    have p1166_3 := h1166c.2.2.2
                                    rcases p1166_3 (m.d 0 1) (by simp) with h1179 | h1179
                                    · rcases p1166_3 (m.d 1 2) (by simp) with h1180 | h1180
                                      · rcases p1166_3 (m.d 1 3) (by simp) with h1181 | h1181
                                        · linarith only [h1101, h1181, hlam]
                                        · linarith only [h1104, h1181, hlam]
                                      · linarith only [h1102, h1180, hlam]
                                    · linarith only [h1179, h2, hlam]
                                  · have p1166_0 := h1166c.1
                                    have p1166_1 := h1166c.2.1
                                    have p1166_2 := h1166c.2.2.1
                                    have p1166_3 := h1166c.2.2.2
                                    rcases p1166_3 (m.d 0 1) (by simp) with h1186 | h1186
                                    · rcases p1166_3 (m.d 1 2) (by simp) with h1187 | h1187
                                      · rcases p1166_3 (m.d 1 3) (by simp) with h1188 | h1188
                                        · linarith only [h1101, h1188, hlam]
                                        · linarith only [h1105, h1188, hlam]
                                      · linarith only [h1103, h1187, hlam]
                                    · linarith only [h1186, h3, hlam]
                                  · have p1166_0 := h1166c.1
                                    have p1166_1 := h1166c.2.1
                                    have p1166_2 := h1166c.2.2.1
                                    have p1166_3 := h1166c.2.2.2
                                    linarith only [h1, hlam, p1166_0]
                                  · have p1166_0 := h1166c.1
                                    have p1166_1 := h1166c.2.1
                                    have p1166_2 := h1166c.2.2.1
                                    have p1166_3 := h1166c.2.2.2
                                    linarith only [h1101, hlam, p1166_1]
                                  · have p1166_0 := h1166c.1
                                    have p1166_1 := h1166c.2.1
                                    have p1166_2 := h1166c.2.2.1
                                    have p1166_3 := h1166c.2.2.2
                                    linarith only [hlam, p1166_0]
                                  · have p1166_0 := h1166c.1
                                    have p1166_1 := h1166c.2.1
                                    have p1166_2 := h1166c.2.2.1
                                    have p1166_3 := h1166c.2.2.2
                                    rcases p1166_3 (m.d 0 1) (by simp) with h1196 | h1196
                                    · rcases p1166_3 (m.d 1 2) (by simp) with h1197 | h1197
                                      · rcases p1166_3 (m.d 1 3) (by simp) with h1198 | h1198
                                        · rcases p1166_3 (m.d 1 4) (by simp) with h1199 | h1199
                                          · linarith only [h1104, h1199, hlam]
                                          · rcases p1166_3 (m.d 1 5) (by simp) with h1201 | h1201
                                            · linarith only [h1105, h1201, hlam]
                                            · linarith only [h1106, h1201, hlam]
                                        · linarith only [h1104, h1198, hlam]
                                      · linarith only [h1102, h1197, hlam]
                                    · linarith only [h1196, h2, hlam]
                                  · have p1166_0 := h1166c.1
                                    have p1166_1 := h1166c.2.1
                                    have p1166_2 := h1166c.2.2.1
                                    have p1166_3 := h1166c.2.2.2
                                    rcases p1166_3 (m.d 0 1) (by simp) with h1207 | h1207
                                    · rcases p1166_3 (m.d 1 2) (by simp) with h1208 | h1208
                                      · rcases p1166_3 (m.d 1 3) (by simp) with h1209 | h1209
                                        · rcases p1166_3 (m.d 1 4) (by simp) with h1210 | h1210
                                          · linarith only [h1104, h1210, hlam]
                                          · rcases p1166_3 (m.d 1 5) (by simp) with h1212 | h1212
                                            · linarith only [h1105, h1212, hlam]
                                            · rcases h3bigk with h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c | h1214c
                                              · have p1214_0 := h1214c.1
                                                have p1214_1 := h1214c.2.1
                                                have p1214_2 := h1214c.2.2.1
                                                have p1214_3 := h1214c.2.2.2
                                                linarith only [hlam, p1214_0]
                                              · have p1214_0 := h1214c.1
                                                have p1214_1 := h1214c.2.1
                                                have p1214_2 := h1214c.2.2.1
                                                have p1214_3 := h1214c.2.2.2
                                                linarith only [h1102, h1106, h1108, h4, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1166_1, p1214_1]
                                              · have p1214_0 := h1214c.1
                                                have p1214_1 := h1214c.2.1
                                                have p1214_2 := h1214c.2.2.1
                                                have p1214_3 := h1214c.2.2.2
                                                rcases p1214_3 (m.d 0 3) (by simp) with h1217 | h1217
                                                · rcases p1214_3 (m.d 1 3) (by simp) with h1218 | h1218
                                                  · linarith only [h1, h1218, hlam]
                                                  · linarith only [h1101, h1218, hlam]
                                                · linarith only [h1217, h4, hlam]
                                              · have p1214_0 := h1214c.1
                                                have p1214_1 := h1214c.2.1
                                                have p1214_2 := h1214c.2.2.1
                                                have p1214_3 := h1214c.2.2.2
                                                linarith only [h1102, h1106, h1108, h3, hlam, p1114_1, p1214_2]
                                              · have p1214_0 := h1214c.1
                                                have p1214_1 := h1214c.2.1
                                                have p1214_2 := h1214c.2.2.1
                                                have p1214_3 := h1214c.2.2.2
                                                linarith only [h8, hlam, p1114_1, p1214_2]
                                              · have p1214_0 := h1214c.1
                                                have p1214_1 := h1214c.2.1
                                                have p1214_2 := h1214c.2.2.1
                                                have p1214_3 := h1214c.2.2.2
                                                linarith only [h1, hlam, p1214_0]
                                              · have p1214_0 := h1214c.1
                                                have p1214_1 := h1214c.2.1
                                                have p1214_2 := h1214c.2.2.1
                                                have p1214_3 := h1214c.2.2.2
                                                linarith only [hlam, p1214_0]
                                              · have p1214_0 := h1214c.1
                                                have p1214_1 := h1214c.2.1
                                                have p1214_2 := h1214c.2.2.1
                                                have p1214_3 := h1214c.2.2.2
                                                linarith only [h1, h1109, hc01, hc35, hlam, hphi, ht0b, ht5b, p1214_1]
                                              · have p1214_0 := h1214c.1
                                                have p1214_1 := h1214c.2.1
                                                have p1214_2 := h1214c.2.2.1
                                                have p1214_3 := h1214c.2.2.2
                                                rcases p1214_3 (m.d 0 3) (by simp) with h1227 | h1227
                                                · rcases p1214_3 (m.d 1 3) (by simp) with h1228 | h1228
                                                  · rcases p1214_3 (m.d 2 3) (by simp) with h1229 | h1229
                                                    · linarith only [h1101, h1229, hlam]
                                                    · linarith only [h1108, h1229, hlam]
                                                  · linarith only [h1228, hlam, p1214_0]
                                                · linarith only [h1227, h7, hlam]
                                              · have p1214_0 := h1214c.1
                                                have p1214_1 := h1214c.2.1
                                                have p1214_2 := h1214c.2.2.1
                                                have p1214_3 := h1214c.2.2.2
                                                rcases p1214_3 (m.d 0 3) (by simp) with h1234 | h1234
                                                · rcases p1214_3 (m.d 1 3) (by simp) with h1235 | h1235
                                                  · rcases p1214_3 (m.d 2 3) (by simp) with h1236 | h1236
                                                    · linarith only [h1101, h1236, hlam]
                                                    · linarith only [h1109, h1236, hlam]
                                                  · linarith only [h1235, hlam, p1214_0]
                                                · linarith only [h1234, h8, hlam]
                                              · have p1214_0 := h1214c.1
                                                have p1214_1 := h1214c.2.1
                                                have p1214_2 := h1214c.2.2.1
                                                have p1214_3 := h1214c.2.2.2
                                                linarith only [h4, hlam, p1214_0]
                                              · have p1214_0 := h1214c.1
                                                have p1214_1 := h1214c.2.1
                                                have p1214_2 := h1214c.2.2.1
                                                have p1214_3 := h1214c.2.2.2
                                                linarith only [h1101, hlam, p1214_0]
                                              · have p1214_0 := h1214c.1
                                                have p1214_1 := h1214c.2.1
                                                have p1214_2 := h1214c.2.2.1
                                                have p1214_3 := h1214c.2.2.2
                                                linarith only [hlam, p1214_0]
                                              · have p1214_0 := h1214c.1
                                                have p1214_1 := h1214c.2.1
                                                have p1214_2 := h1214c.2.2.1
                                                have p1214_3 := h1214c.2.2.2
                                                linarith only [h0, h1101, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1214_1]
                                              · have p1214_0 := h1214c.1
                                                have p1214_1 := h1214c.2.1
                                                have p1214_2 := h1214c.2.2.1
                                                have p1214_3 := h1214c.2.2.2
                                                linarith only [h0, h1101, h1112, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1214_1]
                                              · have p1214_0 := h1214c.1
                                                have p1214_1 := h1214c.2.1
                                                have p1214_2 := h1214c.2.2.1
                                                have p1214_3 := h1214c.2.2.2
                                                linarith only [h7, hlam, p1214_0]
                                              · have p1214_0 := h1214c.1
                                                have p1214_1 := h1214c.2.1
                                                have p1214_2 := h1214c.2.2.1
                                                have p1214_3 := h1214c.2.2.2
                                                linarith only [h1104, hlam, p1214_0]
                                              · have p1214_0 := h1214c.1
                                                have p1214_1 := h1214c.2.1
                                                have p1214_2 := h1214c.2.2.1
                                                have p1214_3 := h1214c.2.2.2
                                                linarith only [h1108, hlam, p1214_0]
                                              · have p1214_0 := h1214c.1
                                                have p1214_1 := h1214c.2.1
                                                have p1214_2 := h1214c.2.2.1
                                                have p1214_3 := h1214c.2.2.2
                                                linarith only [hlam, p1214_0]
                                              · have p1214_0 := h1214c.1
                                                have p1214_1 := h1214c.2.1
                                                have p1214_2 := h1214c.2.2.1
                                                have p1214_3 := h1214c.2.2.2
                                                linarith only [h1112, hlam, p1214_1]
                                              · have p1214_0 := h1214c.1
                                                have p1214_1 := h1214c.2.1
                                                have p1214_2 := h1214c.2.2.1
                                                have p1214_3 := h1214c.2.2.2
                                                linarith only [h8, hlam, p1214_0]
                                              · have p1214_0 := h1214c.1
                                                have p1214_1 := h1214c.2.1
                                                have p1214_2 := h1214c.2.2.1
                                                have p1214_3 := h1214c.2.2.2
                                                linarith only [h1105, hlam, p1214_0]
                                              · have p1214_0 := h1214c.1
                                                have p1214_1 := h1214c.2.1
                                                have p1214_2 := h1214c.2.2.1
                                                have p1214_3 := h1214c.2.2.2
                                                linarith only [h1109, hlam, p1214_0]
                                              · have p1214_0 := h1214c.1
                                                have p1214_1 := h1214c.2.1
                                                have p1214_2 := h1214c.2.2.1
                                                have p1214_3 := h1214c.2.2.2
                                                linarith only [h8, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1114_1, p1214_1]
                                              · have p1214_0 := h1214c.1
                                                have p1214_1 := h1214c.2.1
                                                have p1214_2 := h1214c.2.2.1
                                                have p1214_3 := h1214c.2.2.2
                                                linarith only [hlam, p1214_0]
                                        · linarith only [h1105, h1209, hlam]
                                      · linarith only [h1103, h1208, hlam]
                                    · linarith only [h1207, h3, hlam]
                                  · have p1166_0 := h1166c.1
                                    have p1166_1 := h1166c.2.1
                                    have p1166_2 := h1166c.2.2.1
                                    have p1166_3 := h1166c.2.2.2
                                    linarith only [h2, hlam, p1166_0]
                                  · have p1166_0 := h1166c.1
                                    have p1166_1 := h1166c.2.1
                                    have p1166_2 := h1166c.2.2.1
                                    have p1166_3 := h1166c.2.2.2
                                    linarith only [h1102, hlam, p1166_1]
                                  · have p1166_0 := h1166c.1
                                    have p1166_1 := h1166c.2.1
                                    have p1166_2 := h1166c.2.2.1
                                    have p1166_3 := h1166c.2.2.2
                                    linarith only [h1104, hlam, p1166_0]
                                  · have p1166_0 := h1166c.1
                                    have p1166_1 := h1166c.2.1
                                    have p1166_2 := h1166c.2.2.1
                                    have p1166_3 := h1166c.2.2.2
                                    linarith only [hlam, p1166_0]
                                  · have p1166_0 := h1166c.1
                                    have p1166_1 := h1166c.2.1
                                    have p1166_2 := h1166c.2.2.1
                                    have p1166_3 := h1166c.2.2.2
                                    linarith only [h1106, hlam, p1166_1]
                                  · have p1166_0 := h1166c.1
                                    have p1166_1 := h1166c.2.1
                                    have p1166_2 := h1166c.2.2.1
                                    have p1166_3 := h1166c.2.2.2
                                    linarith only [h3, hlam, p1166_0]
                                  · have p1166_0 := h1166c.1
                                    have p1166_1 := h1166c.2.1
                                    have p1166_2 := h1166c.2.2.1
                                    have p1166_3 := h1166c.2.2.2
                                    linarith only [h1103, hlam, p1166_1]
                                  · have p1166_0 := h1166c.1
                                    have p1166_1 := h1166c.2.1
                                    have p1166_2 := h1166c.2.2.1
                                    have p1166_3 := h1166c.2.2.2
                                    linarith only [h1105, hlam, p1166_0]
                                  · have p1166_0 := h1166c.1
                                    have p1166_1 := h1166c.2.1
                                    have p1166_2 := h1166c.2.2.1
                                    have p1166_3 := h1166c.2.2.2
                                    linarith only [h1, h1102, h1108, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1114_1, p1166_1]
                                  · have p1166_0 := h1166c.1
                                    have p1166_1 := h1166c.2.1
                                    have p1166_2 := h1166c.2.2.1
                                    have p1166_3 := h1166c.2.2.2
                                    linarith only [hlam, p1166_0]
                            · linarith only [h1161, h8, hlam]
                          · linarith only [h1160, h6, hlam]
                        · linarith only [h1159, h3, hlam]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [h2, hlam, p1114_0]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [h5, hlam, p1114_0]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [h7, hlam, p1114_0]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [hlam, p1114_0]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [h9, hlam, p1114_0]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [h3, hlam, p1114_0]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [h6, hlam, p1114_1]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [h8, hlam, p1114_0]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [h1102, h1108, h2, h9, hc34, hc45, hlam, hphi, p1114_1]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [hlam, p1114_0]
                · linarith only [h0, h1101, h1105, h1108, h1109, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1283 | h1283
                · linarith only [h0, h1101, h1104, h1108, h1283, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1285 | h1285
                  · linarith only [h0, h1104, h1108, h1285, h2, h5, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1287 | h1287
                    · linarith only [h1104, h1287, h2, h9, hlam]
                    · rcases h0bigk with h1289c | h1289c | h1289c | h1289c | h1289c | h1289c | h1289c | h1289c | h1289c | h1289c | h1289c | h1289c | h1289c | h1289c | h1289c | h1289c | h1289c | h1289c | h1289c | h1289c | h1289c | h1289c | h1289c | h1289c | h1289c
                      · have p1289_0 := h1289c.1
                        have p1289_1 := h1289c.2.1
                        have p1289_2 := h1289c.2.2.1
                        have p1289_3 := h1289c.2.2.2
                        linarith only [hlam, p1289_0]
                      · have p1289_0 := h1289c.1
                        have p1289_1 := h1289c.2.1
                        have p1289_2 := h1289c.2.2.1
                        have p1289_3 := h1289c.2.2.2
                        linarith only [h0, h1101, h1105, h1108, h1287, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1289_1]
                      · have p1289_0 := h1289c.1
                        have p1289_1 := h1289c.2.1
                        have p1289_2 := h1289c.2.2.1
                        have p1289_3 := h1289c.2.2.2
                        linarith only [h1, h1105, h1108, h1287, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1289_1]
                      · have p1289_0 := h1289c.1
                        have p1289_1 := h1289c.2.1
                        have p1289_2 := h1289c.2.2.1
                        have p1289_3 := h1289c.2.2.2
                        linarith only [h1104, h1108, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1289_1]
                      · have p1289_0 := h1289c.1
                        have p1289_1 := h1289c.2.1
                        have p1289_2 := h1289c.2.2.1
                        have p1289_3 := h1289c.2.2.2
                        linarith only [h1108, h1287, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1289_1]
                      · have p1289_0 := h1289c.1
                        have p1289_1 := h1289c.2.1
                        have p1289_2 := h1289c.2.2.1
                        have p1289_3 := h1289c.2.2.2
                        linarith only [h0, hlam, p1289_0]
                      · have p1289_0 := h1289c.1
                        have p1289_1 := h1289c.2.1
                        have p1289_2 := h1289c.2.2.1
                        have p1289_3 := h1289c.2.2.2
                        linarith only [hlam, p1289_0]
                      · have p1289_0 := h1289c.1
                        have p1289_1 := h1289c.2.1
                        have p1289_2 := h1289c.2.2.1
                        have p1289_3 := h1289c.2.2.2
                        linarith only [h1, h1105, h1108, h1287, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1289_1]
                      · have p1289_0 := h1289c.1
                        have p1289_1 := h1289c.2.1
                        have p1289_2 := h1289c.2.2.1
                        have p1289_3 := h1289c.2.2.2
                        linarith only [h0, h1104, h1108, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1289_1]
                      · have p1289_0 := h1289c.1
                        have p1289_1 := h1289c.2.1
                        have p1289_2 := h1289c.2.2.1
                        have p1289_3 := h1289c.2.2.2
                        linarith only [h0, h1108, h1287, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1289_1]
                      · have p1289_0 := h1289c.1
                        have p1289_1 := h1289c.2.1
                        have p1289_2 := h1289c.2.2.1
                        have p1289_3 := h1289c.2.2.2
                        linarith only [h1, hlam, p1289_1]
                      · have p1289_0 := h1289c.1
                        have p1289_1 := h1289c.2.1
                        have p1289_2 := h1289c.2.2.1
                        have p1289_3 := h1289c.2.2.2
                        linarith only [h4, hlam, p1289_1]
                      · have p1289_0 := h1289c.1
                        have p1289_1 := h1289c.2.1
                        have p1289_2 := h1289c.2.2.1
                        have p1289_3 := h1289c.2.2.2
                        linarith only [hlam, p1289_0]
                      · have p1289_0 := h1289c.1
                        have p1289_1 := h1289c.2.1
                        have p1289_2 := h1289c.2.2.1
                        have p1289_3 := h1289c.2.2.2
                        linarith only [h1104, h1108, h2, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1289_1]
                      · have p1289_0 := h1289c.1
                        have p1289_1 := h1289c.2.1
                        have p1289_2 := h1289c.2.2.1
                        have p1289_3 := h1289c.2.2.2
                        linarith only [h0, h1108, h1287, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1289_1]
                      · have p1289_0 := h1289c.1
                        have p1289_1 := h1289c.2.1
                        have p1289_2 := h1289c.2.2.1
                        have p1289_3 := h1289c.2.2.2
                        linarith only [h2, hlam, p1289_0]
                      · have p1289_0 := h1289c.1
                        have p1289_1 := h1289c.2.1
                        have p1289_2 := h1289c.2.2.1
                        have p1289_3 := h1289c.2.2.2
                        linarith only [h5, hlam, p1289_0]
                      · have p1289_0 := h1289c.1
                        have p1289_1 := h1289c.2.1
                        have p1289_2 := h1289c.2.2.1
                        have p1289_3 := h1289c.2.2.2
                        linarith only [h7, hlam, p1289_0]
                      · have p1289_0 := h1289c.1
                        have p1289_1 := h1289c.2.1
                        have p1289_2 := h1289c.2.2.1
                        have p1289_3 := h1289c.2.2.2
                        linarith only [hlam, p1289_0]
                      · have p1289_0 := h1289c.1
                        have p1289_1 := h1289c.2.1
                        have p1289_2 := h1289c.2.2.1
                        have p1289_3 := h1289c.2.2.2
                        linarith only [h9, hlam, p1289_0]
                      · have p1289_0 := h1289c.1
                        have p1289_1 := h1289c.2.1
                        have p1289_2 := h1289c.2.2.1
                        have p1289_3 := h1289c.2.2.2
                        linarith only [h3, hlam, p1289_0]
                      · have p1289_0 := h1289c.1
                        have p1289_1 := h1289c.2.1
                        have p1289_2 := h1289c.2.2.1
                        have p1289_3 := h1289c.2.2.2
                        linarith only [h6, hlam, p1289_1]
                      · have p1289_0 := h1289c.1
                        have p1289_1 := h1289c.2.1
                        have p1289_2 := h1289c.2.2.1
                        have p1289_3 := h1289c.2.2.2
                        linarith only [h8, hlam, p1289_0]
                      · have p1289_0 := h1289c.1
                        have p1289_1 := h1289c.2.1
                        have p1289_2 := h1289c.2.2.1
                        have p1289_3 := h1289c.2.2.2
                        linarith only [h1104, h1108, h2, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1289_1]
                      · have p1289_0 := h1289c.1
                        have p1289_1 := h1289c.2.1
                        have p1289_2 := h1289c.2.2.1
                        have p1289_3 := h1289c.2.2.2
                        linarith only [hlam, p1289_0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1315 | h1315
            · linarith only [h1315, h2, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1317 | h1317
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1318 | h1318
                · linarith only [h1101, h1105, h1318, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1320 | h1320
                  · linarith only [h1102, h1320, h2, h9, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1322 | h1322
                    · linarith only [h0, h1317, h1322, h2, h4, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases h0bigk with h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c
                      · have p1324_0 := h1324c.1
                        have p1324_1 := h1324c.2.1
                        have p1324_2 := h1324c.2.2.1
                        have p1324_3 := h1324c.2.2.2
                        linarith only [hlam, p1324_0]
                      · have p1324_0 := h1324c.1
                        have p1324_1 := h1324c.2.1
                        have p1324_2 := h1324c.2.2.1
                        have p1324_3 := h1324c.2.2.2
                        linarith only [h1105, h4, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1324_1]
                      · have p1324_0 := h1324c.1
                        have p1324_1 := h1324c.2.1
                        have p1324_2 := h1324c.2.2.1
                        have p1324_3 := h1324c.2.2.2
                        linarith only [h1101, h1105, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1324_1]
                      · have p1324_0 := h1324c.1
                        have p1324_1 := h1324c.2.1
                        have p1324_2 := h1324c.2.2.1
                        have p1324_3 := h1324c.2.2.2
                        rcases p1324_3 (m.d 0 1) (by simp) with h1328 | h1328
                        · rcases p1324_3 (m.d 0 2) (by simp) with h1329 | h1329
                          · linarith only [h0, h1329, hlam]
                          · linarith only [h1329, h5, hlam]
                        · linarith only [h1328, h2, hlam]
                      · have p1324_0 := h1324c.1
                        have p1324_1 := h1324c.2.1
                        have p1324_2 := h1324c.2.2.1
                        have p1324_3 := h1324c.2.2.2
                        linarith only [h1101, h1105, h1317, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1324_1]
                      · have p1324_0 := h1324c.1
                        have p1324_1 := h1324c.2.1
                        have p1324_2 := h1324c.2.2.1
                        have p1324_3 := h1324c.2.2.2
                        linarith only [h0, hlam, p1324_0]
                      · have p1324_0 := h1324c.1
                        have p1324_1 := h1324c.2.1
                        have p1324_2 := h1324c.2.2.1
                        have p1324_3 := h1324c.2.2.2
                        linarith only [hlam, p1324_0]
                      · have p1324_0 := h1324c.1
                        have p1324_1 := h1324c.2.1
                        have p1324_2 := h1324c.2.2.1
                        have p1324_3 := h1324c.2.2.2
                        linarith only [h1101, h1105, h1317, h8, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1324_1]
                      · have p1324_0 := h1324c.1
                        have p1324_1 := h1324c.2.1
                        have p1324_2 := h1324c.2.2.1
                        have p1324_3 := h1324c.2.2.2
                        rcases p1324_3 (m.d 0 1) (by simp) with h1337 | h1337
                        · rcases p1324_3 (m.d 0 2) (by simp) with h1338 | h1338
                          · rcases p1324_3 (m.d 0 3) (by simp) with h1339 | h1339
                            · linarith only [h1339, h4, hlam]
                            · linarith only [h1339, h7, hlam]
                          · linarith only [h1338, h5, hlam]
                        · linarith only [h1337, h2, hlam]
                      · have p1324_0 := h1324c.1
                        have p1324_1 := h1324c.2.1
                        have p1324_2 := h1324c.2.2.1
                        have p1324_3 := h1324c.2.2.2
                        linarith only [h0, h1101, h1105, h1317, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1324_1]
                      · have p1324_0 := h1324c.1
                        have p1324_1 := h1324c.2.1
                        have p1324_2 := h1324c.2.2.1
                        have p1324_3 := h1324c.2.2.2
                        linarith only [h1, hlam, p1324_1]
                      · have p1324_0 := h1324c.1
                        have p1324_1 := h1324c.2.1
                        have p1324_2 := h1324c.2.2.1
                        have p1324_3 := h1324c.2.2.2
                        linarith only [h4, hlam, p1324_1]
                      · have p1324_0 := h1324c.1
                        have p1324_1 := h1324c.2.1
                        have p1324_2 := h1324c.2.2.1
                        have p1324_3 := h1324c.2.2.2
                        linarith only [hlam, p1324_0]
                      · have p1324_0 := h1324c.1
                        have p1324_1 := h1324c.2.1
                        have p1324_2 := h1324c.2.2.1
                        have p1324_3 := h1324c.2.2.2
                        rcases p1324_3 (m.d 0 1) (by simp) with h1348 | h1348
                        · rcases p1324_3 (m.d 0 2) (by simp) with h1349 | h1349
                          · rcases p1324_3 (m.d 0 3) (by simp) with h1350 | h1350
                            · rcases p1324_3 (m.d 0 4) (by simp) with h1351 | h1351
                              · linarith only [h1351, h7, hlam]
                              · rcases p1324_3 (m.d 0 5) (by simp) with h1353 | h1353
                                · linarith only [h1353, h8, hlam]
                                · linarith only [h1353, h9, hlam]
                            · linarith only [h1350, h7, hlam]
                          · linarith only [h1349, h5, hlam]
                        · linarith only [h1348, h2, hlam]
                      · have p1324_0 := h1324c.1
                        have p1324_1 := h1324c.2.1
                        have p1324_2 := h1324c.2.2.1
                        have p1324_3 := h1324c.2.2.2
                        linarith only [h1101, h1105, h1317, h8, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1324_1]
                      · have p1324_0 := h1324c.1
                        have p1324_1 := h1324c.2.1
                        have p1324_2 := h1324c.2.2.1
                        have p1324_3 := h1324c.2.2.2
                        linarith only [h2, hlam, p1324_0]
                      · have p1324_0 := h1324c.1
                        have p1324_1 := h1324c.2.1
                        have p1324_2 := h1324c.2.2.1
                        have p1324_3 := h1324c.2.2.2
                        linarith only [h5, hlam, p1324_0]
                      · have p1324_0 := h1324c.1
                        have p1324_1 := h1324c.2.1
                        have p1324_2 := h1324c.2.2.1
                        have p1324_3 := h1324c.2.2.2
                        linarith only [h7, hlam, p1324_0]
                      · have p1324_0 := h1324c.1
                        have p1324_1 := h1324c.2.1
                        have p1324_2 := h1324c.2.2.1
                        have p1324_3 := h1324c.2.2.2
                        linarith only [hlam, p1324_0]
                      · have p1324_0 := h1324c.1
                        have p1324_1 := h1324c.2.1
                        have p1324_2 := h1324c.2.2.1
                        have p1324_3 := h1324c.2.2.2
                        linarith only [h9, hlam, p1324_0]
                      · have p1324_0 := h1324c.1
                        have p1324_1 := h1324c.2.1
                        have p1324_2 := h1324c.2.2.1
                        have p1324_3 := h1324c.2.2.2
                        linarith only [h3, hlam, p1324_0]
                      · have p1324_0 := h1324c.1
                        have p1324_1 := h1324c.2.1
                        have p1324_2 := h1324c.2.2.1
                        have p1324_3 := h1324c.2.2.2
                        linarith only [h6, hlam, p1324_1]
                      · have p1324_0 := h1324c.1
                        have p1324_1 := h1324c.2.1
                        have p1324_2 := h1324c.2.2.1
                        have p1324_3 := h1324c.2.2.2
                        linarith only [h8, hlam, p1324_0]
                      · have p1324_0 := h1324c.1
                        have p1324_1 := h1324c.2.1
                        have p1324_2 := h1324c.2.2.1
                        have p1324_3 := h1324c.2.2.2
                        linarith only [h1102, h1317, h2, h9, hc34, hc45, hlam, hphi, p1324_1]
                      · have p1324_0 := h1324c.1
                        have p1324_1 := h1324c.2.1
                        have p1324_2 := h1324c.2.2.1
                        have p1324_3 := h1324c.2.2.2
                        linarith only [hlam, p1324_0]
              · linarith only [h1104, h1105, h1317, hc23, hc35, hlam, hphi]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1371 | h1371
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1372 | h1372
            · linarith only [h1104, h1372, h7, h9, hlam]
            · linarith only [h1104, h1371, h1372, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1375 | h1375
            · linarith only [h1375, h2, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1377 | h1377
              · linarith only [h1101, h1104, h1377, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1379 | h1379
                · linarith only [h1101, h1371, h1379, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1381 | h1381
                  · linarith only [h1101, h1102, h1104, h1381, h2, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1383 | h1383
                    · linarith only [h1383, h7, h9, hlam]
                    · rcases h0bigk with h1385c | h1385c | h1385c | h1385c | h1385c | h1385c | h1385c | h1385c | h1385c | h1385c | h1385c | h1385c | h1385c | h1385c | h1385c | h1385c | h1385c | h1385c | h1385c | h1385c | h1385c | h1385c | h1385c | h1385c | h1385c
                      · have p1385_0 := h1385c.1
                        have p1385_1 := h1385c.2.1
                        have p1385_2 := h1385c.2.2.1
                        have p1385_3 := h1385c.2.2.2
                        linarith only [hlam, p1385_0]
                      · have p1385_0 := h1385c.1
                        have p1385_1 := h1385c.2.1
                        have p1385_2 := h1385c.2.2.1
                        have p1385_3 := h1385c.2.2.2
                        linarith only [h1371, h1375, h4, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1385_1]
                      · have p1385_0 := h1385c.1
                        have p1385_1 := h1385c.2.1
                        have p1385_2 := h1385c.2.2.1
                        have p1385_3 := h1385c.2.2.2
                        linarith only [h1371, h1375, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1385_1]
                      · have p1385_0 := h1385c.1
                        have p1385_1 := h1385c.2.1
                        have p1385_2 := h1385c.2.2.1
                        have p1385_3 := h1385c.2.2.2
                        linarith only [h1101, h1104, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1385_1]
                      · have p1385_0 := h1385c.1
                        have p1385_1 := h1385c.2.1
                        have p1385_2 := h1385c.2.2.1
                        have p1385_3 := h1385c.2.2.2
                        linarith only [h1101, h1104, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1385_1]
                      · have p1385_0 := h1385c.1
                        have p1385_1 := h1385c.2.1
                        have p1385_2 := h1385c.2.2.1
                        have p1385_3 := h1385c.2.2.2
                        linarith only [h0, hlam, p1385_0]
                      · have p1385_0 := h1385c.1
                        have p1385_1 := h1385c.2.1
                        have p1385_2 := h1385c.2.2.1
                        have p1385_3 := h1385c.2.2.2
                        linarith only [hlam, p1385_0]
                      · have p1385_0 := h1385c.1
                        have p1385_1 := h1385c.2.1
                        have p1385_2 := h1385c.2.2.1
                        have p1385_3 := h1385c.2.2.2
                        linarith only [h1102, h1371, h1375, h8, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p1385_1]
                      · have p1385_0 := h1385c.1
                        have p1385_1 := h1385c.2.1
                        have p1385_2 := h1385c.2.2.1
                        have p1385_3 := h1385c.2.2.2
                        linarith only [h0, h1101, h1104, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1385_1]
                      · have p1385_0 := h1385c.1
                        have p1385_1 := h1385c.2.1
                        have p1385_2 := h1385c.2.2.1
                        have p1385_3 := h1385c.2.2.2
                        linarith only [h0, h1101, h1104, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1385_1]
                      · have p1385_0 := h1385c.1
                        have p1385_1 := h1385c.2.1
                        have p1385_2 := h1385c.2.2.1
                        have p1385_3 := h1385c.2.2.2
                        linarith only [h1, hlam, p1385_1]
                      · have p1385_0 := h1385c.1
                        have p1385_1 := h1385c.2.1
                        have p1385_2 := h1385c.2.2.1
                        have p1385_3 := h1385c.2.2.2
                        linarith only [h4, hlam, p1385_1]
                      · have p1385_0 := h1385c.1
                        have p1385_1 := h1385c.2.1
                        have p1385_2 := h1385c.2.2.1
                        have p1385_3 := h1385c.2.2.2
                        linarith only [hlam, p1385_0]
                      · have p1385_0 := h1385c.1
                        have p1385_1 := h1385c.2.1
                        have p1385_2 := h1385c.2.2.1
                        have p1385_3 := h1385c.2.2.2
                        linarith only [h1101, h1104, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1385_1]
                      · have p1385_0 := h1385c.1
                        have p1385_1 := h1385c.2.1
                        have p1385_2 := h1385c.2.2.1
                        have p1385_3 := h1385c.2.2.2
                        linarith only [h0, h1101, h1104, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1385_1]
                      · have p1385_0 := h1385c.1
                        have p1385_1 := h1385c.2.1
                        have p1385_2 := h1385c.2.2.1
                        have p1385_3 := h1385c.2.2.2
                        linarith only [h2, hlam, p1385_0]
                      · have p1385_0 := h1385c.1
                        have p1385_1 := h1385c.2.1
                        have p1385_2 := h1385c.2.2.1
                        have p1385_3 := h1385c.2.2.2
                        linarith only [h5, hlam, p1385_0]
                      · have p1385_0 := h1385c.1
                        have p1385_1 := h1385c.2.1
                        have p1385_2 := h1385c.2.2.1
                        have p1385_3 := h1385c.2.2.2
                        linarith only [h7, hlam, p1385_0]
                      · have p1385_0 := h1385c.1
                        have p1385_1 := h1385c.2.1
                        have p1385_2 := h1385c.2.2.1
                        have p1385_3 := h1385c.2.2.2
                        linarith only [hlam, p1385_0]
                      · have p1385_0 := h1385c.1
                        have p1385_1 := h1385c.2.1
                        have p1385_2 := h1385c.2.2.1
                        have p1385_3 := h1385c.2.2.2
                        linarith only [h9, hlam, p1385_0]
                      · have p1385_0 := h1385c.1
                        have p1385_1 := h1385c.2.1
                        have p1385_2 := h1385c.2.2.1
                        have p1385_3 := h1385c.2.2.2
                        linarith only [h3, hlam, p1385_0]
                      · have p1385_0 := h1385c.1
                        have p1385_1 := h1385c.2.1
                        have p1385_2 := h1385c.2.2.1
                        have p1385_3 := h1385c.2.2.2
                        linarith only [h6, hlam, p1385_1]
                      · have p1385_0 := h1385c.1
                        have p1385_1 := h1385c.2.1
                        have p1385_2 := h1385c.2.2.1
                        have p1385_3 := h1385c.2.2.2
                        linarith only [h8, hlam, p1385_0]
                      · have p1385_0 := h1385c.1
                        have p1385_1 := h1385c.2.1
                        have p1385_2 := h1385c.2.2.1
                        have p1385_3 := h1385c.2.2.2
                        linarith only [h1101, h1104, h7, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1385_1]
                      · have p1385_0 := h1385c.1
                        have p1385_1 := h1385c.2.1
                        have p1385_2 := h1385c.2.2.1
                        have p1385_3 := h1385c.2.2.2
                        linarith only [hlam, p1385_0]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1411 | h1411
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1412 | h1412
          · linarith only [h1101, h1103, h1412, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1414 | h1414
            · linarith only [h1414, h2, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1416 | h1416
              · linarith only [h1101, h1103, h1416, h6, h9, hc34, hc45, hlam, hphi]
              · linarith only [h0, h1101, h1103, h1411, h1416, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1419 | h1419
          · linarith only [h1101, h1103, h1411, h1419, h7, h9, hc23, hc45, hlam, hphi, ht34]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1421 | h1421
            · linarith only [h1421, h2, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1423 | h1423
              · linarith only [h1101, h1411, h1423, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1425 | h1425
                · linarith only [h1102, h1103, h1419, h1423, h1425, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1427 | h1427
                  · linarith only [h1102, h1103, h1427, h3, h9, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1429 | h1429
                    · linarith only [h1102, h1103, h1423, h1425, h1429, h8, h9, hc23, hc34, hlam, hphi]
                    · rcases h0bigk with h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c
                      · have p1431_0 := h1431c.1
                        have p1431_1 := h1431c.2.1
                        have p1431_2 := h1431c.2.2.1
                        have p1431_3 := h1431c.2.2.2
                        linarith only [hlam, p1431_0]
                      · have p1431_0 := h1431c.1
                        have p1431_1 := h1431c.2.1
                        have p1431_2 := h1431c.2.2.1
                        have p1431_3 := h1431c.2.2.2
                        linarith only [h1102, h1103, h1423, h1425, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1431_1]
                      · have p1431_0 := h1431c.1
                        have p1431_1 := h1431c.2.1
                        have p1431_2 := h1431c.2.2.1
                        have p1431_3 := h1431c.2.2.2
                        linarith only [h1102, h1103, h1423, h1425, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1431_1]
                      · have p1431_0 := h1431c.1
                        have p1431_1 := h1431c.2.1
                        have p1431_2 := h1431c.2.2.1
                        have p1431_3 := h1431c.2.2.2
                        linarith only [h1101, h1411, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1431_1]
                      · have p1431_0 := h1431c.1
                        have p1431_1 := h1431c.2.1
                        have p1431_2 := h1431c.2.2.1
                        have p1431_3 := h1431c.2.2.2
                        linarith only [h1102, h1103, h1423, h1425, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1431_1]
                      · have p1431_0 := h1431c.1
                        have p1431_1 := h1431c.2.1
                        have p1431_2 := h1431c.2.2.1
                        have p1431_3 := h1431c.2.2.2
                        linarith only [h0, hlam, p1431_0]
                      · have p1431_0 := h1431c.1
                        have p1431_1 := h1431c.2.1
                        have p1431_2 := h1431c.2.2.1
                        have p1431_3 := h1431c.2.2.2
                        linarith only [hlam, p1431_0]
                      · have p1431_0 := h1431c.1
                        have p1431_1 := h1431c.2.1
                        have p1431_2 := h1431c.2.2.1
                        have p1431_3 := h1431c.2.2.2
                        linarith only [h1102, h1103, h1423, h1425, h8, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1431_1]
                      · have p1431_0 := h1431c.1
                        have p1431_1 := h1431c.2.1
                        have p1431_2 := h1431c.2.2.1
                        have p1431_3 := h1431c.2.2.2
                        linarith only [h0, h1101, h1411, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1431_1]
                      · have p1431_0 := h1431c.1
                        have p1431_1 := h1431c.2.1
                        have p1431_2 := h1431c.2.2.1
                        have p1431_3 := h1431c.2.2.2
                        linarith only [h0, h1102, h1103, h1423, h1425, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1431_1]
                      · have p1431_0 := h1431c.1
                        have p1431_1 := h1431c.2.1
                        have p1431_2 := h1431c.2.2.1
                        have p1431_3 := h1431c.2.2.2
                        linarith only [h1, hlam, p1431_1]
                      · have p1431_0 := h1431c.1
                        have p1431_1 := h1431c.2.1
                        have p1431_2 := h1431c.2.2.1
                        have p1431_3 := h1431c.2.2.2
                        linarith only [h4, hlam, p1431_1]
                      · have p1431_0 := h1431c.1
                        have p1431_1 := h1431c.2.1
                        have p1431_2 := h1431c.2.2.1
                        have p1431_3 := h1431c.2.2.2
                        linarith only [hlam, p1431_0]
                      · have p1431_0 := h1431c.1
                        have p1431_1 := h1431c.2.1
                        have p1431_2 := h1431c.2.2.1
                        have p1431_3 := h1431c.2.2.2
                        linarith only [h0, h1101, h1411, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1431_1]
                      · have p1431_0 := h1431c.1
                        have p1431_1 := h1431c.2.1
                        have p1431_2 := h1431c.2.2.1
                        have p1431_3 := h1431c.2.2.2
                        linarith only [h0, h1102, h1103, h1423, h1425, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1431_1]
                      · have p1431_0 := h1431c.1
                        have p1431_1 := h1431c.2.1
                        have p1431_2 := h1431c.2.2.1
                        have p1431_3 := h1431c.2.2.2
                        linarith only [h2, hlam, p1431_0]
                      · have p1431_0 := h1431c.1
                        have p1431_1 := h1431c.2.1
                        have p1431_2 := h1431c.2.2.1
                        have p1431_3 := h1431c.2.2.2
                        linarith only [h5, hlam, p1431_0]
                      · have p1431_0 := h1431c.1
                        have p1431_1 := h1431c.2.1
                        have p1431_2 := h1431c.2.2.1
                        have p1431_3 := h1431c.2.2.2
                        linarith only [h7, hlam, p1431_0]
                      · have p1431_0 := h1431c.1
                        have p1431_1 := h1431c.2.1
                        have p1431_2 := h1431c.2.2.1
                        have p1431_3 := h1431c.2.2.2
                        linarith only [hlam, p1431_0]
                      · have p1431_0 := h1431c.1
                        have p1431_1 := h1431c.2.1
                        have p1431_2 := h1431c.2.2.1
                        have p1431_3 := h1431c.2.2.2
                        linarith only [h9, hlam, p1431_0]
                      · have p1431_0 := h1431c.1
                        have p1431_1 := h1431c.2.1
                        have p1431_2 := h1431c.2.2.1
                        have p1431_3 := h1431c.2.2.2
                        linarith only [h3, hlam, p1431_0]
                      · have p1431_0 := h1431c.1
                        have p1431_1 := h1431c.2.1
                        have p1431_2 := h1431c.2.2.1
                        have p1431_3 := h1431c.2.2.2
                        linarith only [h6, hlam, p1431_1]
                      · have p1431_0 := h1431c.1
                        have p1431_1 := h1431c.2.1
                        have p1431_2 := h1431c.2.2.1
                        have p1431_3 := h1431c.2.2.2
                        linarith only [h8, hlam, p1431_0]
                      · have p1431_0 := h1431c.1
                        have p1431_1 := h1431c.2.1
                        have p1431_2 := h1431c.2.2.1
                        have p1431_3 := h1431c.2.2.2
                        linarith only [h9, hc04, hc45, hlam, hphi, p1431_1]
                      · have p1431_0 := h1431c.1
                        have p1431_1 := h1431c.2.1
                        have p1431_2 := h1431c.2.2.1
                        have p1431_3 := h1431c.2.2.2
                        linarith only [hlam, p1431_0]
    · linarith only [h1101, h1102, h5, h9, hc23, hc45, hlam, hphi, ht34]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1458 | h1458
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1459 | h1459
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1460 | h1460
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1461 | h1461
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1462 | h1462
            · linarith only [h1462, h2, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1464 | h1464
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1465 | h1465
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1466 | h1466
                  · linarith only [h1101, h1458, h1466, h2, h9, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1468 | h1468
                    · linarith only [h1458, h1464, h1468, h2, h9, hlam]
                    · rcases h0bigk with h1470c | h1470c | h1470c | h1470c | h1470c | h1470c | h1470c | h1470c | h1470c | h1470c | h1470c | h1470c | h1470c | h1470c | h1470c | h1470c | h1470c | h1470c | h1470c | h1470c | h1470c | h1470c | h1470c | h1470c | h1470c
                      · have p1470_0 := h1470c.1
                        have p1470_1 := h1470c.2.1
                        have p1470_2 := h1470c.2.2.1
                        have p1470_3 := h1470c.2.2.2
                        linarith only [hlam, p1470_0]
                      · have p1470_0 := h1470c.1
                        have p1470_1 := h1470c.2.1
                        have p1470_2 := h1470c.2.2.1
                        have p1470_3 := h1470c.2.2.2
                        linarith only [h1101, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1470_1]
                      · have p1470_0 := h1470c.1
                        have p1470_1 := h1470c.2.1
                        have p1470_2 := h1470c.2.2.1
                        have p1470_3 := h1470c.2.2.2
                        linarith only [h1, h1101, h1459, h1465, hc01, hc35, hlam, hphi, ht0b, ht5b, p1470_1]
                      · have p1470_0 := h1470c.1
                        have p1470_1 := h1470c.2.1
                        have p1470_2 := h1470c.2.2.1
                        have p1470_3 := h1470c.2.2.2
                        rcases p1470_3 (m.d 0 1) (by simp) with h1474 | h1474
                        · rcases p1470_3 (m.d 0 2) (by simp) with h1475 | h1475
                          · linarith only [h0, h1475, hlam]
                          · linarith only [h1475, h5, hlam]
                        · linarith only [h1474, h2, hlam]
                      · have p1470_0 := h1470c.1
                        have p1470_1 := h1470c.2.1
                        have p1470_2 := h1470c.2.2.1
                        have p1470_3 := h1470c.2.2.2
                        rcases p1470_3 (m.d 0 1) (by simp) with h1479 | h1479
                        · rcases p1470_3 (m.d 0 2) (by simp) with h1480 | h1480
                          · linarith only [h0, h1480, hlam]
                          · linarith only [h1480, h6, hlam]
                        · linarith only [h1479, h3, hlam]
                      · have p1470_0 := h1470c.1
                        have p1470_1 := h1470c.2.1
                        have p1470_2 := h1470c.2.2.1
                        have p1470_3 := h1470c.2.2.2
                        linarith only [h0, hlam, p1470_0]
                      · have p1470_0 := h1470c.1
                        have p1470_1 := h1470c.2.1
                        have p1470_2 := h1470c.2.2.1
                        have p1470_3 := h1470c.2.2.2
                        linarith only [hlam, p1470_0]
                      · have p1470_0 := h1470c.1
                        have p1470_1 := h1470c.2.1
                        have p1470_2 := h1470c.2.2.1
                        have p1470_3 := h1470c.2.2.2
                        linarith only [h1101, h1459, h1464, h1466, h4, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1470_1]
                      · have p1470_0 := h1470c.1
                        have p1470_1 := h1470c.2.1
                        have p1470_2 := h1470c.2.2.1
                        have p1470_3 := h1470c.2.2.2
                        rcases p1470_3 (m.d 0 1) (by simp) with h1487 | h1487
                        · rcases p1470_3 (m.d 0 2) (by simp) with h1488 | h1488
                          · rcases p1470_3 (m.d 0 3) (by simp) with h1489 | h1489
                            · linarith only [h1489, h4, hlam]
                            · linarith only [h1489, h7, hlam]
                          · linarith only [h1488, h5, hlam]
                        · linarith only [h1487, h2, hlam]
                      · have p1470_0 := h1470c.1
                        have p1470_1 := h1470c.2.1
                        have p1470_2 := h1470c.2.2.1
                        have p1470_3 := h1470c.2.2.2
                        rcases p1470_3 (m.d 0 1) (by simp) with h1494 | h1494
                        · rcases p1470_3 (m.d 0 2) (by simp) with h1495 | h1495
                          · rcases p1470_3 (m.d 0 3) (by simp) with h1496 | h1496
                            · linarith only [h1496, h4, hlam]
                            · linarith only [h1496, h8, hlam]
                          · linarith only [h1495, h6, hlam]
                        · linarith only [h1494, h3, hlam]
                      · have p1470_0 := h1470c.1
                        have p1470_1 := h1470c.2.1
                        have p1470_2 := h1470c.2.2.1
                        have p1470_3 := h1470c.2.2.2
                        linarith only [h1, hlam, p1470_1]
                      · have p1470_0 := h1470c.1
                        have p1470_1 := h1470c.2.1
                        have p1470_2 := h1470c.2.2.1
                        have p1470_3 := h1470c.2.2.2
                        linarith only [h4, hlam, p1470_1]
                      · have p1470_0 := h1470c.1
                        have p1470_1 := h1470c.2.1
                        have p1470_2 := h1470c.2.2.1
                        have p1470_3 := h1470c.2.2.2
                        linarith only [hlam, p1470_0]
                      · have p1470_0 := h1470c.1
                        have p1470_1 := h1470c.2.1
                        have p1470_2 := h1470c.2.2.1
                        have p1470_3 := h1470c.2.2.2
                        rcases p1470_3 (m.d 0 1) (by simp) with h1504 | h1504
                        · rcases p1470_3 (m.d 0 2) (by simp) with h1505 | h1505
                          · rcases p1470_3 (m.d 0 3) (by simp) with h1506 | h1506
                            · rcases p1470_3 (m.d 0 4) (by simp) with h1507 | h1507
                              · linarith only [h1507, h7, hlam]
                              · rcases p1470_3 (m.d 0 5) (by simp) with h1509 | h1509
                                · linarith only [h1509, h8, hlam]
                                · linarith only [h1509, h9, hlam]
                            · linarith only [h1506, h7, hlam]
                          · linarith only [h1505, h5, hlam]
                        · linarith only [h1504, h2, hlam]
                      · have p1470_0 := h1470c.1
                        have p1470_1 := h1470c.2.1
                        have p1470_2 := h1470c.2.2.1
                        have p1470_3 := h1470c.2.2.2
                        rcases p1470_3 (m.d 0 1) (by simp) with h1515 | h1515
                        · rcases p1470_3 (m.d 0 2) (by simp) with h1516 | h1516
                          · rcases p1470_3 (m.d 0 3) (by simp) with h1517 | h1517
                            · rcases p1470_3 (m.d 0 4) (by simp) with h1518 | h1518
                              · linarith only [h1518, h7, hlam]
                              · rcases p1470_3 (m.d 0 5) (by simp) with h1520 | h1520
                                · linarith only [h1520, h8, hlam]
                                · rcases h1bigk with h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c
                                  · have p1522_0 := h1522c.1
                                    have p1522_1 := h1522c.2.1
                                    have p1522_2 := h1522c.2.2.1
                                    have p1522_3 := h1522c.2.2.2
                                    linarith only [hlam, p1522_0]
                                  · have p1522_0 := h1522c.1
                                    have p1522_1 := h1522c.2.1
                                    have p1522_2 := h1522c.2.2.1
                                    have p1522_3 := h1522c.2.2.2
                                    rcases p1522_3 (m.d 0 1) (by simp) with h1524 | h1524
                                    · rcases p1522_3 (m.d 1 2) (by simp) with h1525 | h1525
                                      · linarith only [h1525, hlam, p1522_0]
                                      · rcases p1522_3 (m.d 1 3) (by simp) with h1527 | h1527
                                        · linarith only [h1, h1527, hlam]
                                        · linarith only [h1101, h1527, hlam]
                                    · linarith only [h1524, hlam, p1522_0]
                                  · have p1522_0 := h1522c.1
                                    have p1522_1 := h1522c.2.1
                                    have p1522_2 := h1522c.2.2.1
                                    have p1522_3 := h1522c.2.2.2
                                    rcases p1522_3 (m.d 0 1) (by simp) with h1531 | h1531
                                    · rcases p1522_3 (m.d 1 2) (by simp) with h1532 | h1532
                                      · linarith only [h0, h1532, hlam]
                                      · rcases p1522_3 (m.d 1 3) (by simp) with h1534 | h1534
                                        · linarith only [h1534, hlam, p1522_0]
                                        · rcases p1522_3 (m.d 1 4) (by simp) with h1536 | h1536
                                          · linarith only [h1536, h2, hlam]
                                          · rcases p1522_3 (m.d 1 5) (by simp) with h1538 | h1538
                                            · linarith only [h1538, h3, hlam]
                                            · rcases h3bigk with h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c
                                              · have p1540_0 := h1540c.1
                                                have p1540_1 := h1540c.2.1
                                                have p1540_2 := h1540c.2.2.1
                                                have p1540_3 := h1540c.2.2.2
                                                linarith only [hlam, p1540_0]
                                              · have p1540_0 := h1540c.1
                                                have p1540_1 := h1540c.2.1
                                                have p1540_2 := h1540c.2.2.1
                                                have p1540_3 := h1540c.2.2.2
                                                rcases p1540_3 (m.d 0 3) (by simp) with h1542 | h1542
                                                · rcases p1540_3 (m.d 1 3) (by simp) with h1543 | h1543
                                                  · linarith only [h1, h1543, hlam]
                                                  · rcases p1540_3 (m.d 2 3) (by simp) with h1545 | h1545
                                                    · linarith only [h1545, h4, hlam]
                                                    · linarith only [h1101, h1545, hlam]
                                                · linarith only [h1, h1542, hlam]
                                              · have p1540_0 := h1540c.1
                                                have p1540_1 := h1540c.2.1
                                                have p1540_2 := h1540c.2.2.1
                                                have p1540_3 := h1540c.2.2.2
                                                linarith only [h0, h1101, h1459, h1464, h1466, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1540_1]
                                              · have p1540_0 := h1540c.1
                                                have p1540_1 := h1540c.2.1
                                                have p1540_2 := h1540c.2.2.1
                                                have p1540_3 := h1540c.2.2.2
                                                linarith only [h1458, h1464, h2, h9, hlam, p1470_1, p1540_2]
                                              · have p1540_0 := h1540c.1
                                                have p1540_1 := h1540c.2.1
                                                have p1540_2 := h1540c.2.2.1
                                                have p1540_3 := h1540c.2.2.2
                                                linarith only [h8, hlam, p1470_1, p1540_2]
                                              · have p1540_0 := h1540c.1
                                                have p1540_1 := h1540c.2.1
                                                have p1540_2 := h1540c.2.2.1
                                                have p1540_3 := h1540c.2.2.2
                                                linarith only [h1, hlam, p1540_0]
                                              · have p1540_0 := h1540c.1
                                                have p1540_1 := h1540c.2.1
                                                have p1540_2 := h1540c.2.2.1
                                                have p1540_3 := h1540c.2.2.2
                                                linarith only [hlam, p1540_0]
                                              · have p1540_0 := h1540c.1
                                                have p1540_1 := h1540c.2.1
                                                have p1540_2 := h1540c.2.2.1
                                                have p1540_3 := h1540c.2.2.2
                                                linarith only [h1101, hlam, p1540_1]
                                              · have p1540_0 := h1540c.1
                                                have p1540_1 := h1540c.2.1
                                                have p1540_2 := h1540c.2.2.1
                                                have p1540_3 := h1540c.2.2.2
                                                linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1522_1, p1540_1]
                                              · have p1540_0 := h1540c.1
                                                have p1540_1 := h1540c.2.1
                                                have p1540_2 := h1540c.2.2.1
                                                have p1540_3 := h1540c.2.2.2
                                                linarith only [hc01, hc35, hlam, hphi, ht0b, ht5b, p1522_1, p1540_1]
                                              · have p1540_0 := h1540c.1
                                                have p1540_1 := h1540c.2.1
                                                have p1540_2 := h1540c.2.2.1
                                                have p1540_3 := h1540c.2.2.2
                                                linarith only [h4, hlam, p1540_0]
                                              · have p1540_0 := h1540c.1
                                                have p1540_1 := h1540c.2.1
                                                have p1540_2 := h1540c.2.2.1
                                                have p1540_3 := h1540c.2.2.2
                                                linarith only [h0, h4, hlam, p1522_2, p1540_1]
                                              · have p1540_0 := h1540c.1
                                                have p1540_1 := h1540c.2.1
                                                have p1540_2 := h1540c.2.2.1
                                                have p1540_3 := h1540c.2.2.2
                                                linarith only [hlam, p1540_0]
                                              · have p1540_0 := h1540c.1
                                                have p1540_1 := h1540c.2.1
                                                have p1540_2 := h1540c.2.2.1
                                                have p1540_3 := h1540c.2.2.2
                                                rcases p1540_3 (m.d 0 3) (by simp) with h1560 | h1560
                                                · rcases p1540_3 (m.d 1 3) (by simp) with h1561 | h1561
                                                  · linarith only [h1101, h1561, hlam]
                                                  · linarith only [h1460, h1561, hlam]
                                                · linarith only [h1560, h7, hlam]
                                              · have p1540_0 := h1540c.1
                                                have p1540_1 := h1540c.2.1
                                                have p1540_2 := h1540c.2.2.1
                                                have p1540_3 := h1540c.2.2.2
                                                rcases p1540_3 (m.d 0 3) (by simp) with h1565 | h1565
                                                · rcases p1540_3 (m.d 1 3) (by simp) with h1566 | h1566
                                                  · linarith only [h1101, h1566, hlam]
                                                  · linarith only [h1461, h1566, hlam]
                                                · linarith only [h1565, h8, hlam]
                                              · have p1540_0 := h1540c.1
                                                have p1540_1 := h1540c.2.1
                                                have p1540_2 := h1540c.2.2.1
                                                have p1540_3 := h1540c.2.2.2
                                                linarith only [h7, hlam, p1540_0]
                                              · have p1540_0 := h1540c.1
                                                have p1540_1 := h1540c.2.1
                                                have p1540_2 := h1540c.2.2.1
                                                have p1540_3 := h1540c.2.2.2
                                                linarith only [h1460, hlam, p1540_0]
                                              · have p1540_0 := h1540c.1
                                                have p1540_1 := h1540c.2.1
                                                have p1540_2 := h1540c.2.2.1
                                                have p1540_3 := h1540c.2.2.2
                                                linarith only [h1464, hlam, p1540_0]
                                              · have p1540_0 := h1540c.1
                                                have p1540_1 := h1540c.2.1
                                                have p1540_2 := h1540c.2.2.1
                                                have p1540_3 := h1540c.2.2.2
                                                linarith only [hlam, p1540_0]
                                              · have p1540_0 := h1540c.1
                                                have p1540_1 := h1540c.2.1
                                                have p1540_2 := h1540c.2.2.1
                                                have p1540_3 := h1540c.2.2.2
                                                linarith only [h1468, hlam, p1540_1]
                                              · have p1540_0 := h1540c.1
                                                have p1540_1 := h1540c.2.1
                                                have p1540_2 := h1540c.2.2.1
                                                have p1540_3 := h1540c.2.2.2
                                                linarith only [h8, hlam, p1540_0]
                                              · have p1540_0 := h1540c.1
                                                have p1540_1 := h1540c.2.1
                                                have p1540_2 := h1540c.2.2.1
                                                have p1540_3 := h1540c.2.2.2
                                                linarith only [h1461, hlam, p1540_0]
                                              · have p1540_0 := h1540c.1
                                                have p1540_1 := h1540c.2.1
                                                have p1540_2 := h1540c.2.2.1
                                                have p1540_3 := h1540c.2.2.2
                                                linarith only [h1465, hlam, p1540_0]
                                              · have p1540_0 := h1540c.1
                                                have p1540_1 := h1540c.2.1
                                                have p1540_2 := h1540c.2.2.1
                                                have p1540_3 := h1540c.2.2.2
                                                linarith only [h8, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1470_1, p1540_1]
                                              · have p1540_0 := h1540c.1
                                                have p1540_1 := h1540c.2.1
                                                have p1540_2 := h1540c.2.2.1
                                                have p1540_3 := h1540c.2.2.2
                                                linarith only [hlam, p1540_0]
                                    · linarith only [h1531, hlam, p1522_0]
                                  · have p1522_0 := h1522c.1
                                    have p1522_1 := h1522c.2.1
                                    have p1522_2 := h1522c.2.2.1
                                    have p1522_3 := h1522c.2.2.2
                                    linarith only [h0, h2, h4, h9, hlam, p1470_1, p1522_2]
                                  · have p1522_0 := h1522c.1
                                    have p1522_1 := h1522c.2.1
                                    have p1522_2 := h1522c.2.2.1
                                    have p1522_3 := h1522c.2.2.2
                                    linarith only [h0, h3, h4, hlam, p1470_1, p1522_2]
                                  · have p1522_0 := h1522c.1
                                    have p1522_1 := h1522c.2.1
                                    have p1522_2 := h1522c.2.2.1
                                    have p1522_3 := h1522c.2.2.2
                                    linarith only [h0, hlam, p1522_0]
                                  · have p1522_0 := h1522c.1
                                    have p1522_1 := h1522c.2.1
                                    have p1522_2 := h1522c.2.2.1
                                    have p1522_3 := h1522c.2.2.2
                                    linarith only [hlam, p1522_0]
                                  · have p1522_0 := h1522c.1
                                    have p1522_1 := h1522c.2.1
                                    have p1522_2 := h1522c.2.2.1
                                    have p1522_3 := h1522c.2.2.2
                                    linarith only [h1101, hlam, p1522_0]
                                  · have p1522_0 := h1522c.1
                                    have p1522_1 := h1522c.2.1
                                    have p1522_2 := h1522c.2.2.1
                                    have p1522_3 := h1522c.2.2.2
                                    linarith only [h0, h1101, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1522_1]
                                  · have p1522_0 := h1522c.1
                                    have p1522_1 := h1522c.2.1
                                    have p1522_2 := h1522c.2.2.1
                                    have p1522_3 := h1522c.2.2.2
                                    linarith only [h0, h1101, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p1522_1]
                                  · have p1522_0 := h1522c.1
                                    have p1522_1 := h1522c.2.1
                                    have p1522_2 := h1522c.2.2.1
                                    have p1522_3 := h1522c.2.2.2
                                    linarith only [h1, hlam, p1522_0]
                                  · have p1522_0 := h1522c.1
                                    have p1522_1 := h1522c.2.1
                                    have p1522_2 := h1522c.2.2.1
                                    have p1522_3 := h1522c.2.2.2
                                    linarith only [h0, h1101, h1458, h1464, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1522_1]
                                  · have p1522_0 := h1522c.1
                                    have p1522_1 := h1522c.2.1
                                    have p1522_2 := h1522c.2.2.1
                                    have p1522_3 := h1522c.2.2.2
                                    linarith only [hlam, p1522_0]
                                  · have p1522_0 := h1522c.1
                                    have p1522_1 := h1522c.2.1
                                    have p1522_2 := h1522c.2.2.1
                                    have p1522_3 := h1522c.2.2.2
                                    rcases p1522_3 (m.d 0 1) (by simp) with h1591 | h1591
                                    · rcases p1522_3 (m.d 1 2) (by simp) with h1592 | h1592
                                      · linarith only [h1101, h1592, hlam]
                                      · linarith only [h1458, h1592, hlam]
                                    · linarith only [h1591, h2, hlam]
                                  · have p1522_0 := h1522c.1
                                    have p1522_1 := h1522c.2.1
                                    have p1522_2 := h1522c.2.2.1
                                    have p1522_3 := h1522c.2.2.2
                                    rcases p1522_3 (m.d 0 1) (by simp) with h1596 | h1596
                                    · rcases p1522_3 (m.d 1 2) (by simp) with h1597 | h1597
                                      · linarith only [h1101, h1597, hlam]
                                      · linarith only [h1459, h1597, hlam]
                                    · linarith only [h1596, h3, hlam]
                                  · have p1522_0 := h1522c.1
                                    have p1522_1 := h1522c.2.1
                                    have p1522_2 := h1522c.2.2.1
                                    have p1522_3 := h1522c.2.2.2
                                    linarith only [h2, hlam, p1522_0]
                                  · have p1522_0 := h1522c.1
                                    have p1522_1 := h1522c.2.1
                                    have p1522_2 := h1522c.2.2.1
                                    have p1522_3 := h1522c.2.2.2
                                    linarith only [h1458, hlam, p1522_1]
                                  · have p1522_0 := h1522c.1
                                    have p1522_1 := h1522c.2.1
                                    have p1522_2 := h1522c.2.2.1
                                    have p1522_3 := h1522c.2.2.2
                                    linarith only [h1460, hlam, p1522_0]
                                  · have p1522_0 := h1522c.1
                                    have p1522_1 := h1522c.2.1
                                    have p1522_2 := h1522c.2.2.1
                                    have p1522_3 := h1522c.2.2.2
                                    linarith only [hlam, p1522_0]
                                  · have p1522_0 := h1522c.1
                                    have p1522_1 := h1522c.2.1
                                    have p1522_2 := h1522c.2.2.1
                                    have p1522_3 := h1522c.2.2.2
                                    linarith only [h1462, hlam, p1522_1]
                                  · have p1522_0 := h1522c.1
                                    have p1522_1 := h1522c.2.1
                                    have p1522_2 := h1522c.2.2.1
                                    have p1522_3 := h1522c.2.2.2
                                    linarith only [h3, hlam, p1522_0]
                                  · have p1522_0 := h1522c.1
                                    have p1522_1 := h1522c.2.1
                                    have p1522_2 := h1522c.2.2.1
                                    have p1522_3 := h1522c.2.2.2
                                    linarith only [h1459, hlam, p1522_1]
                                  · have p1522_0 := h1522c.1
                                    have p1522_1 := h1522c.2.1
                                    have p1522_2 := h1522c.2.2.1
                                    have p1522_3 := h1522c.2.2.2
                                    linarith only [h1461, hlam, p1522_0]
                                  · have p1522_0 := h1522c.1
                                    have p1522_1 := h1522c.2.1
                                    have p1522_2 := h1522c.2.2.1
                                    have p1522_3 := h1522c.2.2.2
                                    linarith only [h0, h1458, h1464, h3, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1470_1, p1522_1]
                                  · have p1522_0 := h1522c.1
                                    have p1522_1 := h1522c.2.1
                                    have p1522_2 := h1522c.2.2.1
                                    have p1522_3 := h1522c.2.2.2
                                    linarith only [hlam, p1522_0]
                            · linarith only [h1517, h8, hlam]
                          · linarith only [h1516, h6, hlam]
                        · linarith only [h1515, h3, hlam]
                      · have p1470_0 := h1470c.1
                        have p1470_1 := h1470c.2.1
                        have p1470_2 := h1470c.2.2.1
                        have p1470_3 := h1470c.2.2.2
                        linarith only [h2, hlam, p1470_0]
                      · have p1470_0 := h1470c.1
                        have p1470_1 := h1470c.2.1
                        have p1470_2 := h1470c.2.2.1
                        have p1470_3 := h1470c.2.2.2
                        linarith only [h5, hlam, p1470_0]
                      · have p1470_0 := h1470c.1
                        have p1470_1 := h1470c.2.1
                        have p1470_2 := h1470c.2.2.1
                        have p1470_3 := h1470c.2.2.2
                        linarith only [h7, hlam, p1470_0]
                      · have p1470_0 := h1470c.1
                        have p1470_1 := h1470c.2.1
                        have p1470_2 := h1470c.2.2.1
                        have p1470_3 := h1470c.2.2.2
                        linarith only [hlam, p1470_0]
                      · have p1470_0 := h1470c.1
                        have p1470_1 := h1470c.2.1
                        have p1470_2 := h1470c.2.2.1
                        have p1470_3 := h1470c.2.2.2
                        linarith only [h9, hlam, p1470_0]
                      · have p1470_0 := h1470c.1
                        have p1470_1 := h1470c.2.1
                        have p1470_2 := h1470c.2.2.1
                        have p1470_3 := h1470c.2.2.2
                        linarith only [h3, hlam, p1470_0]
                      · have p1470_0 := h1470c.1
                        have p1470_1 := h1470c.2.1
                        have p1470_2 := h1470c.2.2.1
                        have p1470_3 := h1470c.2.2.2
                        linarith only [h6, hlam, p1470_1]
                      · have p1470_0 := h1470c.1
                        have p1470_1 := h1470c.2.1
                        have p1470_2 := h1470c.2.2.1
                        have p1470_3 := h1470c.2.2.2
                        linarith only [h8, hlam, p1470_0]
                      · have p1470_0 := h1470c.1
                        have p1470_1 := h1470c.2.1
                        have p1470_2 := h1470c.2.2.1
                        have p1470_3 := h1470c.2.2.2
                        linarith only [h1458, h1464, h2, h9, hc34, hc45, hlam, hphi, p1470_1]
                      · have p1470_0 := h1470c.1
                        have p1470_1 := h1470c.2.1
                        have p1470_2 := h1470c.2.2.1
                        have p1470_3 := h1470c.2.2.2
                        linarith only [hlam, p1470_0]
                · linarith only [h0, h1101, h1458, h1464, h1465, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h1101, h1458, h1464, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h1101, h1459, h1461, hlam]
        · linarith only [h1101, h1458, h1460, h7, h9, hc24, hc45, hlam, hphi]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1628 | h1628
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1629 | h1629
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1630 | h1630
            · linarith only [h1630, h2, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1632 | h1632
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1633 | h1633
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1634 | h1634
                  · linarith only [h1458, h1459, h1634, h6, h9, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1636 | h1636
                    · linarith only [h1458, h1459, h1632, h1636, h6, h9, hlam]
                    · rcases h0bigk with h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c | h1638c
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [hlam, p1638_0]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [h0, h1458, h1632, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1638_1]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [h1, h1458, h1459, h1629, h1632, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1638_1]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        rcases p1638_3 (m.d 0 1) (by simp) with h1642 | h1642
                        · rcases p1638_3 (m.d 0 2) (by simp) with h1643 | h1643
                          · linarith only [h0, h1643, hlam]
                          · linarith only [h1643, h5, hlam]
                        · linarith only [h1642, h2, hlam]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [h1458, h1459, h1632, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1638_1]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [h0, hlam, p1638_0]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [hlam, p1638_0]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [h1458, h1459, h1632, h1633, h4, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1638_1]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        rcases p1638_3 (m.d 0 1) (by simp) with h1651 | h1651
                        · rcases p1638_3 (m.d 0 2) (by simp) with h1652 | h1652
                          · rcases p1638_3 (m.d 0 3) (by simp) with h1653 | h1653
                            · linarith only [h1653, h4, hlam]
                            · linarith only [h1653, h7, hlam]
                          · linarith only [h1652, h5, hlam]
                        · linarith only [h1651, h2, hlam]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [h0, h1458, h1459, h1632, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1638_1]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [h1, hlam, p1638_1]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [h4, hlam, p1638_1]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [hlam, p1638_0]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        rcases p1638_3 (m.d 0 1) (by simp) with h1662 | h1662
                        · rcases p1638_3 (m.d 0 2) (by simp) with h1663 | h1663
                          · rcases p1638_3 (m.d 0 3) (by simp) with h1664 | h1664
                            · rcases p1638_3 (m.d 0 4) (by simp) with h1665 | h1665
                              · linarith only [h1665, h7, hlam]
                              · rcases p1638_3 (m.d 0 5) (by simp) with h1667 | h1667
                                · linarith only [h1667, h8, hlam]
                                · linarith only [h1667, h9, hlam]
                            · linarith only [h1664, h7, hlam]
                          · linarith only [h1663, h5, hlam]
                        · linarith only [h1662, h2, hlam]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [h0, h1458, h1459, h1632, h4, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1638_1]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [h2, hlam, p1638_0]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [h5, hlam, p1638_0]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [h7, hlam, p1638_0]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [hlam, p1638_0]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [h9, hlam, p1638_0]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [h3, hlam, p1638_0]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [h6, hlam, p1638_1]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [h8, hlam, p1638_0]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [h9, hc04, hc45, hlam, hphi, p1638_1]
                      · have p1638_0 := h1638c.1
                        have p1638_1 := h1638c.2.1
                        have p1638_2 := h1638c.2.2.1
                        have p1638_3 := h1638c.2.2.2
                        linarith only [hlam, p1638_0]
                · linarith only [h1101, h1458, h1629, h1632, h1633, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · linarith only [h0, h1101, h1458, h1632, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1686 | h1686
            · linarith only [h1686, h2, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1688 | h1688
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1689 | h1689
                · linarith only [h0, h1101, h1458, h1629, h1688, h1689, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h1101, h1458, h1688, h1689, h8, h9, hc34, hc45, hlam, hphi]
              · linarith only [h0, h1101, h1458, h1688, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h1101, h1458, h1628, h7, h9, hc24, hc45, hlam, hphi]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1694 | h1694
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1695 | h1695
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1696 | h1696
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1697 | h1697
            · linarith only [h1458, h1694, h1697, h5, h9, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
            · linarith only [h1458, h1694, h1697, hlam]
          · linarith only [h1458, h1694, h1695, h1696, h5, h9, hc34, hc45, hlam, hphi]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1701 | h1701
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1702 | h1702
            · linarith only [h1101, h1694, h1695, h1702, h7, h9, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
            · linarith only [h1458, h1694, h1702, hlam]
          · linarith only [h1101, h1694, h1701, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1706 | h1706
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1707 | h1707
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1708 | h1708
            · linarith only [h1458, h1708, h2, h5, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1710 | h1710
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1711 | h1711
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1712 | h1712
                  · linarith only [h1712, h5, h9, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1714 | h1714
                    · linarith only [h1458, h1714, h5, h9, hc12, hc34, hlam, hphi, ht23]
                    · rcases h0bigk with h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c
                      · have p1716_0 := h1716c.1
                        have p1716_1 := h1716c.2.1
                        have p1716_2 := h1716c.2.2.1
                        have p1716_3 := h1716c.2.2.2
                        linarith only [hlam, p1716_0]
                      · have p1716_0 := h1716c.1
                        have p1716_1 := h1716c.2.1
                        have p1716_2 := h1716c.2.2.1
                        have p1716_3 := h1716c.2.2.2
                        linarith only [h1458, h1711, h1712, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1716_1]
                      · have p1716_0 := h1716c.1
                        have p1716_1 := h1716c.2.1
                        have p1716_2 := h1716c.2.2.1
                        have p1716_3 := h1716c.2.2.2
                        linarith only [h1, h1707, h1714, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1716_1]
                      · have p1716_0 := h1716c.1
                        have p1716_1 := h1716c.2.1
                        have p1716_2 := h1716c.2.2.1
                        have p1716_3 := h1716c.2.2.2
                        linarith only [h1458, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1716_1]
                      · have p1716_0 := h1716c.1
                        have p1716_1 := h1716c.2.1
                        have p1716_2 := h1716c.2.2.1
                        have p1716_3 := h1716c.2.2.2
                        linarith only [h1458, h1712, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1716_1]
                      · have p1716_0 := h1716c.1
                        have p1716_1 := h1716c.2.1
                        have p1716_2 := h1716c.2.2.1
                        have p1716_3 := h1716c.2.2.2
                        linarith only [h0, hlam, p1716_0]
                      · have p1716_0 := h1716c.1
                        have p1716_1 := h1716c.2.1
                        have p1716_2 := h1716c.2.2.1
                        have p1716_3 := h1716c.2.2.2
                        linarith only [hlam, p1716_0]
                      · have p1716_0 := h1716c.1
                        have p1716_1 := h1716c.2.1
                        have p1716_2 := h1716c.2.2.1
                        have p1716_3 := h1716c.2.2.2
                        linarith only [h1458, h1711, h1712, h4, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1716_1]
                      · have p1716_0 := h1716c.1
                        have p1716_1 := h1716c.2.1
                        have p1716_2 := h1716c.2.2.1
                        have p1716_3 := h1716c.2.2.2
                        linarith only [h0, h1458, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1716_1]
                      · have p1716_0 := h1716c.1
                        have p1716_1 := h1716c.2.1
                        have p1716_2 := h1716c.2.2.1
                        have p1716_3 := h1716c.2.2.2
                        linarith only [h0, h1458, h1712, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1716_1]
                      · have p1716_0 := h1716c.1
                        have p1716_1 := h1716c.2.1
                        have p1716_2 := h1716c.2.2.1
                        have p1716_3 := h1716c.2.2.2
                        linarith only [h1, hlam, p1716_1]
                      · have p1716_0 := h1716c.1
                        have p1716_1 := h1716c.2.1
                        have p1716_2 := h1716c.2.2.1
                        have p1716_3 := h1716c.2.2.2
                        linarith only [h4, hlam, p1716_1]
                      · have p1716_0 := h1716c.1
                        have p1716_1 := h1716c.2.1
                        have p1716_2 := h1716c.2.2.1
                        have p1716_3 := h1716c.2.2.2
                        linarith only [hlam, p1716_0]
                      · have p1716_0 := h1716c.1
                        have p1716_1 := h1716c.2.1
                        have p1716_2 := h1716c.2.2.1
                        have p1716_3 := h1716c.2.2.2
                        linarith only [h1458, h5, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1716_1]
                      · have p1716_0 := h1716c.1
                        have p1716_1 := h1716c.2.1
                        have p1716_2 := h1716c.2.2.1
                        have p1716_3 := h1716c.2.2.2
                        linarith only [h0, h1458, h1712, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1716_1]
                      · have p1716_0 := h1716c.1
                        have p1716_1 := h1716c.2.1
                        have p1716_2 := h1716c.2.2.1
                        have p1716_3 := h1716c.2.2.2
                        linarith only [h2, hlam, p1716_0]
                      · have p1716_0 := h1716c.1
                        have p1716_1 := h1716c.2.1
                        have p1716_2 := h1716c.2.2.1
                        have p1716_3 := h1716c.2.2.2
                        linarith only [h5, hlam, p1716_0]
                      · have p1716_0 := h1716c.1
                        have p1716_1 := h1716c.2.1
                        have p1716_2 := h1716c.2.2.1
                        have p1716_3 := h1716c.2.2.2
                        linarith only [h7, hlam, p1716_0]
                      · have p1716_0 := h1716c.1
                        have p1716_1 := h1716c.2.1
                        have p1716_2 := h1716c.2.2.1
                        have p1716_3 := h1716c.2.2.2
                        linarith only [hlam, p1716_0]
                      · have p1716_0 := h1716c.1
                        have p1716_1 := h1716c.2.1
                        have p1716_2 := h1716c.2.2.1
                        have p1716_3 := h1716c.2.2.2
                        linarith only [h9, hlam, p1716_0]
                      · have p1716_0 := h1716c.1
                        have p1716_1 := h1716c.2.1
                        have p1716_2 := h1716c.2.2.1
                        have p1716_3 := h1716c.2.2.2
                        linarith only [h3, hlam, p1716_0]
                      · have p1716_0 := h1716c.1
                        have p1716_1 := h1716c.2.1
                        have p1716_2 := h1716c.2.2.1
                        have p1716_3 := h1716c.2.2.2
                        linarith only [h6, hlam, p1716_1]
                      · have p1716_0 := h1716c.1
                        have p1716_1 := h1716c.2.1
                        have p1716_2 := h1716c.2.2.1
                        have p1716_3 := h1716c.2.2.2
                        linarith only [h8, hlam, p1716_0]
                      · have p1716_0 := h1716c.1
                        have p1716_1 := h1716c.2.1
                        have p1716_2 := h1716c.2.2.1
                        have p1716_3 := h1716c.2.2.2
                        linarith only [h1458, h5, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1716_1]
                      · have p1716_0 := h1716c.1
                        have p1716_1 := h1716c.2.1
                        have p1716_2 := h1716c.2.2.1
                        have p1716_3 := h1716c.2.2.2
                        linarith only [hlam, p1716_0]
                · linarith only [h1, h1101, h1707, h1711, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h1101, h1710, h7, h9, hc12, hc45, hlam, hphi, ht23, ht34]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1744 | h1744
            · linarith only [h1744, h2, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1746 | h1746
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1747 | h1747
                · linarith only [h0, h1706, h1707, h1747, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1749 | h1749
                  · linarith only [h1749, h5, h9, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1751 | h1751
                    · linarith only [h1, h1706, h1751, h9, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases h0bigk with h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c | h1753c
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [hlam, p1753_0]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [h1747, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1753_1]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [h1747, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1753_1]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [h1458, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1753_1]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [h1706, h1707, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1753_1]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [h0, hlam, p1753_0]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [hlam, p1753_0]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [h1747, h8, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1753_1]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [h0, h1458, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1753_1]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [h0, h1706, h1707, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1753_1]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [h1, hlam, p1753_1]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [h4, hlam, p1753_1]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [hlam, p1753_0]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [h1458, h5, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1753_1]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [h0, h1706, h1707, h3, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1753_1]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [h2, hlam, p1753_0]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [h5, hlam, p1753_0]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [h7, hlam, p1753_0]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [hlam, p1753_0]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [h9, hlam, p1753_0]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [h3, hlam, p1753_0]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [h6, hlam, p1753_1]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [h8, hlam, p1753_0]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [h1458, h5, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1753_1]
                      · have p1753_0 := h1753c.1
                        have p1753_1 := h1753c.2.1
                        have p1753_2 := h1753c.2.2.1
                        have p1753_3 := h1753c.2.2.2
                        linarith only [hlam, p1753_0]
              · linarith only [h1101, h1706, h1707, h1746, hc12, hc35, hlam, hphi, ht23]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1780 | h1780
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1781 | h1781
            · linarith only [h1706, h1780, h1781, h7, h9, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
            · linarith only [h1706, h1780, h1781, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1784 | h1784
            · linarith only [h1706, h1784, h2, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1786 | h1786
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1787 | h1787
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1788 | h1788
                  · linarith only [h1788, h5, h9, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1790 | h1790
                    · linarith only [h1786, h1790, h5, h9, hlam]
                    · rcases h0bigk with h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c | h1792c
                      · have p1792_0 := h1792c.1
                        have p1792_1 := h1792c.2.1
                        have p1792_2 := h1792c.2.2.1
                        have p1792_3 := h1792c.2.2.2
                        linarith only [hlam, p1792_0]
                      · have p1792_0 := h1792c.1
                        have p1792_1 := h1792c.2.1
                        have p1792_2 := h1792c.2.2.1
                        have p1792_3 := h1792c.2.2.2
                        linarith only [h1780, h1784, h1787, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1792_1]
                      · have p1792_0 := h1792c.1
                        have p1792_1 := h1792c.2.1
                        have p1792_2 := h1792c.2.2.1
                        have p1792_3 := h1792c.2.2.2
                        linarith only [h1780, h1784, h1787, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1792_1]
                      · have p1792_0 := h1792c.1
                        have p1792_1 := h1792c.2.1
                        have p1792_2 := h1792c.2.2.1
                        have p1792_3 := h1792c.2.2.2
                        linarith only [h1101, h1706, h1786, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1792_1]
                      · have p1792_0 := h1792c.1
                        have p1792_1 := h1792c.2.1
                        have p1792_2 := h1792c.2.2.1
                        have p1792_3 := h1792c.2.2.2
                        linarith only [h1101, h1706, h1786, h5, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1792_1]
                      · have p1792_0 := h1792c.1
                        have p1792_1 := h1792c.2.1
                        have p1792_2 := h1792c.2.2.1
                        have p1792_3 := h1792c.2.2.2
                        linarith only [h0, hlam, p1792_0]
                      · have p1792_0 := h1792c.1
                        have p1792_1 := h1792c.2.1
                        have p1792_2 := h1792c.2.2.1
                        have p1792_3 := h1792c.2.2.2
                        linarith only [hlam, p1792_0]
                      · have p1792_0 := h1792c.1
                        have p1792_1 := h1792c.2.1
                        have p1792_2 := h1792c.2.2.1
                        have p1792_3 := h1792c.2.2.2
                        linarith only [h1101, h1706, h7, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1792_1]
                      · have p1792_0 := h1792c.1
                        have p1792_1 := h1792c.2.1
                        have p1792_2 := h1792c.2.2.1
                        have p1792_3 := h1792c.2.2.2
                        linarith only [h0, h1101, h1706, h1786, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1792_1]
                      · have p1792_0 := h1792c.1
                        have p1792_1 := h1792c.2.1
                        have p1792_2 := h1792c.2.2.1
                        have p1792_3 := h1792c.2.2.2
                        linarith only [h0, h1101, h1706, h1786, h5, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1792_1]
                      · have p1792_0 := h1792c.1
                        have p1792_1 := h1792c.2.1
                        have p1792_2 := h1792c.2.2.1
                        have p1792_3 := h1792c.2.2.2
                        linarith only [h1, hlam, p1792_1]
                      · have p1792_0 := h1792c.1
                        have p1792_1 := h1792c.2.1
                        have p1792_2 := h1792c.2.2.1
                        have p1792_3 := h1792c.2.2.2
                        linarith only [h4, hlam, p1792_1]
                      · have p1792_0 := h1792c.1
                        have p1792_1 := h1792c.2.1
                        have p1792_2 := h1792c.2.2.1
                        have p1792_3 := h1792c.2.2.2
                        linarith only [hlam, p1792_0]
                      · have p1792_0 := h1792c.1
                        have p1792_1 := h1792c.2.1
                        have p1792_2 := h1792c.2.2.1
                        have p1792_3 := h1792c.2.2.2
                        linarith only [h1101, h1706, h1786, h5, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1792_1]
                      · have p1792_0 := h1792c.1
                        have p1792_1 := h1792c.2.1
                        have p1792_2 := h1792c.2.2.1
                        have p1792_3 := h1792c.2.2.2
                        linarith only [h0, h1101, h1706, h1786, h4, h5, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1792_1]
                      · have p1792_0 := h1792c.1
                        have p1792_1 := h1792c.2.1
                        have p1792_2 := h1792c.2.2.1
                        have p1792_3 := h1792c.2.2.2
                        linarith only [h2, hlam, p1792_0]
                      · have p1792_0 := h1792c.1
                        have p1792_1 := h1792c.2.1
                        have p1792_2 := h1792c.2.2.1
                        have p1792_3 := h1792c.2.2.2
                        linarith only [h5, hlam, p1792_0]
                      · have p1792_0 := h1792c.1
                        have p1792_1 := h1792c.2.1
                        have p1792_2 := h1792c.2.2.1
                        have p1792_3 := h1792c.2.2.2
                        linarith only [h7, hlam, p1792_0]
                      · have p1792_0 := h1792c.1
                        have p1792_1 := h1792c.2.1
                        have p1792_2 := h1792c.2.2.1
                        have p1792_3 := h1792c.2.2.2
                        linarith only [hlam, p1792_0]
                      · have p1792_0 := h1792c.1
                        have p1792_1 := h1792c.2.1
                        have p1792_2 := h1792c.2.2.1
                        have p1792_3 := h1792c.2.2.2
                        linarith only [h9, hlam, p1792_0]
                      · have p1792_0 := h1792c.1
                        have p1792_1 := h1792c.2.1
                        have p1792_2 := h1792c.2.2.1
                        have p1792_3 := h1792c.2.2.2
                        linarith only [h3, hlam, p1792_0]
                      · have p1792_0 := h1792c.1
                        have p1792_1 := h1792c.2.1
                        have p1792_2 := h1792c.2.2.1
                        have p1792_3 := h1792c.2.2.2
                        linarith only [h6, hlam, p1792_1]
                      · have p1792_0 := h1792c.1
                        have p1792_1 := h1792c.2.1
                        have p1792_2 := h1792c.2.2.1
                        have p1792_3 := h1792c.2.2.2
                        linarith only [h8, hlam, p1792_0]
                      · have p1792_0 := h1792c.1
                        have p1792_1 := h1792c.2.1
                        have p1792_2 := h1792c.2.2.1
                        have p1792_3 := h1792c.2.2.2
                        linarith only [h1101, h1706, h1786, h5, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1792_1]
                      · have p1792_0 := h1792c.1
                        have p1792_1 := h1792c.2.1
                        have p1792_2 := h1792c.2.2.1
                        have p1792_3 := h1792c.2.2.2
                        linarith only [hlam, p1792_0]
                · linarith only [h1101, h1706, h1786, h1787, hc12, hc35, hlam, hphi, ht23]
              · linarith only [h1101, h1786, h7, h9, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 6236000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s6_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s6_x0_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8 h9
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s6_x0_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8 h9

end R2N4
