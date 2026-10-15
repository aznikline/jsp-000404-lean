import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5714000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s0_x0_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h672 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h951 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1096 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 4 5 (by decide) (by decide) with h1097 | h1097
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1098 | h1098
    · linarith only [h0, h1098, h2, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1100 | h1100
      · linarith only [h0, h1100, h672, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1102 | h1102
        · linarith only [h0, h1102, h951, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1104 | h1104
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1105 | h1105
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1106 | h1106
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1107 | h1107
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1108 | h1108
                  · rcases h2bigk with h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c
                    · have p1109_0 := h1109c.1
                      have p1109_1 := h1109c.2.1
                      have p1109_2 := h1109c.2.2.1
                      have p1109_3 := h1109c.2.2.2
                      linarith only [hlam, p1109_0]
                    · have p1109_0 := h1109c.1
                      have p1109_1 := h1109c.2.1
                      have p1109_2 := h1109c.2.2.1
                      have p1109_3 := h1109c.2.2.2
                      linarith only [h1107, h951, hc12, hc24, hlam, hphi, p1109_1]
                    · have p1109_0 := h1109c.1
                      have p1109_1 := h1109c.2.1
                      have p1109_2 := h1109c.2.2.1
                      have p1109_3 := h1109c.2.2.2
                      linarith only [h2, hlam, p1109_0]
                    · have p1109_0 := h1109c.1
                      have p1109_1 := h1109c.2.1
                      have p1109_2 := h1109c.2.2.1
                      have p1109_3 := h1109c.2.2.2
                      linarith only [h672, hlam, p1109_0]
                    · have p1109_0 := h1109c.1
                      have p1109_1 := h1109c.2.1
                      have p1109_2 := h1109c.2.2.1
                      have p1109_3 := h1109c.2.2.2
                      linarith only [h951, hlam, p1109_0]
                    · have p1109_0 := h1109c.1
                      have p1109_1 := h1109c.2.1
                      have p1109_2 := h1109c.2.2.1
                      have p1109_3 := h1109c.2.2.2
                      linarith only [h0, hlam, p1109_0]
                    · have p1109_0 := h1109c.1
                      have p1109_1 := h1109c.2.1
                      have p1109_2 := h1109c.2.2.1
                      have p1109_3 := h1109c.2.2.2
                      linarith only [hlam, p1109_0]
                    · have p1109_0 := h1109c.1
                      have p1109_1 := h1109c.2.1
                      have p1109_2 := h1109c.2.2.1
                      have p1109_3 := h1109c.2.2.2
                      linarith only [h1098, hlam, p1109_0]
                    · have p1109_0 := h1109c.1
                      have p1109_1 := h1109c.2.1
                      have p1109_2 := h1109c.2.2.1
                      have p1109_3 := h1109c.2.2.2
                      linarith only [h1100, hlam, p1109_0]
                    · have p1109_0 := h1109c.1
                      have p1109_1 := h1109c.2.1
                      have p1109_2 := h1109c.2.2.1
                      have p1109_3 := h1109c.2.2.2
                      linarith only [h1102, hlam, p1109_0]
                    · have p1109_0 := h1109c.1
                      have p1109_1 := h1109c.2.1
                      have p1109_2 := h1109c.2.2.1
                      have p1109_3 := h1109c.2.2.2
                      rcases p1109_3 (m.d 0 2) (by simp) with h1120 | h1120
                      · linarith only [h1120, hlam, p1109_0]
                      · rcases p1109_3 (m.d 1 2) (by simp) with h1122 | h1122
                        · linarith only [h1098, h1122, hlam]
                        · rcases p1109_3 (m.d 2 3) (by simp) with h1124 | h1124
                          · rcases p1109_3 (m.d 2 4) (by simp) with h1125 | h1125
                            · linarith only [h1105, h1125, hlam]
                            · linarith only [h1125, h672, hlam]
                          · linarith only [h1124, hlam, p1109_0]
                    · have p1109_0 := h1109c.1
                      have p1109_1 := h1109c.2.1
                      have p1109_2 := h1109c.2.2.1
                      have p1109_3 := h1109c.2.2.2
                      rcases p1109_3 (m.d 0 2) (by simp) with h1129 | h1129
                      · linarith only [h1129, h2, hlam]
                      · linarith only [h0, h1129, hlam]
                    · have p1109_0 := h1109c.1
                      have p1109_1 := h1109c.2.1
                      have p1109_2 := h1109c.2.2.1
                      have p1109_3 := h1109c.2.2.2
                      linarith only [hlam, p1109_0]
                    · have p1109_0 := h1109c.1
                      have p1109_1 := h1109c.2.1
                      have p1109_2 := h1109c.2.2.1
                      have p1109_3 := h1109c.2.2.2
                      linarith only [h672, hc02, hc23, hlam, hphi, p1109_1]
                    · have p1109_0 := h1109c.1
                      have p1109_1 := h1109c.2.1
                      have p1109_2 := h1109c.2.2.1
                      have p1109_3 := h1109c.2.2.2
                      linarith only [h0, h951, hc12, hc23, hlam, hphi, p1109_1]
                    · have p1109_0 := h1109c.1
                      have p1109_1 := h1109c.2.1
                      have p1109_2 := h1109c.2.2.1
                      have p1109_3 := h1109c.2.2.2
                      rcases p1109_3 (m.d 0 2) (by simp) with h1135 | h1135
                      · linarith only [h1135, hlam, p1109_0]
                      · rcases p1109_3 (m.d 1 2) (by simp) with h1137 | h1137
                        · linarith only [h1100, h1137, hlam]
                        · rcases p1109_3 (m.d 2 3) (by simp) with h1139 | h1139
                          · rcases p1109_3 (m.d 2 4) (by simp) with h1140 | h1140
                            · rcases p1109_3 (m.d 2 5) (by simp) with h1141 | h1141
                              · linarith only [h1107, h1141, hlam]
                              · linarith only [h1141, h951, hlam]
                            · linarith only [h1140, hlam, p1109_0]
                          · linarith only [h1139, h2, hlam]
                    · have p1109_0 := h1109c.1
                      have p1109_1 := h1109c.2.1
                      have p1109_2 := h1109c.2.2.1
                      have p1109_3 := h1109c.2.2.2
                      rcases p1109_3 (m.d 0 2) (by simp) with h1146 | h1146
                      · linarith only [h1146, h672, hlam]
                      · linarith only [h0, h1146, hlam]
                    · have p1109_0 := h1109c.1
                      have p1109_1 := h1109c.2.1
                      have p1109_2 := h1109c.2.2.1
                      have p1109_3 := h1109c.2.2.2
                      linarith only [h1105, hlam, p1109_1]
                    · have p1109_0 := h1109c.1
                      have p1109_1 := h1109c.2.1
                      have p1109_2 := h1109c.2.2.1
                      have p1109_3 := h1109c.2.2.2
                      linarith only [hlam, p1109_0]
                    · have p1109_0 := h1109c.1
                      have p1109_1 := h1109c.2.1
                      have p1109_2 := h1109c.2.2.1
                      have p1109_3 := h1109c.2.2.2
                      linarith only [h0, h951, hc12, hc24, hlam, hphi, p1109_1]
                    · have p1109_0 := h1109c.1
                      have p1109_1 := h1109c.2.1
                      have p1109_2 := h1109c.2.2.1
                      have p1109_3 := h1109c.2.2.2
                      rcases p1109_3 (m.d 0 2) (by simp) with h1152 | h1152
                      · linarith only [h1152, hlam, p1109_0]
                      · rcases p1109_3 (m.d 1 2) (by simp) with h1154 | h1154
                        · linarith only [h1102, h1154, hlam]
                        · rcases p1109_3 (m.d 2 3) (by simp) with h1156 | h1156
                          · rcases p1109_3 (m.d 2 4) (by simp) with h1157 | h1157
                            · rcases p1109_3 (m.d 2 5) (by simp) with h1158 | h1158
                              · rcases h5bigk with h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c | h1159c
                                · have p1159_0 := h1159c.1
                                  have p1159_1 := h1159c.2.1
                                  have p1159_2 := h1159c.2.2.1
                                  have p1159_3 := h1159c.2.2.2
                                  linarith only [hlam, p1159_0]
                                · have p1159_0 := h1159c.1
                                  have p1159_1 := h1159c.2.1
                                  have p1159_2 := h1159c.2.2.1
                                  have p1159_3 := h1159c.2.2.2
                                  linarith only [hc15, hlam, hphi, ht0b, ht5b, p1159_1, u0elo4]
                                · have p1159_0 := h1159c.1
                                  have p1159_1 := h1159c.2.1
                                  have p1159_2 := h1159c.2.2.1
                                  have p1159_3 := h1159c.2.2.2
                                  linarith only [h951, hlam, p1159_0]
                                · have p1159_0 := h1159c.1
                                  have p1159_1 := h1159c.2.1
                                  have p1159_2 := h1159c.2.2.1
                                  have p1159_3 := h1159c.2.2.2
                                  linarith only [h1, h1108, hc45, hlam, hphi, ht0b, ht5b, p1159_1, u0elo0]
                                · have p1159_0 := h1159c.1
                                  have p1159_1 := h1159c.2.1
                                  have p1159_2 := h1159c.2.2.1
                                  have p1159_3 := h1159c.2.2.2
                                  linarith only [h1, hc45, hlam, hphi, ht0b, ht5b, p1159_1, u0elo0]
                                · have p1159_0 := h1159c.1
                                  have p1159_1 := h1159c.2.1
                                  have p1159_2 := h1159c.2.2.1
                                  have p1159_3 := h1159c.2.2.2
                                  linarith only [h1, hlam, p1159_0]
                                · have p1159_0 := h1159c.1
                                  have p1159_1 := h1159c.2.1
                                  have p1159_2 := h1159c.2.2.1
                                  have p1159_3 := h1159c.2.2.2
                                  linarith only [hlam, p1159_0]
                                · have p1159_0 := h1159c.1
                                  have p1159_1 := h1159c.2.1
                                  have p1159_2 := h1159c.2.2.1
                                  have p1159_3 := h1159c.2.2.2
                                  linarith only [h1102, hlam, p1159_0]
                                · have p1159_0 := h1159c.1
                                  have p1159_1 := h1159c.2.1
                                  have p1159_2 := h1159c.2.2.1
                                  have p1159_3 := h1159c.2.2.2
                                  linarith only [h1, h1108, hc45, hlam, hphi, ht0b, ht5b, p1159_1, u0elo0]
                                · have p1159_0 := h1159c.1
                                  have p1159_1 := h1159c.2.1
                                  have p1159_2 := h1159c.2.2.1
                                  have p1159_3 := h1159c.2.2.2
                                  linarith only [h1, hc45, hlam, hphi, ht0b, ht5b, p1159_1, u0elo0]
                                · have p1159_0 := h1159c.1
                                  have p1159_1 := h1159c.2.1
                                  have p1159_2 := h1159c.2.2.1
                                  have p1159_3 := h1159c.2.2.2
                                  linarith only [h0, h951, hc12, hc25, hlam, hphi, p1159_1]
                                · have p1159_0 := h1159c.1
                                  have p1159_1 := h1159c.2.1
                                  have p1159_2 := h1159c.2.2.1
                                  have p1159_3 := h1159c.2.2.2
                                  linarith only [h1102, hc12, hc25, hlam, hphi, p1159_1]
                                · have p1159_0 := h1159c.1
                                  have p1159_1 := h1159c.2.1
                                  have p1159_2 := h1159c.2.2.1
                                  have p1159_3 := h1159c.2.2.2
                                  linarith only [hlam, p1159_0]
                                · have p1159_0 := h1159c.1
                                  have p1159_1 := h1159c.2.1
                                  have p1159_2 := h1159c.2.2.1
                                  have p1159_3 := h1159c.2.2.2
                                  rcases p1159_3 (m.d 0 5) (by simp) with h1173 | h1173
                                  · linarith only [h1173, h951, hlam]
                                  · linarith only [h1096, h1173, hlam]
                                · have p1159_0 := h1159c.1
                                  have p1159_1 := h1159c.2.1
                                  have p1159_2 := h1159c.2.2.1
                                  have p1159_3 := h1159c.2.2.2
                                  rcases p1159_3 (m.d 0 5) (by simp) with h1176 | h1176
                                  · linarith only [h1176, h951, hlam]
                                  · linarith only [h1097, h1176, hlam]
                                · have p1159_0 := h1159c.1
                                  have p1159_1 := h1159c.2.1
                                  have p1159_2 := h1159c.2.2.1
                                  have p1159_3 := h1159c.2.2.2
                                  linarith only [h1096, hlam, p1159_0]
                                · have p1159_0 := h1159c.1
                                  have p1159_1 := h1159c.2.1
                                  have p1159_2 := h1159c.2.2.1
                                  have p1159_3 := h1159c.2.2.2
                                  linarith only [h1096, h1102, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1159_1, u0elo2]
                                · have p1159_0 := h1159c.1
                                  have p1159_1 := h1159c.2.1
                                  have p1159_2 := h1159c.2.2.1
                                  have p1159_3 := h1159c.2.2.2
                                  linarith only [h1106, hlam, p1159_0]
                                · have p1159_0 := h1159c.1
                                  have p1159_1 := h1159c.2.1
                                  have p1159_2 := h1159c.2.2.1
                                  have p1159_3 := h1159c.2.2.2
                                  linarith only [hlam, p1159_0]
                                · have p1159_0 := h1159c.1
                                  have p1159_1 := h1159c.2.1
                                  have p1159_2 := h1159c.2.2.1
                                  have p1159_3 := h1159c.2.2.2
                                  linarith only [h1096, hc45, hlam, hphi, ht0b, ht5b, p1159_1, u0elo2]
                                · have p1159_0 := h1159c.1
                                  have p1159_1 := h1159c.2.1
                                  have p1159_2 := h1159c.2.2.1
                                  have p1159_3 := h1159c.2.2.2
                                  linarith only [h1097, hlam, p1159_0]
                                · have p1159_0 := h1159c.1
                                  have p1159_1 := h1159c.2.1
                                  have p1159_2 := h1159c.2.2.1
                                  have p1159_3 := h1159c.2.2.2
                                  linarith only [h1104, hlam, p1159_0]
                                · have p1159_0 := h1159c.1
                                  have p1159_1 := h1159c.2.1
                                  have p1159_2 := h1159c.2.2.1
                                  have p1159_3 := h1159c.2.2.2
                                  linarith only [h1107, hlam, p1159_0]
                                · have p1159_0 := h1159c.1
                                  have p1159_1 := h1159c.2.1
                                  have p1159_2 := h1159c.2.2.1
                                  have p1159_3 := h1159c.2.2.2
                                  linarith only [h1108, hlam, p1159_0]
                                · have p1159_0 := h1159c.1
                                  have p1159_1 := h1159c.2.1
                                  have p1159_2 := h1159c.2.2.1
                                  have p1159_3 := h1159c.2.2.2
                                  linarith only [hlam, p1159_0]
                              · linarith only [h1158, hlam, p1109_0]
                            · linarith only [h1157, h672, hlam]
                          · linarith only [h1156, h2, hlam]
                    · have p1109_0 := h1109c.1
                      have p1109_1 := h1109c.2.1
                      have p1109_2 := h1109c.2.2.1
                      have p1109_3 := h1109c.2.2.2
                      rcases p1109_3 (m.d 0 2) (by simp) with h1192 | h1192
                      · linarith only [h1192, h951, hlam]
                      · linarith only [h0, h1192, hlam]
                    · have p1109_0 := h1109c.1
                      have p1109_1 := h1109c.2.1
                      have p1109_2 := h1109c.2.2.1
                      have p1109_3 := h1109c.2.2.2
                      linarith only [h1106, hlam, p1109_1]
                    · have p1109_0 := h1109c.1
                      have p1109_1 := h1109c.2.1
                      have p1109_2 := h1109c.2.2.1
                      have p1109_3 := h1109c.2.2.2
                      linarith only [h1107, hlam, p1109_0]
                    · have p1109_0 := h1109c.1
                      have p1109_1 := h1109c.2.1
                      have p1109_2 := h1109c.2.2.1
                      have p1109_3 := h1109c.2.2.2
                      linarith only [hlam, p1109_0]
                  · rcases h2bigk with h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c | h1198c
                    · have p1198_0 := h1198c.1
                      have p1198_1 := h1198c.2.1
                      have p1198_2 := h1198c.2.2.1
                      have p1198_3 := h1198c.2.2.2
                      linarith only [hlam, p1198_0]
                    · have p1198_0 := h1198c.1
                      have p1198_1 := h1198c.2.1
                      have p1198_2 := h1198c.2.2.1
                      have p1198_3 := h1198c.2.2.2
                      linarith only [h2, hc12, hc23, hlam, hphi, p1198_1]
                    · have p1198_0 := h1198c.1
                      have p1198_1 := h1198c.2.1
                      have p1198_2 := h1198c.2.2.1
                      have p1198_3 := h1198c.2.2.2
                      linarith only [h2, hlam, p1198_0]
                    · have p1198_0 := h1198c.1
                      have p1198_1 := h1198c.2.1
                      have p1198_2 := h1198c.2.2.1
                      have p1198_3 := h1198c.2.2.2
                      linarith only [h672, hlam, p1198_0]
                    · have p1198_0 := h1198c.1
                      have p1198_1 := h1198c.2.1
                      have p1198_2 := h1198c.2.2.1
                      have p1198_3 := h1198c.2.2.2
                      linarith only [h951, hlam, p1198_0]
                    · have p1198_0 := h1198c.1
                      have p1198_1 := h1198c.2.1
                      have p1198_2 := h1198c.2.2.1
                      have p1198_3 := h1198c.2.2.2
                      linarith only [h0, hlam, p1198_0]
                    · have p1198_0 := h1198c.1
                      have p1198_1 := h1198c.2.1
                      have p1198_2 := h1198c.2.2.1
                      have p1198_3 := h1198c.2.2.2
                      linarith only [hlam, p1198_0]
                    · have p1198_0 := h1198c.1
                      have p1198_1 := h1198c.2.1
                      have p1198_2 := h1198c.2.2.1
                      have p1198_3 := h1198c.2.2.2
                      linarith only [h1098, hlam, p1198_0]
                    · have p1198_0 := h1198c.1
                      have p1198_1 := h1198c.2.1
                      have p1198_2 := h1198c.2.2.1
                      have p1198_3 := h1198c.2.2.2
                      linarith only [h1100, hlam, p1198_0]
                    · have p1198_0 := h1198c.1
                      have p1198_1 := h1198c.2.1
                      have p1198_2 := h1198c.2.2.1
                      have p1198_3 := h1198c.2.2.2
                      linarith only [h1102, hlam, p1198_0]
                    · have p1198_0 := h1198c.1
                      have p1198_1 := h1198c.2.1
                      have p1198_2 := h1198c.2.2.1
                      have p1198_3 := h1198c.2.2.2
                      rcases p1198_3 (m.d 0 2) (by simp) with h1209 | h1209
                      · linarith only [h1209, hlam, p1198_0]
                      · rcases p1198_3 (m.d 1 2) (by simp) with h1211 | h1211
                        · linarith only [h1098, h1211, hlam]
                        · rcases p1198_3 (m.d 2 3) (by simp) with h1213 | h1213
                          · rcases p1198_3 (m.d 2 4) (by simp) with h1214 | h1214
                            · linarith only [h1105, h1214, hlam]
                            · linarith only [h1214, h672, hlam]
                          · linarith only [h1213, hlam, p1198_0]
                    · have p1198_0 := h1198c.1
                      have p1198_1 := h1198c.2.1
                      have p1198_2 := h1198c.2.2.1
                      have p1198_3 := h1198c.2.2.2
                      rcases p1198_3 (m.d 0 2) (by simp) with h1218 | h1218
                      · linarith only [h1218, h2, hlam]
                      · linarith only [h0, h1218, hlam]
                    · have p1198_0 := h1198c.1
                      have p1198_1 := h1198c.2.1
                      have p1198_2 := h1198c.2.2.1
                      have p1198_3 := h1198c.2.2.2
                      linarith only [hlam, p1198_0]
                    · have p1198_0 := h1198c.1
                      have p1198_1 := h1198c.2.1
                      have p1198_2 := h1198c.2.2.1
                      have p1198_3 := h1198c.2.2.2
                      linarith only [h672, hc02, hc23, hlam, hphi, p1198_1]
                    · have p1198_0 := h1198c.1
                      have p1198_1 := h1198c.2.1
                      have p1198_2 := h1198c.2.2.1
                      have p1198_3 := h1198c.2.2.2
                      linarith only [h0, h951, hc12, hc23, hlam, hphi, p1198_1]
                    · have p1198_0 := h1198c.1
                      have p1198_1 := h1198c.2.1
                      have p1198_2 := h1198c.2.2.1
                      have p1198_3 := h1198c.2.2.2
                      rcases p1198_3 (m.d 0 2) (by simp) with h1224 | h1224
                      · linarith only [h1224, hlam, p1198_0]
                      · rcases p1198_3 (m.d 1 2) (by simp) with h1226 | h1226
                        · linarith only [h1100, h1226, hlam]
                        · rcases p1198_3 (m.d 2 3) (by simp) with h1228 | h1228
                          · rcases p1198_3 (m.d 2 4) (by simp) with h1229 | h1229
                            · rcases p1198_3 (m.d 2 5) (by simp) with h1230 | h1230
                              · linarith only [h1107, h1230, hlam]
                              · linarith only [h1230, h951, hlam]
                            · linarith only [h1229, hlam, p1198_0]
                          · linarith only [h1228, h2, hlam]
                    · have p1198_0 := h1198c.1
                      have p1198_1 := h1198c.2.1
                      have p1198_2 := h1198c.2.2.1
                      have p1198_3 := h1198c.2.2.2
                      rcases p1198_3 (m.d 0 2) (by simp) with h1235 | h1235
                      · linarith only [h1235, h672, hlam]
                      · linarith only [h0, h1235, hlam]
                    · have p1198_0 := h1198c.1
                      have p1198_1 := h1198c.2.1
                      have p1198_2 := h1198c.2.2.1
                      have p1198_3 := h1198c.2.2.2
                      linarith only [h1105, hlam, p1198_1]
                    · have p1198_0 := h1198c.1
                      have p1198_1 := h1198c.2.1
                      have p1198_2 := h1198c.2.2.1
                      have p1198_3 := h1198c.2.2.2
                      linarith only [hlam, p1198_0]
                    · have p1198_0 := h1198c.1
                      have p1198_1 := h1198c.2.1
                      have p1198_2 := h1198c.2.2.1
                      have p1198_3 := h1198c.2.2.2
                      linarith only [h0, h951, hc12, hc24, hlam, hphi, p1198_1]
                    · have p1198_0 := h1198c.1
                      have p1198_1 := h1198c.2.1
                      have p1198_2 := h1198c.2.2.1
                      have p1198_3 := h1198c.2.2.2
                      rcases p1198_3 (m.d 0 2) (by simp) with h1241 | h1241
                      · linarith only [h1241, hlam, p1198_0]
                      · rcases p1198_3 (m.d 1 2) (by simp) with h1243 | h1243
                        · linarith only [h1102, h1243, hlam]
                        · rcases p1198_3 (m.d 2 3) (by simp) with h1245 | h1245
                          · rcases p1198_3 (m.d 2 4) (by simp) with h1246 | h1246
                            · rcases p1198_3 (m.d 2 5) (by simp) with h1247 | h1247
                              · rcases h5bigk with h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c | h1248c
                                · have p1248_0 := h1248c.1
                                  have p1248_1 := h1248c.2.1
                                  have p1248_2 := h1248c.2.2.1
                                  have p1248_3 := h1248c.2.2.2
                                  linarith only [hlam, p1248_0]
                                · have p1248_0 := h1248c.1
                                  have p1248_1 := h1248c.2.1
                                  have p1248_2 := h1248c.2.2.1
                                  have p1248_3 := h1248c.2.2.2
                                  linarith only [h1104, h1108, hc34, hlam, hphi, ht0b, ht45, ht5b, p1248_1, u0elo4]
                                · have p1248_0 := h1248c.1
                                  have p1248_1 := h1248c.2.1
                                  have p1248_2 := h1248c.2.2.1
                                  have p1248_3 := h1248c.2.2.2
                                  linarith only [h951, hlam, p1248_0]
                                · have p1248_0 := h1248c.1
                                  have p1248_1 := h1248c.2.1
                                  have p1248_2 := h1248c.2.2.1
                                  have p1248_3 := h1248c.2.2.2
                                  linarith only [hc35, hlam, hphi, ht0b, ht5b, p1248_1, u0elo4]
                                · have p1248_0 := h1248c.1
                                  have p1248_1 := h1248c.2.1
                                  have p1248_2 := h1248c.2.2.1
                                  have p1248_3 := h1248c.2.2.2
                                  linarith only [h1, h1108, hc34, hlam, hphi, ht0b, ht45, ht5b, p1248_1, u0elo0]
                                · have p1248_0 := h1248c.1
                                  have p1248_1 := h1248c.2.1
                                  have p1248_2 := h1248c.2.2.1
                                  have p1248_3 := h1248c.2.2.2
                                  linarith only [h1, hlam, p1248_0]
                                · have p1248_0 := h1248c.1
                                  have p1248_1 := h1248c.2.1
                                  have p1248_2 := h1248c.2.2.1
                                  have p1248_3 := h1248c.2.2.2
                                  linarith only [hlam, p1248_0]
                                · have p1248_0 := h1248c.1
                                  have p1248_1 := h1248c.2.1
                                  have p1248_2 := h1248c.2.2.1
                                  have p1248_3 := h1248c.2.2.2
                                  linarith only [h1102, hlam, p1248_0]
                                · have p1248_0 := h1248c.1
                                  have p1248_1 := h1248c.2.1
                                  have p1248_2 := h1248c.2.2.1
                                  have p1248_3 := h1248c.2.2.2
                                  linarith only [h1, h1108, hc34, hlam, hphi, ht0b, ht45, ht5b, p1248_1, u0elo0]
                                · have p1248_0 := h1248c.1
                                  have p1248_1 := h1248c.2.1
                                  have p1248_2 := h1248c.2.2.1
                                  have p1248_3 := h1248c.2.2.2
                                  linarith only [h1108, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1248_1]
                                · have p1248_0 := h1248c.1
                                  have p1248_1 := h1248c.2.1
                                  have p1248_2 := h1248c.2.2.1
                                  have p1248_3 := h1248c.2.2.2
                                  linarith only [h0, h951, hc12, hc25, hlam, hphi, p1248_1]
                                · have p1248_0 := h1248c.1
                                  have p1248_1 := h1248c.2.1
                                  have p1248_2 := h1248c.2.2.1
                                  have p1248_3 := h1248c.2.2.2
                                  linarith only [h1102, hc12, hc25, hlam, hphi, p1248_1]
                                · have p1248_0 := h1248c.1
                                  have p1248_1 := h1248c.2.1
                                  have p1248_2 := h1248c.2.2.1
                                  have p1248_3 := h1248c.2.2.2
                                  linarith only [hlam, p1248_0]
                                · have p1248_0 := h1248c.1
                                  have p1248_1 := h1248c.2.1
                                  have p1248_2 := h1248c.2.2.1
                                  have p1248_3 := h1248c.2.2.2
                                  rcases p1248_3 (m.d 0 5) (by simp) with h1262 | h1262
                                  · linarith only [h1262, h951, hlam]
                                  · linarith only [h1096, h1262, hlam]
                                · have p1248_0 := h1248c.1
                                  have p1248_1 := h1248c.2.1
                                  have p1248_2 := h1248c.2.2.1
                                  have p1248_3 := h1248c.2.2.2
                                  linarith only [h1105, h1107, h1108, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1248_1]
                                · have p1248_0 := h1248c.1
                                  have p1248_1 := h1248c.2.1
                                  have p1248_2 := h1248c.2.2.1
                                  have p1248_3 := h1248c.2.2.2
                                  linarith only [h1096, hlam, p1248_0]
                                · have p1248_0 := h1248c.1
                                  have p1248_1 := h1248c.2.1
                                  have p1248_2 := h1248c.2.2.1
                                  have p1248_3 := h1248c.2.2.2
                                  linarith only [h1104, h1108, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1248_1]
                                · have p1248_0 := h1248c.1
                                  have p1248_1 := h1248c.2.1
                                  have p1248_2 := h1248c.2.2.1
                                  have p1248_3 := h1248c.2.2.2
                                  linarith only [h1106, hlam, p1248_0]
                                · have p1248_0 := h1248c.1
                                  have p1248_1 := h1248c.2.1
                                  have p1248_2 := h1248c.2.2.1
                                  have p1248_3 := h1248c.2.2.2
                                  linarith only [hlam, p1248_0]
                                · have p1248_0 := h1248c.1
                                  have p1248_1 := h1248c.2.1
                                  have p1248_2 := h1248c.2.2.1
                                  have p1248_3 := h1248c.2.2.2
                                  linarith only [h1108, hlam, p1248_1]
                                · have p1248_0 := h1248c.1
                                  have p1248_1 := h1248c.2.1
                                  have p1248_2 := h1248c.2.2.1
                                  have p1248_3 := h1248c.2.2.2
                                  linarith only [h1097, hlam, p1248_0]
                                · have p1248_0 := h1248c.1
                                  have p1248_1 := h1248c.2.1
                                  have p1248_2 := h1248c.2.2.1
                                  have p1248_3 := h1248c.2.2.2
                                  linarith only [h1104, hlam, p1248_0]
                                · have p1248_0 := h1248c.1
                                  have p1248_1 := h1248c.2.1
                                  have p1248_2 := h1248c.2.2.1
                                  have p1248_3 := h1248c.2.2.2
                                  linarith only [h1107, hlam, p1248_0]
                                · have p1248_0 := h1248c.1
                                  have p1248_1 := h1248c.2.1
                                  have p1248_2 := h1248c.2.2.1
                                  have p1248_3 := h1248c.2.2.2
                                  linarith only [h1097, hc35, hlam, hphi, ht0b, ht5b, p1248_1, u0elo3]
                                · have p1248_0 := h1248c.1
                                  have p1248_1 := h1248c.2.1
                                  have p1248_2 := h1248c.2.2.1
                                  have p1248_3 := h1248c.2.2.2
                                  linarith only [hlam, p1248_0]
                              · linarith only [h1247, hlam, p1198_0]
                            · linarith only [h1246, h672, hlam]
                          · linarith only [h1245, h2, hlam]
                    · have p1198_0 := h1198c.1
                      have p1198_1 := h1198c.2.1
                      have p1198_2 := h1198c.2.2.1
                      have p1198_3 := h1198c.2.2.2
                      rcases p1198_3 (m.d 0 2) (by simp) with h1279 | h1279
                      · linarith only [h1279, h951, hlam]
                      · linarith only [h0, h1279, hlam]
                    · have p1198_0 := h1198c.1
                      have p1198_1 := h1198c.2.1
                      have p1198_2 := h1198c.2.2.1
                      have p1198_3 := h1198c.2.2.2
                      linarith only [h1106, hlam, p1198_1]
                    · have p1198_0 := h1198c.1
                      have p1198_1 := h1198c.2.1
                      have p1198_2 := h1198c.2.2.1
                      have p1198_3 := h1198c.2.2.2
                      linarith only [h1107, hlam, p1198_0]
                    · have p1198_0 := h1198c.1
                      have p1198_1 := h1198c.2.1
                      have p1198_2 := h1198c.2.2.1
                      have p1198_3 := h1198c.2.2.2
                      linarith only [hlam, p1198_0]
                · linarith only [h0, h1, h1104, h1107, h672, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · linarith only [h1096, h1106, h2, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1287 | h1287
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1288 | h1288
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1289 | h1289
                  · rcases h2bigk with h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c
                    · have p1290_0 := h1290c.1
                      have p1290_1 := h1290c.2.1
                      have p1290_2 := h1290c.2.2.1
                      have p1290_3 := h1290c.2.2.2
                      linarith only [hlam, p1290_0]
                    · have p1290_0 := h1290c.1
                      have p1290_1 := h1290c.2.1
                      have p1290_2 := h1290c.2.2.1
                      have p1290_3 := h1290c.2.2.2
                      linarith only [h1287, h951, hc12, hc23, hlam, hphi, p1290_1]
                    · have p1290_0 := h1290c.1
                      have p1290_1 := h1290c.2.1
                      have p1290_2 := h1290c.2.2.1
                      have p1290_3 := h1290c.2.2.2
                      linarith only [h2, hlam, p1290_0]
                    · have p1290_0 := h1290c.1
                      have p1290_1 := h1290c.2.1
                      have p1290_2 := h1290c.2.2.1
                      have p1290_3 := h1290c.2.2.2
                      linarith only [h672, hlam, p1290_0]
                    · have p1290_0 := h1290c.1
                      have p1290_1 := h1290c.2.1
                      have p1290_2 := h1290c.2.2.1
                      have p1290_3 := h1290c.2.2.2
                      linarith only [h951, hlam, p1290_0]
                    · have p1290_0 := h1290c.1
                      have p1290_1 := h1290c.2.1
                      have p1290_2 := h1290c.2.2.1
                      have p1290_3 := h1290c.2.2.2
                      linarith only [h0, hlam, p1290_0]
                    · have p1290_0 := h1290c.1
                      have p1290_1 := h1290c.2.1
                      have p1290_2 := h1290c.2.2.1
                      have p1290_3 := h1290c.2.2.2
                      linarith only [hlam, p1290_0]
                    · have p1290_0 := h1290c.1
                      have p1290_1 := h1290c.2.1
                      have p1290_2 := h1290c.2.2.1
                      have p1290_3 := h1290c.2.2.2
                      linarith only [h1098, hlam, p1290_0]
                    · have p1290_0 := h1290c.1
                      have p1290_1 := h1290c.2.1
                      have p1290_2 := h1290c.2.2.1
                      have p1290_3 := h1290c.2.2.2
                      linarith only [h1100, hlam, p1290_0]
                    · have p1290_0 := h1290c.1
                      have p1290_1 := h1290c.2.1
                      have p1290_2 := h1290c.2.2.1
                      have p1290_3 := h1290c.2.2.2
                      linarith only [h1102, hlam, p1290_0]
                    · have p1290_0 := h1290c.1
                      have p1290_1 := h1290c.2.1
                      have p1290_2 := h1290c.2.2.1
                      have p1290_3 := h1290c.2.2.2
                      linarith only [h1105, hc02, hc34, hlam, hphi, ht23, p1290_1]
                    · have p1290_0 := h1290c.1
                      have p1290_1 := h1290c.2.1
                      have p1290_2 := h1290c.2.2.1
                      have p1290_3 := h1290c.2.2.2
                      linarith only [h1105, hc12, hc34, hlam, hphi, ht23, p1290_1]
                    · have p1290_0 := h1290c.1
                      have p1290_1 := h1290c.2.1
                      have p1290_2 := h1290c.2.2.1
                      have p1290_3 := h1290c.2.2.2
                      linarith only [hlam, p1290_0]
                    · have p1290_0 := h1290c.1
                      have p1290_1 := h1290c.2.1
                      have p1290_2 := h1290c.2.2.1
                      have p1290_3 := h1290c.2.2.2
                      linarith only [h1105, hlam, p1290_0]
                    · have p1290_0 := h1290c.1
                      have p1290_1 := h1290c.2.1
                      have p1290_2 := h1290c.2.2.1
                      have p1290_3 := h1290c.2.2.2
                      linarith only [h0, h1105, h951, hc12, hc34, hlam, hphi, ht23, p1290_1]
                    · have p1290_0 := h1290c.1
                      have p1290_1 := h1290c.2.1
                      have p1290_2 := h1290c.2.2.1
                      have p1290_3 := h1290c.2.2.2
                      rcases p1290_3 (m.d 0 2) (by simp) with h1306 | h1306
                      · linarith only [h1306, hlam, p1290_0]
                      · rcases p1290_3 (m.d 1 2) (by simp) with h1308 | h1308
                        · linarith only [h1100, h1308, hlam]
                        · rcases p1290_3 (m.d 2 3) (by simp) with h1310 | h1310
                          · linarith only [h1105, h1310, hlam]
                          · linarith only [h1310, h2, hlam]
                    · have p1290_0 := h1290c.1
                      have p1290_1 := h1290c.2.1
                      have p1290_2 := h1290c.2.2.1
                      have p1290_3 := h1290c.2.2.2
                      rcases p1290_3 (m.d 0 2) (by simp) with h1313 | h1313
                      · linarith only [h1313, h672, hlam]
                      · linarith only [h0, h1313, hlam]
                    · have p1290_0 := h1290c.1
                      have p1290_1 := h1290c.2.1
                      have p1290_2 := h1290c.2.2.1
                      have p1290_3 := h1290c.2.2.2
                      linarith only [h0, h1105, h2, hc12, hc34, hlam, hphi, ht23, p1290_1]
                    · have p1290_0 := h1290c.1
                      have p1290_1 := h1290c.2.1
                      have p1290_2 := h1290c.2.2.1
                      have p1290_3 := h1290c.2.2.2
                      linarith only [hlam, p1290_0]
                    · have p1290_0 := h1290c.1
                      have p1290_1 := h1290c.2.1
                      have p1290_2 := h1290c.2.2.1
                      have p1290_3 := h1290c.2.2.2
                      linarith only [h0, h1105, h951, hc12, hc34, hlam, hphi, ht23, p1290_1]
                    · have p1290_0 := h1290c.1
                      have p1290_1 := h1290c.2.1
                      have p1290_2 := h1290c.2.2.1
                      have p1290_3 := h1290c.2.2.2
                      linarith only [h0, h1105, h1287, hc12, hc34, hlam, hphi, ht23, p1290_1]
                    · have p1290_0 := h1290c.1
                      have p1290_1 := h1290c.2.1
                      have p1290_2 := h1290c.2.2.1
                      have p1290_3 := h1290c.2.2.2
                      linarith only [h1105, h1287, hc12, hc34, hlam, hphi, ht23, p1290_1]
                    · have p1290_0 := h1290c.1
                      have p1290_1 := h1290c.2.1
                      have p1290_2 := h1290c.2.2.1
                      have p1290_3 := h1290c.2.2.2
                      linarith only [h1287, hlam, p1290_1]
                    · have p1290_0 := h1290c.1
                      have p1290_1 := h1290c.2.1
                      have p1290_2 := h1290c.2.2.1
                      have p1290_3 := h1290c.2.2.2
                      linarith only [h1288, hlam, p1290_0]
                    · have p1290_0 := h1290c.1
                      have p1290_1 := h1290c.2.1
                      have p1290_2 := h1290c.2.2.1
                      have p1290_3 := h1290c.2.2.2
                      linarith only [hlam, p1290_0]
                  · linarith only [h1096, h1104, h1105, h1289, h2, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · linarith only [h0, h1, h1096, h1104, h1105, h1288, h2, h672, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1096, h1287, h2, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1327 | h1327
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1328 | h1328
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1329 | h1329
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1330 | h1330
                  · linarith only [h1100, h1104, h1327, h1330, hc12, hc23, hlam, hphi]
                  · rcases h2bigk with h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c
                    · have p1332_0 := h1332c.1
                      have p1332_1 := h1332c.2.1
                      have p1332_2 := h1332c.2.2.1
                      have p1332_3 := h1332c.2.2.2
                      linarith only [hlam, p1332_0]
                    · have p1332_0 := h1332c.1
                      have p1332_1 := h1332c.2.1
                      have p1332_2 := h1332c.2.2.1
                      have p1332_3 := h1332c.2.2.2
                      linarith only [h2, hc12, hc23, hlam, hphi, p1332_1]
                    · have p1332_0 := h1332c.1
                      have p1332_1 := h1332c.2.1
                      have p1332_2 := h1332c.2.2.1
                      have p1332_3 := h1332c.2.2.2
                      linarith only [h2, hlam, p1332_0]
                    · have p1332_0 := h1332c.1
                      have p1332_1 := h1332c.2.1
                      have p1332_2 := h1332c.2.2.1
                      have p1332_3 := h1332c.2.2.2
                      linarith only [h672, hlam, p1332_0]
                    · have p1332_0 := h1332c.1
                      have p1332_1 := h1332c.2.1
                      have p1332_2 := h1332c.2.2.1
                      have p1332_3 := h1332c.2.2.2
                      linarith only [h951, hlam, p1332_0]
                    · have p1332_0 := h1332c.1
                      have p1332_1 := h1332c.2.1
                      have p1332_2 := h1332c.2.2.1
                      have p1332_3 := h1332c.2.2.2
                      linarith only [h0, hlam, p1332_0]
                    · have p1332_0 := h1332c.1
                      have p1332_1 := h1332c.2.1
                      have p1332_2 := h1332c.2.2.1
                      have p1332_3 := h1332c.2.2.2
                      linarith only [hlam, p1332_0]
                    · have p1332_0 := h1332c.1
                      have p1332_1 := h1332c.2.1
                      have p1332_2 := h1332c.2.2.1
                      have p1332_3 := h1332c.2.2.2
                      linarith only [h1098, hlam, p1332_0]
                    · have p1332_0 := h1332c.1
                      have p1332_1 := h1332c.2.1
                      have p1332_2 := h1332c.2.2.1
                      have p1332_3 := h1332c.2.2.2
                      linarith only [h1100, hlam, p1332_0]
                    · have p1332_0 := h1332c.1
                      have p1332_1 := h1332c.2.1
                      have p1332_2 := h1332c.2.2.1
                      have p1332_3 := h1332c.2.2.2
                      linarith only [h1102, hlam, p1332_0]
                    · have p1332_0 := h1332c.1
                      have p1332_1 := h1332c.2.1
                      have p1332_2 := h1332c.2.2.1
                      have p1332_3 := h1332c.2.2.2
                      rcases p1332_3 (m.d 0 2) (by simp) with h1343 | h1343
                      · linarith only [h1343, hlam, p1332_0]
                      · rcases p1332_3 (m.d 1 2) (by simp) with h1345 | h1345
                        · linarith only [h1098, h1345, hlam]
                        · rcases p1332_3 (m.d 2 3) (by simp) with h1347 | h1347
                          · rcases p1332_3 (m.d 2 4) (by simp) with h1348 | h1348
                            · linarith only [h1327, h1348, hlam]
                            · linarith only [h1348, h672, hlam]
                          · linarith only [h1347, hlam, p1332_0]
                    · have p1332_0 := h1332c.1
                      have p1332_1 := h1332c.2.1
                      have p1332_2 := h1332c.2.2.1
                      have p1332_3 := h1332c.2.2.2
                      rcases p1332_3 (m.d 0 2) (by simp) with h1352 | h1352
                      · linarith only [h1352, h2, hlam]
                      · linarith only [h0, h1352, hlam]
                    · have p1332_0 := h1332c.1
                      have p1332_1 := h1332c.2.1
                      have p1332_2 := h1332c.2.2.1
                      have p1332_3 := h1332c.2.2.2
                      linarith only [hlam, p1332_0]
                    · have p1332_0 := h1332c.1
                      have p1332_1 := h1332c.2.1
                      have p1332_2 := h1332c.2.2.1
                      have p1332_3 := h1332c.2.2.2
                      linarith only [h1097, h1100, h1104, h672, hc12, hc23, hlam, hphi, p1332_1]
                    · have p1332_0 := h1332c.1
                      have p1332_1 := h1332c.2.1
                      have p1332_2 := h1332c.2.2.1
                      have p1332_3 := h1332c.2.2.2
                      linarith only [h951, hc02, hc23, hlam, hphi, p1332_1]
                    · have p1332_0 := h1332c.1
                      have p1332_1 := h1332c.2.1
                      have p1332_2 := h1332c.2.2.1
                      have p1332_3 := h1332c.2.2.2
                      rcases p1332_3 (m.d 0 2) (by simp) with h1358 | h1358
                      · linarith only [h1358, hlam, p1332_0]
                      · rcases p1332_3 (m.d 1 2) (by simp) with h1360 | h1360
                        · linarith only [h1100, h1360, hlam]
                        · rcases p1332_3 (m.d 2 3) (by simp) with h1362 | h1362
                          · rcases p1332_3 (m.d 2 4) (by simp) with h1363 | h1363
                            · rcases p1332_3 (m.d 2 5) (by simp) with h1364 | h1364
                              · linarith only [h1329, h1364, hlam]
                              · linarith only [h1364, h951, hlam]
                            · linarith only [h1363, hlam, p1332_0]
                          · linarith only [h1362, h2, hlam]
                    · have p1332_0 := h1332c.1
                      have p1332_1 := h1332c.2.1
                      have p1332_2 := h1332c.2.2.1
                      have p1332_3 := h1332c.2.2.2
                      rcases p1332_3 (m.d 0 2) (by simp) with h1369 | h1369
                      · linarith only [h1369, h672, hlam]
                      · linarith only [h0, h1369, hlam]
                    · have p1332_0 := h1332c.1
                      have p1332_1 := h1332c.2.1
                      have p1332_2 := h1332c.2.2.1
                      have p1332_3 := h1332c.2.2.2
                      linarith only [h1327, hlam, p1332_1]
                    · have p1332_0 := h1332c.1
                      have p1332_1 := h1332c.2.1
                      have p1332_2 := h1332c.2.2.1
                      have p1332_3 := h1332c.2.2.2
                      linarith only [hlam, p1332_0]
                    · have p1332_0 := h1332c.1
                      have p1332_1 := h1332c.2.1
                      have p1332_2 := h1332c.2.2.1
                      have p1332_3 := h1332c.2.2.2
                      linarith only [h1097, h1100, h1104, h951, hc12, hc24, hlam, hphi, p1332_1]
                    · have p1332_0 := h1332c.1
                      have p1332_1 := h1332c.2.1
                      have p1332_2 := h1332c.2.2.1
                      have p1332_3 := h1332c.2.2.2
                      rcases p1332_3 (m.d 0 2) (by simp) with h1375 | h1375
                      · linarith only [h1375, hlam, p1332_0]
                      · rcases p1332_3 (m.d 1 2) (by simp) with h1377 | h1377
                        · linarith only [h1102, h1377, hlam]
                        · rcases p1332_3 (m.d 2 3) (by simp) with h1379 | h1379
                          · rcases p1332_3 (m.d 2 4) (by simp) with h1380 | h1380
                            · rcases p1332_3 (m.d 2 5) (by simp) with h1381 | h1381
                              · rcases h5bigk with h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c
                                · have p1382_0 := h1382c.1
                                  have p1382_1 := h1382c.2.1
                                  have p1382_2 := h1382c.2.2.1
                                  have p1382_3 := h1382c.2.2.2
                                  linarith only [hlam, p1382_0]
                                · have p1382_0 := h1382c.1
                                  have p1382_1 := h1382c.2.1
                                  have p1382_2 := h1382c.2.2.1
                                  have p1382_3 := h1382c.2.2.2
                                  linarith only [hc15, hlam, hphi, ht0b, ht5b, p1382_1, u0elo4]
                                · have p1382_0 := h1382c.1
                                  have p1382_1 := h1382c.2.1
                                  have p1382_2 := h1382c.2.2.1
                                  have p1382_3 := h1382c.2.2.2
                                  linarith only [h951, hlam, p1382_0]
                                · have p1382_0 := h1382c.1
                                  have p1382_1 := h1382c.2.1
                                  have p1382_2 := h1382c.2.2.1
                                  have p1382_3 := h1382c.2.2.2
                                  linarith only [h1096, hc35, hlam, hphi, ht0b, ht5b, p1382_1, u0elo2]
                                · have p1382_0 := h1382c.1
                                  have p1382_1 := h1382c.2.1
                                  have p1382_2 := h1382c.2.2.1
                                  have p1382_3 := h1382c.2.2.2
                                  linarith only [h1100, h1104, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1382_1, u0elo4]
                                · have p1382_0 := h1382c.1
                                  have p1382_1 := h1382c.2.1
                                  have p1382_2 := h1382c.2.2.1
                                  have p1382_3 := h1382c.2.2.2
                                  linarith only [h1, hlam, p1382_0]
                                · have p1382_0 := h1382c.1
                                  have p1382_1 := h1382c.2.1
                                  have p1382_2 := h1382c.2.2.1
                                  have p1382_3 := h1382c.2.2.2
                                  linarith only [hlam, p1382_0]
                                · have p1382_0 := h1382c.1
                                  have p1382_1 := h1382c.2.1
                                  have p1382_2 := h1382c.2.2.1
                                  have p1382_3 := h1382c.2.2.2
                                  linarith only [h1102, hlam, p1382_0]
                                · have p1382_0 := h1382c.1
                                  have p1382_1 := h1382c.2.1
                                  have p1382_2 := h1382c.2.2.1
                                  have p1382_3 := h1382c.2.2.2
                                  linarith only [h1, h1330, hc34, hlam, hphi, ht0b, ht45, ht5b, p1382_1, u0elo0]
                                · have p1382_0 := h1382c.1
                                  have p1382_1 := h1382c.2.1
                                  have p1382_2 := h1382c.2.2.1
                                  have p1382_3 := h1382c.2.2.2
                                  linarith only [h1104, hlam, p1382_1]
                                · have p1382_0 := h1382c.1
                                  have p1382_1 := h1382c.2.1
                                  have p1382_2 := h1382c.2.2.1
                                  have p1382_3 := h1382c.2.2.2
                                  linarith only [h0, h951, hc12, hc25, hlam, hphi, p1382_1]
                                · have p1382_0 := h1382c.1
                                  have p1382_1 := h1382c.2.1
                                  have p1382_2 := h1382c.2.2.1
                                  have p1382_3 := h1382c.2.2.2
                                  linarith only [h1102, hc12, hc25, hlam, hphi, p1382_1]
                                · have p1382_0 := h1382c.1
                                  have p1382_1 := h1382c.2.1
                                  have p1382_2 := h1382c.2.2.1
                                  have p1382_3 := h1382c.2.2.2
                                  linarith only [hlam, p1382_0]
                                · have p1382_0 := h1382c.1
                                  have p1382_1 := h1382c.2.1
                                  have p1382_2 := h1382c.2.2.1
                                  have p1382_3 := h1382c.2.2.2
                                  rcases p1382_3 (m.d 0 5) (by simp) with h1396 | h1396
                                  · linarith only [h1396, h951, hlam]
                                  · linarith only [h1096, h1396, hlam]
                                · have p1382_0 := h1382c.1
                                  have p1382_1 := h1382c.2.1
                                  have p1382_2 := h1382c.2.2.1
                                  have p1382_3 := h1382c.2.2.2
                                  linarith only [h1100, h1104, h1327, h1329, hc12, hc23, hlam, hphi, p1382_1]
                                · have p1382_0 := h1382c.1
                                  have p1382_1 := h1382c.2.1
                                  have p1382_2 := h1382c.2.2.1
                                  have p1382_3 := h1382c.2.2.2
                                  linarith only [h1096, hlam, p1382_0]
                                · have p1382_0 := h1382c.1
                                  have p1382_1 := h1382c.2.1
                                  have p1382_2 := h1382c.2.2.1
                                  have p1382_3 := h1382c.2.2.2
                                  linarith only [h1100, h1104, hc12, hc35, hlam, hphi, ht23, p1382_1]
                                · have p1382_0 := h1382c.1
                                  have p1382_1 := h1382c.2.1
                                  have p1382_2 := h1382c.2.2.1
                                  have p1382_3 := h1382c.2.2.2
                                  linarith only [h1328, hlam, p1382_0]
                                · have p1382_0 := h1382c.1
                                  have p1382_1 := h1382c.2.1
                                  have p1382_2 := h1382c.2.2.1
                                  have p1382_3 := h1382c.2.2.2
                                  linarith only [hlam, p1382_0]
                                · have p1382_0 := h1382c.1
                                  have p1382_1 := h1382c.2.1
                                  have p1382_2 := h1382c.2.2.1
                                  have p1382_3 := h1382c.2.2.2
                                  linarith only [h1330, hlam, p1382_1]
                                · have p1382_0 := h1382c.1
                                  have p1382_1 := h1382c.2.1
                                  have p1382_2 := h1382c.2.2.1
                                  have p1382_3 := h1382c.2.2.2
                                  linarith only [h1097, hlam, p1382_0]
                                · have p1382_0 := h1382c.1
                                  have p1382_1 := h1382c.2.1
                                  have p1382_2 := h1382c.2.2.1
                                  have p1382_3 := h1382c.2.2.2
                                  linarith only [h1097, h1100, h1104, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1382_1, u0elo3]
                                · have p1382_0 := h1382c.1
                                  have p1382_1 := h1382c.2.1
                                  have p1382_2 := h1382c.2.2.1
                                  have p1382_3 := h1382c.2.2.2
                                  linarith only [h1329, hlam, p1382_0]
                                · have p1382_0 := h1382c.1
                                  have p1382_1 := h1382c.2.1
                                  have p1382_2 := h1382c.2.2.1
                                  have p1382_3 := h1382c.2.2.2
                                  linarith only [h1097, hc35, hlam, hphi, ht0b, ht5b, p1382_1, u0elo3]
                                · have p1382_0 := h1382c.1
                                  have p1382_1 := h1382c.2.1
                                  have p1382_2 := h1382c.2.2.1
                                  have p1382_3 := h1382c.2.2.2
                                  linarith only [hlam, p1382_0]
                              · linarith only [h1381, hlam, p1332_0]
                            · linarith only [h1380, h672, hlam]
                          · linarith only [h1379, h2, hlam]
                    · have p1332_0 := h1332c.1
                      have p1332_1 := h1332c.2.1
                      have p1332_2 := h1332c.2.2.1
                      have p1332_3 := h1332c.2.2.2
                      rcases p1332_3 (m.d 0 2) (by simp) with h1413 | h1413
                      · linarith only [h1413, h951, hlam]
                      · linarith only [h0, h1413, hlam]
                    · have p1332_0 := h1332c.1
                      have p1332_1 := h1332c.2.1
                      have p1332_2 := h1332c.2.2.1
                      have p1332_3 := h1332c.2.2.2
                      linarith only [h1328, hlam, p1332_1]
                    · have p1332_0 := h1332c.1
                      have p1332_1 := h1332c.2.1
                      have p1332_2 := h1332c.2.2.1
                      have p1332_3 := h1332c.2.2.2
                      linarith only [h1329, hlam, p1332_0]
                    · have p1332_0 := h1332c.1
                      have p1332_1 := h1332c.2.1
                      have p1332_2 := h1332c.2.2.1
                      have p1332_3 := h1332c.2.2.2
                      linarith only [hlam, p1332_0]
                · linarith only [h0, h1097, h1329, h672, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
              · linarith only [h1096, h1328, h2, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1421 | h1421
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1422 | h1422
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1423 | h1423
                  · linarith only [h1096, h1100, h1104, h1327, h1423, h2, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h0, h1327, h1423, h2, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h1097, h1422, h672, hlam]
              · linarith only [h1096, h1421, h2, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1428 | h1428
    · linarith only [h0, h1096, h1428, h2, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1430 | h1430
      · linarith only [h0, h1430, h672, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1432 | h1432
        · linarith only [h0, h1432, h951, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1434 | h1434
          · linarith only [h1, h1097, h1434, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1436 | h1436
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1437 | h1437
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1438 | h1438
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1439 | h1439
                  · linarith only [h0, h1097, h1436, h1439, h672, hc12, hc23, hlam, hphi]
                  · rcases h2bigk with h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c
                    · have p1441_0 := h1441c.1
                      have p1441_1 := h1441c.2.1
                      have p1441_2 := h1441c.2.2.1
                      have p1441_3 := h1441c.2.2.2
                      linarith only [hlam, p1441_0]
                    · have p1441_0 := h1441c.1
                      have p1441_1 := h1441c.2.1
                      have p1441_2 := h1441c.2.2.1
                      have p1441_3 := h1441c.2.2.2
                      linarith only [h1097, h1438, h672, hc12, hc24, hlam, hphi, p1441_1]
                    · have p1441_0 := h1441c.1
                      have p1441_1 := h1441c.2.1
                      have p1441_2 := h1441c.2.2.1
                      have p1441_3 := h1441c.2.2.2
                      linarith only [h2, hlam, p1441_0]
                    · have p1441_0 := h1441c.1
                      have p1441_1 := h1441c.2.1
                      have p1441_2 := h1441c.2.2.1
                      have p1441_3 := h1441c.2.2.2
                      linarith only [h672, hlam, p1441_0]
                    · have p1441_0 := h1441c.1
                      have p1441_1 := h1441c.2.1
                      have p1441_2 := h1441c.2.2.1
                      have p1441_3 := h1441c.2.2.2
                      linarith only [h951, hlam, p1441_0]
                    · have p1441_0 := h1441c.1
                      have p1441_1 := h1441c.2.1
                      have p1441_2 := h1441c.2.2.1
                      have p1441_3 := h1441c.2.2.2
                      linarith only [h0, hlam, p1441_0]
                    · have p1441_0 := h1441c.1
                      have p1441_1 := h1441c.2.1
                      have p1441_2 := h1441c.2.2.1
                      have p1441_3 := h1441c.2.2.2
                      linarith only [hlam, p1441_0]
                    · have p1441_0 := h1441c.1
                      have p1441_1 := h1441c.2.1
                      have p1441_2 := h1441c.2.2.1
                      have p1441_3 := h1441c.2.2.2
                      linarith only [h1428, hlam, p1441_0]
                    · have p1441_0 := h1441c.1
                      have p1441_1 := h1441c.2.1
                      have p1441_2 := h1441c.2.2.1
                      have p1441_3 := h1441c.2.2.2
                      linarith only [h1430, hlam, p1441_0]
                    · have p1441_0 := h1441c.1
                      have p1441_1 := h1441c.2.1
                      have p1441_2 := h1441c.2.2.1
                      have p1441_3 := h1441c.2.2.2
                      linarith only [h1432, hlam, p1441_0]
                    · have p1441_0 := h1441c.1
                      have p1441_1 := h1441c.2.1
                      have p1441_2 := h1441c.2.2.1
                      have p1441_3 := h1441c.2.2.2
                      rcases p1441_3 (m.d 0 2) (by simp) with h1452 | h1452
                      · linarith only [h1452, hlam, p1441_0]
                      · rcases p1441_3 (m.d 1 2) (by simp) with h1454 | h1454
                        · linarith only [h1428, h1454, hlam]
                        · rcases p1441_3 (m.d 2 3) (by simp) with h1456 | h1456
                          · rcases p1441_3 (m.d 2 4) (by simp) with h1457 | h1457
                            · linarith only [h1436, h1457, hlam]
                            · linarith only [h1457, h672, hlam]
                          · linarith only [h1456, hlam, p1441_0]
                    · have p1441_0 := h1441c.1
                      have p1441_1 := h1441c.2.1
                      have p1441_2 := h1441c.2.2.1
                      have p1441_3 := h1441c.2.2.2
                      rcases p1441_3 (m.d 0 2) (by simp) with h1461 | h1461
                      · linarith only [h1461, h2, hlam]
                      · linarith only [h0, h1461, hlam]
                    · have p1441_0 := h1441c.1
                      have p1441_1 := h1441c.2.1
                      have p1441_2 := h1441c.2.2.1
                      have p1441_3 := h1441c.2.2.2
                      linarith only [hlam, p1441_0]
                    · have p1441_0 := h1441c.1
                      have p1441_1 := h1441c.2.1
                      have p1441_2 := h1441c.2.2.1
                      have p1441_3 := h1441c.2.2.2
                      linarith only [h1097, h1438, h672, hc02, hc23, hlam, hphi, p1441_1]
                    · have p1441_0 := h1441c.1
                      have p1441_1 := h1441c.2.1
                      have p1441_2 := h1441c.2.2.1
                      have p1441_3 := h1441c.2.2.2
                      linarith only [h0, h1097, h1438, h672, hc12, hc23, hlam, hphi, p1441_1]
                    · have p1441_0 := h1441c.1
                      have p1441_1 := h1441c.2.1
                      have p1441_2 := h1441c.2.2.1
                      have p1441_3 := h1441c.2.2.2
                      rcases p1441_3 (m.d 0 2) (by simp) with h1467 | h1467
                      · linarith only [h1467, hlam, p1441_0]
                      · rcases p1441_3 (m.d 1 2) (by simp) with h1469 | h1469
                        · linarith only [h1430, h1469, hlam]
                        · rcases p1441_3 (m.d 2 3) (by simp) with h1471 | h1471
                          · rcases p1441_3 (m.d 2 4) (by simp) with h1472 | h1472
                            · rcases p1441_3 (m.d 2 5) (by simp) with h1473 | h1473
                              · linarith only [h1438, h1473, hlam]
                              · linarith only [h1473, h951, hlam]
                            · linarith only [h1472, hlam, p1441_0]
                          · linarith only [h1471, h2, hlam]
                    · have p1441_0 := h1441c.1
                      have p1441_1 := h1441c.2.1
                      have p1441_2 := h1441c.2.2.1
                      have p1441_3 := h1441c.2.2.2
                      rcases p1441_3 (m.d 0 2) (by simp) with h1478 | h1478
                      · linarith only [h1478, h672, hlam]
                      · linarith only [h0, h1478, hlam]
                    · have p1441_0 := h1441c.1
                      have p1441_1 := h1441c.2.1
                      have p1441_2 := h1441c.2.2.1
                      have p1441_3 := h1441c.2.2.2
                      linarith only [h1436, hlam, p1441_1]
                    · have p1441_0 := h1441c.1
                      have p1441_1 := h1441c.2.1
                      have p1441_2 := h1441c.2.2.1
                      have p1441_3 := h1441c.2.2.2
                      linarith only [hlam, p1441_0]
                    · have p1441_0 := h1441c.1
                      have p1441_1 := h1441c.2.1
                      have p1441_2 := h1441c.2.2.1
                      have p1441_3 := h1441c.2.2.2
                      linarith only [h0, h1097, h1438, h672, hc12, hc24, hlam, hphi, p1441_1]
                    · have p1441_0 := h1441c.1
                      have p1441_1 := h1441c.2.1
                      have p1441_2 := h1441c.2.2.1
                      have p1441_3 := h1441c.2.2.2
                      rcases p1441_3 (m.d 0 2) (by simp) with h1484 | h1484
                      · linarith only [h1484, hlam, p1441_0]
                      · rcases p1441_3 (m.d 1 2) (by simp) with h1486 | h1486
                        · linarith only [h1432, h1486, hlam]
                        · rcases p1441_3 (m.d 2 3) (by simp) with h1488 | h1488
                          · rcases p1441_3 (m.d 2 4) (by simp) with h1489 | h1489
                            · rcases p1441_3 (m.d 2 5) (by simp) with h1490 | h1490
                              · rcases h5bigk with h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c | h1491c
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [hlam, p1491_0]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [hc15, hlam, hphi, ht0b, ht5b, p1491_1, u0elo4]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [h951, hlam, p1491_0]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [h1, h1439, hc34, hlam, hphi, ht0b, ht45, ht5b, p1491_1, u0elo0]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [h1097, hlam, p1491_1]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [h1, hlam, p1491_0]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [hlam, p1491_0]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [h1432, hlam, p1491_0]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [h1, h1439, hc34, hlam, hphi, ht0b, ht45, ht5b, p1491_1, u0elo0]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [h1434, hlam, p1491_1]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [h0, h951, hc12, hc25, hlam, hphi, p1491_1]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [h1432, hc12, hc25, hlam, hphi, p1491_1]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [hlam, p1491_0]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  rcases p1491_3 (m.d 0 5) (by simp) with h1505 | h1505
                                  · linarith only [h1505, h951, hlam]
                                  · linarith only [h1096, h1505, hlam]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [h0, h1097, h1436, h1438, h672, hc12, hc23, hlam, hphi, p1491_1]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [h1096, hlam, p1491_0]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [h1430, h1434, hc12, hc35, hlam, hphi, ht23, p1491_1]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [h1437, hlam, p1491_0]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [hlam, p1491_0]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [h1439, hlam, p1491_1]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [h0, h1097, h672, hc12, hc45, hlam, hphi, ht23, ht34, p1491_1]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [h1430, h1434, hc12, hc45, hlam, hphi, ht23, ht34, p1491_1]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [h1438, hlam, p1491_0]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [h1436, h1438, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1491_1]
                                · have p1491_0 := h1491c.1
                                  have p1491_1 := h1491c.2.1
                                  have p1491_2 := h1491c.2.2.1
                                  have p1491_3 := h1491c.2.2.2
                                  linarith only [hlam, p1491_0]
                              · linarith only [h1490, hlam, p1441_0]
                            · linarith only [h1489, h672, hlam]
                          · linarith only [h1488, h2, hlam]
                    · have p1441_0 := h1441c.1
                      have p1441_1 := h1441c.2.1
                      have p1441_2 := h1441c.2.2.1
                      have p1441_3 := h1441c.2.2.2
                      rcases p1441_3 (m.d 0 2) (by simp) with h1522 | h1522
                      · linarith only [h1522, h951, hlam]
                      · linarith only [h0, h1522, hlam]
                    · have p1441_0 := h1441c.1
                      have p1441_1 := h1441c.2.1
                      have p1441_2 := h1441c.2.2.1
                      have p1441_3 := h1441c.2.2.2
                      linarith only [h1437, hlam, p1441_1]
                    · have p1441_0 := h1441c.1
                      have p1441_1 := h1441c.2.1
                      have p1441_2 := h1441c.2.2.1
                      have p1441_3 := h1441c.2.2.2
                      linarith only [h1438, hlam, p1441_0]
                    · have p1441_0 := h1441c.1
                      have p1441_1 := h1441c.2.1
                      have p1441_2 := h1441c.2.2.1
                      have p1441_3 := h1441c.2.2.2
                      linarith only [hlam, p1441_0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1528 | h1528
                  · linarith only [h0, h1438, h1528, h672, hc12, hc34, hlam, hphi, ht23]
                  · rcases h2bigk with h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c
                    · have p1530_0 := h1530c.1
                      have p1530_1 := h1530c.2.1
                      have p1530_2 := h1530c.2.2.1
                      have p1530_3 := h1530c.2.2.2
                      linarith only [hlam, p1530_0]
                    · have p1530_0 := h1530c.1
                      have p1530_1 := h1530c.2.1
                      have p1530_2 := h1530c.2.2.1
                      have p1530_3 := h1530c.2.2.2
                      linarith only [h672, hc12, hc24, hlam, hphi, p1530_1]
                    · have p1530_0 := h1530c.1
                      have p1530_1 := h1530c.2.1
                      have p1530_2 := h1530c.2.2.1
                      have p1530_3 := h1530c.2.2.2
                      linarith only [h2, hlam, p1530_0]
                    · have p1530_0 := h1530c.1
                      have p1530_1 := h1530c.2.1
                      have p1530_2 := h1530c.2.2.1
                      have p1530_3 := h1530c.2.2.2
                      linarith only [h672, hlam, p1530_0]
                    · have p1530_0 := h1530c.1
                      have p1530_1 := h1530c.2.1
                      have p1530_2 := h1530c.2.2.1
                      have p1530_3 := h1530c.2.2.2
                      linarith only [h951, hlam, p1530_0]
                    · have p1530_0 := h1530c.1
                      have p1530_1 := h1530c.2.1
                      have p1530_2 := h1530c.2.2.1
                      have p1530_3 := h1530c.2.2.2
                      linarith only [h0, hlam, p1530_0]
                    · have p1530_0 := h1530c.1
                      have p1530_1 := h1530c.2.1
                      have p1530_2 := h1530c.2.2.1
                      have p1530_3 := h1530c.2.2.2
                      linarith only [hlam, p1530_0]
                    · have p1530_0 := h1530c.1
                      have p1530_1 := h1530c.2.1
                      have p1530_2 := h1530c.2.2.1
                      have p1530_3 := h1530c.2.2.2
                      linarith only [h1428, hlam, p1530_0]
                    · have p1530_0 := h1530c.1
                      have p1530_1 := h1530c.2.1
                      have p1530_2 := h1530c.2.2.1
                      have p1530_3 := h1530c.2.2.2
                      linarith only [h1430, hlam, p1530_0]
                    · have p1530_0 := h1530c.1
                      have p1530_1 := h1530c.2.1
                      have p1530_2 := h1530c.2.2.1
                      have p1530_3 := h1530c.2.2.2
                      linarith only [h1432, hlam, p1530_0]
                    · have p1530_0 := h1530c.1
                      have p1530_1 := h1530c.2.1
                      have p1530_2 := h1530c.2.2.1
                      have p1530_3 := h1530c.2.2.2
                      rcases p1530_3 (m.d 0 2) (by simp) with h1541 | h1541
                      · linarith only [h1541, hlam, p1530_0]
                      · rcases p1530_3 (m.d 1 2) (by simp) with h1543 | h1543
                        · linarith only [h1428, h1543, hlam]
                        · rcases p1530_3 (m.d 2 3) (by simp) with h1545 | h1545
                          · rcases p1530_3 (m.d 2 4) (by simp) with h1546 | h1546
                            · linarith only [h1436, h1546, hlam]
                            · linarith only [h1546, h672, hlam]
                          · linarith only [h1545, hlam, p1530_0]
                    · have p1530_0 := h1530c.1
                      have p1530_1 := h1530c.2.1
                      have p1530_2 := h1530c.2.2.1
                      have p1530_3 := h1530c.2.2.2
                      rcases p1530_3 (m.d 0 2) (by simp) with h1550 | h1550
                      · linarith only [h1550, h2, hlam]
                      · linarith only [h0, h1550, hlam]
                    · have p1530_0 := h1530c.1
                      have p1530_1 := h1530c.2.1
                      have p1530_2 := h1530c.2.2.1
                      have p1530_3 := h1530c.2.2.2
                      linarith only [hlam, p1530_0]
                    · have p1530_0 := h1530c.1
                      have p1530_1 := h1530c.2.1
                      have p1530_2 := h1530c.2.2.1
                      have p1530_3 := h1530c.2.2.2
                      linarith only [h672, hc02, hc23, hlam, hphi, p1530_1]
                    · have p1530_0 := h1530c.1
                      have p1530_1 := h1530c.2.1
                      have p1530_2 := h1530c.2.2.1
                      have p1530_3 := h1530c.2.2.2
                      linarith only [h0, h951, hc12, hc23, hlam, hphi, p1530_1]
                    · have p1530_0 := h1530c.1
                      have p1530_1 := h1530c.2.1
                      have p1530_2 := h1530c.2.2.1
                      have p1530_3 := h1530c.2.2.2
                      linarith only [h0, h1438, hc12, hc45, hlam, hphi, ht23, ht34, p1530_1]
                    · have p1530_0 := h1530c.1
                      have p1530_1 := h1530c.2.1
                      have p1530_2 := h1530c.2.2.1
                      have p1530_3 := h1530c.2.2.2
                      linarith only [h1438, hc12, hc45, hlam, hphi, ht23, ht34, p1530_1]
                    · have p1530_0 := h1530c.1
                      have p1530_1 := h1530c.2.1
                      have p1530_2 := h1530c.2.2.1
                      have p1530_3 := h1530c.2.2.2
                      linarith only [h1436, hlam, p1530_1]
                    · have p1530_0 := h1530c.1
                      have p1530_1 := h1530c.2.1
                      have p1530_2 := h1530c.2.2.1
                      have p1530_3 := h1530c.2.2.2
                      linarith only [hlam, p1530_0]
                    · have p1530_0 := h1530c.1
                      have p1530_1 := h1530c.2.1
                      have p1530_2 := h1530c.2.2.1
                      have p1530_3 := h1530c.2.2.2
                      linarith only [h1438, hlam, p1530_1]
                    · have p1530_0 := h1530c.1
                      have p1530_1 := h1530c.2.1
                      have p1530_2 := h1530c.2.2.1
                      have p1530_3 := h1530c.2.2.2
                      rcases p1530_3 (m.d 0 2) (by simp) with h1561 | h1561
                      · linarith only [h1561, hlam, p1530_0]
                      · rcases p1530_3 (m.d 1 2) (by simp) with h1563 | h1563
                        · linarith only [h1432, h1563, hlam]
                        · rcases p1530_3 (m.d 2 3) (by simp) with h1565 | h1565
                          · rcases p1530_3 (m.d 2 4) (by simp) with h1566 | h1566
                            · linarith only [h1438, h1566, hlam]
                            · linarith only [h1566, h672, hlam]
                          · linarith only [h1565, h2, hlam]
                    · have p1530_0 := h1530c.1
                      have p1530_1 := h1530c.2.1
                      have p1530_2 := h1530c.2.2.1
                      have p1530_3 := h1530c.2.2.2
                      rcases p1530_3 (m.d 0 2) (by simp) with h1570 | h1570
                      · linarith only [h1570, h951, hlam]
                      · linarith only [h0, h1570, hlam]
                    · have p1530_0 := h1530c.1
                      have p1530_1 := h1530c.2.1
                      have p1530_2 := h1530c.2.2.1
                      have p1530_3 := h1530c.2.2.2
                      linarith only [h1437, hlam, p1530_1]
                    · have p1530_0 := h1530c.1
                      have p1530_1 := h1530c.2.1
                      have p1530_2 := h1530c.2.2.1
                      have p1530_3 := h1530c.2.2.2
                      linarith only [h0, h672, hc12, hc25, hlam, hphi, p1530_1]
                    · have p1530_0 := h1530c.1
                      have p1530_1 := h1530c.2.1
                      have p1530_2 := h1530c.2.2.1
                      have p1530_3 := h1530c.2.2.2
                      linarith only [hlam, p1530_0]
              · linarith only [h1096, h1437, h2, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1577 | h1577
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1578 | h1578
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1579 | h1579
                  · linarith only [h0, h1096, h1097, h1436, h1579, h2, h672, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h1096, h1436, h1578, h1579, h2, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · linarith only [h1436, h1577, h1578, hlam]
              · linarith only [h1096, h1577, h2, hlam]

end R2N4
