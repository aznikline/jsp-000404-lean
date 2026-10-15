import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5286000 in
set_option maxHeartbeats 5286000 in
theorem r1l7_20_12_14_M_LI_L_I_L_0_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1079 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1080 | h1080
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1081 | h1081
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1082 | h1082
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1083 | h1083
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1084 | h1084
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1085 | h1085
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1086 | h1086
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1087 | h1087
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1088 | h1088
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1089 | h1089
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1090 | h1090
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1091 | h1091
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1092 | h1092
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1093 | h1093
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1094 | h1094
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1095 | h1095
                                · linarith only [h1079, h1088, h1092, h1095, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                · linarith only [h1087, h1095, hc34, hlam, hphi, u4elo0]
                              · linarith only [h0, h1080, h1091, h1094, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · linarith only [h0, h1079, h1086, h1092, h1093, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1100 | h1100
                            · linarith only [h0, h1079, h1085, h1092, h1100, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1102 | h1102
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1103 | h1103
                                · rcases h0bigk with h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c | h1104c
                                  · have p1104_0 := h1104c.1
                                    have p1104_1 := h1104c.2.1
                                    have p1104_2 := h1104c.2.2.1
                                    have p1104_3 := h1104c.2.2.2
                                    linarith only [hlam, p1104_0]
                                  · have p1104_0 := h1104c.1
                                    have p1104_1 := h1104c.2.1
                                    have p1104_2 := h1104c.2.2.1
                                    have p1104_3 := h1104c.2.2.2
                                    linarith only [h0, hlam, p1104_1]
                                  · have p1104_0 := h1104c.1
                                    have p1104_1 := h1104c.2.1
                                    have p1104_2 := h1104c.2.2.1
                                    have p1104_3 := h1104c.2.2.2
                                    linarith only [h0, h1085, h1100, h1103, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1104_1, u0elo1]
                                  · have p1104_0 := h1104c.1
                                    have p1104_1 := h1104c.2.1
                                    have p1104_2 := h1104c.2.2.1
                                    have p1104_3 := h1104c.2.2.2
                                    linarith only [h0, h1083, h1102, hc45, hlam, hphi, ht0b, ht5b, p1104_1, u0elo1]
                                  · have p1104_0 := h1104c.1
                                    have p1104_1 := h1104c.2.1
                                    have p1104_2 := h1104c.2.2.1
                                    have p1104_3 := h1104c.2.2.2
                                    linarith only [h0, h1086, h1100, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1104_1, u0elo1]
                                  · have p1104_0 := h1104c.1
                                    have p1104_1 := h1104c.2.1
                                    have p1104_2 := h1104c.2.2.1
                                    have p1104_3 := h1104c.2.2.2
                                    linarith only [h1079, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1104_1, u0elo1]
                                  · have p1104_0 := h1104c.1
                                    have p1104_1 := h1104c.2.1
                                    have p1104_2 := h1104c.2.2.1
                                    have p1104_3 := h1104c.2.2.2
                                    linarith only [hlam, p1104_0]
                                  · have p1104_0 := h1104c.1
                                    have p1104_1 := h1104c.2.1
                                    have p1104_2 := h1104c.2.2.1
                                    have p1104_3 := h1104c.2.2.2
                                    linarith only [h1085, h1100, h1103, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1104_1, u0elo1]
                                  · have p1104_0 := h1104c.1
                                    have p1104_1 := h1104c.2.1
                                    have p1104_2 := h1104c.2.2.1
                                    have p1104_3 := h1104c.2.2.2
                                    linarith only [h1085, h1100, h1103, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1104_1, u0elo1]
                                  · have p1104_0 := h1104c.1
                                    have p1104_1 := h1104c.2.1
                                    have p1104_2 := h1104c.2.2.1
                                    have p1104_3 := h1104c.2.2.2
                                    linarith only [h1086, h1100, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1104_1, u0elo1]
                                  · have p1104_0 := h1104c.1
                                    have p1104_1 := h1104c.2.1
                                    have p1104_2 := h1104c.2.2.1
                                    have p1104_3 := h1104c.2.2.2
                                    linarith only [h1079, hlam, p1104_1]
                                  · have p1104_0 := h1104c.1
                                    have p1104_1 := h1104c.2.1
                                    have p1104_2 := h1104c.2.2.1
                                    have p1104_3 := h1104c.2.2.2
                                    linarith only [h1082, hlam, p1104_1]
                                  · have p1104_0 := h1104c.1
                                    have p1104_1 := h1104c.2.1
                                    have p1104_2 := h1104c.2.2.1
                                    have p1104_3 := h1104c.2.2.2
                                    linarith only [hlam, p1104_0]
                                  · have p1104_0 := h1104c.1
                                    have p1104_1 := h1104c.2.1
                                    have p1104_2 := h1104c.2.2.1
                                    have p1104_3 := h1104c.2.2.2
                                    linarith only [h1079, h1085, h1100, h1103, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1104_1, u0elo0]
                                  · have p1104_0 := h1104c.1
                                    have p1104_1 := h1104c.2.1
                                    have p1104_2 := h1104c.2.2.1
                                    have p1104_3 := h1104c.2.2.2
                                    linarith only [h0, h1079, h1086, h1100, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1104_1]
                                  · have p1104_0 := h1104c.1
                                    have p1104_1 := h1104c.2.1
                                    have p1104_2 := h1104c.2.2.1
                                    have p1104_3 := h1104c.2.2.2
                                    linarith only [h1080, hlam, p1104_0]
                                  · have p1104_0 := h1104c.1
                                    have p1104_1 := h1104c.2.1
                                    have p1104_2 := h1104c.2.2.1
                                    have p1104_3 := h1104c.2.2.2
                                    linarith only [h1083, hlam, p1104_0]
                                  · have p1104_0 := h1104c.1
                                    have p1104_1 := h1104c.2.1
                                    have p1104_2 := h1104c.2.2.1
                                    have p1104_3 := h1104c.2.2.2
                                    linarith only [h1085, hlam, p1104_0]
                                  · have p1104_0 := h1104c.1
                                    have p1104_1 := h1104c.2.1
                                    have p1104_2 := h1104c.2.2.1
                                    have p1104_3 := h1104c.2.2.2
                                    linarith only [hlam, p1104_0]
                                  · have p1104_0 := h1104c.1
                                    have p1104_1 := h1104c.2.1
                                    have p1104_2 := h1104c.2.2.1
                                    have p1104_3 := h1104c.2.2.2
                                    linarith only [h1086, h1100, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1104_1, u0elo3]
                                  · have p1104_0 := h1104c.1
                                    have p1104_1 := h1104c.2.1
                                    have p1104_2 := h1104c.2.2.1
                                    have p1104_3 := h1104c.2.2.2
                                    linarith only [h1081, hlam, p1104_0]
                                  · have p1104_0 := h1104c.1
                                    have p1104_1 := h1104c.2.1
                                    have p1104_2 := h1104c.2.2.1
                                    have p1104_3 := h1104c.2.2.2
                                    linarith only [h1084, hlam, p1104_1]
                                  · have p1104_0 := h1104c.1
                                    have p1104_1 := h1104c.2.1
                                    have p1104_2 := h1104c.2.2.1
                                    have p1104_3 := h1104c.2.2.2
                                    linarith only [h1086, hlam, p1104_0]
                                  · have p1104_0 := h1104c.1
                                    have p1104_1 := h1104c.2.1
                                    have p1104_2 := h1104c.2.2.1
                                    have p1104_3 := h1104c.2.2.2
                                    linarith only [h1087, hlam, p1104_1]
                                  · have p1104_0 := h1104c.1
                                    have p1104_1 := h1104c.2.1
                                    have p1104_2 := h1104c.2.2.1
                                    have p1104_3 := h1104c.2.2.2
                                    linarith only [hlam, p1104_0]
                                · linarith only [h1102, h1103, hc34, hlam, hphi, u4elo2]
                              · linarith only [h0, h1080, h1091, h1102, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h1087, h1091, hc14, hlam, hphi, u4elo0]
                      · linarith only [h0, h1084, h1090, hlam]
                    · linarith only [h0, h1089, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h0, h1082, h1088, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1136 | h1136
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1137 | h1137
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1138 | h1138
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1139 | h1139
                        · linarith only [h1087, h1139, hc04, hlam, hphi, u4elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1141 | h1141
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1142 | h1142
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1143 | h1143
                              · linarith only [h1080, h1087, h1137, h1143, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1145 | h1145
                                · linarith only [h1080, h1087, h1137, h1141, h1145, hlam]
                                · rcases h0bigk with h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c
                                  · have p1147_0 := h1147c.1
                                    have p1147_1 := h1147c.2.1
                                    have p1147_2 := h1147c.2.2.1
                                    have p1147_3 := h1147c.2.2.2
                                    linarith only [hlam, p1147_0]
                                  · have p1147_0 := h1147c.1
                                    have p1147_1 := h1147c.2.1
                                    have p1147_2 := h1147c.2.2.1
                                    have p1147_3 := h1147c.2.2.2
                                    linarith only [h0, hlam, p1147_1]
                                  · have p1147_0 := h1147c.1
                                    have p1147_1 := h1147c.2.1
                                    have p1147_2 := h1147c.2.2.1
                                    have p1147_3 := h1147c.2.2.2
                                    linarith only [h1079, h1136, h1142, h1145, hc34, hlam, hphi, ht0b, ht45, ht5b, p1147_1, u0elo0]
                                  · have p1147_0 := h1147c.1
                                    have p1147_1 := h1147c.2.1
                                    have p1147_2 := h1147c.2.2.1
                                    have p1147_3 := h1147c.2.2.2
                                    rcases p1147_3 (m.d 0 1) (by simp) with h1151 | h1151
                                    · rcases p1147_3 (m.d 0 2) (by simp) with h1152 | h1152
                                      · rcases p1147_3 (m.d 0 3) (by simp) with h1153 | h1153
                                        · linarith only [h1079, h1153, hlam]
                                        · linarith only [h1085, h1153, hlam]
                                      · linarith only [h1083, h1152, hlam]
                                    · linarith only [h1080, h1151, hlam]
                                  · have p1147_0 := h1147c.1
                                    have p1147_1 := h1147c.2.1
                                    have p1147_2 := h1147c.2.2.1
                                    have p1147_3 := h1147c.2.2.2
                                    rcases p1147_3 (m.d 0 1) (by simp) with h1158 | h1158
                                    · rcases p1147_3 (m.d 0 2) (by simp) with h1159 | h1159
                                      · rcases p1147_3 (m.d 0 3) (by simp) with h1160 | h1160
                                        · linarith only [h1079, h1160, hlam]
                                        · linarith only [h1086, h1160, hlam]
                                      · linarith only [h1084, h1159, hlam]
                                    · linarith only [h1081, h1158, hlam]
                                  · have p1147_0 := h1147c.1
                                    have p1147_1 := h1147c.2.1
                                    have p1147_2 := h1147c.2.2.1
                                    have p1147_3 := h1147c.2.2.2
                                    linarith only [h1079, h1136, h1142, h1145, hc34, hlam, hphi, ht0b, ht45, ht5b, p1147_1, u0elo1]
                                  · have p1147_0 := h1147c.1
                                    have p1147_1 := h1147c.2.1
                                    have p1147_2 := h1147c.2.2.1
                                    have p1147_3 := h1147c.2.2.2
                                    linarith only [hlam, p1147_0]
                                  · have p1147_0 := h1147c.1
                                    have p1147_1 := h1147c.2.1
                                    have p1147_2 := h1147c.2.2.1
                                    have p1147_3 := h1147c.2.2.2
                                    linarith only [h1079, h1136, h1142, h1145, hc34, hlam, hphi, ht0b, ht45, ht5b, p1147_1, u0elo1]
                                  · have p1147_0 := h1147c.1
                                    have p1147_1 := h1147c.2.1
                                    have p1147_2 := h1147c.2.2.1
                                    have p1147_3 := h1147c.2.2.2
                                    rcases p1147_3 (m.d 0 1) (by simp) with h1168 | h1168
                                    · linarith only [h0, h1168, hlam]
                                    · linarith only [h1080, h1168, hlam]
                                  · have p1147_0 := h1147c.1
                                    have p1147_1 := h1147c.2.1
                                    have p1147_2 := h1147c.2.2.1
                                    have p1147_3 := h1147c.2.2.2
                                    rcases p1147_3 (m.d 0 1) (by simp) with h1171 | h1171
                                    · linarith only [h0, h1171, hlam]
                                    · linarith only [h1081, h1171, hlam]
                                  · have p1147_0 := h1147c.1
                                    have p1147_1 := h1147c.2.1
                                    have p1147_2 := h1147c.2.2.1
                                    have p1147_3 := h1147c.2.2.2
                                    linarith only [h1079, hlam, p1147_1]
                                  · have p1147_0 := h1147c.1
                                    have p1147_1 := h1147c.2.1
                                    have p1147_2 := h1147c.2.2.1
                                    have p1147_3 := h1147c.2.2.2
                                    linarith only [h1082, hlam, p1147_1]
                                  · have p1147_0 := h1147c.1
                                    have p1147_1 := h1147c.2.1
                                    have p1147_2 := h1147c.2.2.1
                                    have p1147_3 := h1147c.2.2.2
                                    linarith only [hlam, p1147_0]
                                  · have p1147_0 := h1147c.1
                                    have p1147_1 := h1147c.2.1
                                    have p1147_2 := h1147c.2.2.1
                                    have p1147_3 := h1147c.2.2.2
                                    rcases p1147_3 (m.d 0 1) (by simp) with h1177 | h1177
                                    · rcases p1147_3 (m.d 0 2) (by simp) with h1178 | h1178
                                      · rcases p1147_3 (m.d 0 3) (by simp) with h1179 | h1179
                                        · rcases p1147_3 (m.d 0 4) (by simp) with h1180 | h1180
                                          · linarith only [h1085, h1180, hlam]
                                          · rcases p1147_3 (m.d 0 5) (by simp) with h1182 | h1182
                                            · linarith only [h1086, h1182, hlam]
                                            · linarith only [h1087, h1182, hlam]
                                        · linarith only [h1085, h1179, hlam]
                                      · linarith only [h1083, h1178, hlam]
                                    · linarith only [h1080, h1177, hlam]
                                  · have p1147_0 := h1147c.1
                                    have p1147_1 := h1147c.2.1
                                    have p1147_2 := h1147c.2.2.1
                                    have p1147_3 := h1147c.2.2.2
                                    rcases p1147_3 (m.d 0 1) (by simp) with h1188 | h1188
                                    · rcases p1147_3 (m.d 0 2) (by simp) with h1189 | h1189
                                      · rcases p1147_3 (m.d 0 3) (by simp) with h1190 | h1190
                                        · rcases p1147_3 (m.d 0 4) (by simp) with h1191 | h1191
                                          · linarith only [h1085, h1191, hlam]
                                          · rcases p1147_3 (m.d 0 5) (by simp) with h1193 | h1193
                                            · linarith only [h1086, h1193, hlam]
                                            · rcases h2bigk with h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c
                                              · have p1195_0 := h1195c.1
                                                have p1195_1 := h1195c.2.1
                                                have p1195_2 := h1195c.2.2.1
                                                have p1195_3 := h1195c.2.2.2
                                                linarith only [hlam, p1195_0]
                                              · have p1195_0 := h1195c.1
                                                have p1195_1 := h1195c.2.1
                                                have p1195_2 := h1195c.2.2.1
                                                have p1195_3 := h1195c.2.2.2
                                                linarith only [h0, hlam, p1195_1]
                                              · have p1195_0 := h1195c.1
                                                have p1195_1 := h1195c.2.1
                                                have p1195_2 := h1195c.2.2.1
                                                have p1195_3 := h1195c.2.2.2
                                                linarith only [h1142, h1145, hc34, hlam, hphi, ht0b, ht45, ht5b, p1195_1, u0elo1]
                                              · have p1195_0 := h1195c.1
                                                have p1195_1 := h1195c.2.1
                                                have p1195_2 := h1195c.2.2.1
                                                have p1195_3 := h1195c.2.2.2
                                                rcases p1195_3 (m.d 0 2) (by simp) with h1199 | h1199
                                                · rcases p1195_3 (m.d 1 2) (by simp) with h1200 | h1200
                                                  · rcases p1195_3 (m.d 2 3) (by simp) with h1201 | h1201
                                                    · linarith only [h1082, h1201, hlam]
                                                    · linarith only [h1141, h1201, hlam]
                                                  · linarith only [h1137, h1200, hlam]
                                                · linarith only [h1199, hlam, p1195_0]
                                              · have p1195_0 := h1195c.1
                                                have p1195_1 := h1195c.2.1
                                                have p1195_2 := h1195c.2.2.1
                                                have p1195_3 := h1195c.2.2.2
                                                rcases p1195_3 (m.d 0 2) (by simp) with h1206 | h1206
                                                · rcases p1195_3 (m.d 1 2) (by simp) with h1207 | h1207
                                                  · rcases p1195_3 (m.d 2 3) (by simp) with h1208 | h1208
                                                    · linarith only [h1082, h1208, hlam]
                                                    · linarith only [h1142, h1208, hlam]
                                                  · linarith only [h1138, h1207, hlam]
                                                · linarith only [h1206, hlam, p1195_0]
                                              · have p1195_0 := h1195c.1
                                                have p1195_1 := h1195c.2.1
                                                have p1195_2 := h1195c.2.2.1
                                                have p1195_3 := h1195c.2.2.2
                                                linarith only [h0, h1079, h1080, h1087, h1137, h1141, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1147_1, p1195_1]
                                              · have p1195_0 := h1195c.1
                                                have p1195_1 := h1195c.2.1
                                                have p1195_2 := h1195c.2.2.1
                                                have p1195_3 := h1195c.2.2.2
                                                linarith only [hlam, p1195_0]
                                              · have p1195_0 := h1195c.1
                                                have p1195_1 := h1195c.2.1
                                                have p1195_2 := h1195c.2.2.1
                                                have p1195_3 := h1195c.2.2.2
                                                rcases p1195_3 (m.d 0 2) (by simp) with h1215 | h1215
                                                · linarith only [h0, h1215, hlam]
                                                · linarith only [h1082, h1215, hlam]
                                              · have p1195_0 := h1195c.1
                                                have p1195_1 := h1195c.2.1
                                                have p1195_2 := h1195c.2.2.1
                                                have p1195_3 := h1195c.2.2.2
                                                linarith only [h0, h1079, h1080, h1087, h1137, hlam, p1147_1, p1195_2]
                                              · have p1195_0 := h1195c.1
                                                have p1195_1 := h1195c.2.1
                                                have p1195_2 := h1195c.2.2.1
                                                have p1195_3 := h1195c.2.2.2
                                                linarith only [h0, h1079, h1084, hlam, p1147_1, p1195_2]
                                              · have p1195_0 := h1195c.1
                                                have p1195_1 := h1195c.2.1
                                                have p1195_2 := h1195c.2.2.1
                                                have p1195_3 := h1195c.2.2.2
                                                linarith only [h1082, hlam, p1195_0]
                                              · have p1195_0 := h1195c.1
                                                have p1195_1 := h1195c.2.1
                                                have p1195_2 := h1195c.2.2.1
                                                have p1195_3 := h1195c.2.2.2
                                                linarith only [h1136, hlam, p1195_0]
                                              · have p1195_0 := h1195c.1
                                                have p1195_1 := h1195c.2.1
                                                have p1195_2 := h1195c.2.2.1
                                                have p1195_3 := h1195c.2.2.2
                                                linarith only [hlam, p1195_0]
                                              · have p1195_0 := h1195c.1
                                                have p1195_1 := h1195c.2.1
                                                have p1195_2 := h1195c.2.2.1
                                                have p1195_3 := h1195c.2.2.2
                                                linarith only [h1079, h1136, h1141, hc34, hlam, hphi, ht0b, ht45, ht5b, p1195_1, u0elo0]
                                              · have p1195_0 := h1195c.1
                                                have p1195_1 := h1195c.2.1
                                                have p1195_2 := h1195c.2.2.1
                                                have p1195_3 := h1195c.2.2.2
                                                linarith only [h0, h1079, h1136, hc25, hlam, hphi, ht0b, ht5b, p1195_1, u0elo1]
                                              · have p1195_0 := h1195c.1
                                                have p1195_1 := h1195c.2.1
                                                have p1195_2 := h1195c.2.2.1
                                                have p1195_3 := h1195c.2.2.2
                                                linarith only [h1083, hlam, p1195_0]
                                              · have p1195_0 := h1195c.1
                                                have p1195_1 := h1195c.2.1
                                                have p1195_2 := h1195c.2.2.1
                                                have p1195_3 := h1195c.2.2.2
                                                linarith only [h1137, hlam, p1195_0]
                                              · have p1195_0 := h1195c.1
                                                have p1195_1 := h1195c.2.1
                                                have p1195_2 := h1195c.2.2.1
                                                have p1195_3 := h1195c.2.2.2
                                                linarith only [h1141, hlam, p1195_1]
                                              · have p1195_0 := h1195c.1
                                                have p1195_1 := h1195c.2.1
                                                have p1195_2 := h1195c.2.2.1
                                                have p1195_3 := h1195c.2.2.2
                                                linarith only [hlam, p1195_0]
                                              · have p1195_0 := h1195c.1
                                                have p1195_1 := h1195c.2.1
                                                have p1195_2 := h1195c.2.2.1
                                                have p1195_3 := h1195c.2.2.2
                                                linarith only [h1143, hlam, p1195_1]
                                              · have p1195_0 := h1195c.1
                                                have p1195_1 := h1195c.2.1
                                                have p1195_2 := h1195c.2.2.1
                                                have p1195_3 := h1195c.2.2.2
                                                linarith only [h1084, hlam, p1195_0]
                                              · have p1195_0 := h1195c.1
                                                have p1195_1 := h1195c.2.1
                                                have p1195_2 := h1195c.2.2.1
                                                have p1195_3 := h1195c.2.2.2
                                                linarith only [h1138, hlam, p1195_0]
                                              · have p1195_0 := h1195c.1
                                                have p1195_1 := h1195c.2.1
                                                have p1195_2 := h1195c.2.2.1
                                                have p1195_3 := h1195c.2.2.2
                                                linarith only [h1142, hlam, p1195_1]
                                              · have p1195_0 := h1195c.1
                                                have p1195_1 := h1195c.2.1
                                                have p1195_2 := h1195c.2.2.1
                                                have p1195_3 := h1195c.2.2.2
                                                linarith only [h1084, h1141, hc34, hlam, hphi, ht0b, ht45, ht5b, p1195_1, u0elo1]
                                              · have p1195_0 := h1195c.1
                                                have p1195_1 := h1195c.2.1
                                                have p1195_2 := h1195c.2.2.1
                                                have p1195_3 := h1195c.2.2.2
                                                linarith only [hlam, p1195_0]
                                        · linarith only [h1086, h1190, hlam]
                                      · linarith only [h1084, h1189, hlam]
                                    · linarith only [h1081, h1188, hlam]
                                  · have p1147_0 := h1147c.1
                                    have p1147_1 := h1147c.2.1
                                    have p1147_2 := h1147c.2.2.1
                                    have p1147_3 := h1147c.2.2.2
                                    linarith only [h1080, hlam, p1147_0]
                                  · have p1147_0 := h1147c.1
                                    have p1147_1 := h1147c.2.1
                                    have p1147_2 := h1147c.2.2.1
                                    have p1147_3 := h1147c.2.2.2
                                    linarith only [h1083, hlam, p1147_0]
                                  · have p1147_0 := h1147c.1
                                    have p1147_1 := h1147c.2.1
                                    have p1147_2 := h1147c.2.2.1
                                    have p1147_3 := h1147c.2.2.2
                                    linarith only [h1085, hlam, p1147_0]
                                  · have p1147_0 := h1147c.1
                                    have p1147_1 := h1147c.2.1
                                    have p1147_2 := h1147c.2.2.1
                                    have p1147_3 := h1147c.2.2.2
                                    linarith only [hlam, p1147_0]
                                  · have p1147_0 := h1147c.1
                                    have p1147_1 := h1147c.2.1
                                    have p1147_2 := h1147c.2.2.1
                                    have p1147_3 := h1147c.2.2.2
                                    linarith only [h1087, hlam, p1147_0]
                                  · have p1147_0 := h1147c.1
                                    have p1147_1 := h1147c.2.1
                                    have p1147_2 := h1147c.2.2.1
                                    have p1147_3 := h1147c.2.2.2
                                    linarith only [h1081, hlam, p1147_0]
                                  · have p1147_0 := h1147c.1
                                    have p1147_1 := h1147c.2.1
                                    have p1147_2 := h1147c.2.2.1
                                    have p1147_3 := h1147c.2.2.2
                                    linarith only [h1084, hlam, p1147_1]
                                  · have p1147_0 := h1147c.1
                                    have p1147_1 := h1147c.2.1
                                    have p1147_2 := h1147c.2.2.1
                                    have p1147_3 := h1147c.2.2.2
                                    linarith only [h1086, hlam, p1147_0]
                                  · have p1147_0 := h1147c.1
                                    have p1147_1 := h1147c.2.1
                                    have p1147_2 := h1147c.2.2.1
                                    have p1147_3 := h1147c.2.2.2
                                    linarith only [h1080, h1087, h1137, h1141, hc34, hlam, hphi, p1147_1, u4elo4]
                                  · have p1147_0 := h1147c.1
                                    have p1147_1 := h1147c.2.1
                                    have p1147_2 := h1147c.2.2.1
                                    have p1147_3 := h1147c.2.2.2
                                    linarith only [hlam, p1147_0]
                            · linarith only [h0, h1079, h1086, h1141, h1142, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · linarith only [h1085, h1087, h1141, hc23, hlam, hphi, ht34, u4elo4]
                      · linarith only [h0, h1084, h1138, hlam]
                    · linarith only [h0, h1137, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h0, h1082, h1136, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1253 | h1253
                · linarith only [h1085, h1086, h1253, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1255 | h1255
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1256 | h1256
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1257 | h1257
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1258 | h1258
                        · linarith only [h1080, h1253, h1258, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1260 | h1260
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1261 | h1261
                            · linarith only [h1079, h1086, h1255, h1261, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1263 | h1263
                              · linarith only [h1080, h1085, h1086, h1253, h1256, h1263, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1265 | h1265
                                · linarith only [h1079, h1253, h1255, h1260, h1265, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                · linarith only [h1085, h1086, h1265, hc34, hlam, hphi, u4elo4]
                          · linarith only [h1085, h1086, h1260, hc23, hc35, hlam, hphi]
                      · linarith only [h0, h1084, h1257, hlam]
                    · linarith only [h0, h1256, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h0, h1082, h1255, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1272 | h1272
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1273 | h1273
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1274 | h1274
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1275 | h1275
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1276 | h1276
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1277 | h1277
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1278 | h1278
                          · linarith only [h1079, h1085, h1274, h1278, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1280 | h1280
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1281 | h1281
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1282 | h1282
                                · rcases h0bigk with h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c
                                  · have p1283_0 := h1283c.1
                                    have p1283_1 := h1283c.2.1
                                    have p1283_2 := h1283c.2.2.1
                                    have p1283_3 := h1283c.2.2.2
                                    linarith only [hlam, p1283_0]
                                  · have p1283_0 := h1283c.1
                                    have p1283_1 := h1283c.2.1
                                    have p1283_2 := h1283c.2.2.1
                                    have p1283_3 := h1283c.2.2.2
                                    linarith only [h0, hlam, p1283_1]
                                  · have p1283_0 := h1283c.1
                                    have p1283_1 := h1283c.2.1
                                    have p1283_2 := h1283c.2.2.1
                                    have p1283_3 := h1283c.2.2.2
                                    linarith only [h0, h1082, h1280, h1282, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1283_1]
                                  · have p1283_0 := h1283c.1
                                    have p1283_1 := h1283c.2.1
                                    have p1283_2 := h1283c.2.2.1
                                    have p1283_3 := h1283c.2.2.2
                                    linarith only [h0, h1080, h1275, h1278, h1280, h1282, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1283_1]
                                  · have p1283_0 := h1283c.1
                                    have p1283_1 := h1283c.2.1
                                    have p1283_2 := h1283c.2.2.1
                                    have p1283_3 := h1283c.2.2.2
                                    rcases p1283_3 (m.d 0 1) (by simp) with h1288 | h1288
                                    · rcases p1283_3 (m.d 0 2) (by simp) with h1289 | h1289
                                      · rcases p1283_3 (m.d 0 3) (by simp) with h1290 | h1290
                                        · linarith only [h1079, h1290, hlam]
                                        · linarith only [h1272, h1290, hlam]
                                      · linarith only [h1084, h1289, hlam]
                                    · linarith only [h1081, h1288, hlam]
                                  · have p1283_0 := h1283c.1
                                    have p1283_1 := h1283c.2.1
                                    have p1283_2 := h1283c.2.2.1
                                    have p1283_3 := h1283c.2.2.2
                                    linarith only [h1079, h1274, h1280, h1282, hc45, hlam, hphi, ht0b, ht5b, p1283_1, u0elo1]
                                  · have p1283_0 := h1283c.1
                                    have p1283_1 := h1283c.2.1
                                    have p1283_2 := h1283c.2.2.1
                                    have p1283_3 := h1283c.2.2.2
                                    linarith only [hlam, p1283_0]
                                  · have p1283_0 := h1283c.1
                                    have p1283_1 := h1283c.2.1
                                    have p1283_2 := h1283c.2.2.1
                                    have p1283_3 := h1283c.2.2.2
                                    linarith only [h1079, h1274, h1280, h1282, hc45, hlam, hphi, ht0b, ht5b, p1283_1, u0elo1]
                                  · have p1283_0 := h1283c.1
                                    have p1283_1 := h1283c.2.1
                                    have p1283_2 := h1283c.2.2.1
                                    have p1283_3 := h1283c.2.2.2
                                    linarith only [h1080, h1275, h1278, h1280, h1282, hc45, hlam, hphi, ht0b, ht5b, p1283_1, u0elo1]
                                  · have p1283_0 := h1283c.1
                                    have p1283_1 := h1283c.2.1
                                    have p1283_2 := h1283c.2.2.1
                                    have p1283_3 := h1283c.2.2.2
                                    rcases p1283_3 (m.d 0 1) (by simp) with h1299 | h1299
                                    · linarith only [h0, h1299, hlam]
                                    · linarith only [h1081, h1299, hlam]
                                  · have p1283_0 := h1283c.1
                                    have p1283_1 := h1283c.2.1
                                    have p1283_2 := h1283c.2.2.1
                                    have p1283_3 := h1283c.2.2.2
                                    linarith only [h1079, hlam, p1283_1]
                                  · have p1283_0 := h1283c.1
                                    have p1283_1 := h1283c.2.1
                                    have p1283_2 := h1283c.2.2.1
                                    have p1283_3 := h1283c.2.2.2
                                    linarith only [h1082, hlam, p1283_1]
                                  · have p1283_0 := h1283c.1
                                    have p1283_1 := h1283c.2.1
                                    have p1283_2 := h1283c.2.2.1
                                    have p1283_3 := h1283c.2.2.2
                                    linarith only [hlam, p1283_0]
                                  · have p1283_0 := h1283c.1
                                    have p1283_1 := h1283c.2.1
                                    have p1283_2 := h1283c.2.2.1
                                    have p1283_3 := h1283c.2.2.2
                                    linarith only [h1085, hlam, p1283_1]
                                  · have p1283_0 := h1283c.1
                                    have p1283_1 := h1283c.2.1
                                    have p1283_2 := h1283c.2.2.1
                                    have p1283_3 := h1283c.2.2.2
                                    linarith only [h1081, h1085, h1276, h1280, h1282, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1283_1, u4elo3]
                                  · have p1283_0 := h1283c.1
                                    have p1283_1 := h1283c.2.1
                                    have p1283_2 := h1283c.2.2.1
                                    have p1283_3 := h1283c.2.2.2
                                    linarith only [h1080, hlam, p1283_0]
                                  · have p1283_0 := h1283c.1
                                    have p1283_1 := h1283c.2.1
                                    have p1283_2 := h1283c.2.2.1
                                    have p1283_3 := h1283c.2.2.2
                                    linarith only [h1083, hlam, p1283_0]
                                  · have p1283_0 := h1283c.1
                                    have p1283_1 := h1283c.2.1
                                    have p1283_2 := h1283c.2.2.1
                                    have p1283_3 := h1283c.2.2.2
                                    linarith only [hc03, hlam, hphi, ht34, p1283_1, u4elo0]
                                  · have p1283_0 := h1283c.1
                                    have p1283_1 := h1283c.2.1
                                    have p1283_2 := h1283c.2.2.1
                                    have p1283_3 := h1283c.2.2.2
                                    linarith only [hlam, p1283_0]
                                  · have p1283_0 := h1283c.1
                                    have p1283_1 := h1283c.2.1
                                    have p1283_2 := h1283c.2.2.1
                                    have p1283_3 := h1283c.2.2.2
                                    rcases p1283_3 (m.d 0 1) (by simp) with h1311 | h1311
                                    · rcases p1283_3 (m.d 0 2) (by simp) with h1312 | h1312
                                      · rcases p1283_3 (m.d 0 3) (by simp) with h1313 | h1313
                                        · linarith only [h1085, h1313, hlam]
                                        · linarith only [h1272, h1313, hlam]
                                      · linarith only [h1084, h1312, hlam]
                                    · linarith only [h1081, h1311, hlam]
                                  · have p1283_0 := h1283c.1
                                    have p1283_1 := h1283c.2.1
                                    have p1283_2 := h1283c.2.2.1
                                    have p1283_3 := h1283c.2.2.2
                                    linarith only [h1081, hlam, p1283_0]
                                  · have p1283_0 := h1283c.1
                                    have p1283_1 := h1283c.2.1
                                    have p1283_2 := h1283c.2.2.1
                                    have p1283_3 := h1283c.2.2.2
                                    linarith only [h1084, hlam, p1283_1]
                                  · have p1283_0 := h1283c.1
                                    have p1283_1 := h1283c.2.1
                                    have p1283_2 := h1283c.2.2.1
                                    have p1283_3 := h1283c.2.2.2
                                    linarith only [h1272, hlam, p1283_0]
                                  · have p1283_0 := h1283c.1
                                    have p1283_1 := h1283c.2.1
                                    have p1283_2 := h1283c.2.2.1
                                    have p1283_3 := h1283c.2.2.2
                                    linarith only [h1273, hlam, p1283_1]
                                  · have p1283_0 := h1283c.1
                                    have p1283_1 := h1283c.2.1
                                    have p1283_2 := h1283c.2.2.1
                                    have p1283_3 := h1283c.2.2.2
                                    linarith only [hlam, p1283_0]
                                · linarith only [h1085, h1282, hc03, hlam, hphi, ht34, u4elo4]
                              · linarith only [h1081, h1277, h1278, h1280, h1281, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                            · linarith only [h1085, h1272, h1280, hc23, hc34, hlam, hphi]
                        · linarith only [h1085, h1273, h1277, hc14, hlam, hphi, u4elo3]
                      · linarith only [h0, h1084, h1276, hlam]
                    · linarith only [h0, h1079, h1274, h1275, hc23, hlam, hphi, ht34, u4elo2]
                  · linarith only [h0, h1082, h1274, hlam]
                · linarith only [h1085, h1272, h1273, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1331 | h1331
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1332 | h1332
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1333 | h1333
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1334 | h1334
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1335 | h1335
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1336 | h1336
                          · linarith only [h1079, h1085, h1332, h1336, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1338 | h1338
                            · linarith only [h1079, h1272, h1332, h1338, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1340 | h1340
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1341 | h1341
                                · rcases h0bigk with h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c
                                  · have p1342_0 := h1342c.1
                                    have p1342_1 := h1342c.2.1
                                    have p1342_2 := h1342c.2.2.1
                                    have p1342_3 := h1342c.2.2.2
                                    linarith only [hlam, p1342_0]
                                  · have p1342_0 := h1342c.1
                                    have p1342_1 := h1342c.2.1
                                    have p1342_2 := h1342c.2.2.1
                                    have p1342_3 := h1342c.2.2.2
                                    linarith only [h0, hlam, p1342_1]
                                  · have p1342_0 := h1342c.1
                                    have p1342_1 := h1342c.2.1
                                    have p1342_2 := h1342c.2.2.1
                                    have p1342_3 := h1342c.2.2.2
                                    rcases p1342_3 (m.d 0 1) (by simp) with h1345 | h1345
                                    · rcases p1342_3 (m.d 0 2) (by simp) with h1346 | h1346
                                      · rcases p1342_3 (m.d 0 3) (by simp) with h1347 | h1347
                                        · linarith only [h1079, h1347, hlam]
                                        · rcases p1342_3 (m.d 0 4) (by simp) with h1349 | h1349
                                          · linarith only [h1080, h1349, hlam]
                                          · linarith only [h1085, h1349, hlam]
                                      · linarith only [h1082, h1346, hlam]
                                    · linarith only [h1079, h1345, hlam]
                                  · have p1342_0 := h1342c.1
                                    have p1342_1 := h1342c.2.1
                                    have p1342_2 := h1342c.2.2.1
                                    have p1342_3 := h1342c.2.2.2
                                    linarith only [h0, h1080, h1333, h1340, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1342_1]
                                  · have p1342_0 := h1342c.1
                                    have p1342_1 := h1342c.2.1
                                    have p1342_2 := h1342c.2.2.1
                                    have p1342_3 := h1342c.2.2.2
                                    rcases p1342_3 (m.d 0 1) (by simp) with h1355 | h1355
                                    · rcases p1342_3 (m.d 0 2) (by simp) with h1356 | h1356
                                      · rcases p1342_3 (m.d 0 3) (by simp) with h1357 | h1357
                                        · linarith only [h1079, h1357, hlam]
                                        · rcases p1342_3 (m.d 0 4) (by simp) with h1359 | h1359
                                          · linarith only [h1080, h1359, hlam]
                                          · linarith only [h1331, h1359, hlam]
                                      · linarith only [h1084, h1356, hlam]
                                    · linarith only [h1081, h1355, hlam]
                                  · have p1342_0 := h1342c.1
                                    have p1342_1 := h1342c.2.1
                                    have p1342_2 := h1342c.2.2.1
                                    have p1342_3 := h1342c.2.2.2
                                    linarith only [h1079, h1332, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1342_1, u0elo1]
                                  · have p1342_0 := h1342c.1
                                    have p1342_1 := h1342c.2.1
                                    have p1342_2 := h1342c.2.2.1
                                    have p1342_3 := h1342c.2.2.2
                                    linarith only [hlam, p1342_0]
                                  · have p1342_0 := h1342c.1
                                    have p1342_1 := h1342c.2.1
                                    have p1342_2 := h1342c.2.2.1
                                    have p1342_3 := h1342c.2.2.2
                                    rcases p1342_3 (m.d 0 1) (by simp) with h1366 | h1366
                                    · linarith only [h0, h1366, hlam]
                                    · linarith only [h1079, h1366, hlam]
                                  · have p1342_0 := h1342c.1
                                    have p1342_1 := h1342c.2.1
                                    have p1342_2 := h1342c.2.2.1
                                    have p1342_3 := h1342c.2.2.2
                                    linarith only [h1080, h1333, h1340, hc45, hlam, hphi, ht0b, ht5b, p1342_1, u0elo1]
                                  · have p1342_0 := h1342c.1
                                    have p1342_1 := h1342c.2.1
                                    have p1342_2 := h1342c.2.2.1
                                    have p1342_3 := h1342c.2.2.2
                                    rcases p1342_3 (m.d 0 1) (by simp) with h1370 | h1370
                                    · linarith only [h0, h1370, hlam]
                                    · linarith only [h1081, h1370, hlam]
                                  · have p1342_0 := h1342c.1
                                    have p1342_1 := h1342c.2.1
                                    have p1342_2 := h1342c.2.2.1
                                    have p1342_3 := h1342c.2.2.2
                                    linarith only [h1079, hlam, p1342_1]
                                  · have p1342_0 := h1342c.1
                                    have p1342_1 := h1342c.2.1
                                    have p1342_2 := h1342c.2.2.1
                                    have p1342_3 := h1342c.2.2.2
                                    linarith only [h1082, hlam, p1342_1]
                                  · have p1342_0 := h1342c.1
                                    have p1342_1 := h1342c.2.1
                                    have p1342_2 := h1342c.2.2.1
                                    have p1342_3 := h1342c.2.2.2
                                    linarith only [hlam, p1342_0]
                                  · have p1342_0 := h1342c.1
                                    have p1342_1 := h1342c.2.1
                                    have p1342_2 := h1342c.2.2.1
                                    have p1342_3 := h1342c.2.2.2
                                    linarith only [h1085, hlam, p1342_1]
                                  · have p1342_0 := h1342c.1
                                    have p1342_1 := h1342c.2.1
                                    have p1342_2 := h1342c.2.2.1
                                    have p1342_3 := h1342c.2.2.2
                                    linarith only [h1272, hlam, p1342_1]
                                  · have p1342_0 := h1342c.1
                                    have p1342_1 := h1342c.2.1
                                    have p1342_2 := h1342c.2.2.1
                                    have p1342_3 := h1342c.2.2.2
                                    linarith only [h1080, hlam, p1342_0]
                                  · have p1342_0 := h1342c.1
                                    have p1342_1 := h1342c.2.1
                                    have p1342_2 := h1342c.2.2.1
                                    have p1342_3 := h1342c.2.2.2
                                    linarith only [h1083, hlam, p1342_0]
                                  · have p1342_0 := h1342c.1
                                    have p1342_1 := h1342c.2.1
                                    have p1342_2 := h1342c.2.2.1
                                    have p1342_3 := h1342c.2.2.2
                                    linarith only [h1079, h1332, hc23, hlam, hphi, ht34, p1342_1, u4elo0]
                                  · have p1342_0 := h1342c.1
                                    have p1342_1 := h1342c.2.1
                                    have p1342_2 := h1342c.2.2.1
                                    have p1342_3 := h1342c.2.2.2
                                    linarith only [hlam, p1342_0]
                                  · have p1342_0 := h1342c.1
                                    have p1342_1 := h1342c.2.1
                                    have p1342_2 := h1342c.2.2.1
                                    have p1342_3 := h1342c.2.2.2
                                    linarith only [h1079, h1085, h1272, h1332, hc23, hlam, hphi, ht34, p1342_1, u4elo3]
                                  · have p1342_0 := h1342c.1
                                    have p1342_1 := h1342c.2.1
                                    have p1342_2 := h1342c.2.2.1
                                    have p1342_3 := h1342c.2.2.2
                                    linarith only [h1081, hlam, p1342_0]
                                  · have p1342_0 := h1342c.1
                                    have p1342_1 := h1342c.2.1
                                    have p1342_2 := h1342c.2.2.1
                                    have p1342_3 := h1342c.2.2.2
                                    linarith only [h1084, hlam, p1342_1]
                                  · have p1342_0 := h1342c.1
                                    have p1342_1 := h1342c.2.1
                                    have p1342_2 := h1342c.2.2.1
                                    have p1342_3 := h1342c.2.2.2
                                    linarith only [h1079, h1085, h1331, h1332, hc23, hlam, hphi, ht34, p1342_1, u4elo3]
                                  · have p1342_0 := h1342c.1
                                    have p1342_1 := h1342c.2.1
                                    have p1342_2 := h1342c.2.2.1
                                    have p1342_3 := h1342c.2.2.2
                                    linarith only [h1331, hlam, p1342_1]
                                  · have p1342_0 := h1342c.1
                                    have p1342_1 := h1342c.2.1
                                    have p1342_2 := h1342c.2.2.1
                                    have p1342_3 := h1342c.2.2.2
                                    linarith only [hlam, p1342_0]
                                · linarith only [h1080, h1085, h1333, h1340, h1341, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · linarith only [h1080, h1335, h1336, h1340, hc23, hlam, hphi, ht34, u4elo0]
                        · linarith only [h1085, h1331, h1335, hc14, hlam, hphi, u4elo3]
                      · linarith only [h0, h1084, h1334, hlam]
                    · linarith only [h0, h1333, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h0, h1082, h1332, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1394 | h1394
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1395 | h1395
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1396 | h1396
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1397 | h1397
                        · linarith only [h1080, h1085, h1331, h1397, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1399 | h1399
                          · linarith only [h1079, h1085, h1394, h1399, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1401 | h1401
                            · linarith only [h1079, h1272, h1394, h1401, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1403 | h1403
                              · linarith only [h1080, h1331, h1395, h1403, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1405 | h1405
                                · linarith only [h1331, h1405, hc04, hlam, hphi, u4elo3]
                                · linarith only [h1079, h1085, h1394, h1405, hc23, hlam, hphi, ht34, u4elo4]
                      · linarith only [h0, h1084, h1396, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1395, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h0, h1082, h1394, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · linarith only [h0, h1081, h1084, hlam]
        · linarith only [h0, h1079, h1083, hc13, hlam, hphi, ht34, u4elo2]
      · linarith only [h0, h1079, h1082, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1414 | h1414
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1415 | h1415
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1416 | h1416
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1417 | h1417
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1418 | h1418
              · linarith only [h1079, h1081, h1418, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1420 | h1420
                · linarith only [h1079, h1081, h1417, h1420, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1422 | h1422
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1423 | h1423
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1424 | h1424
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1425 | h1425
                        · linarith only [h1080, h1420, h1425, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h1079, h1081, h1425, hc13, hlam, hphi, ht34, u4elo4]
                      · linarith only [h0, h1079, h1416, h1422, h1424, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1079, h1422, h1423, hc23, hlam, hphi, ht34, u4elo2]
                  · linarith only [h0, h1414, h1422, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1431 | h1431
              · linarith only [h1079, h1081, h1431, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1433 | h1433
                · linarith only [h1080, h1081, h1433, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1435 | h1435
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1436 | h1436
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1437 | h1437
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1438 | h1438
                        · linarith only [h1080, h1417, h1433, h1438, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h1079, h1081, h1435, h1438, hc23, hlam, hphi, ht34, u4elo4]
                      · linarith only [h0, h1079, h1416, h1435, h1437, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1079, h1435, h1436, hc23, hlam, hphi, ht34, u4elo2]
                  · linarith only [h0, h1414, h1435, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1444 | h1444
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1445 | h1445
              · linarith only [h0, h1079, h1416, h1445, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1447 | h1447
                · linarith only [h0, h1080, h1416, h1447, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1449 | h1449
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1450 | h1450
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1451 | h1451
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1452 | h1452
                        · linarith only [h1447, h1452, hc04, hlam, hphi, u4elo1]
                        · linarith only [h0, h1079, h1416, h1449, h1451, h1452, hc23, hlam, hphi, ht34, u4elo4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1455 | h1455
                        · linarith only [h0, h1080, h1451, h1455, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h1080, h1081, h1455, hc14, hlam, hphi, u4elo4]
                    · linarith only [h0, h1079, h1449, h1450, hc23, hlam, hphi, ht34, u4elo2]
                  · linarith only [h0, h1414, h1449, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1460 | h1460
              · linarith only [h1079, h1081, h1460, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1462 | h1462
                · linarith only [h0, h1080, h1416, h1462, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1464 | h1464
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1465 | h1465
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1466 | h1466
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1467 | h1467
                        · linarith only [h0, h1080, h1416, h1444, h1462, h1466, h1467, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h0, h1079, h1416, h1464, h1466, h1467, hc23, hlam, hphi, ht34, u4elo4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1470 | h1470
                        · linarith only [h0, h1080, h1466, h1470, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h1079, h1081, h1464, h1470, hc23, hlam, hphi, ht34, u4elo4]
                    · linarith only [h0, h1079, h1464, h1465, hc23, hlam, hphi, ht34, u4elo2]
                  · linarith only [h0, h1414, h1464, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
        · linarith only [h0, h1079, h1415, hc13, hlam, hphi, ht34, u4elo2]
      · linarith only [h0, h1079, h1414, hlam]
  · linarith only [h1079, h1080, hc13, hlam, hphi, ht34, u4elo1]

set_option maxHeartbeats 5286000 in
set_option maxHeartbeats 5286000 in
theorem r1l7_20_12_14_M_LI_L_I_L_0_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1079 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1478 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1479 | h1479
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1480 | h1480
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1481 | h1481
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1482 | h1482
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1483 | h1483
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1484 | h1484
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1485 | h1485
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1486 | h1486
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1487 | h1487
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1488 | h1488
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1489 | h1489
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1490 | h1490
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1491 | h1491
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1492 | h1492
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1493 | h1493
                              · linarith only [h1480, h1490, h1493, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                              · linarith only [h1478, h1487, h1492, h1493, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h1485, h1492, hc24, hlam, hphi, u4elo0]
                          · linarith only [h1484, h1485, h1490, h1491, hc34, hlam, hphi, u4elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1498 | h1498
                          · linarith only [h1483, h1490, h1498, hc35, hlam, hphi, ht0b, ht5b, u0elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1500 | h1500
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1501 | h1501
                              · rcases h0bigk with h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [hlam, p1502_0]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h0, hlam, p1502_1]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1079, hlam, p1502_0]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1079, h1484, h1485, h1486, h1498, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1502_1]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1079, h1484, h1486, h1498, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1502_1]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1478, hc14, hlam, hphi, ht0b, ht45, ht5b, p1502_1, u0elo1]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [hlam, p1502_0]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1079, h1478, h1487, h1500, hc45, hlam, hphi, ht0b, ht5b, p1502_1, u0elo1]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1478, h1487, h1500, hc45, hlam, hphi, ht0b, ht5b, p1502_1, u0elo1]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1484, h1498, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1502_1, u0elo1]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1478, h1487, h1500, hc45, hlam, hphi, ht0b, ht5b, p1502_1, u0elo2]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1480, hlam, p1502_1]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [hlam, p1502_0]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1478, h1480, h1487, h1500, hc45, hlam, hphi, ht0b, ht5b, p1502_1, u0elo1]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1480, h1484, h1498, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1502_1, u0elo1]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1478, hlam, p1502_0]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1481, hlam, p1502_0]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1483, hlam, p1502_0]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [hlam, p1502_0]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1484, h1498, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1502_1, u0elo3]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1479, hlam, p1502_0]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1482, hlam, p1502_1]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1484, hlam, p1502_0]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1485, hlam, p1502_1]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [hlam, p1502_0]
                              · linarith only [h1478, h1487, h1500, h1501, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h1485, h1500, hc24, hlam, hphi, u4elo0]
                      · linarith only [h1485, h1489, hc14, hlam, hphi, u4elo0]
                    · linarith only [h0, h1482, h1488, hlam]
                  · linarith only [h1079, h1486, h1487, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h1480, h1486, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1534 | h1534
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1535 | h1535
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1536 | h1536
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1537 | h1537
                      · linarith only [h1478, h1485, h1537, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1539 | h1539
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1540 | h1540
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1541 | h1541
                            · linarith only [h1478, h1485, h1535, h1541, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1543 | h1543
                              · linarith only [h1480, h1485, h1539, h1543, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · rcases h0bigk with h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c
                                · have p1545_0 := h1545c.1
                                  have p1545_1 := h1545c.2.1
                                  have p1545_2 := h1545c.2.2.1
                                  have p1545_3 := h1545c.2.2.2
                                  linarith only [hlam, p1545_0]
                                · have p1545_0 := h1545c.1
                                  have p1545_1 := h1545c.2.1
                                  have p1545_2 := h1545c.2.2.1
                                  have p1545_3 := h1545c.2.2.2
                                  linarith only [h0, hlam, p1545_1]
                                · have p1545_0 := h1545c.1
                                  have p1545_1 := h1545c.2.1
                                  have p1545_2 := h1545c.2.2.1
                                  have p1545_3 := h1545c.2.2.2
                                  linarith only [h1079, hlam, p1545_0]
                                · have p1545_0 := h1545c.1
                                  have p1545_1 := h1545c.2.1
                                  have p1545_2 := h1545c.2.2.1
                                  have p1545_3 := h1545c.2.2.2
                                  rcases p1545_3 (m.d 0 1) (by simp) with h1549 | h1549
                                  · rcases p1545_3 (m.d 0 2) (by simp) with h1550 | h1550
                                    · rcases p1545_3 (m.d 0 3) (by simp) with h1551 | h1551
                                      · rcases p1545_3 (m.d 0 4) (by simp) with h1552 | h1552
                                        · linarith only [h1478, h1552, hlam]
                                        · rcases p1545_3 (m.d 0 5) (by simp) with h1554 | h1554
                                          · linarith only [h1479, h1554, hlam]
                                          · linarith only [h1485, h1554, hlam]
                                      · linarith only [h1483, h1551, hlam]
                                    · linarith only [h1481, h1550, hlam]
                                  · linarith only [h1478, h1549, hlam]
                                · have p1545_0 := h1545c.1
                                  have p1545_1 := h1545c.2.1
                                  have p1545_2 := h1545c.2.2.1
                                  have p1545_3 := h1545c.2.2.2
                                  rcases p1545_3 (m.d 0 1) (by simp) with h1560 | h1560
                                  · rcases p1545_3 (m.d 0 2) (by simp) with h1561 | h1561
                                    · rcases p1545_3 (m.d 0 3) (by simp) with h1562 | h1562
                                      · rcases p1545_3 (m.d 0 4) (by simp) with h1563 | h1563
                                        · linarith only [h1478, h1563, hlam]
                                        · rcases p1545_3 (m.d 0 5) (by simp) with h1565 | h1565
                                          · linarith only [h1479, h1565, hlam]
                                          · rcases h2bigk with h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c | h1567c
                                            · have p1567_0 := h1567c.1
                                              have p1567_1 := h1567c.2.1
                                              have p1567_2 := h1567c.2.2.1
                                              have p1567_3 := h1567c.2.2.2
                                              linarith only [hlam, p1567_0]
                                            · have p1567_0 := h1567c.1
                                              have p1567_1 := h1567c.2.1
                                              have p1567_2 := h1567c.2.2.1
                                              have p1567_3 := h1567c.2.2.2
                                              linarith only [h0, hlam, p1567_1]
                                            · have p1567_0 := h1567c.1
                                              have p1567_1 := h1567c.2.1
                                              have p1567_2 := h1567c.2.2.1
                                              have p1567_3 := h1567c.2.2.2
                                              linarith only [h1539, hc34, hlam, hphi, ht0b, ht45, ht5b, p1567_1, u0elo1]
                                            · have p1567_0 := h1567c.1
                                              have p1567_1 := h1567c.2.1
                                              have p1567_2 := h1567c.2.2.1
                                              have p1567_3 := h1567c.2.2.2
                                              rcases p1567_3 (m.d 0 2) (by simp) with h1571 | h1571
                                              · rcases p1567_3 (m.d 1 2) (by simp) with h1572 | h1572
                                                · rcases p1567_3 (m.d 2 3) (by simp) with h1573 | h1573
                                                  · linarith only [h1480, h1573, hlam]
                                                  · linarith only [h1539, h1573, hlam]
                                                · linarith only [h1535, h1572, hlam]
                                              · linarith only [h1571, hlam, p1567_0]
                                            · have p1567_0 := h1567c.1
                                              have p1567_1 := h1567c.2.1
                                              have p1567_2 := h1567c.2.2.1
                                              have p1567_3 := h1567c.2.2.2
                                              rcases p1567_3 (m.d 0 2) (by simp) with h1578 | h1578
                                              · rcases p1567_3 (m.d 1 2) (by simp) with h1579 | h1579
                                                · rcases p1567_3 (m.d 2 3) (by simp) with h1580 | h1580
                                                  · linarith only [h1480, h1580, hlam]
                                                  · linarith only [h1540, h1580, hlam]
                                                · linarith only [h1536, h1579, hlam]
                                              · linarith only [h1578, hlam, p1567_0]
                                            · have p1567_0 := h1567c.1
                                              have p1567_1 := h1567c.2.1
                                              have p1567_2 := h1567c.2.2.1
                                              have p1567_3 := h1567c.2.2.2
                                              linarith only [h1079, h1478, h1480, h1485, h1535, h1539, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1545_1, p1567_1]
                                            · have p1567_0 := h1567c.1
                                              have p1567_1 := h1567c.2.1
                                              have p1567_2 := h1567c.2.2.1
                                              have p1567_3 := h1567c.2.2.2
                                              linarith only [hlam, p1567_0]
                                            · have p1567_0 := h1567c.1
                                              have p1567_1 := h1567c.2.1
                                              have p1567_2 := h1567c.2.2.1
                                              have p1567_3 := h1567c.2.2.2
                                              rcases p1567_3 (m.d 0 2) (by simp) with h1587 | h1587
                                              · linarith only [h0, h1587, hlam]
                                              · linarith only [h1480, h1587, hlam]
                                            · have p1567_0 := h1567c.1
                                              have p1567_1 := h1567c.2.1
                                              have p1567_2 := h1567c.2.2.1
                                              have p1567_3 := h1567c.2.2.2
                                              linarith only [h0, h1478, h1485, h1535, hlam, p1545_1, p1567_2]
                                            · have p1567_0 := h1567c.1
                                              have p1567_1 := h1567c.2.1
                                              have p1567_2 := h1567c.2.2.1
                                              have p1567_3 := h1567c.2.2.2
                                              linarith only [h1079, h1482, h1534, hlam, p1545_1, p1567_2]
                                            · have p1567_0 := h1567c.1
                                              have p1567_1 := h1567c.2.1
                                              have p1567_2 := h1567c.2.2.1
                                              have p1567_3 := h1567c.2.2.2
                                              linarith only [h1480, hlam, p1567_0]
                                            · have p1567_0 := h1567c.1
                                              have p1567_1 := h1567c.2.1
                                              have p1567_2 := h1567c.2.2.1
                                              have p1567_3 := h1567c.2.2.2
                                              linarith only [h1534, hlam, p1567_0]
                                            · have p1567_0 := h1567c.1
                                              have p1567_1 := h1567c.2.1
                                              have p1567_2 := h1567c.2.2.1
                                              have p1567_3 := h1567c.2.2.2
                                              linarith only [hlam, p1567_0]
                                            · have p1567_0 := h1567c.1
                                              have p1567_1 := h1567c.2.1
                                              have p1567_2 := h1567c.2.2.1
                                              have p1567_3 := h1567c.2.2.2
                                              linarith only [h1480, h1539, hc34, hlam, hphi, ht0b, ht45, ht5b, p1567_1, u0elo1]
                                            · have p1567_0 := h1567c.1
                                              have p1567_1 := h1567c.2.1
                                              have p1567_2 := h1567c.2.2.1
                                              have p1567_3 := h1567c.2.2.2
                                              linarith only [h1480, hc25, hlam, hphi, ht0b, ht5b, p1567_1, u0elo1]
                                            · have p1567_0 := h1567c.1
                                              have p1567_1 := h1567c.2.1
                                              have p1567_2 := h1567c.2.2.1
                                              have p1567_3 := h1567c.2.2.2
                                              linarith only [h1481, hlam, p1567_0]
                                            · have p1567_0 := h1567c.1
                                              have p1567_1 := h1567c.2.1
                                              have p1567_2 := h1567c.2.2.1
                                              have p1567_3 := h1567c.2.2.2
                                              linarith only [h1535, hlam, p1567_0]
                                            · have p1567_0 := h1567c.1
                                              have p1567_1 := h1567c.2.1
                                              have p1567_2 := h1567c.2.2.1
                                              have p1567_3 := h1567c.2.2.2
                                              linarith only [h1539, hlam, p1567_1]
                                            · have p1567_0 := h1567c.1
                                              have p1567_1 := h1567c.2.1
                                              have p1567_2 := h1567c.2.2.1
                                              have p1567_3 := h1567c.2.2.2
                                              linarith only [hlam, p1567_0]
                                            · have p1567_0 := h1567c.1
                                              have p1567_1 := h1567c.2.1
                                              have p1567_2 := h1567c.2.2.1
                                              have p1567_3 := h1567c.2.2.2
                                              linarith only [h1541, hlam, p1567_1]
                                            · have p1567_0 := h1567c.1
                                              have p1567_1 := h1567c.2.1
                                              have p1567_2 := h1567c.2.2.1
                                              have p1567_3 := h1567c.2.2.2
                                              linarith only [h1482, hlam, p1567_0]
                                            · have p1567_0 := h1567c.1
                                              have p1567_1 := h1567c.2.1
                                              have p1567_2 := h1567c.2.2.1
                                              have p1567_3 := h1567c.2.2.2
                                              linarith only [h1536, hlam, p1567_0]
                                            · have p1567_0 := h1567c.1
                                              have p1567_1 := h1567c.2.1
                                              have p1567_2 := h1567c.2.2.1
                                              have p1567_3 := h1567c.2.2.2
                                              linarith only [h1540, hlam, p1567_1]
                                            · have p1567_0 := h1567c.1
                                              have p1567_1 := h1567c.2.1
                                              have p1567_2 := h1567c.2.2.1
                                              have p1567_3 := h1567c.2.2.2
                                              linarith only [h1482, h1539, hc34, hlam, hphi, ht0b, ht45, ht5b, p1567_1, u0elo1]
                                            · have p1567_0 := h1567c.1
                                              have p1567_1 := h1567c.2.1
                                              have p1567_2 := h1567c.2.2.1
                                              have p1567_3 := h1567c.2.2.2
                                              linarith only [hlam, p1567_0]
                                      · linarith only [h1484, h1562, hlam]
                                    · linarith only [h1482, h1561, hlam]
                                  · linarith only [h1479, h1560, hlam]
                                · have p1545_0 := h1545c.1
                                  have p1545_1 := h1545c.2.1
                                  have p1545_2 := h1545c.2.2.1
                                  have p1545_3 := h1545c.2.2.2
                                  linarith only [h1478, h1535, h1539, hc34, hlam, hphi, ht0b, ht45, ht5b, p1545_1, u0elo1]
                                · have p1545_0 := h1545c.1
                                  have p1545_1 := h1545c.2.1
                                  have p1545_2 := h1545c.2.2.1
                                  have p1545_3 := h1545c.2.2.2
                                  linarith only [hlam, p1545_0]
                                · have p1545_0 := h1545c.1
                                  have p1545_1 := h1545c.2.1
                                  have p1545_2 := h1545c.2.2.1
                                  have p1545_3 := h1545c.2.2.2
                                  linarith only [h1079, h1478, h1535, h1539, hc34, hlam, hphi, ht0b, ht45, ht5b, p1545_1, u0elo1]
                                · have p1545_0 := h1545c.1
                                  have p1545_1 := h1545c.2.1
                                  have p1545_2 := h1545c.2.2.1
                                  have p1545_3 := h1545c.2.2.2
                                  rcases p1545_3 (m.d 0 1) (by simp) with h1613 | h1613
                                  · linarith only [h0, h1613, hlam]
                                  · linarith only [h1478, h1613, hlam]
                                · have p1545_0 := h1545c.1
                                  have p1545_1 := h1545c.2.1
                                  have p1545_2 := h1545c.2.2.1
                                  have p1545_3 := h1545c.2.2.2
                                  rcases p1545_3 (m.d 0 1) (by simp) with h1616 | h1616
                                  · linarith only [h0, h1616, hlam]
                                  · linarith only [h1479, h1616, hlam]
                                · have p1545_0 := h1545c.1
                                  have p1545_1 := h1545c.2.1
                                  have p1545_2 := h1545c.2.2.1
                                  have p1545_3 := h1545c.2.2.2
                                  linarith only [h1479, h1535, h1537, h1539, hc34, hlam, hphi, ht0b, ht45, ht5b, p1545_1, u0elo2]
                                · have p1545_0 := h1545c.1
                                  have p1545_1 := h1545c.2.1
                                  have p1545_2 := h1545c.2.2.1
                                  have p1545_3 := h1545c.2.2.2
                                  linarith only [h1480, hlam, p1545_1]
                                · have p1545_0 := h1545c.1
                                  have p1545_1 := h1545c.2.1
                                  have p1545_2 := h1545c.2.2.1
                                  have p1545_3 := h1545c.2.2.2
                                  linarith only [hlam, p1545_0]
                                · have p1545_0 := h1545c.1
                                  have p1545_1 := h1545c.2.1
                                  have p1545_2 := h1545c.2.2.1
                                  have p1545_3 := h1545c.2.2.2
                                  rcases p1545_3 (m.d 0 1) (by simp) with h1622 | h1622
                                  · linarith only [h1079, h1622, hlam]
                                  · linarith only [h1478, h1622, hlam]
                                · have p1545_0 := h1545c.1
                                  have p1545_1 := h1545c.2.1
                                  have p1545_2 := h1545c.2.2.1
                                  have p1545_3 := h1545c.2.2.2
                                  rcases p1545_3 (m.d 0 1) (by simp) with h1625 | h1625
                                  · linarith only [h1079, h1625, hlam]
                                  · linarith only [h1479, h1625, hlam]
                                · have p1545_0 := h1545c.1
                                  have p1545_1 := h1545c.2.1
                                  have p1545_2 := h1545c.2.2.1
                                  have p1545_3 := h1545c.2.2.2
                                  linarith only [h1478, hlam, p1545_0]
                                · have p1545_0 := h1545c.1
                                  have p1545_1 := h1545c.2.1
                                  have p1545_2 := h1545c.2.2.1
                                  have p1545_3 := h1545c.2.2.2
                                  linarith only [h1481, hlam, p1545_0]
                                · have p1545_0 := h1545c.1
                                  have p1545_1 := h1545c.2.1
                                  have p1545_2 := h1545c.2.2.1
                                  have p1545_3 := h1545c.2.2.2
                                  linarith only [h1483, hlam, p1545_0]
                                · have p1545_0 := h1545c.1
                                  have p1545_1 := h1545c.2.1
                                  have p1545_2 := h1545c.2.2.1
                                  have p1545_3 := h1545c.2.2.2
                                  linarith only [hlam, p1545_0]
                                · have p1545_0 := h1545c.1
                                  have p1545_1 := h1545c.2.1
                                  have p1545_2 := h1545c.2.2.1
                                  have p1545_3 := h1545c.2.2.2
                                  linarith only [h1485, hlam, p1545_0]
                                · have p1545_0 := h1545c.1
                                  have p1545_1 := h1545c.2.1
                                  have p1545_2 := h1545c.2.2.1
                                  have p1545_3 := h1545c.2.2.2
                                  linarith only [h1479, hlam, p1545_0]
                                · have p1545_0 := h1545c.1
                                  have p1545_1 := h1545c.2.1
                                  have p1545_2 := h1545c.2.2.1
                                  have p1545_3 := h1545c.2.2.2
                                  linarith only [h1482, hlam, p1545_1]
                                · have p1545_0 := h1545c.1
                                  have p1545_1 := h1545c.2.1
                                  have p1545_2 := h1545c.2.2.1
                                  have p1545_3 := h1545c.2.2.2
                                  linarith only [h1484, hlam, p1545_0]
                                · have p1545_0 := h1545c.1
                                  have p1545_1 := h1545c.2.1
                                  have p1545_2 := h1545c.2.2.1
                                  have p1545_3 := h1545c.2.2.2
                                  linarith only [h1478, h1485, h1535, h1539, hc34, hlam, hphi, p1545_1, u4elo4]
                                · have p1545_0 := h1545c.1
                                  have p1545_1 := h1545c.2.1
                                  have p1545_2 := h1545c.2.2.1
                                  have p1545_3 := h1545c.2.2.2
                                  linarith only [hlam, p1545_0]
                          · linarith only [h1480, h1484, h1539, h1540, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h1483, h1485, h1539, hc23, hlam, hphi, ht34, u4elo4]
                    · linarith only [h0, h1482, h1536, hlam]
                  · linarith only [h1079, h1534, h1535, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h1480, h1534, hlam]
            · linarith only [h1079, h1479, h1484, hlam]
          · linarith only [h1079, h1478, h1483, hc14, hlam, hphi, u4elo3]
        · linarith only [h0, h1479, h1482, hlam]
      · linarith only [h1079, h1478, h1480, h1481, hc14, hlam, hphi, u4elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1647 | h1647
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1648 | h1648
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1649 | h1649
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1650 | h1650
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1651 | h1651
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1652 | h1652
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1653 | h1653
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1654 | h1654
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1655 | h1655
                      · linarith only [h0, h1478, h1480, h1652, h1655, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h0, h1478, h1480, h1651, h1652, h1655, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h1480, h1652, h1654, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h1480, h1647, h1652, h1653, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1660 | h1660
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1661 | h1661
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1662 | h1662
                      · linarith only [h0, h1478, h1652, h1662, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h1478, h1651, h1652, h1662, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h1648, h1661, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h1478, h1660, hc14, hlam, hphi, u4elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1667 | h1667
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1668 | h1668
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1669 | h1669
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1670 | h1670
                      · linarith only [h1651, h1670, hc04, hlam, hphi, u4elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1672 | h1672
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1673 | h1673
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1674 | h1674
                            · linarith only [h1478, h1651, h1668, h1674, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1676 | h1676
                              · linarith only [h1478, h1651, h1668, h1672, h1676, hlam]
                              · rcases h0bigk with h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c
                                · have p1678_0 := h1678c.1
                                  have p1678_1 := h1678c.2.1
                                  have p1678_2 := h1678c.2.2.1
                                  have p1678_3 := h1678c.2.2.2
                                  linarith only [hlam, p1678_0]
                                · have p1678_0 := h1678c.1
                                  have p1678_1 := h1678c.2.1
                                  have p1678_2 := h1678c.2.2.1
                                  have p1678_3 := h1678c.2.2.2
                                  linarith only [h0, hlam, p1678_1]
                                · have p1678_0 := h1678c.1
                                  have p1678_1 := h1678c.2.1
                                  have p1678_2 := h1678c.2.2.1
                                  have p1678_3 := h1678c.2.2.2
                                  linarith only [h1079, hlam, p1678_0]
                                · have p1678_0 := h1678c.1
                                  have p1678_1 := h1678c.2.1
                                  have p1678_2 := h1678c.2.2.1
                                  have p1678_3 := h1678c.2.2.2
                                  linarith only [h0, h1478, h1480, h1667, h1668, h1672, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1678_1]
                                · have p1678_0 := h1678c.1
                                  have p1678_1 := h1678c.2.1
                                  have p1678_2 := h1678c.2.2.1
                                  have p1678_3 := h1678c.2.2.2
                                  linarith only [h0, h1478, h1480, h1651, h1667, h1668, h1672, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1678_1]
                                · have p1678_0 := h1678c.1
                                  have p1678_1 := h1678c.2.1
                                  have p1678_2 := h1678c.2.2.1
                                  have p1678_3 := h1678c.2.2.2
                                  linarith only [h1478, h1668, h1672, hc34, hlam, hphi, ht0b, ht45, ht5b, p1678_1, u0elo1]
                                · have p1678_0 := h1678c.1
                                  have p1678_1 := h1678c.2.1
                                  have p1678_2 := h1678c.2.2.1
                                  have p1678_3 := h1678c.2.2.2
                                  linarith only [hlam, p1678_0]
                                · have p1678_0 := h1678c.1
                                  have p1678_1 := h1678c.2.1
                                  have p1678_2 := h1678c.2.2.1
                                  have p1678_3 := h1678c.2.2.2
                                  linarith only [h1480, hlam, p1678_0]
                                · have p1678_0 := h1678c.1
                                  have p1678_1 := h1678c.2.1
                                  have p1678_2 := h1678c.2.2.1
                                  have p1678_3 := h1678c.2.2.2
                                  linarith only [h1478, h1480, h1667, h1668, h1672, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1678_1]
                                · have p1678_0 := h1678c.1
                                  have p1678_1 := h1678c.2.1
                                  have p1678_2 := h1678c.2.2.1
                                  have p1678_3 := h1678c.2.2.2
                                  linarith only [h1478, h1480, h1651, h1667, h1668, h1672, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1678_1]
                                · have p1678_0 := h1678c.1
                                  have p1678_1 := h1678c.2.1
                                  have p1678_2 := h1678c.2.2.1
                                  have p1678_3 := h1678c.2.2.2
                                  linarith only [h1479, h1480, h1667, h1668, h1670, h1672, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1678_1]
                                · have p1678_0 := h1678c.1
                                  have p1678_1 := h1678c.2.1
                                  have p1678_2 := h1678c.2.2.1
                                  have p1678_3 := h1678c.2.2.2
                                  linarith only [h0, h1479, h1480, h1667, h1668, h1670, h1672, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1678_1]
                                · have p1678_0 := h1678c.1
                                  have p1678_1 := h1678c.2.1
                                  have p1678_2 := h1678c.2.2.1
                                  have p1678_3 := h1678c.2.2.2
                                  linarith only [hlam, p1678_0]
                                · have p1678_0 := h1678c.1
                                  have p1678_1 := h1678c.2.1
                                  have p1678_2 := h1678c.2.2.1
                                  have p1678_3 := h1678c.2.2.2
                                  rcases p1678_3 (m.d 0 1) (by simp) with h1692 | h1692
                                  · linarith only [h1079, h1692, hlam]
                                  · linarith only [h1478, h1692, hlam]
                                · have p1678_0 := h1678c.1
                                  have p1678_1 := h1678c.2.1
                                  have p1678_2 := h1678c.2.2.1
                                  have p1678_3 := h1678c.2.2.2
                                  rcases p1678_3 (m.d 0 1) (by simp) with h1695 | h1695
                                  · linarith only [h1079, h1695, hlam]
                                  · linarith only [h1479, h1695, hlam]
                                · have p1678_0 := h1678c.1
                                  have p1678_1 := h1678c.2.1
                                  have p1678_2 := h1678c.2.2.1
                                  have p1678_3 := h1678c.2.2.2
                                  linarith only [h1478, hlam, p1678_0]
                                · have p1678_0 := h1678c.1
                                  have p1678_1 := h1678c.2.1
                                  have p1678_2 := h1678c.2.2.1
                                  have p1678_3 := h1678c.2.2.2
                                  linarith only [h1647, hlam, p1678_0]
                                · have p1678_0 := h1678c.1
                                  have p1678_1 := h1678c.2.1
                                  have p1678_2 := h1678c.2.2.1
                                  have p1678_3 := h1678c.2.2.2
                                  linarith only [h1649, hlam, p1678_0]
                                · have p1678_0 := h1678c.1
                                  have p1678_1 := h1678c.2.1
                                  have p1678_2 := h1678c.2.2.1
                                  have p1678_3 := h1678c.2.2.2
                                  linarith only [hlam, p1678_0]
                                · have p1678_0 := h1678c.1
                                  have p1678_1 := h1678c.2.1
                                  have p1678_2 := h1678c.2.2.1
                                  have p1678_3 := h1678c.2.2.2
                                  linarith only [h1651, hlam, p1678_0]
                                · have p1678_0 := h1678c.1
                                  have p1678_1 := h1678c.2.1
                                  have p1678_2 := h1678c.2.2.1
                                  have p1678_3 := h1678c.2.2.2
                                  linarith only [h1479, hlam, p1678_0]
                                · have p1678_0 := h1678c.1
                                  have p1678_1 := h1678c.2.1
                                  have p1678_2 := h1678c.2.2.1
                                  have p1678_3 := h1678c.2.2.2
                                  linarith only [h1648, hlam, p1678_1]
                                · have p1678_0 := h1678c.1
                                  have p1678_1 := h1678c.2.1
                                  have p1678_2 := h1678c.2.2.1
                                  have p1678_3 := h1678c.2.2.2
                                  linarith only [h1650, hlam, p1678_0]
                                · have p1678_0 := h1678c.1
                                  have p1678_1 := h1678c.2.1
                                  have p1678_2 := h1678c.2.2.1
                                  have p1678_3 := h1678c.2.2.2
                                  linarith only [h0, h1478, h1479, h1480, h1667, h1668, h1672, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1678_1]
                                · have p1678_0 := h1678c.1
                                  have p1678_1 := h1678c.2.1
                                  have p1678_2 := h1678c.2.2.1
                                  have p1678_3 := h1678c.2.2.2
                                  linarith only [hlam, p1678_0]
                          · linarith only [h1480, h1650, h1673, hlam]
                        · linarith only [h0, h1480, h1672, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h1480, h1648, h1667, h1669, hlam]
                  · linarith only [h0, h1478, h1480, h1667, h1668, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1712 | h1712
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1713 | h1713
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1714 | h1714
                      · linarith only [h1478, h1651, h1714, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1716 | h1716
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1717 | h1717
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1718 | h1718
                            · linarith only [h1478, h1651, h1712, h1718, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1720 | h1720
                              · linarith only [h1478, h1651, h1712, h1716, h1720, hlam]
                              · rcases h0bigk with h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c | h1722c
                                · have p1722_0 := h1722c.1
                                  have p1722_1 := h1722c.2.1
                                  have p1722_2 := h1722c.2.2.1
                                  have p1722_3 := h1722c.2.2.2
                                  linarith only [hlam, p1722_0]
                                · have p1722_0 := h1722c.1
                                  have p1722_1 := h1722c.2.1
                                  have p1722_2 := h1722c.2.2.1
                                  have p1722_3 := h1722c.2.2.2
                                  linarith only [h0, hlam, p1722_1]
                                · have p1722_0 := h1722c.1
                                  have p1722_1 := h1722c.2.1
                                  have p1722_2 := h1722c.2.2.1
                                  have p1722_3 := h1722c.2.2.2
                                  linarith only [h1079, hlam, p1722_0]
                                · have p1722_0 := h1722c.1
                                  have p1722_1 := h1722c.2.1
                                  have p1722_2 := h1722c.2.2.1
                                  have p1722_3 := h1722c.2.2.2
                                  linarith only [h0, h1478, h1667, h1712, h1716, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1722_1]
                                · have p1722_0 := h1722c.1
                                  have p1722_1 := h1722c.2.1
                                  have p1722_2 := h1722c.2.2.1
                                  have p1722_3 := h1722c.2.2.2
                                  linarith only [h0, h1667, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1722_1]
                                · have p1722_0 := h1722c.1
                                  have p1722_1 := h1722c.2.1
                                  have p1722_2 := h1722c.2.2.1
                                  have p1722_3 := h1722c.2.2.2
                                  linarith only [h0, h1667, hc01, hc23, hlam, hphi, ht12, p1722_1]
                                · have p1722_0 := h1722c.1
                                  have p1722_1 := h1722c.2.1
                                  have p1722_2 := h1722c.2.2.1
                                  have p1722_3 := h1722c.2.2.2
                                  linarith only [hlam, p1722_0]
                                · have p1722_0 := h1722c.1
                                  have p1722_1 := h1722c.2.1
                                  have p1722_2 := h1722c.2.2.1
                                  have p1722_3 := h1722c.2.2.2
                                  linarith only [h1480, hlam, p1722_0]
                                · have p1722_0 := h1722c.1
                                  have p1722_1 := h1722c.2.1
                                  have p1722_2 := h1722c.2.2.1
                                  have p1722_3 := h1722c.2.2.2
                                  rcases p1722_3 (m.d 0 1) (by simp) with h1731 | h1731
                                  · linarith only [h0, h1731, hlam]
                                  · linarith only [h1478, h1731, hlam]
                                · have p1722_0 := h1722c.1
                                  have p1722_1 := h1722c.2.1
                                  have p1722_2 := h1722c.2.2.1
                                  have p1722_3 := h1722c.2.2.2
                                  rcases p1722_3 (m.d 0 1) (by simp) with h1734 | h1734
                                  · linarith only [h0, h1734, hlam]
                                  · linarith only [h1479, h1734, hlam]
                                · have p1722_0 := h1722c.1
                                  have p1722_1 := h1722c.2.1
                                  have p1722_2 := h1722c.2.2.1
                                  have p1722_3 := h1722c.2.2.2
                                  linarith only [h1479, h1712, h1714, h1716, hc34, hlam, hphi, ht0b, ht45, ht5b, p1722_1, u0elo2]
                                · have p1722_0 := h1722c.1
                                  have p1722_1 := h1722c.2.1
                                  have p1722_2 := h1722c.2.2.1
                                  have p1722_3 := h1722c.2.2.2
                                  linarith only [h0, h1479, h1712, h1714, h1716, hc34, hlam, hphi, ht0b, ht45, ht5b, p1722_1, u0elo2]
                                · have p1722_0 := h1722c.1
                                  have p1722_1 := h1722c.2.1
                                  have p1722_2 := h1722c.2.2.1
                                  have p1722_3 := h1722c.2.2.2
                                  linarith only [hlam, p1722_0]
                                · have p1722_0 := h1722c.1
                                  have p1722_1 := h1722c.2.1
                                  have p1722_2 := h1722c.2.2.1
                                  have p1722_3 := h1722c.2.2.2
                                  rcases p1722_3 (m.d 0 1) (by simp) with h1740 | h1740
                                  · linarith only [h1079, h1740, hlam]
                                  · linarith only [h1478, h1740, hlam]
                                · have p1722_0 := h1722c.1
                                  have p1722_1 := h1722c.2.1
                                  have p1722_2 := h1722c.2.2.1
                                  have p1722_3 := h1722c.2.2.2
                                  rcases p1722_3 (m.d 0 1) (by simp) with h1743 | h1743
                                  · linarith only [h1079, h1743, hlam]
                                  · linarith only [h1479, h1743, hlam]
                                · have p1722_0 := h1722c.1
                                  have p1722_1 := h1722c.2.1
                                  have p1722_2 := h1722c.2.2.1
                                  have p1722_3 := h1722c.2.2.2
                                  linarith only [h1478, hlam, p1722_0]
                                · have p1722_0 := h1722c.1
                                  have p1722_1 := h1722c.2.1
                                  have p1722_2 := h1722c.2.2.1
                                  have p1722_3 := h1722c.2.2.2
                                  linarith only [h1647, hlam, p1722_0]
                                · have p1722_0 := h1722c.1
                                  have p1722_1 := h1722c.2.1
                                  have p1722_2 := h1722c.2.2.1
                                  have p1722_3 := h1722c.2.2.2
                                  linarith only [h1649, hlam, p1722_0]
                                · have p1722_0 := h1722c.1
                                  have p1722_1 := h1722c.2.1
                                  have p1722_2 := h1722c.2.2.1
                                  have p1722_3 := h1722c.2.2.2
                                  linarith only [hlam, p1722_0]
                                · have p1722_0 := h1722c.1
                                  have p1722_1 := h1722c.2.1
                                  have p1722_2 := h1722c.2.2.1
                                  have p1722_3 := h1722c.2.2.2
                                  linarith only [h1651, hlam, p1722_0]
                                · have p1722_0 := h1722c.1
                                  have p1722_1 := h1722c.2.1
                                  have p1722_2 := h1722c.2.2.1
                                  have p1722_3 := h1722c.2.2.2
                                  linarith only [h1479, hlam, p1722_0]
                                · have p1722_0 := h1722c.1
                                  have p1722_1 := h1722c.2.1
                                  have p1722_2 := h1722c.2.2.1
                                  have p1722_3 := h1722c.2.2.2
                                  linarith only [h1648, hlam, p1722_1]
                                · have p1722_0 := h1722c.1
                                  have p1722_1 := h1722c.2.1
                                  have p1722_2 := h1722c.2.2.1
                                  have p1722_3 := h1722c.2.2.2
                                  linarith only [h1650, hlam, p1722_0]
                                · have p1722_0 := h1722c.1
                                  have p1722_1 := h1722c.2.1
                                  have p1722_2 := h1722c.2.2.1
                                  have p1722_3 := h1722c.2.2.2
                                  linarith only [h0, h1478, h1479, h1667, h1712, h1716, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1722_1]
                                · have p1722_0 := h1722c.1
                                  have p1722_1 := h1722c.2.1
                                  have p1722_2 := h1722c.2.2.1
                                  have p1722_3 := h1722c.2.2.2
                                  linarith only [hlam, p1722_0]
                          · linarith only [h0, h1667, h1717, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h1667, h1716, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h1478, h1648, h1712, h1713, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h0, h1478, h1712, hc14, hlam, hphi, u4elo2]
            · linarith only [h1079, h1479, h1650, hlam]
          · linarith only [h0, h1478, h1480, h1649, hc14, hlam, hphi, u4elo3]
        · linarith only [h0, h1479, h1648, hlam]
      · linarith only [h0, h1478, h1647, hc14, hlam, hphi, u4elo2]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1764 | h1764
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1765 | h1765
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1766 | h1766
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1767 | h1767
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1768 | h1768
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1769 | h1769
              · linarith only [h1478, h1479, h1769, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1771 | h1771
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1772 | h1772
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1773 | h1773
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1774 | h1774
                      · linarith only [h1478, h1769, h1774, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h1478, h1479, h1772, h1774, hc24, hlam, hphi, u4elo4]
                    · linarith only [h1079, h1478, h1766, h1771, h1772, h1773, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h0, h1764, h1772, hc23, hlam, hphi, ht34, u4elo2]
                · linarith only [h0, h1764, h1771, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1780 | h1780
              · linarith only [h1478, h1479, h1780, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1782 | h1782
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1783 | h1783
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1784 | h1784
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1785 | h1785
                      · linarith only [h1478, h1780, h1785, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h1478, h1479, h1783, h1785, hc24, hlam, hphi, u4elo4]
                    · linarith only [h0, h1766, h1784, hlam]
                  · linarith only [h1079, h1478, h1782, h1783, hc14, hlam, hphi, u4elo2]
                · linarith only [h0, h1764, h1782, hlam]
          · linarith only [h1079, h1478, h1767, hc14, hlam, hphi, u4elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1792 | h1792
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1793 | h1793
            · linarith only [h1764, h1766, h1793, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1795 | h1795
              · linarith only [h0, h1478, h1766, h1795, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1797 | h1797
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1798 | h1798
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1799 | h1799
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1800 | h1800
                      · linarith only [h1478, h1795, h1800, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h1764, h1766, h1799, h1800, hc23, hlam, hphi, ht34, u4elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1803 | h1803
                      · linarith only [h1079, h1478, h1795, h1797, h1799, h1803, hc05, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h1079, h1478, h1797, h1798, h1799, h1803, hc24, hlam, hphi, u4elo4]
                  · linarith only [h1079, h1478, h1797, h1798, hc14, hlam, hphi, u4elo2]
                · linarith only [h0, h1478, h1764, h1797, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
          · linarith only [h1079, h1478, h1792, hc14, hlam, hphi, u4elo3]
      · linarith only [h0, h1478, h1765, hc14, hlam, hphi, u4elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1810 | h1810
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1811 | h1811
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1812 | h1812
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1813 | h1813
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1814 | h1814
              · linarith only [h1478, h1479, h1814, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1816 | h1816
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1817 | h1817
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1818 | h1818
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1819 | h1819
                      · linarith only [h1478, h1814, h1819, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h1478, h1479, h1817, h1819, hc24, hlam, hphi, u4elo4]
                    · linarith only [h1764, h1811, h1816, h1818, hlam]
                  · linarith only [h1764, h1816, h1817, hc02, hc24, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1824 | h1824
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1825 | h1825
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1826 | h1826
                      · linarith only [h1478, h1479, h1816, h1825, h1826, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h1478, h1479, h1826, hc14, hlam, hphi, u4elo4]
                    · linarith only [h0, h1478, h1811, h1824, h1825, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h0, h1478, h1824, hc14, hlam, hphi, u4elo2]
            · linarith only [h1764, h1811, h1813, hlam]
          · linarith only [h0, h1478, h1764, h1812, hc14, hlam, hphi, u4elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1833 | h1833
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1834 | h1834
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1835 | h1835
              · linarith only [h0, h1478, h1811, h1835, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1837 | h1837
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1838 | h1838
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1839 | h1839
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1840 | h1840
                      · linarith only [h1478, h1835, h1840, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h0, h1478, h1811, h1838, h1839, h1840, hc24, hlam, hphi, u4elo4]
                    · linarith only [h0, h1478, h1764, h1837, h1838, h1839, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h1478, h1764, h1837, h1838, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1845 | h1845
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1846 | h1846
                    · linarith only [h0, h1478, h1811, h1837, h1845, h1846, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1848 | h1848
                      · linarith only [h0, h1478, h1837, h1848, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h1478, h1846, h1848, hc14, hlam, hphi, u4elo4]
                  · linarith only [h0, h1478, h1845, hc14, hlam, hphi, u4elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1852 | h1852
              · linarith only [h1079, h1478, h1834, h1852, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1854 | h1854
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1855 | h1855
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1856 | h1856
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1857 | h1857
                      · linarith only [h1478, h1852, h1857, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h0, h1478, h1811, h1855, h1856, h1857, hc24, hlam, hphi, u4elo4]
                    · linarith only [h0, h1478, h1764, h1854, h1855, h1856, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h1478, h1764, h1854, h1855, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1862 | h1862
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1863 | h1863
                    · linarith only [h0, h1478, h1811, h1854, h1862, h1863, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1865 | h1865
                      · linarith only [h0, h1478, h1834, h1852, h1854, h1865, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · linarith only [h0, h1478, h1863, h1865, hc14, hlam, hphi, u4elo4]
                  · linarith only [h0, h1478, h1862, hc14, hlam, hphi, u4elo2]
          · linarith only [h0, h1478, h1764, h1833, hc14, hlam, hphi, u4elo3]
      · linarith only [h0, h1478, h1810, hc14, hlam, hphi, u4elo2]

end R2N4
