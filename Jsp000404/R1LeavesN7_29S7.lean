import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_29S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10236000 in
set_option maxHeartbeats 10236000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h2emin := hb2.2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1165 | h1165
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1166 | h1166
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1167 | h1167
      · linarith only [h0, h1167, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1169 | h1169
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1170 | h1170
          · linarith only [h1, h1170, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1172 | h1172
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1173 | h1173
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1174 | h1174
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1175 | h1175
                  · linarith only [h0, h1167, h1175, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1177 | h1177
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1178 | h1178
                      · linarith only [h0, h1, h1166, h1170, h1174, h1178, h2, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h1174, h1178, h2, hc23, hc34, hlam, hphi]
                    · linarith only [h1174, h1177, hc23, hlam, hphi, ht34, ht45, u5elo2]
                · linarith only [h1166, h1167, h1174, hc12, hc24, hlam, hphi]
              · linarith only [h0, h1173, h2, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1184 | h1184
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1185 | h1185
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1186 | h1186
                  · linarith only [h0, h1167, h1186, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1188 | h1188
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1189 | h1189
                      · linarith only [h1, h1172, h1189, hc34, hlam, hphi, ht45, u5elo3]
                      · linarith only [h0, h1185, h1189, h2, hc23, hc34, hlam, hphi]
                    · linarith only [h1185, h1188, hc23, hlam, hphi, ht34, ht45, u5elo2]
                · linarith only [h1166, h1172, h1185, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · linarith only [h0, h1184, h2, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
        · linarith only [h1166, h1169, hc23, hlam, hphi, ht34, ht45, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1196 | h1196
      · linarith only [h0, h1196, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1198 | h1198
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1199 | h1199
          · linarith only [h1, h1199, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1201 | h1201
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1202 | h1202
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1203 | h1203
                · linarith only [h0, h1166, h1203, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1205 | h1205
                  · linarith only [h0, h1196, h1205, h2, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1207 | h1207
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1208 | h1208
                      · linarith only [h1, h1166, h1199, h1208, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1210 | h1210
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1211 | h1211
                          · linarith only [h1, h1203, h1207, h1208, h1211, h2, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1213 | h1213
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1214 | h1214
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1215 | h1215
                                · rcases h0bigk with h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c
                                  · have p1216_0 := h1216c.1
                                    have p1216_1 := h1216c.2.1
                                    have p1216_2 := h1216c.2.2.1
                                    have p1216_3 := h1216c.2.2.2
                                    linarith only [hlam, p1216_0]
                                  · have p1216_0 := h1216c.1
                                    have p1216_1 := h1216c.2.1
                                    have p1216_2 := h1216c.2.2.1
                                    have p1216_3 := h1216c.2.2.2
                                    linarith only [h0, h1205, h1207, h1211, h1213, h1215, h2, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1216_1]
                                  · have p1216_0 := h1216c.1
                                    have p1216_1 := h1216c.2.1
                                    have p1216_2 := h1216c.2.2.1
                                    have p1216_3 := h1216c.2.2.2
                                    linarith only [h0, h1166, h1205, h1207, h1211, h1213, h1215, h2, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1216_1]
                                  · have p1216_0 := h1216c.1
                                    have p1216_1 := h1216c.2.1
                                    have p1216_2 := h1216c.2.2.1
                                    have p1216_3 := h1216c.2.2.2
                                    linarith only [h2, hlam, p1216_1]
                                  · have p1216_0 := h1216c.1
                                    have p1216_1 := h1216c.2.1
                                    have p1216_2 := h1216c.2.2.1
                                    have p1216_3 := h1216c.2.2.2
                                    rcases p1216_3 (m.d 0 1) (by simp) with h1221 | h1221
                                    · rcases p1216_3 (m.d 0 2) (by simp) with h1222 | h1222
                                      · linarith only [h0, h1222, hlam]
                                      · linarith only [h1198, h1222, hlam]
                                    · linarith only [h1165, h1221, hlam]
                                  · have p1216_0 := h1216c.1
                                    have p1216_1 := h1216c.2.1
                                    have p1216_2 := h1216c.2.2.1
                                    have p1216_3 := h1216c.2.2.2
                                    linarith only [h0, hlam, p1216_0]
                                  · have p1216_0 := h1216c.1
                                    have p1216_1 := h1216c.2.1
                                    have p1216_2 := h1216c.2.2.1
                                    have p1216_3 := h1216c.2.2.2
                                    linarith only [hlam, p1216_0]
                                  · have p1216_0 := h1216c.1
                                    have p1216_1 := h1216c.2.1
                                    have p1216_2 := h1216c.2.2.1
                                    have p1216_3 := h1216c.2.2.2
                                    linarith only [h1166, hlam, p1216_0]
                                  · have p1216_0 := h1216c.1
                                    have p1216_1 := h1216c.2.1
                                    have p1216_2 := h1216c.2.2.1
                                    have p1216_3 := h1216c.2.2.2
                                    linarith only [h1196, hlam, p1216_1]
                                  · have p1216_0 := h1216c.1
                                    have p1216_1 := h1216c.2.1
                                    have p1216_2 := h1216c.2.2.1
                                    have p1216_3 := h1216c.2.2.2
                                    linarith only [h1165, h1166, h1211, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1216_1]
                                  · have p1216_0 := h1216c.1
                                    have p1216_1 := h1216c.2.1
                                    have p1216_2 := h1216c.2.2.1
                                    have p1216_3 := h1216c.2.2.2
                                    linarith only [h1, hlam, p1216_1]
                                  · have p1216_0 := h1216c.1
                                    have p1216_1 := h1216c.2.1
                                    have p1216_2 := h1216c.2.2.1
                                    have p1216_3 := h1216c.2.2.2
                                    linarith only [h0, h1207, h1213, h1215, hc45, hlam, hphi, ht0b, ht5b, p1216_1, u0elo2]
                                  · have p1216_0 := h1216c.1
                                    have p1216_1 := h1216c.2.1
                                    have p1216_2 := h1216c.2.2.1
                                    have p1216_3 := h1216c.2.2.2
                                    linarith only [hlam, p1216_0]
                                  · have p1216_0 := h1216c.1
                                    have p1216_1 := h1216c.2.1
                                    have p1216_2 := h1216c.2.2.1
                                    have p1216_3 := h1216c.2.2.2
                                    linarith only [h1199, hlam, p1216_1]
                                  · have p1216_0 := h1216c.1
                                    have p1216_1 := h1216c.2.1
                                    have p1216_2 := h1216c.2.2.1
                                    have p1216_3 := h1216c.2.2.2
                                    rcases p1216_3 (m.d 0 1) (by simp) with h1235 | h1235
                                    · rcases p1216_3 (m.d 0 2) (by simp) with h1236 | h1236
                                      · linarith only [h1166, h1236, hlam]
                                      · linarith only [h1198, h1236, hlam]
                                    · linarith only [h1165, h1235, hlam]
                                  · have p1216_0 := h1216c.1
                                    have p1216_1 := h1216c.2.1
                                    have p1216_2 := h1216c.2.2.1
                                    have p1216_3 := h1216c.2.2.2
                                    linarith only [h0, h1207, h1213, h1215, hc45, hlam, hphi, ht0b, ht5b, p1216_1, u0elo3]
                                  · have p1216_0 := h1216c.1
                                    have p1216_1 := h1216c.2.1
                                    have p1216_2 := h1216c.2.2.1
                                    have p1216_3 := h1216c.2.2.2
                                    linarith only [h0, h1207, h1213, h1215, hc45, hlam, hphi, ht0b, ht5b, p1216_1, u0elo3]
                                  · have p1216_0 := h1216c.1
                                    have p1216_1 := h1216c.2.1
                                    have p1216_2 := h1216c.2.2.1
                                    have p1216_3 := h1216c.2.2.2
                                    linarith only [h1, h1203, h1207, h1213, h1215, hc45, hlam, hphi, ht0b, ht5b, p1216_1, u0elo3]
                                  · have p1216_0 := h1216c.1
                                    have p1216_1 := h1216c.2.1
                                    have p1216_2 := h1216c.2.2.1
                                    have p1216_3 := h1216c.2.2.2
                                    linarith only [hlam, p1216_0]
                                  · have p1216_0 := h1216c.1
                                    have p1216_1 := h1216c.2.1
                                    have p1216_2 := h1216c.2.2.1
                                    have p1216_3 := h1216c.2.2.2
                                    rcases p1216_3 (m.d 0 1) (by simp) with h1244 | h1244
                                    · linarith only [h1244, h2, hlam]
                                    · linarith only [h1165, h1244, hlam]
                                  · have p1216_0 := h1216c.1
                                    have p1216_1 := h1216c.2.1
                                    have p1216_2 := h1216c.2.2.1
                                    have p1216_3 := h1216c.2.2.2
                                    linarith only [h1165, hlam, p1216_0]
                                  · have p1216_0 := h1216c.1
                                    have p1216_1 := h1216c.2.1
                                    have p1216_2 := h1216c.2.2.1
                                    have p1216_3 := h1216c.2.2.2
                                    linarith only [h1198, hlam, p1216_1]
                                  · have p1216_0 := h1216c.1
                                    have p1216_1 := h1216c.2.1
                                    have p1216_2 := h1216c.2.2.1
                                    have p1216_3 := h1216c.2.2.2
                                    linarith only [h1201, hlam, p1216_0]
                                  · have p1216_0 := h1216c.1
                                    have p1216_1 := h1216c.2.1
                                    have p1216_2 := h1216c.2.2.1
                                    have p1216_3 := h1216c.2.2.2
                                    linarith only [h1202, hlam, p1216_1]
                                  · have p1216_0 := h1216c.1
                                    have p1216_1 := h1216c.2.1
                                    have p1216_2 := h1216c.2.2.1
                                    have p1216_3 := h1216c.2.2.2
                                    linarith only [hlam, p1216_0]
                                · linarith only [h1211, h1215, hc23, hlam, hphi, ht34, ht45, u5elo4]
                              · linarith only [h1, h1202, h1203, h1205, h1214, h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                            · linarith only [h0, h1166, h1207, h1213, hc25, hlam, hphi, u5elo3]
                        · linarith only [h1201, h1203, h1207, h1210, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                    · linarith only [h1166, h1198, h1207, hc12, hc23, hlam, hphi]
              · linarith only [h0, h1202, h2, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
            · linarith only [h1166, h1198, h1201, hc25, hlam, hphi, u5elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1259 | h1259
          · linarith only [h1, h1259, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1261 | h1261
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1262 | h1262
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1263 | h1263
                · linarith only [h0, h1198, h1263, hc23, hlam, hphi, ht34, ht45, u5elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1265 | h1265
                  · linarith only [h0, h1196, h1198, h1265, h2, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1267 | h1267
                    · linarith only [h1, h1198, h1263, h1267, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1269 | h1269
                      · linarith only [h1, h1259, h1265, h1269, h2, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1271 | h1271
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1272 | h1272
                          · linarith only [h0, h1269, h1272, h2, hc12, hc23, hlam, hphi]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1274 | h1274
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1275 | h1275
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1276 | h1276
                                · rcases h0bigk with h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c
                                  · have p1277_0 := h1277c.1
                                    have p1277_1 := h1277c.2.1
                                    have p1277_2 := h1277c.2.2.1
                                    have p1277_3 := h1277c.2.2.2
                                    linarith only [hlam, p1277_0]
                                  · have p1277_0 := h1277c.1
                                    have p1277_1 := h1277c.2.1
                                    have p1277_2 := h1277c.2.2.1
                                    have p1277_3 := h1277c.2.2.2
                                    linarith only [h0, h1265, h1272, h2, hc12, hc34, hlam, hphi, ht23, p1277_1]
                                  · have p1277_0 := h1277c.1
                                    have p1277_1 := h1277c.2.1
                                    have p1277_2 := h1277c.2.2.1
                                    have p1277_3 := h1277c.2.2.2
                                    linarith only [h1, h1271, h1276, h2, hc45, hlam, hphi, ht0b, ht5b, p1277_1, u0elo3]
                                  · have p1277_0 := h1277c.1
                                    have p1277_1 := h1277c.2.1
                                    have p1277_2 := h1277c.2.2.1
                                    have p1277_3 := h1277c.2.2.2
                                    linarith only [h2, hlam, p1277_1]
                                  · have p1277_0 := h1277c.1
                                    have p1277_1 := h1277c.2.1
                                    have p1277_2 := h1277c.2.2.1
                                    have p1277_3 := h1277c.2.2.2
                                    linarith only [h0, h1198, h1265, h1272, h2, hc12, hc34, hlam, hphi, ht23, p1277_1]
                                  · have p1277_0 := h1277c.1
                                    have p1277_1 := h1277c.2.1
                                    have p1277_2 := h1277c.2.2.1
                                    have p1277_3 := h1277c.2.2.2
                                    linarith only [h0, hlam, p1277_0]
                                  · have p1277_0 := h1277c.1
                                    have p1277_1 := h1277c.2.1
                                    have p1277_2 := h1277c.2.2.1
                                    have p1277_3 := h1277c.2.2.2
                                    linarith only [hlam, p1277_0]
                                  · have p1277_0 := h1277c.1
                                    have p1277_1 := h1277c.2.1
                                    have p1277_2 := h1277c.2.2.1
                                    have p1277_3 := h1277c.2.2.2
                                    linarith only [h1166, hlam, p1277_0]
                                  · have p1277_0 := h1277c.1
                                    have p1277_1 := h1277c.2.1
                                    have p1277_2 := h1277c.2.2.1
                                    have p1277_3 := h1277c.2.2.2
                                    linarith only [h1196, hlam, p1277_1]
                                  · have p1277_0 := h1277c.1
                                    have p1277_1 := h1277c.2.1
                                    have p1277_2 := h1277c.2.2.1
                                    have p1277_3 := h1277c.2.2.2
                                    linarith only [h1198, hlam, p1277_0]
                                  · have p1277_0 := h1277c.1
                                    have p1277_1 := h1277c.2.1
                                    have p1277_2 := h1277c.2.2.1
                                    have p1277_3 := h1277c.2.2.2
                                    linarith only [h1, hlam, p1277_1]
                                  · have p1277_0 := h1277c.1
                                    have p1277_1 := h1277c.2.1
                                    have p1277_2 := h1277c.2.2.1
                                    have p1277_3 := h1277c.2.2.2
                                    linarith only [h0, h1166, h1272, hc12, hc34, hlam, hphi, ht23, p1277_1]
                                  · have p1277_0 := h1277c.1
                                    have p1277_1 := h1277c.2.1
                                    have p1277_2 := h1277c.2.2.1
                                    have p1277_3 := h1277c.2.2.2
                                    linarith only [hlam, p1277_0]
                                  · have p1277_0 := h1277c.1
                                    have p1277_1 := h1277c.2.1
                                    have p1277_2 := h1277c.2.2.1
                                    have p1277_3 := h1277c.2.2.2
                                    linarith only [h1259, hlam, p1277_1]
                                  · have p1277_0 := h1277c.1
                                    have p1277_1 := h1277c.2.1
                                    have p1277_2 := h1277c.2.2.1
                                    have p1277_3 := h1277c.2.2.2
                                    linarith only [h0, h1166, h1198, h1272, hc12, hc34, hlam, hphi, ht23, p1277_1]
                                  · have p1277_0 := h1277c.1
                                    have p1277_1 := h1277c.2.1
                                    have p1277_2 := h1277c.2.2.1
                                    have p1277_3 := h1277c.2.2.2
                                    linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1277_1, u0elo3]
                                  · have p1277_0 := h1277c.1
                                    have p1277_1 := h1277c.2.1
                                    have p1277_2 := h1277c.2.2.1
                                    have p1277_3 := h1277c.2.2.2
                                    rcases p1277_3 (m.d 0 1) (by simp) with h1294 | h1294
                                    · linarith only [h1294, h2, hlam]
                                    · linarith only [h0, h1294, hlam]
                                  · have p1277_0 := h1277c.1
                                    have p1277_1 := h1277c.2.1
                                    have p1277_2 := h1277c.2.2.1
                                    have p1277_3 := h1277c.2.2.2
                                    linarith only [h1, h1271, h1276, hc45, hlam, hphi, ht0b, ht5b, p1277_1, u0elo3]
                                  · have p1277_0 := h1277c.1
                                    have p1277_1 := h1277c.2.1
                                    have p1277_2 := h1277c.2.2.1
                                    have p1277_3 := h1277c.2.2.2
                                    linarith only [hlam, p1277_0]
                                  · have p1277_0 := h1277c.1
                                    have p1277_1 := h1277c.2.1
                                    have p1277_2 := h1277c.2.2.1
                                    have p1277_3 := h1277c.2.2.2
                                    rcases p1277_3 (m.d 0 1) (by simp) with h1299 | h1299
                                    · linarith only [h1299, h2, hlam]
                                    · linarith only [h1165, h1299, hlam]
                                  · have p1277_0 := h1277c.1
                                    have p1277_1 := h1277c.2.1
                                    have p1277_2 := h1277c.2.2.1
                                    have p1277_3 := h1277c.2.2.2
                                    linarith only [h1165, hlam, p1277_0]
                                  · have p1277_0 := h1277c.1
                                    have p1277_1 := h1277c.2.1
                                    have p1277_2 := h1277c.2.2.1
                                    have p1277_3 := h1277c.2.2.2
                                    linarith only [h0, h1, h1265, h1271, h1272, h1276, h2, hc12, hc34, hc45, hlam, hphi, ht23, p1277_1, u5elo0]
                                  · have p1277_0 := h1277c.1
                                    have p1277_1 := h1277c.2.1
                                    have p1277_2 := h1277c.2.2.1
                                    have p1277_3 := h1277c.2.2.2
                                    linarith only [h1261, hlam, p1277_0]
                                  · have p1277_0 := h1277c.1
                                    have p1277_1 := h1277c.2.1
                                    have p1277_2 := h1277c.2.2.1
                                    have p1277_3 := h1277c.2.2.2
                                    linarith only [h1262, hlam, p1277_1]
                                  · have p1277_0 := h1277c.1
                                    have p1277_1 := h1277c.2.1
                                    have p1277_2 := h1277c.2.2.1
                                    have p1277_3 := h1277c.2.2.2
                                    linarith only [hlam, p1277_0]
                                · linarith only [h1, h1265, h1271, h1272, h1276, h2, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                              · linarith only [h1, h1261, h1262, h1265, h1271, h1275, h2, hc35, hlam, hphi, ht0b, ht5b, u0elo2]
                            · linarith only [h1, h1271, h1274, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h1, h1261, h1269, h1271, h2, hc13, hc34, hlam, hphi]
              · linarith only [h1, h1261, h1262, h2, hc35, hlam, hphi, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1312 | h1312
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1313 | h1313
                · linarith only [h0, h1166, h1313, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1315 | h1315
                  · linarith only [h1, h1261, h1313, h1315, hc24, hlam, hphi, ht45, u5elo3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1317 | h1317
                    · linarith only [h1, h1261, h1313, h1317, hc25, hlam, hphi, u5elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1319 | h1319
                      · linarith only [h1, h1261, h1319, hc34, hlam, hphi, ht45, u5elo3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1321 | h1321
                        · linarith only [h1, h1261, h1321, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1323 | h1323
                          · linarith only [h1165, h1313, h1319, h1321, h1323, h2, hc12, hc23, hlam, hphi]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1325 | h1325
                            · linarith only [h0, h1166, h1261, h1323, h1325, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h0, h1166, h1325, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · linarith only [h1165, h1312, h2, hc15, hlam, hphi, u5elo4]
  · linarith only [h0, h1165, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]

set_option maxHeartbeats 10236000 in
set_option maxHeartbeats 10236000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h2emin := hb2.2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h1 h2
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h1 h2

set_option maxHeartbeats 10236000 in
set_option maxHeartbeats 10236000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h2emin := hb2.2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1330 | h1330
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1331 | h1331
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1332 | h1332
      · linarith only [h0, h1, h1332, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1334 | h1334
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1335 | h1335
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1336 | h1336
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1337 | h1337
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1338 | h1338
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1339 | h1339
                  · linarith only [h0, h1332, h1339, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1341 | h1341
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1342 | h1342
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1343 | h1343
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1344 | h1344
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1345 | h1345
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1346 | h1346
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1347 | h1347
                                · linarith only [h0, h1, h1339, h1341, h1347, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1349 | h1349
                                  · linarith only [h1345, h1347, h1349, hlam]
                                  · rcases h0bigk with h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c
                                    · have p1351_0 := h1351c.1
                                      have p1351_1 := h1351c.2.1
                                      have p1351_2 := h1351c.2.2.1
                                      have p1351_3 := h1351c.2.2.2
                                      linarith only [hlam, p1351_0]
                                    · have p1351_0 := h1351c.1
                                      have p1351_1 := h1351c.2.1
                                      have p1351_2 := h1351c.2.2.1
                                      have p1351_3 := h1351c.2.2.2
                                      linarith only [h1, h1339, hc02, hc23, hlam, hphi, p1351_1]
                                    · have p1351_0 := h1351c.1
                                      have p1351_1 := h1351c.2.1
                                      have p1351_2 := h1351c.2.2.1
                                      have p1351_3 := h1351c.2.2.2
                                      linarith only [h1, hlam, p1351_0]
                                    · have p1351_0 := h1351c.1
                                      have p1351_1 := h1351c.2.1
                                      have p1351_2 := h1351c.2.2.1
                                      have p1351_3 := h1351c.2.2.2
                                      linarith only [h1, h1338, h1339, h1345, h1347, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1351_1]
                                    · have p1351_0 := h1351c.1
                                      have p1351_1 := h1351c.2.1
                                      have p1351_2 := h1351c.2.2.1
                                      have p1351_3 := h1351c.2.2.2
                                      linarith only [h1, h1338, h1339, h1345, h1347, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1351_1]
                                    · have p1351_0 := h1351c.1
                                      have p1351_1 := h1351c.2.1
                                      have p1351_2 := h1351c.2.2.1
                                      have p1351_3 := h1351c.2.2.2
                                      linarith only [h0, hlam, p1351_0]
                                    · have p1351_0 := h1351c.1
                                      have p1351_1 := h1351c.2.1
                                      have p1351_2 := h1351c.2.2.1
                                      have p1351_3 := h1351c.2.2.2
                                      linarith only [hlam, p1351_0]
                                    · have p1351_0 := h1351c.1
                                      have p1351_1 := h1351c.2.1
                                      have p1351_2 := h1351c.2.2.1
                                      have p1351_3 := h1351c.2.2.2
                                      linarith only [h1332, hlam, p1351_0]
                                    · have p1351_0 := h1351c.1
                                      have p1351_1 := h1351c.2.1
                                      have p1351_2 := h1351c.2.2.1
                                      have p1351_3 := h1351c.2.2.2
                                      linarith only [h0, h1, h1338, h1339, h1345, h1347, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1351_1]
                                    · have p1351_0 := h1351c.1
                                      have p1351_1 := h1351c.2.1
                                      have p1351_2 := h1351c.2.2.1
                                      have p1351_3 := h1351c.2.2.2
                                      linarith only [h0, h1, h1338, h1339, h1345, h1347, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1351_1]
                                    · have p1351_0 := h1351c.1
                                      have p1351_1 := h1351c.2.1
                                      have p1351_2 := h1351c.2.2.1
                                      have p1351_3 := h1351c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1351_1, u0elo2]
                                    · have p1351_0 := h1351c.1
                                      have p1351_1 := h1351c.2.1
                                      have p1351_2 := h1351c.2.2.1
                                      have p1351_3 := h1351c.2.2.2
                                      linarith only [h0, h1342, h1346, hc35, hlam, hphi, ht0b, ht5b, p1351_1, u0elo2]
                                    · have p1351_0 := h1351c.1
                                      have p1351_1 := h1351c.2.1
                                      have p1351_2 := h1351c.2.2.1
                                      have p1351_3 := h1351c.2.2.2
                                      linarith only [hlam, p1351_0]
                                    · have p1351_0 := h1351c.1
                                      have p1351_1 := h1351c.2.1
                                      have p1351_2 := h1351c.2.2.1
                                      have p1351_3 := h1351c.2.2.2
                                      linarith only [h1338, h1345, h1347, hc34, hlam, hphi, ht0b, ht45, ht5b, p1351_1, u0elo2]
                                    · have p1351_0 := h1351c.1
                                      have p1351_1 := h1351c.2.1
                                      have p1351_2 := h1351c.2.2.1
                                      have p1351_3 := h1351c.2.2.2
                                      linarith only [h1338, h1345, h1347, hc34, hlam, hphi, ht0b, ht45, ht5b, p1351_1, u0elo2]
                                    · have p1351_0 := h1351c.1
                                      have p1351_1 := h1351c.2.1
                                      have p1351_2 := h1351c.2.2.1
                                      have p1351_3 := h1351c.2.2.2
                                      linarith only [h1330, hlam, p1351_0]
                                    · have p1351_0 := h1351c.1
                                      have p1351_1 := h1351c.2.1
                                      have p1351_2 := h1351c.2.2.1
                                      have p1351_3 := h1351c.2.2.2
                                      linarith only [h1334, hlam, p1351_0]
                                    · have p1351_0 := h1351c.1
                                      have p1351_1 := h1351c.2.1
                                      have p1351_2 := h1351c.2.2.1
                                      have p1351_3 := h1351c.2.2.2
                                      linarith only [h1336, hlam, p1351_0]
                                    · have p1351_0 := h1351c.1
                                      have p1351_1 := h1351c.2.1
                                      have p1351_2 := h1351c.2.2.1
                                      have p1351_3 := h1351c.2.2.2
                                      linarith only [hlam, p1351_0]
                                    · have p1351_0 := h1351c.1
                                      have p1351_1 := h1351c.2.1
                                      have p1351_2 := h1351c.2.2.1
                                      have p1351_3 := h1351c.2.2.2
                                      linarith only [h1338, h1345, h1347, hc34, hlam, hphi, ht0b, ht45, ht5b, p1351_1, u0elo3]
                                    · have p1351_0 := h1351c.1
                                      have p1351_1 := h1351c.2.1
                                      have p1351_2 := h1351c.2.2.1
                                      have p1351_3 := h1351c.2.2.2
                                      linarith only [h1331, hlam, p1351_0]
                                    · have p1351_0 := h1351c.1
                                      have p1351_1 := h1351c.2.1
                                      have p1351_2 := h1351c.2.2.1
                                      have p1351_3 := h1351c.2.2.2
                                      linarith only [h1335, hlam, p1351_1]
                                    · have p1351_0 := h1351c.1
                                      have p1351_1 := h1351c.2.1
                                      have p1351_2 := h1351c.2.2.1
                                      have p1351_3 := h1351c.2.2.2
                                      linarith only [h1337, hlam, p1351_0]
                                    · have p1351_0 := h1351c.1
                                      have p1351_1 := h1351c.2.1
                                      have p1351_2 := h1351c.2.2.1
                                      have p1351_3 := h1351c.2.2.2
                                      linarith only [h1338, hlam, p1351_1]
                                    · have p1351_0 := h1351c.1
                                      have p1351_1 := h1351c.2.1
                                      have p1351_2 := h1351c.2.2.1
                                      have p1351_3 := h1351c.2.2.2
                                      linarith only [hlam, p1351_0]
                              · linarith only [h1, h1339, h1346, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                            · linarith only [h0, h1, h1339, h1341, h1345, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1, h1341, h1344, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h1, h1341, h1343, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h1341, h1342, hc24, hlam, hphi, ht45, u5elo2]
                    · linarith only [h0, h1, h1334, h1339, h1341, hc12, hc23, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1383 | h1383
                  · linarith only [h0, h1, h1332, h1383, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1385 | h1385
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1386 | h1386
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1387 | h1387
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1388 | h1388
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1389 | h1389
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1390 | h1390
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1391 | h1391
                                · linarith only [h0, h1, h1338, h1383, h1385, h1391, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1393 | h1393
                                  · linarith only [h1330, h1338, h1385, h1389, h1393, hlam]
                                  · rcases h0bigk with h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c
                                    · have p1395_0 := h1395c.1
                                      have p1395_1 := h1395c.2.1
                                      have p1395_2 := h1395c.2.2.1
                                      have p1395_3 := h1395c.2.2.2
                                      linarith only [hlam, p1395_0]
                                    · have p1395_0 := h1395c.1
                                      have p1395_1 := h1395c.2.1
                                      have p1395_2 := h1395c.2.2.1
                                      have p1395_3 := h1395c.2.2.2
                                      linarith only [h1, h1383, hc02, hc23, hlam, hphi, p1395_1]
                                    · have p1395_0 := h1395c.1
                                      have p1395_1 := h1395c.2.1
                                      have p1395_2 := h1395c.2.2.1
                                      have p1395_3 := h1395c.2.2.2
                                      linarith only [h1, hlam, p1395_0]
                                    · have p1395_0 := h1395c.1
                                      have p1395_1 := h1395c.2.1
                                      have p1395_2 := h1395c.2.2.1
                                      have p1395_3 := h1395c.2.2.2
                                      rcases p1395_3 (m.d 0 1) (by simp) with h1399 | h1399
                                      · rcases p1395_3 (m.d 0 2) (by simp) with h1400 | h1400
                                        · linarith only [h0, h1400, hlam]
                                        · linarith only [h1334, h1400, hlam]
                                      · linarith only [h1330, h1399, hlam]
                                    · have p1395_0 := h1395c.1
                                      have p1395_1 := h1395c.2.1
                                      have p1395_2 := h1395c.2.2.1
                                      have p1395_3 := h1395c.2.2.2
                                      rcases p1395_3 (m.d 0 1) (by simp) with h1404 | h1404
                                      · rcases p1395_3 (m.d 0 2) (by simp) with h1405 | h1405
                                        · linarith only [h0, h1405, hlam]
                                        · linarith only [h1335, h1405, hlam]
                                      · linarith only [h1331, h1404, hlam]
                                    · have p1395_0 := h1395c.1
                                      have p1395_1 := h1395c.2.1
                                      have p1395_2 := h1395c.2.2.1
                                      have p1395_3 := h1395c.2.2.2
                                      linarith only [h0, hlam, p1395_0]
                                    · have p1395_0 := h1395c.1
                                      have p1395_1 := h1395c.2.1
                                      have p1395_2 := h1395c.2.2.1
                                      have p1395_3 := h1395c.2.2.2
                                      linarith only [hlam, p1395_0]
                                    · have p1395_0 := h1395c.1
                                      have p1395_1 := h1395c.2.1
                                      have p1395_2 := h1395c.2.2.1
                                      have p1395_3 := h1395c.2.2.2
                                      linarith only [h1332, hlam, p1395_0]
                                    · have p1395_0 := h1395c.1
                                      have p1395_1 := h1395c.2.1
                                      have p1395_2 := h1395c.2.2.1
                                      have p1395_3 := h1395c.2.2.2
                                      rcases p1395_3 (m.d 0 1) (by simp) with h1412 | h1412
                                      · rcases p1395_3 (m.d 0 2) (by simp) with h1413 | h1413
                                        · rcases p1395_3 (m.d 0 3) (by simp) with h1414 | h1414
                                          · rcases p1395_3 (m.d 0 4) (by simp) with h1415 | h1415
                                            · linarith only [h1334, h1415, hlam]
                                            · rcases p1395_3 (m.d 0 5) (by simp) with h1417 | h1417
                                              · linarith only [h1335, h1417, hlam]
                                              · linarith only [h1338, h1417, hlam]
                                          · linarith only [h1336, h1414, hlam]
                                        · linarith only [h1334, h1413, hlam]
                                      · linarith only [h1330, h1412, hlam]
                                    · have p1395_0 := h1395c.1
                                      have p1395_1 := h1395c.2.1
                                      have p1395_2 := h1395c.2.2.1
                                      have p1395_3 := h1395c.2.2.2
                                      rcases p1395_3 (m.d 0 1) (by simp) with h1423 | h1423
                                      · rcases p1395_3 (m.d 0 2) (by simp) with h1424 | h1424
                                        · rcases p1395_3 (m.d 0 3) (by simp) with h1425 | h1425
                                          · rcases p1395_3 (m.d 0 4) (by simp) with h1426 | h1426
                                            · linarith only [h1334, h1426, hlam]
                                            · rcases p1395_3 (m.d 0 5) (by simp) with h1428 | h1428
                                              · linarith only [h1335, h1428, hlam]
                                              · rcases h2bigk with h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c
                                                · have p1430_0 := h1430c.1
                                                  have p1430_1 := h1430c.2.1
                                                  have p1430_2 := h1430c.2.2.1
                                                  have p1430_3 := h1430c.2.2.2
                                                  linarith only [hlam, p1430_0]
                                                · have p1430_0 := h1430c.1
                                                  have p1430_1 := h1430c.2.1
                                                  have p1430_2 := h1430c.2.2.1
                                                  have p1430_3 := h1430c.2.2.2
                                                  linarith only [h0, h1, h1383, h1386, h1389, h1391, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1430_1]
                                                · have p1430_0 := h1430c.1
                                                  have p1430_1 := h1430c.2.1
                                                  have p1430_2 := h1430c.2.2.1
                                                  have p1430_3 := h1430c.2.2.2
                                                  linarith only [h1332, hlam, p1430_0]
                                                · have p1430_0 := h1430c.1
                                                  have p1430_1 := h1430c.2.1
                                                  have p1430_2 := h1430c.2.2.1
                                                  have p1430_3 := h1430c.2.2.2
                                                  rcases p1430_3 (m.d 0 2) (by simp) with h1434 | h1434
                                                  · rcases p1430_3 (m.d 1 2) (by simp) with h1435 | h1435
                                                    · linarith only [h0, h1435, hlam]
                                                    · linarith only [h1385, h1435, hlam]
                                                  · linarith only [h1434, hlam, p1430_0]
                                                · have p1430_0 := h1430c.1
                                                  have p1430_1 := h1430c.2.1
                                                  have p1430_2 := h1430c.2.2.1
                                                  have p1430_3 := h1430c.2.2.2
                                                  rcases p1430_3 (m.d 0 2) (by simp) with h1439 | h1439
                                                  · rcases p1430_3 (m.d 1 2) (by simp) with h1440 | h1440
                                                    · linarith only [h0, h1440, hlam]
                                                    · linarith only [h1386, h1440, hlam]
                                                  · linarith only [h1439, hlam, p1430_0]
                                                · have p1430_0 := h1430c.1
                                                  have p1430_1 := h1430c.2.1
                                                  have p1430_2 := h1430c.2.2.1
                                                  have p1430_3 := h1430c.2.2.2
                                                  linarith only [h0, hlam, p1430_0]
                                                · have p1430_0 := h1430c.1
                                                  have p1430_1 := h1430c.2.1
                                                  have p1430_2 := h1430c.2.2.1
                                                  have p1430_3 := h1430c.2.2.2
                                                  linarith only [hlam, p1430_0]
                                                · have p1430_0 := h1430c.1
                                                  have p1430_1 := h1430c.2.1
                                                  have p1430_2 := h1430c.2.2.1
                                                  have p1430_3 := h1430c.2.2.2
                                                  linarith only [h1383, hlam, p1430_0]
                                                · have p1430_0 := h1430c.1
                                                  have p1430_1 := h1430c.2.1
                                                  have p1430_2 := h1430c.2.2.1
                                                  have p1430_3 := h1430c.2.2.2
                                                  linarith only [h0, h1, h1383, h1389, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1430_1]
                                                · have p1430_0 := h1430c.1
                                                  have p1430_1 := h1430c.2.1
                                                  have p1430_2 := h1430c.2.2.1
                                                  have p1430_3 := h1430c.2.2.2
                                                  linarith only [h0, h1, h1383, h1389, h1391, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1430_1]
                                                · have p1430_0 := h1430c.1
                                                  have p1430_1 := h1430c.2.1
                                                  have p1430_2 := h1430c.2.2.1
                                                  have p1430_3 := h1430c.2.2.2
                                                  linarith only [hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1395_1, p1430_1]
                                                · have p1430_0 := h1430c.1
                                                  have p1430_1 := h1430c.2.1
                                                  have p1430_2 := h1430c.2.2.1
                                                  have p1430_3 := h1430c.2.2.2
                                                  rcases p1430_3 (m.d 0 2) (by simp) with h1450 | h1450
                                                  · linarith only [h1332, h1450, hlam]
                                                  · linarith only [h0, h1450, hlam]
                                                · have p1430_0 := h1430c.1
                                                  have p1430_1 := h1430c.2.1
                                                  have p1430_2 := h1430c.2.2.1
                                                  have p1430_3 := h1430c.2.2.2
                                                  linarith only [hlam, p1430_0]
                                                · have p1430_0 := h1430c.1
                                                  have p1430_1 := h1430c.2.1
                                                  have p1430_2 := h1430c.2.2.1
                                                  have p1430_3 := h1430c.2.2.2
                                                  linarith only [h0, h1, h1330, h1338, h1383, h1385, hlam, p1395_1, p1430_2]
                                                · have p1430_0 := h1430c.1
                                                  have p1430_1 := h1430c.2.1
                                                  have p1430_2 := h1430c.2.2.1
                                                  have p1430_3 := h1430c.2.2.2
                                                  linarith only [h0, h1, h1331, h1383, h1386, hlam, p1395_1, p1430_2]
                                                · have p1430_0 := h1430c.1
                                                  have p1430_1 := h1430c.2.1
                                                  have p1430_2 := h1430c.2.2.1
                                                  have p1430_3 := h1430c.2.2.2
                                                  linarith only [h1334, hlam, p1430_0]
                                                · have p1430_0 := h1430c.1
                                                  have p1430_1 := h1430c.2.1
                                                  have p1430_2 := h1430c.2.2.1
                                                  have p1430_3 := h1430c.2.2.2
                                                  linarith only [h1385, hlam, p1430_0]
                                                · have p1430_0 := h1430c.1
                                                  have p1430_1 := h1430c.2.1
                                                  have p1430_2 := h1430c.2.2.1
                                                  have p1430_3 := h1430c.2.2.2
                                                  linarith only [h1389, hlam, p1430_1]
                                                · have p1430_0 := h1430c.1
                                                  have p1430_1 := h1430c.2.1
                                                  have p1430_2 := h1430c.2.2.1
                                                  have p1430_3 := h1430c.2.2.2
                                                  linarith only [hlam, p1430_0]
                                                · have p1430_0 := h1430c.1
                                                  have p1430_1 := h1430c.2.1
                                                  have p1430_2 := h1430c.2.2.1
                                                  have p1430_3 := h1430c.2.2.2
                                                  linarith only [h1391, hlam, p1430_1]
                                                · have p1430_0 := h1430c.1
                                                  have p1430_1 := h1430c.2.1
                                                  have p1430_2 := h1430c.2.2.1
                                                  have p1430_3 := h1430c.2.2.2
                                                  linarith only [h1335, hlam, p1430_0]
                                                · have p1430_0 := h1430c.1
                                                  have p1430_1 := h1430c.2.1
                                                  have p1430_2 := h1430c.2.2.1
                                                  have p1430_3 := h1430c.2.2.2
                                                  linarith only [h1386, hlam, p1430_0]
                                                · have p1430_0 := h1430c.1
                                                  have p1430_1 := h1430c.2.1
                                                  have p1430_2 := h1430c.2.2.1
                                                  have p1430_3 := h1430c.2.2.2
                                                  linarith only [h1390, hlam, p1430_1]
                                                · have p1430_0 := h1430c.1
                                                  have p1430_1 := h1430c.2.1
                                                  have p1430_2 := h1430c.2.2.1
                                                  have p1430_3 := h1430c.2.2.2
                                                  linarith only [h0, h1331, h1386, h1389, hc34, hlam, hphi, ht0b, ht45, ht5b, p1395_1, p1430_1, u0elo0]
                                                · have p1430_0 := h1430c.1
                                                  have p1430_1 := h1430c.2.1
                                                  have p1430_2 := h1430c.2.2.1
                                                  have p1430_3 := h1430c.2.2.2
                                                  linarith only [hlam, p1430_0]
                                          · linarith only [h1337, h1425, hlam]
                                        · linarith only [h1335, h1424, hlam]
                                      · linarith only [h1331, h1423, hlam]
                                    · have p1395_0 := h1395c.1
                                      have p1395_1 := h1395c.2.1
                                      have p1395_2 := h1395c.2.2.1
                                      have p1395_3 := h1395c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1395_1, u0elo2]
                                    · have p1395_0 := h1395c.1
                                      have p1395_1 := h1395c.2.1
                                      have p1395_2 := h1395c.2.2.1
                                      have p1395_3 := h1395c.2.2.2
                                      linarith only [h1334, h1389, hc34, hlam, hphi, ht0b, ht45, ht5b, p1395_1, u0elo2]
                                    · have p1395_0 := h1395c.1
                                      have p1395_1 := h1395c.2.1
                                      have p1395_2 := h1395c.2.2.1
                                      have p1395_3 := h1395c.2.2.2
                                      linarith only [hlam, p1395_0]
                                    · have p1395_0 := h1395c.1
                                      have p1395_1 := h1395c.2.1
                                      have p1395_2 := h1395c.2.2.1
                                      have p1395_3 := h1395c.2.2.2
                                      rcases p1395_3 (m.d 0 1) (by simp) with h1472 | h1472
                                      · linarith only [h1, h1472, hlam]
                                      · linarith only [h1330, h1472, hlam]
                                    · have p1395_0 := h1395c.1
                                      have p1395_1 := h1395c.2.1
                                      have p1395_2 := h1395c.2.2.1
                                      have p1395_3 := h1395c.2.2.2
                                      rcases p1395_3 (m.d 0 1) (by simp) with h1475 | h1475
                                      · linarith only [h1, h1475, hlam]
                                      · linarith only [h1331, h1475, hlam]
                                    · have p1395_0 := h1395c.1
                                      have p1395_1 := h1395c.2.1
                                      have p1395_2 := h1395c.2.2.1
                                      have p1395_3 := h1395c.2.2.2
                                      linarith only [h1330, hlam, p1395_0]
                                    · have p1395_0 := h1395c.1
                                      have p1395_1 := h1395c.2.1
                                      have p1395_2 := h1395c.2.2.1
                                      have p1395_3 := h1395c.2.2.2
                                      linarith only [h1334, hlam, p1395_0]
                                    · have p1395_0 := h1395c.1
                                      have p1395_1 := h1395c.2.1
                                      have p1395_2 := h1395c.2.2.1
                                      have p1395_3 := h1395c.2.2.2
                                      linarith only [h1336, hlam, p1395_0]
                                    · have p1395_0 := h1395c.1
                                      have p1395_1 := h1395c.2.1
                                      have p1395_2 := h1395c.2.2.1
                                      have p1395_3 := h1395c.2.2.2
                                      linarith only [hlam, p1395_0]
                                    · have p1395_0 := h1395c.1
                                      have p1395_1 := h1395c.2.1
                                      have p1395_2 := h1395c.2.2.1
                                      have p1395_3 := h1395c.2.2.2
                                      linarith only [h1338, hlam, p1395_0]
                                    · have p1395_0 := h1395c.1
                                      have p1395_1 := h1395c.2.1
                                      have p1395_2 := h1395c.2.2.1
                                      have p1395_3 := h1395c.2.2.2
                                      linarith only [h1331, hlam, p1395_0]
                                    · have p1395_0 := h1395c.1
                                      have p1395_1 := h1395c.2.1
                                      have p1395_2 := h1395c.2.2.1
                                      have p1395_3 := h1395c.2.2.2
                                      linarith only [h1335, hlam, p1395_1]
                                    · have p1395_0 := h1395c.1
                                      have p1395_1 := h1395c.2.1
                                      have p1395_2 := h1395c.2.2.1
                                      have p1395_3 := h1395c.2.2.2
                                      linarith only [h1337, hlam, p1395_0]
                                    · have p1395_0 := h1395c.1
                                      have p1395_1 := h1395c.2.1
                                      have p1395_2 := h1395c.2.2.1
                                      have p1395_3 := h1395c.2.2.2
                                      linarith only [h1330, h1385, h1389, hc34, hlam, hphi, ht45, p1395_1, u5elo0]
                                    · have p1395_0 := h1395c.1
                                      have p1395_1 := h1395c.2.1
                                      have p1395_2 := h1395c.2.2.1
                                      have p1395_3 := h1395c.2.2.2
                                      linarith only [hlam, p1395_0]
                              · linarith only [h0, h1, h1383, h1385, h1389, h1390, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h0, h1, h1383, h1385, h1389, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1, h1385, h1388, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h1, h1385, h1387, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h1385, h1386, hc24, hlam, hphi, ht45, u5elo2]
                    · linarith only [h0, h1, h1334, h1383, h1385, hc12, hc23, hlam, hphi]
              · linarith only [h0, h1, h1334, h1337, hc24, hlam, hphi, ht45, u5elo3]
            · linarith only [h1, h1330, h1336, hlam]
          · linarith only [h1334, h1335, hc24, hlam, hphi, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1497 | h1497
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1498 | h1498
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1499 | h1499
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1500 | h1500
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1501 | h1501
                  · linarith only [h0, h1332, h1497, h1501, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1503 | h1503
                    · linarith only [h0, h1334, h1503, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1505 | h1505
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1506 | h1506
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1507 | h1507
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1508 | h1508
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1509 | h1509
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1510 | h1510
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1511 | h1511
                                  · rcases h0bigk with h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c | h1512c
                                    · have p1512_0 := h1512c.1
                                      have p1512_1 := h1512c.2.1
                                      have p1512_2 := h1512c.2.2.1
                                      have p1512_3 := h1512c.2.2.2
                                      linarith only [hlam, p1512_0]
                                    · have p1512_0 := h1512c.1
                                      have p1512_1 := h1512c.2.1
                                      have p1512_2 := h1512c.2.2.1
                                      have p1512_3 := h1512c.2.2.2
                                      linarith only [h0, h1, h1501, h1505, h1509, h1511, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1512_1]
                                    · have p1512_0 := h1512c.1
                                      have p1512_1 := h1512c.2.1
                                      have p1512_2 := h1512c.2.2.1
                                      have p1512_3 := h1512c.2.2.2
                                      linarith only [h1, hlam, p1512_0]
                                    · have p1512_0 := h1512c.1
                                      have p1512_1 := h1512c.2.1
                                      have p1512_2 := h1512c.2.2.1
                                      have p1512_3 := h1512c.2.2.2
                                      linarith only [h0, h1, h1334, h1501, h1505, h1509, h1511, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1512_1]
                                    · have p1512_0 := h1512c.1
                                      have p1512_1 := h1512c.2.1
                                      have p1512_2 := h1512c.2.2.1
                                      have p1512_3 := h1512c.2.2.2
                                      rcases p1512_3 (m.d 0 1) (by simp) with h1517 | h1517
                                      · rcases p1512_3 (m.d 0 2) (by simp) with h1518 | h1518
                                        · linarith only [h0, h1518, hlam]
                                        · linarith only [h1497, h1518, hlam]
                                      · linarith only [h1331, h1517, hlam]
                                    · have p1512_0 := h1512c.1
                                      have p1512_1 := h1512c.2.1
                                      have p1512_2 := h1512c.2.2.1
                                      have p1512_3 := h1512c.2.2.2
                                      linarith only [h0, hlam, p1512_0]
                                    · have p1512_0 := h1512c.1
                                      have p1512_1 := h1512c.2.1
                                      have p1512_2 := h1512c.2.2.1
                                      have p1512_3 := h1512c.2.2.2
                                      linarith only [hlam, p1512_0]
                                    · have p1512_0 := h1512c.1
                                      have p1512_1 := h1512c.2.1
                                      have p1512_2 := h1512c.2.2.1
                                      have p1512_3 := h1512c.2.2.2
                                      linarith only [h1332, hlam, p1512_0]
                                    · have p1512_0 := h1512c.1
                                      have p1512_1 := h1512c.2.1
                                      have p1512_2 := h1512c.2.2.1
                                      have p1512_3 := h1512c.2.2.2
                                      linarith only [h1334, hlam, p1512_1]
                                    · have p1512_0 := h1512c.1
                                      have p1512_1 := h1512c.2.1
                                      have p1512_2 := h1512c.2.2.1
                                      have p1512_3 := h1512c.2.2.2
                                      rcases p1512_3 (m.d 0 1) (by simp) with h1526 | h1526
                                      · rcases p1512_3 (m.d 0 2) (by simp) with h1527 | h1527
                                        · rcases p1512_3 (m.d 0 3) (by simp) with h1528 | h1528
                                          · rcases p1512_3 (m.d 0 4) (by simp) with h1529 | h1529
                                            · rcases p1512_3 (m.d 0 5) (by simp) with h1530 | h1530
                                              · linarith only [h1497, h1530, hlam]
                                              · rcases h2bigk with h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c | h1532c
                                                · have p1532_0 := h1532c.1
                                                  have p1532_1 := h1532c.2.1
                                                  have p1532_2 := h1532c.2.2.1
                                                  have p1532_3 := h1532c.2.2.2
                                                  linarith only [hlam, p1532_0]
                                                · have p1532_0 := h1532c.1
                                                  have p1532_1 := h1532c.2.1
                                                  have p1532_2 := h1532c.2.2.1
                                                  have p1532_3 := h1532c.2.2.2
                                                  linarith only [h1505, h1509, h1511, hc45, hlam, hphi, ht0b, ht5b, p1532_1, u0elo1]
                                                · have p1532_0 := h1532c.1
                                                  have p1532_1 := h1532c.2.1
                                                  have p1532_2 := h1532c.2.2.1
                                                  have p1532_3 := h1532c.2.2.2
                                                  linarith only [h1332, hlam, p1532_0]
                                                · have p1532_0 := h1532c.1
                                                  have p1532_1 := h1532c.2.1
                                                  have p1532_2 := h1532c.2.2.1
                                                  have p1532_3 := h1532c.2.2.2
                                                  linarith only [h1334, hlam, p1532_0]
                                                · have p1532_0 := h1532c.1
                                                  have p1532_1 := h1532c.2.1
                                                  have p1532_2 := h1532c.2.2.1
                                                  have p1532_3 := h1532c.2.2.2
                                                  rcases p1532_3 (m.d 0 2) (by simp) with h1537 | h1537
                                                  · rcases p1532_3 (m.d 1 2) (by simp) with h1538 | h1538
                                                    · linarith only [h0, h1538, hlam]
                                                    · linarith only [h1505, h1538, hlam]
                                                  · linarith only [h1537, hlam, p1532_0]
                                                · have p1532_0 := h1532c.1
                                                  have p1532_1 := h1532c.2.1
                                                  have p1532_2 := h1532c.2.2.1
                                                  have p1532_3 := h1532c.2.2.2
                                                  linarith only [h0, hlam, p1532_0]
                                                · have p1532_0 := h1532c.1
                                                  have p1532_1 := h1532c.2.1
                                                  have p1532_2 := h1532c.2.2.1
                                                  have p1532_3 := h1532c.2.2.2
                                                  linarith only [hlam, p1532_0]
                                                · have p1532_0 := h1532c.1
                                                  have p1532_1 := h1532c.2.1
                                                  have p1532_2 := h1532c.2.2.1
                                                  have p1532_3 := h1532c.2.2.2
                                                  linarith only [h1501, hlam, p1532_0]
                                                · have p1532_0 := h1532c.1
                                                  have p1532_1 := h1532c.2.1
                                                  have p1532_2 := h1532c.2.2.1
                                                  have p1532_3 := h1532c.2.2.2
                                                  linarith only [h1503, hlam, p1532_0]
                                                · have p1532_0 := h1532c.1
                                                  have p1532_1 := h1532c.2.1
                                                  have p1532_2 := h1532c.2.2.1
                                                  have p1532_3 := h1532c.2.2.2
                                                  linarith only [h0, h1, h1501, h1509, h1511, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1532_1]
                                                · have p1532_0 := h1532c.1
                                                  have p1532_1 := h1532c.2.1
                                                  have p1532_2 := h1532c.2.2.1
                                                  have p1532_3 := h1532c.2.2.2
                                                  linarith only [h1331, h1505, h1509, h1511, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1512_1, p1532_1]
                                                · have p1532_0 := h1532c.1
                                                  have p1532_1 := h1532c.2.1
                                                  have p1532_2 := h1532c.2.2.1
                                                  have p1532_3 := h1532c.2.2.2
                                                  rcases p1532_3 (m.d 0 2) (by simp) with h1548 | h1548
                                                  · linarith only [h1332, h1548, hlam]
                                                  · linarith only [h0, h1548, hlam]
                                                · have p1532_0 := h1532c.1
                                                  have p1532_1 := h1532c.2.1
                                                  have p1532_2 := h1532c.2.2.1
                                                  have p1532_3 := h1532c.2.2.2
                                                  linarith only [hlam, p1532_0]
                                                · have p1532_0 := h1532c.1
                                                  have p1532_1 := h1532c.2.1
                                                  have p1532_2 := h1532c.2.2.1
                                                  have p1532_3 := h1532c.2.2.2
                                                  linarith only [h1331, h1334, h1505, h1509, h1511, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1512_1, p1532_1]
                                                · have p1532_0 := h1532c.1
                                                  have p1532_1 := h1532c.2.1
                                                  have p1532_2 := h1532c.2.2.1
                                                  have p1532_3 := h1532c.2.2.2
                                                  linarith only [h0, h1, h1331, h1501, h1505, hlam, p1512_1, p1532_2]
                                                · have p1532_0 := h1532c.1
                                                  have p1532_1 := h1532c.2.1
                                                  have p1532_2 := h1532c.2.2.1
                                                  have p1532_3 := h1532c.2.2.2
                                                  linarith only [hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p1512_1, p1532_1]
                                                · have p1532_0 := h1532c.1
                                                  have p1532_1 := h1532c.2.1
                                                  have p1532_2 := h1532c.2.2.1
                                                  have p1532_3 := h1532c.2.2.2
                                                  rcases p1532_3 (m.d 0 2) (by simp) with h1555 | h1555
                                                  · linarith only [h1334, h1555, hlam]
                                                  · linarith only [h0, h1555, hlam]
                                                · have p1532_0 := h1532c.1
                                                  have p1532_1 := h1532c.2.1
                                                  have p1532_2 := h1532c.2.2.1
                                                  have p1532_3 := h1532c.2.2.2
                                                  linarith only [h1508, hlam, p1532_1]
                                                · have p1532_0 := h1532c.1
                                                  have p1532_1 := h1532c.2.1
                                                  have p1532_2 := h1532c.2.2.1
                                                  have p1532_3 := h1532c.2.2.2
                                                  linarith only [hlam, p1532_0]
                                                · have p1532_0 := h1532c.1
                                                  have p1532_1 := h1532c.2.1
                                                  have p1532_2 := h1532c.2.2.1
                                                  have p1532_3 := h1532c.2.2.2
                                                  linarith only [h1331, h1334, h1505, hlam, p1512_1, p1532_2]
                                                · have p1532_0 := h1532c.1
                                                  have p1532_1 := h1532c.2.1
                                                  have p1532_2 := h1532c.2.2.1
                                                  have p1532_3 := h1532c.2.2.2
                                                  linarith only [h1497, hlam, p1532_0]
                                                · have p1532_0 := h1532c.1
                                                  have p1532_1 := h1532c.2.1
                                                  have p1532_2 := h1532c.2.2.1
                                                  have p1532_3 := h1532c.2.2.2
                                                  linarith only [h1505, hlam, p1532_0]
                                                · have p1532_0 := h1532c.1
                                                  have p1532_1 := h1532c.2.1
                                                  have p1532_2 := h1532c.2.2.1
                                                  have p1532_3 := h1532c.2.2.2
                                                  linarith only [h1509, hlam, p1532_1]
                                                · have p1532_0 := h1532c.1
                                                  have p1532_1 := h1532c.2.1
                                                  have p1532_2 := h1532c.2.2.1
                                                  have p1532_3 := h1532c.2.2.2
                                                  linarith only [h1510, hlam, p1532_0]
                                                · have p1532_0 := h1532c.1
                                                  have p1532_1 := h1532c.2.1
                                                  have p1532_2 := h1532c.2.2.1
                                                  have p1532_3 := h1532c.2.2.2
                                                  linarith only [hlam, p1532_0]
                                            · linarith only [h1500, h1529, hlam]
                                          · linarith only [h1499, h1528, hlam]
                                        · linarith only [h1497, h1527, hlam]
                                      · linarith only [h1331, h1526, hlam]
                                    · have p1512_0 := h1512c.1
                                      have p1512_1 := h1512c.2.1
                                      have p1512_2 := h1512c.2.2.1
                                      have p1512_3 := h1512c.2.2.2
                                      linarith only [h1330, h1503, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1512_1, u0elo2]
                                    · have p1512_0 := h1512c.1
                                      have p1512_1 := h1512c.2.1
                                      have p1512_2 := h1512c.2.2.1
                                      have p1512_3 := h1512c.2.2.2
                                      linarith only [h1497, h1509, h1511, hc45, hlam, hphi, ht0b, ht5b, p1512_1, u0elo2]
                                    · have p1512_0 := h1512c.1
                                      have p1512_1 := h1512c.2.1
                                      have p1512_2 := h1512c.2.2.1
                                      have p1512_3 := h1512c.2.2.2
                                      linarith only [hlam, p1512_0]
                                    · have p1512_0 := h1512c.1
                                      have p1512_1 := h1512c.2.1
                                      have p1512_2 := h1512c.2.2.1
                                      have p1512_3 := h1512c.2.2.2
                                      linarith only [h1334, h1497, h1509, h1511, hc45, hlam, hphi, ht0b, ht5b, p1512_1, u0elo2]
                                    · have p1512_0 := h1512c.1
                                      have p1512_1 := h1512c.2.1
                                      have p1512_2 := h1512c.2.2.1
                                      have p1512_3 := h1512c.2.2.2
                                      rcases p1512_3 (m.d 0 1) (by simp) with h1574 | h1574
                                      · linarith only [h1, h1574, hlam]
                                      · linarith only [h1331, h1574, hlam]
                                    · have p1512_0 := h1512c.1
                                      have p1512_1 := h1512c.2.1
                                      have p1512_2 := h1512c.2.2.1
                                      have p1512_3 := h1512c.2.2.2
                                      linarith only [h1330, hlam, p1512_0]
                                    · have p1512_0 := h1512c.1
                                      have p1512_1 := h1512c.2.1
                                      have p1512_2 := h1512c.2.2.1
                                      have p1512_3 := h1512c.2.2.2
                                      linarith only [h0, h1505, h1509, h1511, hc45, hlam, hphi, ht0b, ht5b, p1512_1, u0elo3]
                                    · have p1512_0 := h1512c.1
                                      have p1512_1 := h1512c.2.1
                                      have p1512_2 := h1512c.2.2.1
                                      have p1512_3 := h1512c.2.2.2
                                      linarith only [h1498, hlam, p1512_0]
                                    · have p1512_0 := h1512c.1
                                      have p1512_1 := h1512c.2.1
                                      have p1512_2 := h1512c.2.2.1
                                      have p1512_3 := h1512c.2.2.2
                                      linarith only [hlam, p1512_0]
                                    · have p1512_0 := h1512c.1
                                      have p1512_1 := h1512c.2.1
                                      have p1512_2 := h1512c.2.2.1
                                      have p1512_3 := h1512c.2.2.2
                                      rcases p1512_3 (m.d 0 1) (by simp) with h1581 | h1581
                                      · rcases p1512_3 (m.d 0 2) (by simp) with h1582 | h1582
                                        · linarith only [h1334, h1582, hlam]
                                        · linarith only [h1497, h1582, hlam]
                                      · linarith only [h1331, h1581, hlam]
                                    · have p1512_0 := h1512c.1
                                      have p1512_1 := h1512c.2.1
                                      have p1512_2 := h1512c.2.2.1
                                      have p1512_3 := h1512c.2.2.2
                                      linarith only [h1331, hlam, p1512_0]
                                    · have p1512_0 := h1512c.1
                                      have p1512_1 := h1512c.2.1
                                      have p1512_2 := h1512c.2.2.1
                                      have p1512_3 := h1512c.2.2.2
                                      linarith only [h1497, hlam, p1512_1]
                                    · have p1512_0 := h1512c.1
                                      have p1512_1 := h1512c.2.1
                                      have p1512_2 := h1512c.2.2.1
                                      have p1512_3 := h1512c.2.2.2
                                      linarith only [h1499, hlam, p1512_0]
                                    · have p1512_0 := h1512c.1
                                      have p1512_1 := h1512c.2.1
                                      have p1512_2 := h1512c.2.2.1
                                      have p1512_3 := h1512c.2.2.2
                                      linarith only [h1500, hlam, p1512_1]
                                    · have p1512_0 := h1512c.1
                                      have p1512_1 := h1512c.2.1
                                      have p1512_2 := h1512c.2.2.1
                                      have p1512_3 := h1512c.2.2.2
                                      linarith only [hlam, p1512_0]
                                  · linarith only [h1, h1330, h1501, h1503, h1505, h1510, h1511, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h0, h1334, h1500, h1505, h1510, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                              · linarith only [h1, h1330, h1501, h1503, h1505, h1509, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h1, h1330, h1501, h1503, h1505, h1508, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h1, h1330, h1503, h1505, h1507, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h1, h1330, h1503, h1505, h1506, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h1, h1330, h1334, h1497, h1501, h1505, hc12, hc23, hlam, hphi]
                · linarith only [h1334, h1497, h1500, hc25, hlam, hphi, u5elo4]
              · linarith only [h0, h1, h1499, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
            · linarith only [h1, h1330, h1498, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1601 | h1601
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1602 | h1602
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1603 | h1603
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1604 | h1604
                  · linarith only [h0, h1497, h1604, hc23, hlam, hphi, ht34, ht45, u5elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1606 | h1606
                    · linarith only [h0, h1497, h1606, hc24, hlam, hphi, ht45, u5elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1608 | h1608
                      · linarith only [h0, h1497, h1608, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1610 | h1610
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1611 | h1611
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1612 | h1612
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1613 | h1613
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1614 | h1614
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1615 | h1615
                                  · rcases h0bigk with h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c | h1616c
                                    · have p1616_0 := h1616c.1
                                      have p1616_1 := h1616c.2.1
                                      have p1616_2 := h1616c.2.2.1
                                      have p1616_3 := h1616c.2.2.2
                                      linarith only [hlam, p1616_0]
                                    · have p1616_0 := h1616c.1
                                      have p1616_1 := h1616c.2.1
                                      have p1616_2 := h1616c.2.2.1
                                      have p1616_3 := h1616c.2.2.2
                                      linarith only [h1, h1604, hc02, hc23, hlam, hphi, p1616_1]
                                    · have p1616_0 := h1616c.1
                                      have p1616_1 := h1616c.2.1
                                      have p1616_2 := h1616c.2.2.1
                                      have p1616_3 := h1616c.2.2.2
                                      linarith only [h1, hlam, p1616_0]
                                    · have p1616_0 := h1616c.1
                                      have p1616_1 := h1616c.2.1
                                      have p1616_2 := h1616c.2.2.1
                                      have p1616_3 := h1616c.2.2.2
                                      linarith only [h1, h1330, h1604, h1610, h1615, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1616_1]
                                    · have p1616_0 := h1616c.1
                                      have p1616_1 := h1616c.2.1
                                      have p1616_2 := h1616c.2.2.1
                                      have p1616_3 := h1616c.2.2.2
                                      linarith only [h0, h1, h1497, h1604, hc12, hc23, hlam, hphi, p1616_1]
                                    · have p1616_0 := h1616c.1
                                      have p1616_1 := h1616c.2.1
                                      have p1616_2 := h1616c.2.2.1
                                      have p1616_3 := h1616c.2.2.2
                                      linarith only [h0, hlam, p1616_0]
                                    · have p1616_0 := h1616c.1
                                      have p1616_1 := h1616c.2.1
                                      have p1616_2 := h1616c.2.2.1
                                      have p1616_3 := h1616c.2.2.2
                                      linarith only [hlam, p1616_0]
                                    · have p1616_0 := h1616c.1
                                      have p1616_1 := h1616c.2.1
                                      have p1616_2 := h1616c.2.2.1
                                      have p1616_3 := h1616c.2.2.2
                                      linarith only [h1332, hlam, p1616_0]
                                    · have p1616_0 := h1616c.1
                                      have p1616_1 := h1616c.2.1
                                      have p1616_2 := h1616c.2.2.1
                                      have p1616_3 := h1616c.2.2.2
                                      linarith only [h1334, hlam, p1616_1]
                                    · have p1616_0 := h1616c.1
                                      have p1616_1 := h1616c.2.1
                                      have p1616_2 := h1616c.2.2.1
                                      have p1616_3 := h1616c.2.2.2
                                      linarith only [h1497, hlam, p1616_0]
                                    · have p1616_0 := h1616c.1
                                      have p1616_1 := h1616c.2.1
                                      have p1616_2 := h1616c.2.2.1
                                      have p1616_3 := h1616c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1616_1, u0elo2]
                                    · have p1616_0 := h1616c.1
                                      have p1616_1 := h1616c.2.1
                                      have p1616_2 := h1616c.2.2.1
                                      have p1616_3 := h1616c.2.2.2
                                      rcases p1616_3 (m.d 0 1) (by simp) with h1628 | h1628
                                      · linarith only [h1, h1628, hlam]
                                      · linarith only [h0, h1628, hlam]
                                    · have p1616_0 := h1616c.1
                                      have p1616_1 := h1616c.2.1
                                      have p1616_2 := h1616c.2.2.1
                                      have p1616_3 := h1616c.2.2.2
                                      linarith only [hlam, p1616_0]
                                    · have p1616_0 := h1616c.1
                                      have p1616_1 := h1616c.2.1
                                      have p1616_2 := h1616c.2.2.1
                                      have p1616_3 := h1616c.2.2.2
                                      linarith only [h1330, h1610, h1615, hc45, hlam, hphi, ht0b, ht5b, p1616_1, u0elo2]
                                    · have p1616_0 := h1616c.1
                                      have p1616_1 := h1616c.2.1
                                      have p1616_2 := h1616c.2.2.1
                                      have p1616_3 := h1616c.2.2.2
                                      rcases p1616_3 (m.d 0 1) (by simp) with h1633 | h1633
                                      · linarith only [h1, h1633, hlam]
                                      · linarith only [h1331, h1633, hlam]
                                    · have p1616_0 := h1616c.1
                                      have p1616_1 := h1616c.2.1
                                      have p1616_2 := h1616c.2.2.1
                                      have p1616_3 := h1616c.2.2.2
                                      linarith only [h1330, hlam, p1616_0]
                                    · have p1616_0 := h1616c.1
                                      have p1616_1 := h1616c.2.1
                                      have p1616_2 := h1616c.2.2.1
                                      have p1616_3 := h1616c.2.2.2
                                      linarith only [h0, h1, h1330, h1604, hc12, hc23, hlam, hphi, p1616_1]
                                    · have p1616_0 := h1616c.1
                                      have p1616_1 := h1616c.2.1
                                      have p1616_2 := h1616c.2.2.1
                                      have p1616_3 := h1616c.2.2.2
                                      linarith only [h1601, hlam, p1616_0]
                                    · have p1616_0 := h1616c.1
                                      have p1616_1 := h1616c.2.1
                                      have p1616_2 := h1616c.2.2.1
                                      have p1616_3 := h1616c.2.2.2
                                      linarith only [hlam, p1616_0]
                                    · have p1616_0 := h1616c.1
                                      have p1616_1 := h1616c.2.1
                                      have p1616_2 := h1616c.2.2.1
                                      have p1616_3 := h1616c.2.2.2
                                      linarith only [h0, h1, h1330, h1497, h1604, hc12, hc23, hlam, hphi, p1616_1]
                                    · have p1616_0 := h1616c.1
                                      have p1616_1 := h1616c.2.1
                                      have p1616_2 := h1616c.2.2.1
                                      have p1616_3 := h1616c.2.2.2
                                      linarith only [h1331, hlam, p1616_0]
                                    · have p1616_0 := h1616c.1
                                      have p1616_1 := h1616c.2.1
                                      have p1616_2 := h1616c.2.2.1
                                      have p1616_3 := h1616c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p1616_1, u5elo0]
                                    · have p1616_0 := h1616c.1
                                      have p1616_1 := h1616c.2.1
                                      have p1616_2 := h1616c.2.2.1
                                      have p1616_3 := h1616c.2.2.2
                                      linarith only [h1602, hlam, p1616_0]
                                    · have p1616_0 := h1616c.1
                                      have p1616_1 := h1616c.2.1
                                      have p1616_2 := h1616c.2.2.1
                                      have p1616_3 := h1616c.2.2.2
                                      linarith only [h1603, hlam, p1616_1]
                                    · have p1616_0 := h1616c.1
                                      have p1616_1 := h1616c.2.1
                                      have p1616_2 := h1616c.2.2.1
                                      have p1616_3 := h1616c.2.2.2
                                      linarith only [hlam, p1616_0]
                                  · rcases h0bigk with h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c
                                    · have p1646_0 := h1646c.1
                                      have p1646_1 := h1646c.2.1
                                      have p1646_2 := h1646c.2.2.1
                                      have p1646_3 := h1646c.2.2.2
                                      linarith only [hlam, p1646_0]
                                    · have p1646_0 := h1646c.1
                                      have p1646_1 := h1646c.2.1
                                      have p1646_2 := h1646c.2.2.1
                                      have p1646_3 := h1646c.2.2.2
                                      linarith only [h0, h1, h1604, hc12, hc23, hlam, hphi, p1646_1]
                                    · have p1646_0 := h1646c.1
                                      have p1646_1 := h1646c.2.1
                                      have p1646_2 := h1646c.2.2.1
                                      have p1646_3 := h1646c.2.2.2
                                      linarith only [h1, hlam, p1646_0]
                                    · have p1646_0 := h1646c.1
                                      have p1646_1 := h1646c.2.1
                                      have p1646_2 := h1646c.2.2.1
                                      have p1646_3 := h1646c.2.2.2
                                      linarith only [h1, h1603, h1604, h1615, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1646_1]
                                    · have p1646_0 := h1646c.1
                                      have p1646_1 := h1646c.2.1
                                      have p1646_2 := h1646c.2.2.1
                                      have p1646_3 := h1646c.2.2.2
                                      linarith only [h1, h1331, h1604, h1608, hc12, hc23, hlam, hphi, p1646_1]
                                    · have p1646_0 := h1646c.1
                                      have p1646_1 := h1646c.2.1
                                      have p1646_2 := h1646c.2.2.1
                                      have p1646_3 := h1646c.2.2.2
                                      linarith only [h0, hlam, p1646_0]
                                    · have p1646_0 := h1646c.1
                                      have p1646_1 := h1646c.2.1
                                      have p1646_2 := h1646c.2.2.1
                                      have p1646_3 := h1646c.2.2.2
                                      linarith only [hlam, p1646_0]
                                    · have p1646_0 := h1646c.1
                                      have p1646_1 := h1646c.2.1
                                      have p1646_2 := h1646c.2.2.1
                                      have p1646_3 := h1646c.2.2.2
                                      linarith only [h1332, hlam, p1646_0]
                                    · have p1646_0 := h1646c.1
                                      have p1646_1 := h1646c.2.1
                                      have p1646_2 := h1646c.2.2.1
                                      have p1646_3 := h1646c.2.2.2
                                      linarith only [h1334, hlam, p1646_1]
                                    · have p1646_0 := h1646c.1
                                      have p1646_1 := h1646c.2.1
                                      have p1646_2 := h1646c.2.2.1
                                      have p1646_3 := h1646c.2.2.2
                                      linarith only [h1497, hlam, p1646_0]
                                    · have p1646_0 := h1646c.1
                                      have p1646_1 := h1646c.2.1
                                      have p1646_2 := h1646c.2.2.1
                                      have p1646_3 := h1646c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1646_1, u0elo2]
                                    · have p1646_0 := h1646c.1
                                      have p1646_1 := h1646c.2.1
                                      have p1646_2 := h1646c.2.2.1
                                      have p1646_3 := h1646c.2.2.2
                                      rcases p1646_3 (m.d 0 1) (by simp) with h1658 | h1658
                                      · linarith only [h1, h1658, hlam]
                                      · linarith only [h0, h1658, hlam]
                                    · have p1646_0 := h1646c.1
                                      have p1646_1 := h1646c.2.1
                                      have p1646_2 := h1646c.2.2.1
                                      have p1646_3 := h1646c.2.2.2
                                      linarith only [hlam, p1646_0]
                                    · have p1646_0 := h1646c.1
                                      have p1646_1 := h1646c.2.1
                                      have p1646_2 := h1646c.2.2.1
                                      have p1646_3 := h1646c.2.2.2
                                      linarith only [h1603, h1615, hc34, hlam, hphi, ht0b, ht45, ht5b, p1646_1, u0elo2]
                                    · have p1646_0 := h1646c.1
                                      have p1646_1 := h1646c.2.1
                                      have p1646_2 := h1646c.2.2.1
                                      have p1646_3 := h1646c.2.2.2
                                      linarith only [h1603, h1615, hc34, hlam, hphi, ht0b, ht45, ht5b, p1646_1, u0elo2]
                                    · have p1646_0 := h1646c.1
                                      have p1646_1 := h1646c.2.1
                                      have p1646_2 := h1646c.2.2.1
                                      have p1646_3 := h1646c.2.2.2
                                      linarith only [h1330, hlam, p1646_0]
                                    · have p1646_0 := h1646c.1
                                      have p1646_1 := h1646c.2.1
                                      have p1646_2 := h1646c.2.2.1
                                      have p1646_3 := h1646c.2.2.2
                                      linarith only [h0, h1, h1330, h1604, hc12, hc23, hlam, hphi, p1646_1]
                                    · have p1646_0 := h1646c.1
                                      have p1646_1 := h1646c.2.1
                                      have p1646_2 := h1646c.2.2.1
                                      have p1646_3 := h1646c.2.2.2
                                      linarith only [h1601, hlam, p1646_0]
                                    · have p1646_0 := h1646c.1
                                      have p1646_1 := h1646c.2.1
                                      have p1646_2 := h1646c.2.2.1
                                      have p1646_3 := h1646c.2.2.2
                                      linarith only [hlam, p1646_0]
                                    · have p1646_0 := h1646c.1
                                      have p1646_1 := h1646c.2.1
                                      have p1646_2 := h1646c.2.2.1
                                      have p1646_3 := h1646c.2.2.2
                                      linarith only [h1, h1330, h1603, h1604, h1615, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1646_1]
                                    · have p1646_0 := h1646c.1
                                      have p1646_1 := h1646c.2.1
                                      have p1646_2 := h1646c.2.2.1
                                      have p1646_3 := h1646c.2.2.2
                                      linarith only [h1331, hlam, p1646_0]
                                    · have p1646_0 := h1646c.1
                                      have p1646_1 := h1646c.2.1
                                      have p1646_2 := h1646c.2.2.1
                                      have p1646_3 := h1646c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p1646_1, u5elo0]
                                    · have p1646_0 := h1646c.1
                                      have p1646_1 := h1646c.2.1
                                      have p1646_2 := h1646c.2.2.1
                                      have p1646_3 := h1646c.2.2.2
                                      linarith only [h1602, hlam, p1646_0]
                                    · have p1646_0 := h1646c.1
                                      have p1646_1 := h1646c.2.1
                                      have p1646_2 := h1646c.2.2.1
                                      have p1646_3 := h1646c.2.2.2
                                      linarith only [h1603, hlam, p1646_1]
                                    · have p1646_0 := h1646c.1
                                      have p1646_1 := h1646c.2.1
                                      have p1646_2 := h1646c.2.2.1
                                      have p1646_3 := h1646c.2.2.2
                                      linarith only [hlam, p1646_0]
                                · linarith only [h1334, h1603, h1614, hlam]
                              · linarith only [h1, h1604, h1613, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                            · linarith only [h1, h1330, h1604, h1606, h1612, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h1, h1330, h1606, h1611, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h1330, h1606, h1610, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1679 | h1679
                  · linarith only [h0, h1332, h1679, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1681 | h1681
                    · linarith only [h0, h1334, h1681, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1683 | h1683
                      · linarith only [h0, h1334, h1603, h1683, hc25, hlam, hphi, u5elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1685 | h1685
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1686 | h1686
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1687 | h1687
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1688 | h1688
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1689 | h1689
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1690 | h1690
                                  · linarith only [h1330, h1603, h1685, h1690, hlam]
                                  · rcases h0bigk with h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c | h1692c
                                    · have p1692_0 := h1692c.1
                                      have p1692_1 := h1692c.2.1
                                      have p1692_2 := h1692c.2.2.1
                                      have p1692_3 := h1692c.2.2.2
                                      linarith only [hlam, p1692_0]
                                    · have p1692_0 := h1692c.1
                                      have p1692_1 := h1692c.2.1
                                      have p1692_2 := h1692c.2.2.1
                                      have p1692_3 := h1692c.2.2.2
                                      linarith only [h0, h1, h1679, hc12, hc23, hlam, hphi, p1692_1]
                                    · have p1692_0 := h1692c.1
                                      have p1692_1 := h1692c.2.1
                                      have p1692_2 := h1692c.2.2.1
                                      have p1692_3 := h1692c.2.2.2
                                      linarith only [h1, hlam, p1692_0]
                                    · have p1692_0 := h1692c.1
                                      have p1692_1 := h1692c.2.1
                                      have p1692_2 := h1692c.2.2.1
                                      have p1692_3 := h1692c.2.2.2
                                      linarith only [h0, h1, h1334, h1679, hc12, hc23, hlam, hphi, p1692_1]
                                    · have p1692_0 := h1692c.1
                                      have p1692_1 := h1692c.2.1
                                      have p1692_2 := h1692c.2.2.1
                                      have p1692_3 := h1692c.2.2.2
                                      linarith only [h0, h1, h1497, h1679, hc12, hc23, hlam, hphi, p1692_1]
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
                                      linarith only [h1332, hlam, p1692_0]
                                    · have p1692_0 := h1692c.1
                                      have p1692_1 := h1692c.2.1
                                      have p1692_2 := h1692c.2.2.1
                                      have p1692_3 := h1692c.2.2.2
                                      linarith only [h1334, hlam, p1692_1]
                                    · have p1692_0 := h1692c.1
                                      have p1692_1 := h1692c.2.1
                                      have p1692_2 := h1692c.2.2.1
                                      have p1692_3 := h1692c.2.2.2
                                      linarith only [h1497, hlam, p1692_0]
                                    · have p1692_0 := h1692c.1
                                      have p1692_1 := h1692c.2.1
                                      have p1692_2 := h1692c.2.2.1
                                      have p1692_3 := h1692c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1692_1, u0elo2]
                                    · have p1692_0 := h1692c.1
                                      have p1692_1 := h1692c.2.1
                                      have p1692_2 := h1692c.2.2.1
                                      have p1692_3 := h1692c.2.2.2
                                      rcases p1692_3 (m.d 0 1) (by simp) with h1704 | h1704
                                      · linarith only [h1, h1704, hlam]
                                      · linarith only [h0, h1704, hlam]
                                    · have p1692_0 := h1692c.1
                                      have p1692_1 := h1692c.2.1
                                      have p1692_2 := h1692c.2.2.1
                                      have p1692_3 := h1692c.2.2.2
                                      linarith only [hlam, p1692_0]
                                    · have p1692_0 := h1692c.1
                                      have p1692_1 := h1692c.2.1
                                      have p1692_2 := h1692c.2.2.1
                                      have p1692_3 := h1692c.2.2.2
                                      rcases p1692_3 (m.d 0 1) (by simp) with h1708 | h1708
                                      · linarith only [h1, h1708, hlam]
                                      · linarith only [h1330, h1708, hlam]
                                    · have p1692_0 := h1692c.1
                                      have p1692_1 := h1692c.2.1
                                      have p1692_2 := h1692c.2.2.1
                                      have p1692_3 := h1692c.2.2.2
                                      rcases p1692_3 (m.d 0 1) (by simp) with h1711 | h1711
                                      · linarith only [h1, h1711, hlam]
                                      · linarith only [h1331, h1711, hlam]
                                    · have p1692_0 := h1692c.1
                                      have p1692_1 := h1692c.2.1
                                      have p1692_2 := h1692c.2.2.1
                                      have p1692_3 := h1692c.2.2.2
                                      linarith only [h1330, hlam, p1692_0]
                                    · have p1692_0 := h1692c.1
                                      have p1692_1 := h1692c.2.1
                                      have p1692_2 := h1692c.2.2.1
                                      have p1692_3 := h1692c.2.2.2
                                      linarith only [h0, h1603, hc12, hlam, hphi, ht23, ht34, ht45, p1692_1, u5elo0]
                                    · have p1692_0 := h1692c.1
                                      have p1692_1 := h1692c.2.1
                                      have p1692_2 := h1692c.2.2.1
                                      have p1692_3 := h1692c.2.2.2
                                      linarith only [h1601, hlam, p1692_0]
                                    · have p1692_0 := h1692c.1
                                      have p1692_1 := h1692c.2.1
                                      have p1692_2 := h1692c.2.2.1
                                      have p1692_3 := h1692c.2.2.2
                                      linarith only [hlam, p1692_0]
                                    · have p1692_0 := h1692c.1
                                      have p1692_1 := h1692c.2.1
                                      have p1692_2 := h1692c.2.2.1
                                      have p1692_3 := h1692c.2.2.2
                                      linarith only [h1603, hlam, p1692_0]
                                    · have p1692_0 := h1692c.1
                                      have p1692_1 := h1692c.2.1
                                      have p1692_2 := h1692c.2.2.1
                                      have p1692_3 := h1692c.2.2.2
                                      linarith only [h1331, hlam, p1692_0]
                                    · have p1692_0 := h1692c.1
                                      have p1692_1 := h1692c.2.1
                                      have p1692_2 := h1692c.2.2.1
                                      have p1692_3 := h1692c.2.2.2
                                      linarith only [h0, h1497, hc12, hlam, hphi, ht23, ht34, ht45, p1692_1, u5elo2]
                                    · have p1692_0 := h1692c.1
                                      have p1692_1 := h1692c.2.1
                                      have p1692_2 := h1692c.2.2.1
                                      have p1692_3 := h1692c.2.2.2
                                      linarith only [h1602, hlam, p1692_0]
                                    · have p1692_0 := h1692c.1
                                      have p1692_1 := h1692c.2.1
                                      have p1692_2 := h1692c.2.2.1
                                      have p1692_3 := h1692c.2.2.2
                                      linarith only [h1497, hc04, hlam, hphi, ht45, p1692_1, u5elo2]
                                    · have p1692_0 := h1692c.1
                                      have p1692_1 := h1692c.2.1
                                      have p1692_2 := h1692c.2.2.1
                                      have p1692_3 := h1692c.2.2.2
                                      linarith only [hlam, p1692_0]
                                · linarith only [h0, h1334, h1689, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                              · linarith only [h1, h1679, h1688, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                            · linarith only [h1, h1330, h1679, h1681, h1687, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h1, h1330, h1681, h1686, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h1330, h1681, h1685, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h1330, h1602, hc14, hlam, hphi, ht45, u5elo3]
            · linarith only [h1, h1330, h1601, hlam]
    · linarith only [h0, h1331, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1732 | h1732
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1733 | h1733
      · linarith only [h0, h1, h1733, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1735 | h1735
        · linarith only [h0, h1330, h1735, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1737 | h1737
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1738 | h1738
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1739 | h1739
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1740 | h1740
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1741 | h1741
                  · linarith only [h0, h1733, h1741, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1743 | h1743
                    · linarith only [h0, h1330, h1735, h1743, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1745 | h1745
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1746 | h1746
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1747 | h1747
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1748 | h1748
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1749 | h1749
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1750 | h1750
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1751 | h1751
                                  · rcases h0bigk with h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c
                                    · have p1752_0 := h1752c.1
                                      have p1752_1 := h1752c.2.1
                                      have p1752_2 := h1752c.2.2.1
                                      have p1752_3 := h1752c.2.2.2
                                      linarith only [hlam, p1752_0]
                                    · have p1752_0 := h1752c.1
                                      have p1752_1 := h1752c.2.1
                                      have p1752_2 := h1752c.2.2.1
                                      have p1752_3 := h1752c.2.2.2
                                      linarith only [h1330, h1741, h1746, hc02, hc23, hlam, hphi, p1752_1]
                                    · have p1752_0 := h1752c.1
                                      have p1752_1 := h1752c.2.1
                                      have p1752_2 := h1752c.2.2.1
                                      have p1752_3 := h1752c.2.2.2
                                      linarith only [h1, hlam, p1752_0]
                                    · have p1752_0 := h1752c.1
                                      have p1752_1 := h1752c.2.1
                                      have p1752_2 := h1752c.2.2.1
                                      have p1752_3 := h1752c.2.2.2
                                      linarith only [h1330, hlam, p1752_1]
                                    · have p1752_0 := h1752c.1
                                      have p1752_1 := h1752c.2.1
                                      have p1752_2 := h1752c.2.2.1
                                      have p1752_3 := h1752c.2.2.2
                                      rcases p1752_3 (m.d 0 1) (by simp) with h1757 | h1757
                                      · rcases p1752_3 (m.d 0 2) (by simp) with h1758 | h1758
                                        · linarith only [h0, h1758, hlam]
                                        · linarith only [h1737, h1758, hlam]
                                      · linarith only [h1732, h1757, hlam]
                                    · have p1752_0 := h1752c.1
                                      have p1752_1 := h1752c.2.1
                                      have p1752_2 := h1752c.2.2.1
                                      have p1752_3 := h1752c.2.2.2
                                      linarith only [h0, hlam, p1752_0]
                                    · have p1752_0 := h1752c.1
                                      have p1752_1 := h1752c.2.1
                                      have p1752_2 := h1752c.2.2.1
                                      have p1752_3 := h1752c.2.2.2
                                      linarith only [hlam, p1752_0]
                                    · have p1752_0 := h1752c.1
                                      have p1752_1 := h1752c.2.1
                                      have p1752_2 := h1752c.2.2.1
                                      have p1752_3 := h1752c.2.2.2
                                      linarith only [h1733, hlam, p1752_0]
                                    · have p1752_0 := h1752c.1
                                      have p1752_1 := h1752c.2.1
                                      have p1752_2 := h1752c.2.2.1
                                      have p1752_3 := h1752c.2.2.2
                                      linarith only [h1735, hlam, p1752_1]
                                    · have p1752_0 := h1752c.1
                                      have p1752_1 := h1752c.2.1
                                      have p1752_2 := h1752c.2.2.1
                                      have p1752_3 := h1752c.2.2.2
                                      rcases p1752_3 (m.d 0 1) (by simp) with h1766 | h1766
                                      · rcases p1752_3 (m.d 0 2) (by simp) with h1767 | h1767
                                        · rcases p1752_3 (m.d 0 3) (by simp) with h1768 | h1768
                                          · rcases p1752_3 (m.d 0 4) (by simp) with h1769 | h1769
                                            · rcases p1752_3 (m.d 0 5) (by simp) with h1770 | h1770
                                              · linarith only [h1737, h1770, hlam]
                                              · rcases h2bigk with h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c | h1772c
                                                · have p1772_0 := h1772c.1
                                                  have p1772_1 := h1772c.2.1
                                                  have p1772_2 := h1772c.2.2.1
                                                  have p1772_3 := h1772c.2.2.2
                                                  linarith only [hlam, p1772_0]
                                                · have p1772_0 := h1772c.1
                                                  have p1772_1 := h1772c.2.1
                                                  have p1772_2 := h1772c.2.2.1
                                                  have p1772_3 := h1772c.2.2.2
                                                  linarith only [h0, h1330, h1741, h1746, hc12, hc23, hlam, hphi, p1772_1]
                                                · have p1772_0 := h1772c.1
                                                  have p1772_1 := h1772c.2.1
                                                  have p1772_2 := h1772c.2.2.1
                                                  have p1772_3 := h1772c.2.2.2
                                                  linarith only [h1733, hlam, p1772_0]
                                                · have p1772_0 := h1772c.1
                                                  have p1772_1 := h1772c.2.1
                                                  have p1772_2 := h1772c.2.2.1
                                                  have p1772_3 := h1772c.2.2.2
                                                  linarith only [h1735, hlam, p1772_0]
                                                · have p1772_0 := h1772c.1
                                                  have p1772_1 := h1772c.2.1
                                                  have p1772_2 := h1772c.2.2.1
                                                  have p1772_3 := h1772c.2.2.2
                                                  rcases p1772_3 (m.d 0 2) (by simp) with h1777 | h1777
                                                  · rcases p1772_3 (m.d 1 2) (by simp) with h1778 | h1778
                                                    · linarith only [h0, h1778, hlam]
                                                    · linarith only [h1745, h1778, hlam]
                                                  · linarith only [h1777, hlam, p1772_0]
                                                · have p1772_0 := h1772c.1
                                                  have p1772_1 := h1772c.2.1
                                                  have p1772_2 := h1772c.2.2.1
                                                  have p1772_3 := h1772c.2.2.2
                                                  linarith only [h0, hlam, p1772_0]
                                                · have p1772_0 := h1772c.1
                                                  have p1772_1 := h1772c.2.1
                                                  have p1772_2 := h1772c.2.2.1
                                                  have p1772_3 := h1772c.2.2.2
                                                  linarith only [hlam, p1772_0]
                                                · have p1772_0 := h1772c.1
                                                  have p1772_1 := h1772c.2.1
                                                  have p1772_2 := h1772c.2.2.1
                                                  have p1772_3 := h1772c.2.2.2
                                                  linarith only [h1741, hlam, p1772_0]
                                                · have p1772_0 := h1772c.1
                                                  have p1772_1 := h1772c.2.1
                                                  have p1772_2 := h1772c.2.2.1
                                                  have p1772_3 := h1772c.2.2.2
                                                  linarith only [h1743, hlam, p1772_0]
                                                · have p1772_0 := h1772c.1
                                                  have p1772_1 := h1772c.2.1
                                                  have p1772_2 := h1772c.2.2.1
                                                  have p1772_3 := h1772c.2.2.2
                                                  linarith only [h0, h1330, h1741, h1746, h1749, h1751, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1772_1]
                                                · have p1772_0 := h1772c.1
                                                  have p1772_1 := h1772c.2.1
                                                  have p1772_2 := h1772c.2.2.1
                                                  have p1772_3 := h1772c.2.2.2
                                                  linarith only [h1732, h1745, h1749, h1751, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1752_1, p1772_1]
                                                · have p1772_0 := h1772c.1
                                                  have p1772_1 := h1772c.2.1
                                                  have p1772_2 := h1772c.2.2.1
                                                  have p1772_3 := h1772c.2.2.2
                                                  rcases p1772_3 (m.d 0 2) (by simp) with h1788 | h1788
                                                  · linarith only [h1733, h1788, hlam]
                                                  · linarith only [h0, h1788, hlam]
                                                · have p1772_0 := h1772c.1
                                                  have p1772_1 := h1772c.2.1
                                                  have p1772_2 := h1772c.2.2.1
                                                  have p1772_3 := h1772c.2.2.2
                                                  linarith only [hlam, p1772_0]
                                                · have p1772_0 := h1772c.1
                                                  have p1772_1 := h1772c.2.1
                                                  have p1772_2 := h1772c.2.2.1
                                                  have p1772_3 := h1772c.2.2.2
                                                  linarith only [h1330, h1743, hc01, hc23, hlam, hphi, ht12, p1772_1]
                                                · have p1772_0 := h1772c.1
                                                  have p1772_1 := h1772c.2.1
                                                  have p1772_2 := h1772c.2.2.1
                                                  have p1772_3 := h1772c.2.2.2
                                                  linarith only [h0, h1330, h1732, h1741, h1745, h1746, hlam, p1752_1, p1772_2]
                                                · have p1772_0 := h1772c.1
                                                  have p1772_1 := h1772c.2.1
                                                  have p1772_2 := h1772c.2.2.1
                                                  have p1772_3 := h1772c.2.2.2
                                                  linarith only [h1732, h1745, h1749, h1751, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1752_1, p1772_1]
                                                · have p1772_0 := h1772c.1
                                                  have p1772_1 := h1772c.2.1
                                                  have p1772_2 := h1772c.2.2.1
                                                  have p1772_3 := h1772c.2.2.2
                                                  rcases p1772_3 (m.d 0 2) (by simp) with h1795 | h1795
                                                  · linarith only [h1735, h1795, hlam]
                                                  · linarith only [h0, h1795, hlam]
                                                · have p1772_0 := h1772c.1
                                                  have p1772_1 := h1772c.2.1
                                                  have p1772_2 := h1772c.2.2.1
                                                  have p1772_3 := h1772c.2.2.2
                                                  linarith only [h1748, hlam, p1772_1]
                                                · have p1772_0 := h1772c.1
                                                  have p1772_1 := h1772c.2.1
                                                  have p1772_2 := h1772c.2.2.1
                                                  have p1772_3 := h1772c.2.2.2
                                                  linarith only [hlam, p1772_0]
                                                · have p1772_0 := h1772c.1
                                                  have p1772_1 := h1772c.2.1
                                                  have p1772_2 := h1772c.2.2.1
                                                  have p1772_3 := h1772c.2.2.2
                                                  linarith only [h1732, h1735, h1745, hlam, p1752_1, p1772_2]
                                                · have p1772_0 := h1772c.1
                                                  have p1772_1 := h1772c.2.1
                                                  have p1772_2 := h1772c.2.2.1
                                                  have p1772_3 := h1772c.2.2.2
                                                  linarith only [h1737, hlam, p1772_0]
                                                · have p1772_0 := h1772c.1
                                                  have p1772_1 := h1772c.2.1
                                                  have p1772_2 := h1772c.2.2.1
                                                  have p1772_3 := h1772c.2.2.2
                                                  linarith only [h1745, hlam, p1772_0]
                                                · have p1772_0 := h1772c.1
                                                  have p1772_1 := h1772c.2.1
                                                  have p1772_2 := h1772c.2.2.1
                                                  have p1772_3 := h1772c.2.2.2
                                                  linarith only [h1749, hlam, p1772_1]
                                                · have p1772_0 := h1772c.1
                                                  have p1772_1 := h1772c.2.1
                                                  have p1772_2 := h1772c.2.2.1
                                                  have p1772_3 := h1772c.2.2.2
                                                  linarith only [h1750, hlam, p1772_0]
                                                · have p1772_0 := h1772c.1
                                                  have p1772_1 := h1772c.2.1
                                                  have p1772_2 := h1772c.2.2.1
                                                  have p1772_3 := h1772c.2.2.2
                                                  linarith only [hlam, p1772_0]
                                            · linarith only [h1740, h1769, hlam]
                                          · linarith only [h1739, h1768, hlam]
                                        · linarith only [h1737, h1767, hlam]
                                      · linarith only [h1732, h1766, hlam]
                                    · have p1752_0 := h1752c.1
                                      have p1752_1 := h1752c.2.1
                                      have p1752_2 := h1752c.2.2.1
                                      have p1752_3 := h1752c.2.2.2
                                      linarith only [h0, h1745, h1749, h1751, hc45, hlam, hphi, ht0b, ht5b, p1752_1, u0elo2]
                                    · have p1752_0 := h1752c.1
                                      have p1752_1 := h1752c.2.1
                                      have p1752_2 := h1752c.2.2.1
                                      have p1752_3 := h1752c.2.2.2
                                      linarith only [h0, h1745, h1749, h1751, hc45, hlam, hphi, ht0b, ht5b, p1752_1, u0elo2]
                                    · have p1752_0 := h1752c.1
                                      have p1752_1 := h1752c.2.1
                                      have p1752_2 := h1752c.2.2.1
                                      have p1752_3 := h1752c.2.2.2
                                      linarith only [hlam, p1752_0]
                                    · have p1752_0 := h1752c.1
                                      have p1752_1 := h1752c.2.1
                                      have p1752_2 := h1752c.2.2.1
                                      have p1752_3 := h1752c.2.2.2
                                      linarith only [h0, h1330, h1745, h1749, h1751, hc45, hlam, hphi, ht0b, ht5b, p1752_1, u0elo2]
                                    · have p1752_0 := h1752c.1
                                      have p1752_1 := h1752c.2.1
                                      have p1752_2 := h1752c.2.2.1
                                      have p1752_3 := h1752c.2.2.2
                                      rcases p1752_3 (m.d 0 1) (by simp) with h1814 | h1814
                                      · linarith only [h1, h1814, hlam]
                                      · linarith only [h1732, h1814, hlam]
                                    · have p1752_0 := h1752c.1
                                      have p1752_1 := h1752c.2.1
                                      have p1752_2 := h1752c.2.2.1
                                      have p1752_3 := h1752c.2.2.2
                                      linarith only [h0, h1745, h1749, h1751, hc45, hlam, hphi, ht0b, ht5b, p1752_1, u0elo3]
                                    · have p1752_0 := h1752c.1
                                      have p1752_1 := h1752c.2.1
                                      have p1752_2 := h1752c.2.2.1
                                      have p1752_3 := h1752c.2.2.2
                                      linarith only [h0, h1745, h1749, h1751, hc45, hlam, hphi, ht0b, ht5b, p1752_1, u0elo3]
                                    · have p1752_0 := h1752c.1
                                      have p1752_1 := h1752c.2.1
                                      have p1752_2 := h1752c.2.2.1
                                      have p1752_3 := h1752c.2.2.2
                                      linarith only [h1738, hlam, p1752_0]
                                    · have p1752_0 := h1752c.1
                                      have p1752_1 := h1752c.2.1
                                      have p1752_2 := h1752c.2.2.1
                                      have p1752_3 := h1752c.2.2.2
                                      linarith only [hlam, p1752_0]
                                    · have p1752_0 := h1752c.1
                                      have p1752_1 := h1752c.2.1
                                      have p1752_2 := h1752c.2.2.1
                                      have p1752_3 := h1752c.2.2.2
                                      rcases p1752_3 (m.d 0 1) (by simp) with h1821 | h1821
                                      · linarith only [h1330, h1821, hlam]
                                      · linarith only [h1732, h1821, hlam]
                                    · have p1752_0 := h1752c.1
                                      have p1752_1 := h1752c.2.1
                                      have p1752_2 := h1752c.2.2.1
                                      have p1752_3 := h1752c.2.2.2
                                      linarith only [h1732, hlam, p1752_0]
                                    · have p1752_0 := h1752c.1
                                      have p1752_1 := h1752c.2.1
                                      have p1752_2 := h1752c.2.2.1
                                      have p1752_3 := h1752c.2.2.2
                                      linarith only [h1737, hlam, p1752_1]
                                    · have p1752_0 := h1752c.1
                                      have p1752_1 := h1752c.2.1
                                      have p1752_2 := h1752c.2.2.1
                                      have p1752_3 := h1752c.2.2.2
                                      linarith only [h1739, hlam, p1752_0]
                                    · have p1752_0 := h1752c.1
                                      have p1752_1 := h1752c.2.1
                                      have p1752_2 := h1752c.2.2.1
                                      have p1752_3 := h1752c.2.2.2
                                      linarith only [h1740, hlam, p1752_1]
                                    · have p1752_0 := h1752c.1
                                      have p1752_1 := h1752c.2.1
                                      have p1752_2 := h1752c.2.2.1
                                      have p1752_3 := h1752c.2.2.2
                                      linarith only [hlam, p1752_0]
                                  · linarith only [h0, h1330, h1741, h1745, h1746, h1750, h1751, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h0, h1330, h1740, h1743, h1750, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                              · linarith only [h0, h1330, h1741, h1745, h1746, h1749, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h0, h1330, h1741, h1745, h1746, h1748, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h0, h1330, h1745, h1746, h1747, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h0, h1, h1738, h1745, h1746, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                      · linarith only [h0, h1, h1737, h1741, h1745, hc12, hc23, hlam, hphi]
                · linarith only [h0, h1330, h1737, h1740, hc25, hlam, hphi, u5elo4]
              · linarith only [h0, h1, h1739, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1838 | h1838
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1839 | h1839
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1840 | h1840
                  · linarith only [h0, h1733, h1737, h1840, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1842 | h1842
                    · linarith only [h0, h1735, h1842, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1844 | h1844
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1845 | h1845
                        · linarith only [h0, h1, h1738, h1840, h1845, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h1844, h1845, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h0, h1330, h1737, h1842, h1844, hc12, hc24, hlam, hphi]
                · linarith only [h0, h1330, h1737, h1839, hc25, hlam, hphi, u5elo4]
              · linarith only [h0, h1, h1838, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1851 | h1851
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1852 | h1852
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1853 | h1853
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1854 | h1854
                  · linarith only [h0, h1737, h1854, hc23, hlam, hphi, ht34, ht45, u5elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1856 | h1856
                    · linarith only [h0, h1737, h1856, hc24, hlam, hphi, ht45, u5elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1858 | h1858
                      · linarith only [h0, h1737, h1858, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1860 | h1860
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1861 | h1861
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1862 | h1862
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1863 | h1863
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1864 | h1864
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1865 | h1865
                                  · rcases h0bigk with h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c | h1866c
                                    · have p1866_0 := h1866c.1
                                      have p1866_1 := h1866c.2.1
                                      have p1866_2 := h1866c.2.2.1
                                      have p1866_3 := h1866c.2.2.2
                                      linarith only [hlam, p1866_0]
                                    · have p1866_0 := h1866c.1
                                      have p1866_1 := h1866c.2.1
                                      have p1866_2 := h1866c.2.2.1
                                      have p1866_3 := h1866c.2.2.2
                                      linarith only [h1330, h1854, h1860, hc02, hc23, hlam, hphi, p1866_1]
                                    · have p1866_0 := h1866c.1
                                      have p1866_1 := h1866c.2.1
                                      have p1866_2 := h1866c.2.2.1
                                      have p1866_3 := h1866c.2.2.2
                                      linarith only [h1, hlam, p1866_0]
                                    · have p1866_0 := h1866c.1
                                      have p1866_1 := h1866c.2.1
                                      have p1866_2 := h1866c.2.2.1
                                      have p1866_3 := h1866c.2.2.2
                                      linarith only [h1330, hlam, p1866_1]
                                    · have p1866_0 := h1866c.1
                                      have p1866_1 := h1866c.2.1
                                      have p1866_2 := h1866c.2.2.1
                                      have p1866_3 := h1866c.2.2.2
                                      linarith only [h0, h1330, h1737, h1854, h1860, hc12, hc23, hlam, hphi, p1866_1]
                                    · have p1866_0 := h1866c.1
                                      have p1866_1 := h1866c.2.1
                                      have p1866_2 := h1866c.2.2.1
                                      have p1866_3 := h1866c.2.2.2
                                      linarith only [h0, hlam, p1866_0]
                                    · have p1866_0 := h1866c.1
                                      have p1866_1 := h1866c.2.1
                                      have p1866_2 := h1866c.2.2.1
                                      have p1866_3 := h1866c.2.2.2
                                      linarith only [hlam, p1866_0]
                                    · have p1866_0 := h1866c.1
                                      have p1866_1 := h1866c.2.1
                                      have p1866_2 := h1866c.2.2.1
                                      have p1866_3 := h1866c.2.2.2
                                      linarith only [h1733, hlam, p1866_0]
                                    · have p1866_0 := h1866c.1
                                      have p1866_1 := h1866c.2.1
                                      have p1866_2 := h1866c.2.2.1
                                      have p1866_3 := h1866c.2.2.2
                                      linarith only [h1735, hlam, p1866_1]
                                    · have p1866_0 := h1866c.1
                                      have p1866_1 := h1866c.2.1
                                      have p1866_2 := h1866c.2.2.1
                                      have p1866_3 := h1866c.2.2.2
                                      linarith only [h1737, hlam, p1866_0]
                                    · have p1866_0 := h1866c.1
                                      have p1866_1 := h1866c.2.1
                                      have p1866_2 := h1866c.2.2.1
                                      have p1866_3 := h1866c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1866_1, u0elo2]
                                    · have p1866_0 := h1866c.1
                                      have p1866_1 := h1866c.2.1
                                      have p1866_2 := h1866c.2.2.1
                                      have p1866_3 := h1866c.2.2.2
                                      rcases p1866_3 (m.d 0 1) (by simp) with h1878 | h1878
                                      · linarith only [h1, h1878, hlam]
                                      · linarith only [h0, h1878, hlam]
                                    · have p1866_0 := h1866c.1
                                      have p1866_1 := h1866c.2.1
                                      have p1866_2 := h1866c.2.2.1
                                      have p1866_3 := h1866c.2.2.2
                                      linarith only [hlam, p1866_0]
                                    · have p1866_0 := h1866c.1
                                      have p1866_1 := h1866c.2.1
                                      have p1866_2 := h1866c.2.2.1
                                      have p1866_3 := h1866c.2.2.2
                                      linarith only [h1330, h1732, h1858, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1866_1, u0elo2]
                                    · have p1866_0 := h1866c.1
                                      have p1866_1 := h1866c.2.1
                                      have p1866_2 := h1866c.2.2.1
                                      have p1866_3 := h1866c.2.2.2
                                      rcases p1866_3 (m.d 0 1) (by simp) with h1883 | h1883
                                      · linarith only [h1, h1883, hlam]
                                      · linarith only [h1732, h1883, hlam]
                                    · have p1866_0 := h1866c.1
                                      have p1866_1 := h1866c.2.1
                                      have p1866_2 := h1866c.2.2.1
                                      have p1866_3 := h1866c.2.2.2
                                      linarith only [h1732, h1858, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1866_1, u0elo3]
                                    · have p1866_0 := h1866c.1
                                      have p1866_1 := h1866c.2.1
                                      have p1866_2 := h1866c.2.2.1
                                      have p1866_3 := h1866c.2.2.2
                                      rcases p1866_3 (m.d 0 1) (by simp) with h1887 | h1887
                                      · linarith only [h1330, h1887, hlam]
                                      · linarith only [h0, h1887, hlam]
                                    · have p1866_0 := h1866c.1
                                      have p1866_1 := h1866c.2.1
                                      have p1866_2 := h1866c.2.2.1
                                      have p1866_3 := h1866c.2.2.2
                                      linarith only [h1851, hlam, p1866_0]
                                    · have p1866_0 := h1866c.1
                                      have p1866_1 := h1866c.2.1
                                      have p1866_2 := h1866c.2.2.1
                                      have p1866_3 := h1866c.2.2.2
                                      linarith only [hlam, p1866_0]
                                    · have p1866_0 := h1866c.1
                                      have p1866_1 := h1866c.2.1
                                      have p1866_2 := h1866c.2.2.1
                                      have p1866_3 := h1866c.2.2.2
                                      rcases p1866_3 (m.d 0 1) (by simp) with h1892 | h1892
                                      · linarith only [h1330, h1892, hlam]
                                      · linarith only [h1732, h1892, hlam]
                                    · have p1866_0 := h1866c.1
                                      have p1866_1 := h1866c.2.1
                                      have p1866_2 := h1866c.2.2.1
                                      have p1866_3 := h1866c.2.2.2
                                      linarith only [h1732, hlam, p1866_0]
                                    · have p1866_0 := h1866c.1
                                      have p1866_1 := h1866c.2.1
                                      have p1866_2 := h1866c.2.2.1
                                      have p1866_3 := h1866c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p1866_1, u5elo0]
                                    · have p1866_0 := h1866c.1
                                      have p1866_1 := h1866c.2.1
                                      have p1866_2 := h1866c.2.2.1
                                      have p1866_3 := h1866c.2.2.2
                                      linarith only [h1852, hlam, p1866_0]
                                    · have p1866_0 := h1866c.1
                                      have p1866_1 := h1866c.2.1
                                      have p1866_2 := h1866c.2.2.1
                                      have p1866_3 := h1866c.2.2.2
                                      linarith only [h1853, hlam, p1866_1]
                                    · have p1866_0 := h1866c.1
                                      have p1866_1 := h1866c.2.1
                                      have p1866_2 := h1866c.2.2.1
                                      have p1866_3 := h1866c.2.2.2
                                      linarith only [hlam, p1866_0]
                                  · rcases h0bigk with h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c | h1900c
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [hlam, p1900_0]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [h0, h1330, h1854, h1860, hc12, hc23, hlam, hphi, p1900_1]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [h1, hlam, p1900_0]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [h1330, hlam, p1900_1]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [h1330, h1732, h1854, h1858, h1860, hc12, hc23, hlam, hphi, p1900_1]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [h0, hlam, p1900_0]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [hlam, p1900_0]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [h1733, hlam, p1900_0]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [h1735, hlam, p1900_1]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [h1737, hlam, p1900_0]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1900_1, u0elo2]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      rcases p1900_3 (m.d 0 1) (by simp) with h1912 | h1912
                                      · linarith only [h1, h1912, hlam]
                                      · linarith only [h0, h1912, hlam]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [hlam, p1900_0]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [h1330, h1732, h1858, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1900_1, u0elo2]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [h1853, h1865, hc34, hlam, hphi, ht0b, ht45, ht5b, p1900_1, u0elo2]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [h1732, h1858, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1900_1, u0elo3]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      rcases p1900_3 (m.d 0 1) (by simp) with h1919 | h1919
                                      · linarith only [h1330, h1919, hlam]
                                      · linarith only [h0, h1919, hlam]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [h1851, hlam, p1900_0]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [hlam, p1900_0]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [h1851, h1853, h1865, hc34, hlam, hphi, ht0b, ht45, ht5b, p1900_1, u0elo2]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [h1732, hlam, p1900_0]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p1900_1, u5elo0]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [h1852, hlam, p1900_0]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [h1853, hlam, p1900_1]
                                    · have p1900_0 := h1900c.1
                                      have p1900_1 := h1900c.2.1
                                      have p1900_2 := h1900c.2.2.1
                                      have p1900_3 := h1900c.2.2.2
                                      linarith only [hlam, p1900_0]
                                · linarith only [h1330, h1856, h1864, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                              · linarith only [h1, h1732, h1854, h1861, h1863, hlam]
                            · linarith only [h0, h1330, h1854, h1860, h1862, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h1330, h1732, h1858, h1860, h1861, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h1851, h1860, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h0, h1330, h1853, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
              · linarith only [h0, h1, h1852, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1937 | h1937
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1938 | h1938
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1939 | h1939
                  · linarith only [h0, h1733, h1939, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1941 | h1941
                    · linarith only [h0, h1735, h1941, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1943 | h1943
                      · linarith only [h0, h1737, h1943, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1945 | h1945
                        · linarith only [h1, h1732, h1851, h1939, h1943, h1945, hc12, hc23, hlam, hphi]
                        · linarith only [h1, h1732, h1943, h1945, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h0, h1330, h1938, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
              · linarith only [h0, h1, h1937, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
    · linarith only [h0, h1732, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]

set_option maxHeartbeats 10236000 in
set_option maxHeartbeats 10236000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h2emin := hb2.2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_x0_x0 m hb0 hb2 hb3 hb5 h0 h1
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_x0_x1 m hb0 hb2 hb3 hb5 h0 h1

end R2N4
