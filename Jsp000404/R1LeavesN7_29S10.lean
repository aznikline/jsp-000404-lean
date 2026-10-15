import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5254000 in
set_option maxHeartbeats 5254000 in
theorem r1l7_21_15_M_LI_L_I_s1_x0_x0_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h947 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1183 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 3 5 (by decide) (by decide) with h1184 | h1184
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1185 | h1185
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1186 | h1186
      · linarith only [h0, h1186, h4, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1188 | h1188
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1189 | h1189
          · linarith only [h0, h1189, h947, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1191 | h1191
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1192 | h1192
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1193 | h1193
                · linarith only [h1188, h1189, h1193, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1195 | h1195
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1196 | h1196
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1197 | h1197
                      · linarith only [h1188, h1189, h1193, h1197, hlam]
                      · linarith only [h0, h1, h1183, h1185, h1188, h1195, h1197, h947, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · linarith only [h1, h1192, h1196, h4, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h1183, h1195, h4, hlam]
              · linarith only [h1, h1184, h1186, h1188, h1192, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · linarith only [h1, h1183, h1186, h1188, h1191, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1204 | h1204
          · linarith only [h0, h1204, h947, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1206 | h1206
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1207 | h1207
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1208 | h1208
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1209 | h1209
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1210 | h1210
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1211 | h1211
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1212 | h1212
                        · linarith only [h1, h1206, h1212, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · linarith only [h1208, h1212, h2, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · linarith only [h1, h1206, h1208, h1211, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · linarith only [h1, h1207, h1210, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h1183, h1209, h4, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1218 | h1218
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1219 | h1219
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1220 | h1220
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1221 | h1221
                        · linarith only [h1206, h1208, h1221, hlam]
                        · rcases h1bigk with h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c
                          · have p1223_0 := h1223c.1
                            have p1223_1 := h1223c.2.1
                            have p1223_2 := h1223c.2.2.1
                            have p1223_3 := h1223c.2.2.2
                            linarith only [hlam, p1223_0]
                          · have p1223_0 := h1223c.1
                            have p1223_1 := h1223c.2.1
                            have p1223_2 := h1223c.2.2.1
                            have p1223_3 := h1223c.2.2.2
                            rcases p1223_3 (m.d 0 1) (by simp) with h1225 | h1225
                            · rcases p1223_3 (m.d 1 2) (by simp) with h1226 | h1226
                              · linarith only [h1226, hlam, p1223_0]
                              · rcases p1223_3 (m.d 1 3) (by simp) with h1228 | h1228
                                · linarith only [h1, h1228, hlam]
                                · linarith only [h1186, h1228, hlam]
                            · linarith only [h1225, hlam, p1223_0]
                          · have p1223_0 := h1223c.1
                            have p1223_1 := h1223c.2.1
                            have p1223_2 := h1223c.2.2.1
                            have p1223_3 := h1223c.2.2.2
                            linarith only [h1206, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1223_1, u1elo0]
                          · have p1223_0 := h1223c.1
                            have p1223_1 := h1223c.2.1
                            have p1223_2 := h1223c.2.2.1
                            have p1223_3 := h1223c.2.2.2
                            rcases p1223_3 (m.d 0 1) (by simp) with h1233 | h1233
                            · rcases p1223_3 (m.d 1 2) (by simp) with h1234 | h1234
                              · linarith only [h0, h1234, hlam]
                              · rcases p1223_3 (m.d 1 3) (by simp) with h1236 | h1236
                                · linarith only [h1, h1236, hlam]
                                · linarith only [h1206, h1236, hlam]
                            · linarith only [h1233, hlam, p1223_0]
                          · have p1223_0 := h1223c.1
                            have p1223_1 := h1223c.2.1
                            have p1223_2 := h1223c.2.2.1
                            have p1223_3 := h1223c.2.2.2
                            rcases p1223_3 (m.d 0 1) (by simp) with h1240 | h1240
                            · rcases p1223_3 (m.d 1 2) (by simp) with h1241 | h1241
                              · linarith only [h0, h1241, hlam]
                              · rcases p1223_3 (m.d 1 3) (by simp) with h1243 | h1243
                                · linarith only [h1, h1243, hlam]
                                · linarith only [h1207, h1243, hlam]
                            · linarith only [h1240, hlam, p1223_0]
                          · have p1223_0 := h1223c.1
                            have p1223_1 := h1223c.2.1
                            have p1223_2 := h1223c.2.2.1
                            have p1223_3 := h1223c.2.2.2
                            linarith only [h0, hlam, p1223_0]
                          · have p1223_0 := h1223c.1
                            have p1223_1 := h1223c.2.1
                            have p1223_2 := h1223c.2.2.1
                            have p1223_3 := h1223c.2.2.2
                            linarith only [hlam, p1223_0]
                          · have p1223_0 := h1223c.1
                            have p1223_1 := h1223c.2.1
                            have p1223_2 := h1223c.2.2.1
                            have p1223_3 := h1223c.2.2.2
                            linarith only [h1186, hlam, p1223_0]
                          · have p1223_0 := h1223c.1
                            have p1223_1 := h1223c.2.1
                            have p1223_2 := h1223c.2.2.1
                            have p1223_3 := h1223c.2.2.2
                            linarith only [h1188, hlam, p1223_0]
                          · have p1223_0 := h1223c.1
                            have p1223_1 := h1223c.2.1
                            have p1223_2 := h1223c.2.2.1
                            have p1223_3 := h1223c.2.2.2
                            linarith only [h1204, hlam, p1223_0]
                          · have p1223_0 := h1223c.1
                            have p1223_1 := h1223c.2.1
                            have p1223_2 := h1223c.2.2.1
                            have p1223_3 := h1223c.2.2.2
                            linarith only [h1, hlam, p1223_0]
                          · have p1223_0 := h1223c.1
                            have p1223_1 := h1223c.2.1
                            have p1223_2 := h1223c.2.2.1
                            have p1223_3 := h1223c.2.2.2
                            linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1223_1, u1elo0]
                          · have p1223_0 := h1223c.1
                            have p1223_1 := h1223c.2.1
                            have p1223_2 := h1223c.2.2.1
                            have p1223_3 := h1223c.2.2.2
                            linarith only [hlam, p1223_0]
                          · have p1223_0 := h1223c.1
                            have p1223_1 := h1223c.2.1
                            have p1223_2 := h1223c.2.2.1
                            have p1223_3 := h1223c.2.2.2
                            linarith only [h1, h1188, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1223_1, u1elo0]
                          · have p1223_0 := h1223c.1
                            have p1223_1 := h1223c.2.1
                            have p1223_2 := h1223c.2.2.1
                            have p1223_3 := h1223c.2.2.2
                            linarith only [h1, h1188, h1208, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1223_1, u1elo0]
                          · have p1223_0 := h1223c.1
                            have p1223_1 := h1223c.2.1
                            have p1223_2 := h1223c.2.2.1
                            have p1223_3 := h1223c.2.2.2
                            linarith only [h2, hlam, p1223_0]
                          · have p1223_0 := h1223c.1
                            have p1223_1 := h1223c.2.1
                            have p1223_2 := h1223c.2.2.1
                            have p1223_3 := h1223c.2.2.2
                            linarith only [h1183, h1185, h1208, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1223_1]
                          · have p1223_0 := h1223c.1
                            have p1223_1 := h1223c.2.1
                            have p1223_2 := h1223c.2.2.1
                            have p1223_3 := h1223c.2.2.2
                            linarith only [h1206, hlam, p1223_0]
                          · have p1223_0 := h1223c.1
                            have p1223_1 := h1223c.2.1
                            have p1223_2 := h1223c.2.2.1
                            have p1223_3 := h1223c.2.2.2
                            linarith only [hlam, p1223_0]
                          · have p1223_0 := h1223c.1
                            have p1223_1 := h1223c.2.1
                            have p1223_2 := h1223c.2.2.1
                            have p1223_3 := h1223c.2.2.2
                            linarith only [h1208, hlam, p1223_1]
                          · have p1223_0 := h1223c.1
                            have p1223_1 := h1223c.2.1
                            have p1223_2 := h1223c.2.2.1
                            have p1223_3 := h1223c.2.2.2
                            linarith only [h3, hlam, p1223_0]
                          · have p1223_0 := h1223c.1
                            have p1223_1 := h1223c.2.1
                            have p1223_2 := h1223c.2.2.1
                            have p1223_3 := h1223c.2.2.2
                            linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1223_1, u1elo0]
                          · have p1223_0 := h1223c.1
                            have p1223_1 := h1223c.2.1
                            have p1223_2 := h1223c.2.2.1
                            have p1223_3 := h1223c.2.2.2
                            linarith only [h1207, hlam, p1223_0]
                          · have p1223_0 := h1223c.1
                            have p1223_1 := h1223c.2.1
                            have p1223_2 := h1223c.2.2.1
                            have p1223_3 := h1223c.2.2.2
                            linarith only [h1, h1183, h1185, h1208, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1223_1, u1elo0]
                          · have p1223_0 := h1223c.1
                            have p1223_1 := h1223c.2.1
                            have p1223_2 := h1223c.2.2.1
                            have p1223_3 := h1223c.2.2.2
                            linarith only [hlam, p1223_0]
                      · linarith only [h1, h1183, h1185, h1188, h1220, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h1184, h1219, h4, hlam]
                  · linarith only [h1183, h1185, h1188, h1208, h1218, h4, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h1184, h1206, h1207, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1271 | h1271
              · linarith only [h1, h1183, h1206, h1271, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1273 | h1273
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1274 | h1274
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1275 | h1275
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1276 | h1276
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1277 | h1277
                        · rcases h1bigk with h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c
                          · have p1278_0 := h1278c.1
                            have p1278_1 := h1278c.2.1
                            have p1278_2 := h1278c.2.2.1
                            have p1278_3 := h1278c.2.2.2
                            linarith only [hlam, p1278_0]
                          · have p1278_0 := h1278c.1
                            have p1278_1 := h1278c.2.1
                            have p1278_2 := h1278c.2.2.1
                            have p1278_3 := h1278c.2.2.2
                            rcases p1278_3 (m.d 0 1) (by simp) with h1280 | h1280
                            · rcases p1278_3 (m.d 1 2) (by simp) with h1281 | h1281
                              · linarith only [h1281, hlam, p1278_0]
                              · rcases p1278_3 (m.d 1 3) (by simp) with h1283 | h1283
                                · linarith only [h1, h1283, hlam]
                                · linarith only [h1186, h1283, hlam]
                            · linarith only [h1280, hlam, p1278_0]
                          · have p1278_0 := h1278c.1
                            have p1278_1 := h1278c.2.1
                            have p1278_2 := h1278c.2.2.1
                            have p1278_3 := h1278c.2.2.2
                            rcases p1278_3 (m.d 0 1) (by simp) with h1287 | h1287
                            · rcases p1278_3 (m.d 1 2) (by simp) with h1288 | h1288
                              · linarith only [h0, h1288, hlam]
                              · rcases p1278_3 (m.d 1 3) (by simp) with h1290 | h1290
                                · linarith only [h1290, hlam, p1278_0]
                                · rcases p1278_3 (m.d 1 4) (by simp) with h1292 | h1292
                                  · linarith only [h1292, h2, hlam]
                                  · linarith only [h1206, h1292, hlam]
                            · linarith only [h1287, hlam, p1278_0]
                          · have p1278_0 := h1278c.1
                            have p1278_1 := h1278c.2.1
                            have p1278_2 := h1278c.2.2.1
                            have p1278_3 := h1278c.2.2.2
                            linarith only [h1273, hc45, hlam, hphi, ht01, ht0b, ht5b, p1278_1, u1elo0]
                          · have p1278_0 := h1278c.1
                            have p1278_1 := h1278c.2.1
                            have p1278_2 := h1278c.2.2.1
                            have p1278_3 := h1278c.2.2.2
                            rcases p1278_3 (m.d 0 1) (by simp) with h1297 | h1297
                            · rcases p1278_3 (m.d 1 2) (by simp) with h1298 | h1298
                              · linarith only [h0, h1298, hlam]
                              · rcases p1278_3 (m.d 1 3) (by simp) with h1300 | h1300
                                · linarith only [h1, h1300, hlam]
                                · rcases p1278_3 (m.d 1 4) (by simp) with h1302 | h1302
                                  · linarith only [h1302, h2, hlam]
                                  · linarith only [h1273, h1302, hlam]
                            · linarith only [h1297, hlam, p1278_0]
                          · have p1278_0 := h1278c.1
                            have p1278_1 := h1278c.2.1
                            have p1278_2 := h1278c.2.2.1
                            have p1278_3 := h1278c.2.2.2
                            linarith only [h0, hlam, p1278_0]
                          · have p1278_0 := h1278c.1
                            have p1278_1 := h1278c.2.1
                            have p1278_2 := h1278c.2.2.1
                            have p1278_3 := h1278c.2.2.2
                            linarith only [hlam, p1278_0]
                          · have p1278_0 := h1278c.1
                            have p1278_1 := h1278c.2.1
                            have p1278_2 := h1278c.2.2.1
                            have p1278_3 := h1278c.2.2.2
                            linarith only [h1186, hlam, p1278_0]
                          · have p1278_0 := h1278c.1
                            have p1278_1 := h1278c.2.1
                            have p1278_2 := h1278c.2.2.1
                            have p1278_3 := h1278c.2.2.2
                            linarith only [h1188, hlam, p1278_0]
                          · have p1278_0 := h1278c.1
                            have p1278_1 := h1278c.2.1
                            have p1278_2 := h1278c.2.2.1
                            have p1278_3 := h1278c.2.2.2
                            linarith only [h1204, hlam, p1278_0]
                          · have p1278_0 := h1278c.1
                            have p1278_1 := h1278c.2.1
                            have p1278_2 := h1278c.2.2.1
                            have p1278_3 := h1278c.2.2.2
                            linarith only [h1, hlam, p1278_0]
                          · have p1278_0 := h1278c.1
                            have p1278_1 := h1278c.2.1
                            have p1278_2 := h1278c.2.2.1
                            have p1278_3 := h1278c.2.2.2
                            linarith only [h1184, h1271, h947, hc12, hc25, hlam, hphi, p1278_1]
                          · have p1278_0 := h1278c.1
                            have p1278_1 := h1278c.2.1
                            have p1278_2 := h1278c.2.2.1
                            have p1278_3 := h1278c.2.2.2
                            linarith only [hlam, p1278_0]
                          · have p1278_0 := h1278c.1
                            have p1278_1 := h1278c.2.1
                            have p1278_2 := h1278c.2.2.1
                            have p1278_3 := h1278c.2.2.2
                            linarith only [h1206, hlam, p1278_1]
                          · have p1278_0 := h1278c.1
                            have p1278_1 := h1278c.2.1
                            have p1278_2 := h1278c.2.2.1
                            have p1278_3 := h1278c.2.2.2
                            linarith only [h1271, hlam, p1278_1]
                          · have p1278_0 := h1278c.1
                            have p1278_1 := h1278c.2.1
                            have p1278_2 := h1278c.2.2.1
                            have p1278_3 := h1278c.2.2.2
                            linarith only [h2, hlam, p1278_0]
                          · have p1278_0 := h1278c.1
                            have p1278_1 := h1278c.2.1
                            have p1278_2 := h1278c.2.2.1
                            have p1278_3 := h1278c.2.2.2
                            linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1278_1, u1elo0]
                          · have p1278_0 := h1278c.1
                            have p1278_1 := h1278c.2.1
                            have p1278_2 := h1278c.2.2.1
                            have p1278_3 := h1278c.2.2.2
                            linarith only [h1, h1183, h1206, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1278_1, u1elo0]
                          · have p1278_0 := h1278c.1
                            have p1278_1 := h1278c.2.1
                            have p1278_2 := h1278c.2.2.1
                            have p1278_3 := h1278c.2.2.2
                            linarith only [hlam, p1278_0]
                          · have p1278_0 := h1278c.1
                            have p1278_1 := h1278c.2.1
                            have p1278_2 := h1278c.2.2.1
                            have p1278_3 := h1278c.2.2.2
                            linarith only [h1, h1183, h1206, hc15, hlam, hphi, ht01, ht0b, ht5b, p1278_1, u1elo0]
                          · have p1278_0 := h1278c.1
                            have p1278_1 := h1278c.2.1
                            have p1278_2 := h1278c.2.2.1
                            have p1278_3 := h1278c.2.2.2
                            linarith only [h3, hlam, p1278_0]
                          · have p1278_0 := h1278c.1
                            have p1278_1 := h1278c.2.1
                            have p1278_2 := h1278c.2.2.1
                            have p1278_3 := h1278c.2.2.2
                            linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1278_1, u1elo0]
                          · have p1278_0 := h1278c.1
                            have p1278_1 := h1278c.2.1
                            have p1278_2 := h1278c.2.2.1
                            have p1278_3 := h1278c.2.2.2
                            linarith only [h1, h1184, h1186, h1271, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1278_1, u1elo0]
                          · have p1278_0 := h1278c.1
                            have p1278_1 := h1278c.2.1
                            have p1278_2 := h1278c.2.2.1
                            have p1278_3 := h1278c.2.2.2
                            linarith only [h1273, hlam, p1278_0]
                          · have p1278_0 := h1278c.1
                            have p1278_1 := h1278c.2.1
                            have p1278_2 := h1278c.2.2.1
                            have p1278_3 := h1278c.2.2.2
                            linarith only [hlam, p1278_0]
                        · linarith only [h1, h1183, h1185, h1186, h1206, h1277, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                      · linarith only [h1273, h1276, h2, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · linarith only [h1184, h1275, h4, hlam]
                  · linarith only [h1183, h1274, h4, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1330 | h1330
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1331 | h1331
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1332 | h1332
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1333 | h1333
                        · linarith only [h1, h1183, h1273, h1333, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · linarith only [h1, h1183, h1185, h1186, h1206, h1333, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                      · linarith only [h1, h1183, h1185, h1188, h1332, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h1184, h1331, h4, hlam]
                  · linarith only [h1183, h1330, h4, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1339 | h1339
      · linarith only [h0, h1183, h1339, h4, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1341 | h1341
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1342 | h1342
          · linarith only [h0, h1342, h947, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1344 | h1344
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1345 | h1345
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1346 | h1346
                · linarith only [h1185, h1346, h2, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1348 | h1348
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1349 | h1349
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1350 | h1350
                      · linarith only [h0, h1185, h1341, h1350, hc05, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1352 | h1352
                        · linarith only [h0, h1341, h1348, h1350, h1352, h947, hlam]
                        · rcases h1bigk with h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c
                          · have p1354_0 := h1354c.1
                            have p1354_1 := h1354c.2.1
                            have p1354_2 := h1354c.2.2.1
                            have p1354_3 := h1354c.2.2.2
                            linarith only [hlam, p1354_0]
                          · have p1354_0 := h1354c.1
                            have p1354_1 := h1354c.2.1
                            have p1354_2 := h1354c.2.2.1
                            have p1354_3 := h1354c.2.2.2
                            linarith only [h1341, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1354_1, u1elo0]
                          · have p1354_0 := h1354c.1
                            have p1354_1 := h1354c.2.1
                            have p1354_2 := h1354c.2.2.1
                            have p1354_3 := h1354c.2.2.2
                            linarith only [h1341, h1342, h1345, h1348, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1354_1, u1elo0]
                          · have p1354_0 := h1354c.1
                            have p1354_1 := h1354c.2.1
                            have p1354_2 := h1354c.2.2.1
                            have p1354_3 := h1354c.2.2.2
                            rcases p1354_3 (m.d 0 1) (by simp) with h1358 | h1358
                            · rcases p1354_3 (m.d 1 2) (by simp) with h1359 | h1359
                              · linarith only [h0, h1359, hlam]
                              · linarith only [h1341, h1359, hlam]
                            · linarith only [h1358, hlam, p1354_0]
                          · have p1354_0 := h1354c.1
                            have p1354_1 := h1354c.2.1
                            have p1354_2 := h1354c.2.2.1
                            have p1354_3 := h1354c.2.2.2
                            linarith only [h1341, h1342, h1348, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1354_1, u1elo0]
                          · have p1354_0 := h1354c.1
                            have p1354_1 := h1354c.2.1
                            have p1354_2 := h1354c.2.2.1
                            have p1354_3 := h1354c.2.2.2
                            linarith only [h0, hlam, p1354_0]
                          · have p1354_0 := h1354c.1
                            have p1354_1 := h1354c.2.1
                            have p1354_2 := h1354c.2.2.1
                            have p1354_3 := h1354c.2.2.2
                            linarith only [hlam, p1354_0]
                          · have p1354_0 := h1354c.1
                            have p1354_1 := h1354c.2.1
                            have p1354_2 := h1354c.2.2.1
                            have p1354_3 := h1354c.2.2.2
                            linarith only [h1339, hlam, p1354_0]
                          · have p1354_0 := h1354c.1
                            have p1354_1 := h1354c.2.1
                            have p1354_2 := h1354c.2.2.1
                            have p1354_3 := h1354c.2.2.2
                            linarith only [h0, h1341, h1348, h1350, h947, hc34, hc45, hlam, hphi, p1354_1]
                          · have p1354_0 := h1354c.1
                            have p1354_1 := h1354c.2.1
                            have p1354_2 := h1354c.2.2.1
                            have p1354_3 := h1354c.2.2.2
                            linarith only [h1342, hlam, p1354_0]
                          · have p1354_0 := h1354c.1
                            have p1354_1 := h1354c.2.1
                            have p1354_2 := h1354c.2.2.1
                            have p1354_3 := h1354c.2.2.2
                            linarith only [h1, hlam, p1354_0]
                          · have p1354_0 := h1354c.1
                            have p1354_1 := h1354c.2.1
                            have p1354_2 := h1354c.2.2.1
                            have p1354_3 := h1354c.2.2.2
                            linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1354_1, u1elo0]
                          · have p1354_0 := h1354c.1
                            have p1354_1 := h1354c.2.1
                            have p1354_2 := h1354c.2.2.1
                            have p1354_3 := h1354c.2.2.2
                            linarith only [hlam, p1354_0]
                          · have p1354_0 := h1354c.1
                            have p1354_1 := h1354c.2.1
                            have p1354_2 := h1354c.2.2.1
                            have p1354_3 := h1354c.2.2.2
                            linarith only [h1, h1341, h1348, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1354_1, u1elo0]
                          · have p1354_0 := h1354c.1
                            have p1354_1 := h1354c.2.1
                            have p1354_2 := h1354c.2.2.1
                            have p1354_3 := h1354c.2.2.2
                            linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p1354_1, u1elo0]
                          · have p1354_0 := h1354c.1
                            have p1354_1 := h1354c.2.1
                            have p1354_2 := h1354c.2.2.1
                            have p1354_3 := h1354c.2.2.2
                            linarith only [h2, hlam, p1354_0]
                          · have p1354_0 := h1354c.1
                            have p1354_1 := h1354c.2.1
                            have p1354_2 := h1354c.2.2.1
                            have p1354_3 := h1354c.2.2.2
                            linarith only [h1341, hlam, p1354_1]
                          · have p1354_0 := h1354c.1
                            have p1354_1 := h1354c.2.1
                            have p1354_2 := h1354c.2.2.1
                            have p1354_3 := h1354c.2.2.2
                            linarith only [h1344, hlam, p1354_0]
                          · have p1354_0 := h1354c.1
                            have p1354_1 := h1354c.2.1
                            have p1354_2 := h1354c.2.2.1
                            have p1354_3 := h1354c.2.2.2
                            linarith only [hlam, p1354_0]
                          · have p1354_0 := h1354c.1
                            have p1354_1 := h1354c.2.1
                            have p1354_2 := h1354c.2.2.1
                            have p1354_3 := h1354c.2.2.2
                            linarith only [h1346, hlam, p1354_1]
                          · have p1354_0 := h1354c.1
                            have p1354_1 := h1354c.2.1
                            have p1354_2 := h1354c.2.2.1
                            have p1354_3 := h1354c.2.2.2
                            linarith only [h3, hlam, p1354_0]
                          · have p1354_0 := h1354c.1
                            have p1354_1 := h1354c.2.1
                            have p1354_2 := h1354c.2.2.1
                            have p1354_3 := h1354c.2.2.2
                            linarith only [h1341, h1348, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1354_1, u1elo4]
                          · have p1354_0 := h1354c.1
                            have p1354_1 := h1354c.2.1
                            have p1354_2 := h1354c.2.2.1
                            have p1354_3 := h1354c.2.2.2
                            linarith only [h1345, hlam, p1354_0]
                          · have p1354_0 := h1354c.1
                            have p1354_1 := h1354c.2.1
                            have p1354_2 := h1354c.2.2.1
                            have p1354_3 := h1354c.2.2.2
                            linarith only [h1341, h1348, h3, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1354_1, u1elo0]
                          · have p1354_0 := h1354c.1
                            have p1354_1 := h1354c.2.1
                            have p1354_2 := h1354c.2.2.1
                            have p1354_3 := h1354c.2.2.2
                            linarith only [hlam, p1354_0]
                    · linarith only [h1, h1345, h1349, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h0, h1183, h1341, h1348, h4, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h1, h1184, h1344, h1345, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · linarith only [h1, h1183, h1339, h1341, h1344, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1388 | h1388
          · linarith only [h0, h1388, h947, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1390 | h1390
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1391 | h1391
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1392 | h1392
                · linarith only [h1, h1185, h1390, h1392, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1394 | h1394
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1395 | h1395
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1396 | h1396
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1397 | h1397
                        · linarith only [h1, h1185, h1390, h1397, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h1bigk with h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [hlam, p1399_0]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            rcases p1399_3 (m.d 0 1) (by simp) with h1401 | h1401
                            · rcases p1399_3 (m.d 1 2) (by simp) with h1402 | h1402
                              · linarith only [h1402, hlam, p1399_0]
                              · rcases p1399_3 (m.d 1 3) (by simp) with h1404 | h1404
                                · linarith only [h1, h1404, hlam]
                                · linarith only [h1339, h1404, hlam]
                            · linarith only [h1401, hlam, p1399_0]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [h1391, hc35, hlam, hphi, ht01, ht0b, ht5b, p1399_1, u1elo0]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            rcases p1399_3 (m.d 0 1) (by simp) with h1409 | h1409
                            · rcases p1399_3 (m.d 1 2) (by simp) with h1410 | h1410
                              · linarith only [h0, h1410, hlam]
                              · rcases p1399_3 (m.d 1 3) (by simp) with h1412 | h1412
                                · linarith only [h1, h1412, hlam]
                                · linarith only [h1390, h1412, hlam]
                            · linarith only [h1409, hlam, p1399_0]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            rcases p1399_3 (m.d 0 1) (by simp) with h1416 | h1416
                            · rcases p1399_3 (m.d 1 2) (by simp) with h1417 | h1417
                              · linarith only [h0, h1417, hlam]
                              · rcases p1399_3 (m.d 1 3) (by simp) with h1419 | h1419
                                · linarith only [h1, h1419, hlam]
                                · linarith only [h1391, h1419, hlam]
                            · linarith only [h1416, hlam, p1399_0]
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
                            linarith only [h1339, hlam, p1399_0]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [h1341, hlam, p1399_0]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [h1388, hlam, p1399_0]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [h1, hlam, p1399_0]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1399_1, u1elo0]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [hlam, p1399_0]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [h1, h1341, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1399_1, u1elo0]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [h1, h1341, h1392, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1399_1, u1elo0]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [h2, hlam, p1399_0]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [h1185, h1394, h1396, h2, hc12, hc23, hlam, hphi, p1399_1]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [h1390, hlam, p1399_0]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [hlam, p1399_0]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [h1392, hlam, p1399_1]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [h3, hlam, p1399_0]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1399_1, u1elo0]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [h1391, hlam, p1399_0]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1399_1, u1elo0]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [hlam, p1399_0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1443 | h1443
                        · linarith only [h1390, h1396, h1443, h2, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · rcases h1bigk with h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c
                          · have p1445_0 := h1445c.1
                            have p1445_1 := h1445c.2.1
                            have p1445_2 := h1445c.2.2.1
                            have p1445_3 := h1445c.2.2.2
                            linarith only [hlam, p1445_0]
                          · have p1445_0 := h1445c.1
                            have p1445_1 := h1445c.2.1
                            have p1445_2 := h1445c.2.2.1
                            have p1445_3 := h1445c.2.2.2
                            rcases p1445_3 (m.d 0 1) (by simp) with h1447 | h1447
                            · rcases p1445_3 (m.d 1 2) (by simp) with h1448 | h1448
                              · linarith only [h1448, hlam, p1445_0]
                              · rcases p1445_3 (m.d 1 3) (by simp) with h1450 | h1450
                                · linarith only [h1, h1450, hlam]
                                · linarith only [h1339, h1450, hlam]
                            · linarith only [h1447, hlam, p1445_0]
                          · have p1445_0 := h1445c.1
                            have p1445_1 := h1445c.2.1
                            have p1445_2 := h1445c.2.2.1
                            have p1445_3 := h1445c.2.2.2
                            linarith only [h1391, hc35, hlam, hphi, ht01, ht0b, ht5b, p1445_1, u1elo0]
                          · have p1445_0 := h1445c.1
                            have p1445_1 := h1445c.2.1
                            have p1445_2 := h1445c.2.2.1
                            have p1445_3 := h1445c.2.2.2
                            rcases p1445_3 (m.d 0 1) (by simp) with h1455 | h1455
                            · rcases p1445_3 (m.d 1 2) (by simp) with h1456 | h1456
                              · linarith only [h0, h1456, hlam]
                              · rcases p1445_3 (m.d 1 3) (by simp) with h1458 | h1458
                                · linarith only [h1, h1458, hlam]
                                · linarith only [h1390, h1458, hlam]
                            · linarith only [h1455, hlam, p1445_0]
                          · have p1445_0 := h1445c.1
                            have p1445_1 := h1445c.2.1
                            have p1445_2 := h1445c.2.2.1
                            have p1445_3 := h1445c.2.2.2
                            rcases p1445_3 (m.d 0 1) (by simp) with h1462 | h1462
                            · rcases p1445_3 (m.d 1 2) (by simp) with h1463 | h1463
                              · linarith only [h0, h1463, hlam]
                              · rcases p1445_3 (m.d 1 3) (by simp) with h1465 | h1465
                                · linarith only [h1, h1465, hlam]
                                · linarith only [h1391, h1465, hlam]
                            · linarith only [h1462, hlam, p1445_0]
                          · have p1445_0 := h1445c.1
                            have p1445_1 := h1445c.2.1
                            have p1445_2 := h1445c.2.2.1
                            have p1445_3 := h1445c.2.2.2
                            linarith only [h0, hlam, p1445_0]
                          · have p1445_0 := h1445c.1
                            have p1445_1 := h1445c.2.1
                            have p1445_2 := h1445c.2.2.1
                            have p1445_3 := h1445c.2.2.2
                            linarith only [hlam, p1445_0]
                          · have p1445_0 := h1445c.1
                            have p1445_1 := h1445c.2.1
                            have p1445_2 := h1445c.2.2.1
                            have p1445_3 := h1445c.2.2.2
                            linarith only [h1339, hlam, p1445_0]
                          · have p1445_0 := h1445c.1
                            have p1445_1 := h1445c.2.1
                            have p1445_2 := h1445c.2.2.1
                            have p1445_3 := h1445c.2.2.2
                            linarith only [h1341, hlam, p1445_0]
                          · have p1445_0 := h1445c.1
                            have p1445_1 := h1445c.2.1
                            have p1445_2 := h1445c.2.2.1
                            have p1445_3 := h1445c.2.2.2
                            linarith only [h1388, hlam, p1445_0]
                          · have p1445_0 := h1445c.1
                            have p1445_1 := h1445c.2.1
                            have p1445_2 := h1445c.2.2.1
                            have p1445_3 := h1445c.2.2.2
                            linarith only [h1, hlam, p1445_0]
                          · have p1445_0 := h1445c.1
                            have p1445_1 := h1445c.2.1
                            have p1445_2 := h1445c.2.2.1
                            have p1445_3 := h1445c.2.2.2
                            linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1445_1, u1elo0]
                          · have p1445_0 := h1445c.1
                            have p1445_1 := h1445c.2.1
                            have p1445_2 := h1445c.2.2.1
                            have p1445_3 := h1445c.2.2.2
                            linarith only [hlam, p1445_0]
                          · have p1445_0 := h1445c.1
                            have p1445_1 := h1445c.2.1
                            have p1445_2 := h1445c.2.2.1
                            have p1445_3 := h1445c.2.2.2
                            linarith only [h1, h1341, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1445_1, u1elo0]
                          · have p1445_0 := h1445c.1
                            have p1445_1 := h1445c.2.1
                            have p1445_2 := h1445c.2.2.1
                            have p1445_3 := h1445c.2.2.2
                            linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p1445_1, u1elo0]
                          · have p1445_0 := h1445c.1
                            have p1445_1 := h1445c.2.1
                            have p1445_2 := h1445c.2.2.1
                            have p1445_3 := h1445c.2.2.2
                            linarith only [h2, hlam, p1445_0]
                          · have p1445_0 := h1445c.1
                            have p1445_1 := h1445c.2.1
                            have p1445_2 := h1445c.2.2.1
                            have p1445_3 := h1445c.2.2.2
                            linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1445_1, u1elo0]
                          · have p1445_0 := h1445c.1
                            have p1445_1 := h1445c.2.1
                            have p1445_2 := h1445c.2.2.1
                            have p1445_3 := h1445c.2.2.2
                            linarith only [h1390, hlam, p1445_0]
                          · have p1445_0 := h1445c.1
                            have p1445_1 := h1445c.2.1
                            have p1445_2 := h1445c.2.2.1
                            have p1445_3 := h1445c.2.2.2
                            linarith only [hlam, p1445_0]
                          · have p1445_0 := h1445c.1
                            have p1445_1 := h1445c.2.1
                            have p1445_2 := h1445c.2.2.1
                            have p1445_3 := h1445c.2.2.2
                            linarith only [h1392, hlam, p1445_1]
                          · have p1445_0 := h1445c.1
                            have p1445_1 := h1445c.2.1
                            have p1445_2 := h1445c.2.2.1
                            have p1445_3 := h1445c.2.2.2
                            linarith only [h3, hlam, p1445_0]
                          · have p1445_0 := h1445c.1
                            have p1445_1 := h1445c.2.1
                            have p1445_2 := h1445c.2.2.1
                            have p1445_3 := h1445c.2.2.2
                            linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1445_1, u1elo0]
                          · have p1445_0 := h1445c.1
                            have p1445_1 := h1445c.2.1
                            have p1445_2 := h1445c.2.2.1
                            have p1445_3 := h1445c.2.2.2
                            linarith only [h1391, hlam, p1445_0]
                          · have p1445_0 := h1445c.1
                            have p1445_1 := h1445c.2.1
                            have p1445_2 := h1445c.2.2.1
                            have p1445_3 := h1445c.2.2.2
                            linarith only [h1, h1341, h1391, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1445_1, u1elo0]
                          · have p1445_0 := h1445c.1
                            have p1445_1 := h1445c.2.1
                            have p1445_2 := h1445c.2.2.1
                            have p1445_3 := h1445c.2.2.2
                            linarith only [hlam, p1445_0]
                    · linarith only [h1184, h1395, h4, hlam]
                  · linarith only [h1183, h1394, h4, hlam]
              · linarith only [h1, h1184, h1390, h1391, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1492 | h1492
              · linarith only [h1, h1183, h1390, h1492, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1494 | h1494
                · linarith only [h1185, h1494, h2, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1496 | h1496
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1497 | h1497
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1498 | h1498
                      · linarith only [h1183, h1185, h1339, h1390, h1498, hc12, hc24, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1500 | h1500
                        · linarith only [h1183, h1185, h1500, hlam]
                        · rcases h1bigk with h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c
                          · have p1502_0 := h1502c.1
                            have p1502_1 := h1502c.2.1
                            have p1502_2 := h1502c.2.2.1
                            have p1502_3 := h1502c.2.2.2
                            linarith only [hlam, p1502_0]
                          · have p1502_0 := h1502c.1
                            have p1502_1 := h1502c.2.1
                            have p1502_2 := h1502c.2.2.1
                            have p1502_3 := h1502c.2.2.2
                            rcases p1502_3 (m.d 0 1) (by simp) with h1504 | h1504
                            · rcases p1502_3 (m.d 1 2) (by simp) with h1505 | h1505
                              · linarith only [h1505, hlam, p1502_0]
                              · rcases p1502_3 (m.d 1 3) (by simp) with h1507 | h1507
                                · linarith only [h1, h1507, hlam]
                                · linarith only [h1339, h1507, hlam]
                            · linarith only [h1504, hlam, p1502_0]
                          · have p1502_0 := h1502c.1
                            have p1502_1 := h1502c.2.1
                            have p1502_2 := h1502c.2.2.1
                            have p1502_3 := h1502c.2.2.2
                            rcases p1502_3 (m.d 0 1) (by simp) with h1511 | h1511
                            · rcases p1502_3 (m.d 1 2) (by simp) with h1512 | h1512
                              · linarith only [h0, h1512, hlam]
                              · rcases p1502_3 (m.d 1 3) (by simp) with h1514 | h1514
                                · linarith only [h1514, hlam, p1502_0]
                                · rcases p1502_3 (m.d 1 4) (by simp) with h1516 | h1516
                                  · linarith only [h1516, h2, hlam]
                                  · linarith only [h1390, h1516, hlam]
                            · linarith only [h1511, hlam, p1502_0]
                          · have p1502_0 := h1502c.1
                            have p1502_1 := h1502c.2.1
                            have p1502_2 := h1502c.2.2.1
                            have p1502_3 := h1502c.2.2.2
                            rcases p1502_3 (m.d 0 1) (by simp) with h1520 | h1520
                            · rcases p1502_3 (m.d 1 2) (by simp) with h1521 | h1521
                              · linarith only [h0, h1521, hlam]
                              · rcases p1502_3 (m.d 1 3) (by simp) with h1523 | h1523
                                · linarith only [h1, h1523, hlam]
                                · rcases p1502_3 (m.d 1 4) (by simp) with h1525 | h1525
                                  · linarith only [h1525, hlam, p1502_0]
                                  · rcases p1502_3 (m.d 1 5) (by simp) with h1527 | h1527
                                    · linarith only [h1527, h3, hlam]
                                    · linarith only [h1494, h1527, hlam]
                            · linarith only [h1520, hlam, p1502_0]
                          · have p1502_0 := h1502c.1
                            have p1502_1 := h1502c.2.1
                            have p1502_2 := h1502c.2.2.1
                            have p1502_3 := h1502c.2.2.2
                            rcases p1502_3 (m.d 0 1) (by simp) with h1531 | h1531
                            · rcases p1502_3 (m.d 1 2) (by simp) with h1532 | h1532
                              · linarith only [h0, h1532, hlam]
                              · rcases p1502_3 (m.d 1 3) (by simp) with h1534 | h1534
                                · linarith only [h1, h1534, hlam]
                                · rcases p1502_3 (m.d 1 4) (by simp) with h1536 | h1536
                                  · linarith only [h1536, h2, hlam]
                                  · rcases p1502_3 (m.d 1 5) (by simp) with h1538 | h1538
                                    · linarith only [h1538, hlam, p1502_0]
                                    · rcases h5bigk with h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c | h1540c
                                      · have p1540_0 := h1540c.1
                                        have p1540_1 := h1540c.2.1
                                        have p1540_2 := h1540c.2.2.1
                                        have p1540_3 := h1540c.2.2.2
                                        linarith only [hlam, p1540_0]
                                      · have p1540_0 := h1540c.1
                                        have p1540_1 := h1540c.2.1
                                        have p1540_2 := h1540c.2.2.1
                                        have p1540_3 := h1540c.2.2.2
                                        rcases p1540_3 (m.d 0 5) (by simp) with h1542 | h1542
                                        · rcases p1540_3 (m.d 1 5) (by simp) with h1543 | h1543
                                          · linarith only [h1543, h3, hlam]
                                          · rcases p1540_3 (m.d 2 5) (by simp) with h1545 | h1545
                                            · rcases p1540_3 (m.d 3 5) (by simp) with h1546 | h1546
                                              · linarith only [h1184, h1546, hlam]
                                              · linarith only [h1492, h1546, hlam]
                                            · linarith only [h1388, h1545, hlam]
                                        · linarith only [h1542, h3, hlam]
                                      · have p1540_0 := h1540c.1
                                        have p1540_1 := h1540c.2.1
                                        have p1540_2 := h1540c.2.2.1
                                        have p1540_3 := h1540c.2.2.2
                                        linarith only [h947, hlam, p1540_0]
                                      · have p1540_0 := h1540c.1
                                        have p1540_1 := h1540c.2.1
                                        have p1540_2 := h1540c.2.2.1
                                        have p1540_3 := h1540c.2.2.2
                                        linarith only [h1339, h1492, h947, hc12, hc25, hlam, hphi, p1540_1]
                                      · have p1540_0 := h1540c.1
                                        have p1540_1 := h1540c.2.1
                                        have p1540_2 := h1540c.2.2.1
                                        have p1540_3 := h1540c.2.2.2
                                        linarith only [h1185, hlam, p1540_1]
                                      · have p1540_0 := h1540c.1
                                        have p1540_1 := h1540c.2.1
                                        have p1540_2 := h1540c.2.2.1
                                        have p1540_3 := h1540c.2.2.2
                                        linarith only [h3, hlam, p1540_0]
                                      · have p1540_0 := h1540c.1
                                        have p1540_1 := h1540c.2.1
                                        have p1540_2 := h1540c.2.2.1
                                        have p1540_3 := h1540c.2.2.2
                                        linarith only [hlam, p1540_0]
                                      · have p1540_0 := h1540c.1
                                        have p1540_1 := h1540c.2.1
                                        have p1540_2 := h1540c.2.2.1
                                        have p1540_3 := h1540c.2.2.2
                                        linarith only [h1388, hlam, p1540_0]
                                      · have p1540_0 := h1540c.1
                                        have p1540_1 := h1540c.2.1
                                        have p1540_2 := h1540c.2.2.1
                                        have p1540_3 := h1540c.2.2.2
                                        linarith only [h1492, hlam, p1540_1]
                                      · have p1540_0 := h1540c.1
                                        have p1540_1 := h1540c.2.1
                                        have p1540_2 := h1540c.2.2.1
                                        have p1540_3 := h1540c.2.2.2
                                        linarith only [h1494, hlam, p1540_1]
                                      · have p1540_0 := h1540c.1
                                        have p1540_1 := h1540c.2.1
                                        have p1540_2 := h1540c.2.2.1
                                        have p1540_3 := h1540c.2.2.2
                                        linarith only [h1184, h1339, h1492, h1498, hc12, hc45, hlam, hphi, ht23, ht34, p1540_1]
                                      · have p1540_0 := h1540c.1
                                        have p1540_1 := h1540c.2.1
                                        have p1540_2 := h1540c.2.2.1
                                        have p1540_3 := h1540c.2.2.2
                                        rcases p1540_3 (m.d 0 5) (by simp) with h1560 | h1560
                                        · linarith only [h1560, h947, hlam]
                                        · linarith only [h1560, h3, hlam]
                                      · have p1540_0 := h1540c.1
                                        have p1540_1 := h1540c.2.1
                                        have p1540_2 := h1540c.2.2.1
                                        have p1540_3 := h1540c.2.2.2
                                        linarith only [hlam, p1540_0]
                                      · have p1540_0 := h1540c.1
                                        have p1540_1 := h1540c.2.1
                                        have p1540_2 := h1540c.2.2.1
                                        have p1540_3 := h1540c.2.2.2
                                        linarith only [h1339, h1390, h1498, h1500, hc12, hc45, hlam, hphi, ht23, ht34, p1540_1]
                                      · have p1540_0 := h1540c.1
                                        have p1540_1 := h1540c.2.1
                                        have p1540_2 := h1540c.2.2.1
                                        have p1540_3 := h1540c.2.2.2
                                        linarith only [h1498, hlam, p1540_1]
                                      · have p1540_0 := h1540c.1
                                        have p1540_1 := h1540c.2.1
                                        have p1540_2 := h1540c.2.2.1
                                        have p1540_3 := h1540c.2.2.2
                                        linarith only [h1184, hlam, p1540_0]
                                      · have p1540_0 := h1540c.1
                                        have p1540_1 := h1540c.2.1
                                        have p1540_2 := h1540c.2.2.1
                                        have p1540_3 := h1540c.2.2.2
                                        linarith only [h1, h1184, h1339, h1390, h1494, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1540_1, u1elo0]
                                      · have p1540_0 := h1540c.1
                                        have p1540_1 := h1540c.2.1
                                        have p1540_2 := h1540c.2.2.1
                                        have p1540_3 := h1540c.2.2.2
                                        linarith only [h1497, hlam, p1540_0]
                                      · have p1540_0 := h1540c.1
                                        have p1540_1 := h1540c.2.1
                                        have p1540_2 := h1540c.2.2.1
                                        have p1540_3 := h1540c.2.2.2
                                        linarith only [hlam, p1540_0]
                                      · have p1540_0 := h1540c.1
                                        have p1540_1 := h1540c.2.1
                                        have p1540_2 := h1540c.2.2.1
                                        have p1540_3 := h1540c.2.2.2
                                        linarith only [h1500, hlam, p1540_1]
                                      · have p1540_0 := h1540c.1
                                        have p1540_1 := h1540c.2.1
                                        have p1540_2 := h1540c.2.2.1
                                        have p1540_3 := h1540c.2.2.2
                                        linarith only [h1183, h1185, h1339, h1390, hc12, hc45, hlam, hphi, ht23, ht34, p1540_1]
                                      · have p1540_0 := h1540c.1
                                        have p1540_1 := h1540c.2.1
                                        have p1540_2 := h1540c.2.2.1
                                        have p1540_3 := h1540c.2.2.2
                                        rcases p1540_3 (m.d 0 5) (by simp) with h1572 | h1572
                                        · linarith only [h1185, h1572, hlam]
                                        · linarith only [h1572, h3, hlam]
                                      · have p1540_0 := h1540c.1
                                        have p1540_1 := h1540c.2.1
                                        have p1540_2 := h1540c.2.2.1
                                        have p1540_3 := h1540c.2.2.2
                                        linarith only [h0, h947, hc12, hc45, hlam, hphi, ht23, ht34, p1540_1]
                                      · have p1540_0 := h1540c.1
                                        have p1540_1 := h1540c.2.1
                                        have p1540_2 := h1540c.2.2.1
                                        have p1540_3 := h1540c.2.2.2
                                        linarith only [h1339, h1492, hc12, hc45, hlam, hphi, ht23, ht34, p1540_1]
                                      · have p1540_0 := h1540c.1
                                        have p1540_1 := h1540c.2.1
                                        have p1540_2 := h1540c.2.2.1
                                        have p1540_3 := h1540c.2.2.2
                                        linarith only [hlam, p1540_0]
                            · linarith only [h1531, hlam, p1502_0]
                          · have p1502_0 := h1502c.1
                            have p1502_1 := h1502c.2.1
                            have p1502_2 := h1502c.2.2.1
                            have p1502_3 := h1502c.2.2.2
                            linarith only [h0, hlam, p1502_0]
                          · have p1502_0 := h1502c.1
                            have p1502_1 := h1502c.2.1
                            have p1502_2 := h1502c.2.2.1
                            have p1502_3 := h1502c.2.2.2
                            linarith only [hlam, p1502_0]
                          · have p1502_0 := h1502c.1
                            have p1502_1 := h1502c.2.1
                            have p1502_2 := h1502c.2.2.1
                            have p1502_3 := h1502c.2.2.2
                            linarith only [h1339, hlam, p1502_0]
                          · have p1502_0 := h1502c.1
                            have p1502_1 := h1502c.2.1
                            have p1502_2 := h1502c.2.2.1
                            have p1502_3 := h1502c.2.2.2
                            linarith only [h1341, hlam, p1502_0]
                          · have p1502_0 := h1502c.1
                            have p1502_1 := h1502c.2.1
                            have p1502_2 := h1502c.2.2.1
                            have p1502_3 := h1502c.2.2.2
                            linarith only [h1388, hlam, p1502_0]
                          · have p1502_0 := h1502c.1
                            have p1502_1 := h1502c.2.1
                            have p1502_2 := h1502c.2.2.1
                            have p1502_3 := h1502c.2.2.2
                            linarith only [h1, hlam, p1502_0]
                          · have p1502_0 := h1502c.1
                            have p1502_1 := h1502c.2.1
                            have p1502_2 := h1502c.2.2.1
                            have p1502_3 := h1502c.2.2.2
                            linarith only [h1183, h1185, h1390, h947, hc12, hc25, hlam, hphi, p1502_1]
                          · have p1502_0 := h1502c.1
                            have p1502_1 := h1502c.2.1
                            have p1502_2 := h1502c.2.2.1
                            have p1502_3 := h1502c.2.2.2
                            linarith only [hlam, p1502_0]
                          · have p1502_0 := h1502c.1
                            have p1502_1 := h1502c.2.1
                            have p1502_2 := h1502c.2.2.1
                            have p1502_3 := h1502c.2.2.2
                            linarith only [h1390, hlam, p1502_1]
                          · have p1502_0 := h1502c.1
                            have p1502_1 := h1502c.2.1
                            have p1502_2 := h1502c.2.2.1
                            have p1502_3 := h1502c.2.2.2
                            linarith only [h1492, hlam, p1502_1]
                          · have p1502_0 := h1502c.1
                            have p1502_1 := h1502c.2.1
                            have p1502_2 := h1502c.2.2.1
                            have p1502_3 := h1502c.2.2.2
                            linarith only [h2, hlam, p1502_0]
                          · have p1502_0 := h1502c.1
                            have p1502_1 := h1502c.2.1
                            have p1502_2 := h1502c.2.2.1
                            have p1502_3 := h1502c.2.2.2
                            linarith only [h1494, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1502_1, u1elo0]
                          · have p1502_0 := h1502c.1
                            have p1502_1 := h1502c.2.1
                            have p1502_2 := h1502c.2.2.1
                            have p1502_3 := h1502c.2.2.2
                            linarith only [h1494, h3, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1502_1, u1elo0]
                          · have p1502_0 := h1502c.1
                            have p1502_1 := h1502c.2.1
                            have p1502_2 := h1502c.2.2.1
                            have p1502_3 := h1502c.2.2.2
                            linarith only [hlam, p1502_0]
                          · have p1502_0 := h1502c.1
                            have p1502_1 := h1502c.2.1
                            have p1502_2 := h1502c.2.2.1
                            have p1502_3 := h1502c.2.2.2
                            linarith only [h1494, hlam, p1502_1]
                          · have p1502_0 := h1502c.1
                            have p1502_1 := h1502c.2.1
                            have p1502_2 := h1502c.2.2.1
                            have p1502_3 := h1502c.2.2.2
                            linarith only [h3, hlam, p1502_0]
                          · have p1502_0 := h1502c.1
                            have p1502_1 := h1502c.2.1
                            have p1502_2 := h1502c.2.2.1
                            have p1502_3 := h1502c.2.2.2
                            linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1502_1, u1elo0]
                          · have p1502_0 := h1502c.1
                            have p1502_1 := h1502c.2.1
                            have p1502_2 := h1502c.2.2.1
                            have p1502_3 := h1502c.2.2.2
                            linarith only [h1339, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1502_1, u1elo0]
                          · have p1502_0 := h1502c.1
                            have p1502_1 := h1502c.2.1
                            have p1502_2 := h1502c.2.2.1
                            have p1502_3 := h1502c.2.2.2
                            linarith only [h1, h1184, h1492, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1502_1, u1elo0]
                          · have p1502_0 := h1502c.1
                            have p1502_1 := h1502c.2.1
                            have p1502_2 := h1502c.2.2.1
                            have p1502_3 := h1502c.2.2.2
                            linarith only [hlam, p1502_0]
                    · linarith only [h0, h1, h1184, h1497, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h1183, h1496, h4, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1601 | h1601
    · linarith only [h1183, h1184, h1601, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1603 | h1603
      · linarith only [h0, h1183, h1603, h4, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1605 | h1605
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1606 | h1606
          · linarith only [h0, h1606, h947, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1608 | h1608
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1609 | h1609
              · linarith only [h0, h1184, h1605, h1609, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1611 | h1611
                · linarith only [h1601, h1611, h2, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1613 | h1613
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1614 | h1614
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1615 | h1615
                      · linarith only [h0, h1184, h1601, h1605, h1615, h4, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1617 | h1617
                        · linarith only [h0, h1184, h1605, h1613, h1614, h1615, h1617, h4, hlam]
                        · rcases h1bigk with h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c | h1619c
                          · have p1619_0 := h1619c.1
                            have p1619_1 := h1619c.2.1
                            have p1619_2 := h1619c.2.2.1
                            have p1619_3 := h1619c.2.2.2
                            linarith only [hlam, p1619_0]
                          · have p1619_0 := h1619c.1
                            have p1619_1 := h1619c.2.1
                            have p1619_2 := h1619c.2.2.1
                            have p1619_3 := h1619c.2.2.2
                            linarith only [h1605, h1613, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1619_1, u1elo0]
                          · have p1619_0 := h1619c.1
                            have p1619_1 := h1619c.2.1
                            have p1619_2 := h1619c.2.2.1
                            have p1619_3 := h1619c.2.2.2
                            linarith only [h1603, h1605, h1613, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1619_1, u1elo0]
                          · have p1619_0 := h1619c.1
                            have p1619_1 := h1619c.2.1
                            have p1619_2 := h1619c.2.2.1
                            have p1619_3 := h1619c.2.2.2
                            rcases p1619_3 (m.d 0 1) (by simp) with h1623 | h1623
                            · rcases p1619_3 (m.d 1 2) (by simp) with h1624 | h1624
                              · linarith only [h0, h1624, hlam]
                              · linarith only [h1605, h1624, hlam]
                            · linarith only [h1623, hlam, p1619_0]
                          · have p1619_0 := h1619c.1
                            have p1619_1 := h1619c.2.1
                            have p1619_2 := h1619c.2.2.1
                            have p1619_3 := h1619c.2.2.2
                            linarith only [h1603, h1605, h1609, h1613, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1619_1, u1elo0]
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
                            linarith only [h1603, hlam, p1619_0]
                          · have p1619_0 := h1619c.1
                            have p1619_1 := h1619c.2.1
                            have p1619_2 := h1619c.2.2.1
                            have p1619_3 := h1619c.2.2.2
                            linarith only [h0, h1184, h1605, h1613, h1614, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1619_1]
                          · have p1619_0 := h1619c.1
                            have p1619_1 := h1619c.2.1
                            have p1619_2 := h1619c.2.2.1
                            have p1619_3 := h1619c.2.2.2
                            linarith only [h1606, hlam, p1619_0]
                          · have p1619_0 := h1619c.1
                            have p1619_1 := h1619c.2.1
                            have p1619_2 := h1619c.2.2.1
                            have p1619_3 := h1619c.2.2.2
                            linarith only [h1, hlam, p1619_0]
                          · have p1619_0 := h1619c.1
                            have p1619_1 := h1619c.2.1
                            have p1619_2 := h1619c.2.2.1
                            have p1619_3 := h1619c.2.2.2
                            linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1619_1, u1elo0]
                          · have p1619_0 := h1619c.1
                            have p1619_1 := h1619c.2.1
                            have p1619_2 := h1619c.2.2.1
                            have p1619_3 := h1619c.2.2.2
                            linarith only [hlam, p1619_0]
                          · have p1619_0 := h1619c.1
                            have p1619_1 := h1619c.2.1
                            have p1619_2 := h1619c.2.2.1
                            have p1619_3 := h1619c.2.2.2
                            linarith only [h1, h1184, h1605, h1613, h1614, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1619_1]
                          · have p1619_0 := h1619c.1
                            have p1619_1 := h1619c.2.1
                            have p1619_2 := h1619c.2.2.1
                            have p1619_3 := h1619c.2.2.2
                            linarith only [h1609, hlam, p1619_1]
                          · have p1619_0 := h1619c.1
                            have p1619_1 := h1619c.2.1
                            have p1619_2 := h1619c.2.2.1
                            have p1619_3 := h1619c.2.2.2
                            linarith only [h2, hlam, p1619_0]
                          · have p1619_0 := h1619c.1
                            have p1619_1 := h1619c.2.1
                            have p1619_2 := h1619c.2.2.1
                            have p1619_3 := h1619c.2.2.2
                            linarith only [h1605, hlam, p1619_1]
                          · have p1619_0 := h1619c.1
                            have p1619_1 := h1619c.2.1
                            have p1619_2 := h1619c.2.2.1
                            have p1619_3 := h1619c.2.2.2
                            linarith only [h1608, hlam, p1619_0]
                          · have p1619_0 := h1619c.1
                            have p1619_1 := h1619c.2.1
                            have p1619_2 := h1619c.2.2.1
                            have p1619_3 := h1619c.2.2.2
                            linarith only [hlam, p1619_0]
                          · have p1619_0 := h1619c.1
                            have p1619_1 := h1619c.2.1
                            have p1619_2 := h1619c.2.2.1
                            have p1619_3 := h1619c.2.2.2
                            linarith only [h1611, hlam, p1619_1]
                          · have p1619_0 := h1619c.1
                            have p1619_1 := h1619c.2.1
                            have p1619_2 := h1619c.2.2.1
                            have p1619_3 := h1619c.2.2.2
                            linarith only [h3, hlam, p1619_0]
                          · have p1619_0 := h1619c.1
                            have p1619_1 := h1619c.2.1
                            have p1619_2 := h1619c.2.2.1
                            have p1619_3 := h1619c.2.2.2
                            linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1619_1, u1elo0]
                          · have p1619_0 := h1619c.1
                            have p1619_1 := h1619c.2.1
                            have p1619_2 := h1619c.2.2.1
                            have p1619_3 := h1619c.2.2.2
                            linarith only [h3, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1619_1, u1elo0]
                          · have p1619_0 := h1619c.1
                            have p1619_1 := h1619c.2.1
                            have p1619_2 := h1619c.2.2.1
                            have p1619_3 := h1619c.2.2.2
                            linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1619_1, u1elo0]
                          · have p1619_0 := h1619c.1
                            have p1619_1 := h1619c.2.1
                            have p1619_2 := h1619c.2.2.1
                            have p1619_3 := h1619c.2.2.2
                            linarith only [hlam, p1619_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1649 | h1649
                      · linarith only [h0, h1605, h1649, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1651 | h1651
                        · linarith only [h0, h1605, h1613, h1614, h1649, h1651, h4, hlam]
                        · linarith only [h0, h1605, h1614, h1651, h4, hc24, hc45, hlam, hphi]
                  · linarith only [h0, h1183, h1605, h1613, h4, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h1183, h1184, h1603, h1605, h1608, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1656 | h1656
          · linarith only [h1, h1183, h1184, h1603, h1656, h947, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1658 | h1658
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1659 | h1659
              · linarith only [h1, h1184, h1659, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1661 | h1661
                · linarith only [h1601, h1661, h2, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1663 | h1663
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1664 | h1664
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1665 | h1665
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1666 | h1666
                        · linarith only [h1601, h1658, h1666, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                        · rcases h1bigk with h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c | h1668c
                          · have p1668_0 := h1668c.1
                            have p1668_1 := h1668c.2.1
                            have p1668_2 := h1668c.2.2.1
                            have p1668_3 := h1668c.2.2.2
                            linarith only [hlam, p1668_0]
                          · have p1668_0 := h1668c.1
                            have p1668_1 := h1668c.2.1
                            have p1668_2 := h1668c.2.2.1
                            have p1668_3 := h1668c.2.2.2
                            rcases p1668_3 (m.d 0 1) (by simp) with h1670 | h1670
                            · rcases p1668_3 (m.d 1 2) (by simp) with h1671 | h1671
                              · linarith only [h1671, hlam, p1668_0]
                              · rcases p1668_3 (m.d 1 3) (by simp) with h1673 | h1673
                                · linarith only [h1, h1673, hlam]
                                · linarith only [h1603, h1673, hlam]
                            · linarith only [h1670, hlam, p1668_0]
                          · have p1668_0 := h1668c.1
                            have p1668_1 := h1668c.2.1
                            have p1668_2 := h1668c.2.2.1
                            have p1668_3 := h1668c.2.2.2
                            linarith only [h1658, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1668_1, u1elo0]
                          · have p1668_0 := h1668c.1
                            have p1668_1 := h1668c.2.1
                            have p1668_2 := h1668c.2.2.1
                            have p1668_3 := h1668c.2.2.2
                            rcases p1668_3 (m.d 0 1) (by simp) with h1678 | h1678
                            · rcases p1668_3 (m.d 1 2) (by simp) with h1679 | h1679
                              · linarith only [h0, h1679, hlam]
                              · rcases p1668_3 (m.d 1 3) (by simp) with h1681 | h1681
                                · linarith only [h1, h1681, hlam]
                                · linarith only [h1658, h1681, hlam]
                            · linarith only [h1678, hlam, p1668_0]
                          · have p1668_0 := h1668c.1
                            have p1668_1 := h1668c.2.1
                            have p1668_2 := h1668c.2.2.1
                            have p1668_3 := h1668c.2.2.2
                            linarith only [h1658, h1659, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1668_1, u1elo0]
                          · have p1668_0 := h1668c.1
                            have p1668_1 := h1668c.2.1
                            have p1668_2 := h1668c.2.2.1
                            have p1668_3 := h1668c.2.2.2
                            linarith only [h0, hlam, p1668_0]
                          · have p1668_0 := h1668c.1
                            have p1668_1 := h1668c.2.1
                            have p1668_2 := h1668c.2.2.1
                            have p1668_3 := h1668c.2.2.2
                            linarith only [hlam, p1668_0]
                          · have p1668_0 := h1668c.1
                            have p1668_1 := h1668c.2.1
                            have p1668_2 := h1668c.2.2.1
                            have p1668_3 := h1668c.2.2.2
                            linarith only [h1603, hlam, p1668_0]
                          · have p1668_0 := h1668c.1
                            have p1668_1 := h1668c.2.1
                            have p1668_2 := h1668c.2.2.1
                            have p1668_3 := h1668c.2.2.2
                            linarith only [h1605, hlam, p1668_0]
                          · have p1668_0 := h1668c.1
                            have p1668_1 := h1668c.2.1
                            have p1668_2 := h1668c.2.2.1
                            have p1668_3 := h1668c.2.2.2
                            linarith only [h1656, hlam, p1668_0]
                          · have p1668_0 := h1668c.1
                            have p1668_1 := h1668c.2.1
                            have p1668_2 := h1668c.2.2.1
                            have p1668_3 := h1668c.2.2.2
                            linarith only [h1, hlam, p1668_0]
                          · have p1668_0 := h1668c.1
                            have p1668_1 := h1668c.2.1
                            have p1668_2 := h1668c.2.2.1
                            have p1668_3 := h1668c.2.2.2
                            linarith only [h1, h1184, h1663, h1665, h1666, hc12, hc23, hlam, hphi, p1668_1]
                          · have p1668_0 := h1668c.1
                            have p1668_1 := h1668c.2.1
                            have p1668_2 := h1668c.2.2.1
                            have p1668_3 := h1668c.2.2.2
                            linarith only [hlam, p1668_0]
                          · have p1668_0 := h1668c.1
                            have p1668_1 := h1668c.2.1
                            have p1668_2 := h1668c.2.2.1
                            have p1668_3 := h1668c.2.2.2
                            linarith only [h1, h1184, h1605, h1663, h1665, h1666, hc12, hc23, hlam, hphi, p1668_1]
                          · have p1668_0 := h1668c.1
                            have p1668_1 := h1668c.2.1
                            have p1668_2 := h1668c.2.2.1
                            have p1668_3 := h1668c.2.2.2
                            linarith only [h1659, hlam, p1668_1]
                          · have p1668_0 := h1668c.1
                            have p1668_1 := h1668c.2.1
                            have p1668_2 := h1668c.2.2.1
                            have p1668_3 := h1668c.2.2.2
                            linarith only [h2, hlam, p1668_0]
                          · have p1668_0 := h1668c.1
                            have p1668_1 := h1668c.2.1
                            have p1668_2 := h1668c.2.2.1
                            have p1668_3 := h1668c.2.2.2
                            linarith only [h1, h1184, h1658, h1663, h1665, h1666, h2, hc12, hc23, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1668_1, u1elo0]
                          · have p1668_0 := h1668c.1
                            have p1668_1 := h1668c.2.1
                            have p1668_2 := h1668c.2.2.1
                            have p1668_3 := h1668c.2.2.2
                            linarith only [h1658, hlam, p1668_0]
                          · have p1668_0 := h1668c.1
                            have p1668_1 := h1668c.2.1
                            have p1668_2 := h1668c.2.2.1
                            have p1668_3 := h1668c.2.2.2
                            linarith only [hlam, p1668_0]
                          · have p1668_0 := h1668c.1
                            have p1668_1 := h1668c.2.1
                            have p1668_2 := h1668c.2.2.1
                            have p1668_3 := h1668c.2.2.2
                            linarith only [h1661, hlam, p1668_1]
                          · have p1668_0 := h1668c.1
                            have p1668_1 := h1668c.2.1
                            have p1668_2 := h1668c.2.2.1
                            have p1668_3 := h1668c.2.2.2
                            linarith only [h3, hlam, p1668_0]
                          · have p1668_0 := h1668c.1
                            have p1668_1 := h1668c.2.1
                            have p1668_2 := h1668c.2.2.1
                            have p1668_3 := h1668c.2.2.2
                            linarith only [h1, h1184, h1658, h1663, h1665, h1666, h3, hc12, hc23, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1668_1, u1elo0]
                          · have p1668_0 := h1668c.1
                            have p1668_1 := h1668c.2.1
                            have p1668_2 := h1668c.2.2.1
                            have p1668_3 := h1668c.2.2.2
                            linarith only [h1658, h3, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1668_1, u1elo0]
                          · have p1668_0 := h1668c.1
                            have p1668_1 := h1668c.2.1
                            have p1668_2 := h1668c.2.2.1
                            have p1668_3 := h1668c.2.2.2
                            linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1668_1, u1elo0]
                          · have p1668_0 := h1668c.1
                            have p1668_1 := h1668c.2.1
                            have p1668_2 := h1668c.2.2.1
                            have p1668_3 := h1668c.2.2.2
                            linarith only [hlam, p1668_0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1706 | h1706
                        · linarith only [h1, h1605, h1658, h1665, h1706, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases h1bigk with h1708c | h1708c | h1708c | h1708c | h1708c | h1708c | h1708c | h1708c | h1708c | h1708c | h1708c | h1708c | h1708c | h1708c | h1708c | h1708c | h1708c | h1708c | h1708c | h1708c | h1708c | h1708c | h1708c | h1708c | h1708c
                          · have p1708_0 := h1708c.1
                            have p1708_1 := h1708c.2.1
                            have p1708_2 := h1708c.2.2.1
                            have p1708_3 := h1708c.2.2.2
                            linarith only [hlam, p1708_0]
                          · have p1708_0 := h1708c.1
                            have p1708_1 := h1708c.2.1
                            have p1708_2 := h1708c.2.2.1
                            have p1708_3 := h1708c.2.2.2
                            rcases p1708_3 (m.d 0 1) (by simp) with h1710 | h1710
                            · rcases p1708_3 (m.d 1 2) (by simp) with h1711 | h1711
                              · linarith only [h1711, hlam, p1708_0]
                              · rcases p1708_3 (m.d 1 3) (by simp) with h1713 | h1713
                                · linarith only [h1, h1713, hlam]
                                · linarith only [h1603, h1713, hlam]
                            · linarith only [h1710, hlam, p1708_0]
                          · have p1708_0 := h1708c.1
                            have p1708_1 := h1708c.2.1
                            have p1708_2 := h1708c.2.2.1
                            have p1708_3 := h1708c.2.2.2
                            linarith only [h1658, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1708_1, u1elo0]
                          · have p1708_0 := h1708c.1
                            have p1708_1 := h1708c.2.1
                            have p1708_2 := h1708c.2.2.1
                            have p1708_3 := h1708c.2.2.2
                            rcases p1708_3 (m.d 0 1) (by simp) with h1718 | h1718
                            · rcases p1708_3 (m.d 1 2) (by simp) with h1719 | h1719
                              · linarith only [h0, h1719, hlam]
                              · rcases p1708_3 (m.d 1 3) (by simp) with h1721 | h1721
                                · linarith only [h1, h1721, hlam]
                                · linarith only [h1658, h1721, hlam]
                            · linarith only [h1718, hlam, p1708_0]
                          · have p1708_0 := h1708c.1
                            have p1708_1 := h1708c.2.1
                            have p1708_2 := h1708c.2.2.1
                            have p1708_3 := h1708c.2.2.2
                            linarith only [h1658, h1659, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1708_1, u1elo0]
                          · have p1708_0 := h1708c.1
                            have p1708_1 := h1708c.2.1
                            have p1708_2 := h1708c.2.2.1
                            have p1708_3 := h1708c.2.2.2
                            linarith only [h0, hlam, p1708_0]
                          · have p1708_0 := h1708c.1
                            have p1708_1 := h1708c.2.1
                            have p1708_2 := h1708c.2.2.1
                            have p1708_3 := h1708c.2.2.2
                            linarith only [hlam, p1708_0]
                          · have p1708_0 := h1708c.1
                            have p1708_1 := h1708c.2.1
                            have p1708_2 := h1708c.2.2.1
                            have p1708_3 := h1708c.2.2.2
                            linarith only [h1603, hlam, p1708_0]
                          · have p1708_0 := h1708c.1
                            have p1708_1 := h1708c.2.1
                            have p1708_2 := h1708c.2.2.1
                            have p1708_3 := h1708c.2.2.2
                            linarith only [h1605, hlam, p1708_0]
                          · have p1708_0 := h1708c.1
                            have p1708_1 := h1708c.2.1
                            have p1708_2 := h1708c.2.2.1
                            have p1708_3 := h1708c.2.2.2
                            linarith only [h1656, hlam, p1708_0]
                          · have p1708_0 := h1708c.1
                            have p1708_1 := h1708c.2.1
                            have p1708_2 := h1708c.2.2.1
                            have p1708_3 := h1708c.2.2.2
                            linarith only [h1, hlam, p1708_0]
                          · have p1708_0 := h1708c.1
                            have p1708_1 := h1708c.2.1
                            have p1708_2 := h1708c.2.2.1
                            have p1708_3 := h1708c.2.2.2
                            linarith only [h1, h1184, h1664, hc12, hc25, hlam, hphi, p1708_1]
                          · have p1708_0 := h1708c.1
                            have p1708_1 := h1708c.2.1
                            have p1708_2 := h1708c.2.2.1
                            have p1708_3 := h1708c.2.2.2
                            linarith only [hlam, p1708_0]
                          · have p1708_0 := h1708c.1
                            have p1708_1 := h1708c.2.1
                            have p1708_2 := h1708c.2.2.1
                            have p1708_3 := h1708c.2.2.2
                            linarith only [h1, h1605, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1708_1, u1elo0]
                          · have p1708_0 := h1708c.1
                            have p1708_1 := h1708c.2.1
                            have p1708_2 := h1708c.2.2.1
                            have p1708_3 := h1708c.2.2.2
                            linarith only [h1659, hlam, p1708_1]
                          · have p1708_0 := h1708c.1
                            have p1708_1 := h1708c.2.1
                            have p1708_2 := h1708c.2.2.1
                            have p1708_3 := h1708c.2.2.2
                            linarith only [h2, hlam, p1708_0]
                          · have p1708_0 := h1708c.1
                            have p1708_1 := h1708c.2.1
                            have p1708_2 := h1708c.2.2.1
                            have p1708_3 := h1708c.2.2.2
                            linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1708_1, u1elo0]
                          · have p1708_0 := h1708c.1
                            have p1708_1 := h1708c.2.1
                            have p1708_2 := h1708c.2.2.1
                            have p1708_3 := h1708c.2.2.2
                            linarith only [h1658, hlam, p1708_0]
                          · have p1708_0 := h1708c.1
                            have p1708_1 := h1708c.2.1
                            have p1708_2 := h1708c.2.2.1
                            have p1708_3 := h1708c.2.2.2
                            linarith only [hlam, p1708_0]
                          · have p1708_0 := h1708c.1
                            have p1708_1 := h1708c.2.1
                            have p1708_2 := h1708c.2.2.1
                            have p1708_3 := h1708c.2.2.2
                            linarith only [h1661, hlam, p1708_1]
                          · have p1708_0 := h1708c.1
                            have p1708_1 := h1708c.2.1
                            have p1708_2 := h1708c.2.2.1
                            have p1708_3 := h1708c.2.2.2
                            linarith only [h3, hlam, p1708_0]
                          · have p1708_0 := h1708c.1
                            have p1708_1 := h1708c.2.1
                            have p1708_2 := h1708c.2.2.1
                            have p1708_3 := h1708c.2.2.2
                            linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1708_1, u1elo0]
                          · have p1708_0 := h1708c.1
                            have p1708_1 := h1708c.2.1
                            have p1708_2 := h1708c.2.2.1
                            have p1708_3 := h1708c.2.2.2
                            linarith only [h3, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1708_1, u1elo0]
                          · have p1708_0 := h1708c.1
                            have p1708_1 := h1708c.2.1
                            have p1708_2 := h1708c.2.2.1
                            have p1708_3 := h1708c.2.2.2
                            linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1708_1, u1elo0]
                          · have p1708_0 := h1708c.1
                            have p1708_1 := h1708c.2.1
                            have p1708_2 := h1708c.2.2.1
                            have p1708_3 := h1708c.2.2.2
                            linarith only [hlam, p1708_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1746 | h1746
                      · linarith only [h1601, h1605, h1663, h1664, h1746, h2, hc12, hc35, hlam, hphi, ht23]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1748 | h1748
                        · linarith only [h1605, h1658, h1746, h1748, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                        · rcases h1bigk with h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c
                          · have p1750_0 := h1750c.1
                            have p1750_1 := h1750c.2.1
                            have p1750_2 := h1750c.2.2.1
                            have p1750_3 := h1750c.2.2.2
                            linarith only [hlam, p1750_0]
                          · have p1750_0 := h1750c.1
                            have p1750_1 := h1750c.2.1
                            have p1750_2 := h1750c.2.2.1
                            have p1750_3 := h1750c.2.2.2
                            rcases p1750_3 (m.d 0 1) (by simp) with h1752 | h1752
                            · rcases p1750_3 (m.d 1 2) (by simp) with h1753 | h1753
                              · linarith only [h1753, hlam, p1750_0]
                              · rcases p1750_3 (m.d 1 3) (by simp) with h1755 | h1755
                                · linarith only [h1, h1755, hlam]
                                · linarith only [h1603, h1755, hlam]
                            · linarith only [h1752, hlam, p1750_0]
                          · have p1750_0 := h1750c.1
                            have p1750_1 := h1750c.2.1
                            have p1750_2 := h1750c.2.2.1
                            have p1750_3 := h1750c.2.2.2
                            linarith only [h1658, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1750_1, u1elo0]
                          · have p1750_0 := h1750c.1
                            have p1750_1 := h1750c.2.1
                            have p1750_2 := h1750c.2.2.1
                            have p1750_3 := h1750c.2.2.2
                            rcases p1750_3 (m.d 0 1) (by simp) with h1760 | h1760
                            · rcases p1750_3 (m.d 1 2) (by simp) with h1761 | h1761
                              · linarith only [h0, h1761, hlam]
                              · rcases p1750_3 (m.d 1 3) (by simp) with h1763 | h1763
                                · linarith only [h1, h1763, hlam]
                                · linarith only [h1658, h1763, hlam]
                            · linarith only [h1760, hlam, p1750_0]
                          · have p1750_0 := h1750c.1
                            have p1750_1 := h1750c.2.1
                            have p1750_2 := h1750c.2.2.1
                            have p1750_3 := h1750c.2.2.2
                            linarith only [h1658, h1659, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1750_1, u1elo0]
                          · have p1750_0 := h1750c.1
                            have p1750_1 := h1750c.2.1
                            have p1750_2 := h1750c.2.2.1
                            have p1750_3 := h1750c.2.2.2
                            linarith only [h0, hlam, p1750_0]
                          · have p1750_0 := h1750c.1
                            have p1750_1 := h1750c.2.1
                            have p1750_2 := h1750c.2.2.1
                            have p1750_3 := h1750c.2.2.2
                            linarith only [hlam, p1750_0]
                          · have p1750_0 := h1750c.1
                            have p1750_1 := h1750c.2.1
                            have p1750_2 := h1750c.2.2.1
                            have p1750_3 := h1750c.2.2.2
                            linarith only [h1603, hlam, p1750_0]
                          · have p1750_0 := h1750c.1
                            have p1750_1 := h1750c.2.1
                            have p1750_2 := h1750c.2.2.1
                            have p1750_3 := h1750c.2.2.2
                            linarith only [h1605, hlam, p1750_0]
                          · have p1750_0 := h1750c.1
                            have p1750_1 := h1750c.2.1
                            have p1750_2 := h1750c.2.2.1
                            have p1750_3 := h1750c.2.2.2
                            linarith only [h1656, hlam, p1750_0]
                          · have p1750_0 := h1750c.1
                            have p1750_1 := h1750c.2.1
                            have p1750_2 := h1750c.2.2.1
                            have p1750_3 := h1750c.2.2.2
                            linarith only [h1, hlam, p1750_0]
                          · have p1750_0 := h1750c.1
                            have p1750_1 := h1750c.2.1
                            have p1750_2 := h1750c.2.2.1
                            have p1750_3 := h1750c.2.2.2
                            linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1750_1, u1elo0]
                          · have p1750_0 := h1750c.1
                            have p1750_1 := h1750c.2.1
                            have p1750_2 := h1750c.2.2.1
                            have p1750_3 := h1750c.2.2.2
                            linarith only [hlam, p1750_0]
                          · have p1750_0 := h1750c.1
                            have p1750_1 := h1750c.2.1
                            have p1750_2 := h1750c.2.2.1
                            have p1750_3 := h1750c.2.2.2
                            linarith only [h1, h1605, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1750_1, u1elo0]
                          · have p1750_0 := h1750c.1
                            have p1750_1 := h1750c.2.1
                            have p1750_2 := h1750c.2.2.1
                            have p1750_3 := h1750c.2.2.2
                            linarith only [h1659, hlam, p1750_1]
                          · have p1750_0 := h1750c.1
                            have p1750_1 := h1750c.2.1
                            have p1750_2 := h1750c.2.2.1
                            have p1750_3 := h1750c.2.2.2
                            linarith only [h2, hlam, p1750_0]
                          · have p1750_0 := h1750c.1
                            have p1750_1 := h1750c.2.1
                            have p1750_2 := h1750c.2.2.1
                            have p1750_3 := h1750c.2.2.2
                            linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1750_1, u1elo0]
                          · have p1750_0 := h1750c.1
                            have p1750_1 := h1750c.2.1
                            have p1750_2 := h1750c.2.2.1
                            have p1750_3 := h1750c.2.2.2
                            linarith only [h1658, hlam, p1750_0]
                          · have p1750_0 := h1750c.1
                            have p1750_1 := h1750c.2.1
                            have p1750_2 := h1750c.2.2.1
                            have p1750_3 := h1750c.2.2.2
                            linarith only [hlam, p1750_0]
                          · have p1750_0 := h1750c.1
                            have p1750_1 := h1750c.2.1
                            have p1750_2 := h1750c.2.2.1
                            have p1750_3 := h1750c.2.2.2
                            linarith only [h1661, hlam, p1750_1]
                          · have p1750_0 := h1750c.1
                            have p1750_1 := h1750c.2.1
                            have p1750_2 := h1750c.2.2.1
                            have p1750_3 := h1750c.2.2.2
                            linarith only [h3, hlam, p1750_0]
                          · have p1750_0 := h1750c.1
                            have p1750_1 := h1750c.2.1
                            have p1750_2 := h1750c.2.2.1
                            have p1750_3 := h1750c.2.2.2
                            linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1750_1, u1elo0]
                          · have p1750_0 := h1750c.1
                            have p1750_1 := h1750c.2.1
                            have p1750_2 := h1750c.2.2.1
                            have p1750_3 := h1750c.2.2.2
                            linarith only [h3, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1750_1, u1elo0]
                          · have p1750_0 := h1750c.1
                            have p1750_1 := h1750c.2.1
                            have p1750_2 := h1750c.2.2.1
                            have p1750_3 := h1750c.2.2.2
                            linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1750_1, u1elo0]
                          · have p1750_0 := h1750c.1
                            have p1750_1 := h1750c.2.1
                            have p1750_2 := h1750c.2.2.1
                            have p1750_3 := h1750c.2.2.2
                            linarith only [hlam, p1750_0]
                  · linarith only [h1183, h1663, h4, hlam]
            · linarith only [h1183, h1184, h1658, hc13, hc35, hlam, hphi]

end R2N4
