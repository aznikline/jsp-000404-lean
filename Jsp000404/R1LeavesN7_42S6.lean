import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6528000 in
set_option maxHeartbeats 6528000 in
theorem r1l7_20_12_14_M_LI_L_I_L_R_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1180 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1181 | h1181
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1182 | h1182
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1183 | h1183
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1184 | h1184
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1185 | h1185
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1186 | h1186
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1187 | h1187
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1188 | h1188
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1189 | h1189
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1190 | h1190
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1191 | h1191
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1192 | h1192
                        · linarith only [h1180, h1192, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1194 | h1194
                          · linarith only [h0, h1181, h1194, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                          · linarith only [h1188, h1194, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                      · linarith only [h0, h1180, h1186, h1188, h1191, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · linarith only [h0, h1180, h1186, h1188, h1190, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                  · linarith only [h0, h1180, h1186, h1188, h1189, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1200 | h1200
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1201 | h1201
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1202 | h1202
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1203 | h1203
                        · linarith only [h1180, h1203, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1205 | h1205
                          · linarith only [h0, h1181, h1205, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1207 | h1207
                            · linarith only [h1200, h1203, h1207, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1209 | h1209
                              · linarith only [h0, h1180, h1186, h1200, h1203, h1209, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1211 | h1211
                                · linarith only [h0, h1180, h1186, h1188, h1201, h1203, h1211, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1213 | h1213
                                  · linarith only [h1186, h1188, h1213, hlam]
                                  · rcases h0bigk with h1215c | h1215c | h1215c | h1215c | h1215c | h1215c | h1215c | h1215c | h1215c | h1215c | h1215c | h1215c | h1215c | h1215c | h1215c | h1215c | h1215c | h1215c | h1215c | h1215c | h1215c | h1215c | h1215c | h1215c | h1215c
                                    · have p1215_0 := h1215c.1
                                      have p1215_1 := h1215c.2.1
                                      have p1215_2 := h1215c.2.2.1
                                      have p1215_3 := h1215c.2.2.2
                                      linarith only [hlam, p1215_0]
                                    · have p1215_0 := h1215c.1
                                      have p1215_1 := h1215c.2.1
                                      have p1215_2 := h1215c.2.2.1
                                      have p1215_3 := h1215c.2.2.2
                                      linarith only [h0, hlam, p1215_1]
                                    · have p1215_0 := h1215c.1
                                      have p1215_1 := h1215c.2.1
                                      have p1215_2 := h1215c.2.2.1
                                      have p1215_3 := h1215c.2.2.2
                                      linarith only [h0, h1187, h1203, h1213, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1215_1]
                                    · have p1215_0 := h1215c.1
                                      have p1215_1 := h1215c.2.1
                                      have p1215_2 := h1215c.2.2.1
                                      have p1215_3 := h1215c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1215_1, u4ehi0]
                                    · have p1215_0 := h1215c.1
                                      have p1215_1 := h1215c.2.1
                                      have p1215_2 := h1215c.2.2.1
                                      have p1215_3 := h1215c.2.2.2
                                      linarith only [h0, h1187, h1200, h1203, h1213, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1215_1]
                                    · have p1215_0 := h1215c.1
                                      have p1215_1 := h1215c.2.1
                                      have p1215_2 := h1215c.2.2.1
                                      have p1215_3 := h1215c.2.2.2
                                      linarith only [h1180, h1200, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1215_1, u0elo1]
                                    · have p1215_0 := h1215c.1
                                      have p1215_1 := h1215c.2.1
                                      have p1215_2 := h1215c.2.2.1
                                      have p1215_3 := h1215c.2.2.2
                                      linarith only [hlam, p1215_0]
                                    · have p1215_0 := h1215c.1
                                      have p1215_1 := h1215c.2.1
                                      have p1215_2 := h1215c.2.2.1
                                      have p1215_3 := h1215c.2.2.2
                                      linarith only [h1187, h1200, h1203, h1213, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1215_1, u0elo1]
                                    · have p1215_0 := h1215c.1
                                      have p1215_1 := h1215c.2.1
                                      have p1215_2 := h1215c.2.2.1
                                      have p1215_3 := h1215c.2.2.2
                                      linarith only [h1186, h1200, h1203, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1215_1, u0elo1]
                                    · have p1215_0 := h1215c.1
                                      have p1215_1 := h1215c.2.1
                                      have p1215_2 := h1215c.2.2.1
                                      have p1215_3 := h1215c.2.2.2
                                      linarith only [h1187, h1200, h1203, h1213, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1215_1, u0elo1]
                                    · have p1215_0 := h1215c.1
                                      have p1215_1 := h1215c.2.1
                                      have p1215_2 := h1215c.2.2.1
                                      have p1215_3 := h1215c.2.2.2
                                      linarith only [h1180, hlam, p1215_1]
                                    · have p1215_0 := h1215c.1
                                      have p1215_1 := h1215c.2.1
                                      have p1215_2 := h1215c.2.2.1
                                      have p1215_3 := h1215c.2.2.2
                                      linarith only [h1183, hlam, p1215_1]
                                    · have p1215_0 := h1215c.1
                                      have p1215_1 := h1215c.2.1
                                      have p1215_2 := h1215c.2.2.1
                                      have p1215_3 := h1215c.2.2.2
                                      linarith only [hlam, p1215_0]
                                    · have p1215_0 := h1215c.1
                                      have p1215_1 := h1215c.2.1
                                      have p1215_2 := h1215c.2.2.1
                                      have p1215_3 := h1215c.2.2.2
                                      linarith only [h1180, h1186, h1200, h1203, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1215_1, u0elo0]
                                    · have p1215_0 := h1215c.1
                                      have p1215_1 := h1215c.2.1
                                      have p1215_2 := h1215c.2.2.1
                                      have p1215_3 := h1215c.2.2.2
                                      linarith only [h0, h1180, h1187, h1200, h1203, h1213, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1215_1]
                                    · have p1215_0 := h1215c.1
                                      have p1215_1 := h1215c.2.1
                                      have p1215_2 := h1215c.2.2.1
                                      have p1215_3 := h1215c.2.2.2
                                      linarith only [h1181, hlam, p1215_0]
                                    · have p1215_0 := h1215c.1
                                      have p1215_1 := h1215c.2.1
                                      have p1215_2 := h1215c.2.2.1
                                      have p1215_3 := h1215c.2.2.2
                                      linarith only [h1184, hlam, p1215_0]
                                    · have p1215_0 := h1215c.1
                                      have p1215_1 := h1215c.2.1
                                      have p1215_2 := h1215c.2.2.1
                                      have p1215_3 := h1215c.2.2.2
                                      linarith only [h1186, hlam, p1215_0]
                                    · have p1215_0 := h1215c.1
                                      have p1215_1 := h1215c.2.1
                                      have p1215_2 := h1215c.2.2.1
                                      have p1215_3 := h1215c.2.2.2
                                      linarith only [hlam, p1215_0]
                                    · have p1215_0 := h1215c.1
                                      have p1215_1 := h1215c.2.1
                                      have p1215_2 := h1215c.2.2.1
                                      have p1215_3 := h1215c.2.2.2
                                      linarith only [h1188, hlam, p1215_0]
                                    · have p1215_0 := h1215c.1
                                      have p1215_1 := h1215c.2.1
                                      have p1215_2 := h1215c.2.2.1
                                      have p1215_3 := h1215c.2.2.2
                                      linarith only [h1182, hlam, p1215_0]
                                    · have p1215_0 := h1215c.1
                                      have p1215_1 := h1215c.2.1
                                      have p1215_2 := h1215c.2.2.1
                                      have p1215_3 := h1215c.2.2.2
                                      linarith only [h1185, hlam, p1215_1]
                                    · have p1215_0 := h1215c.1
                                      have p1215_1 := h1215c.2.1
                                      have p1215_2 := h1215c.2.2.1
                                      have p1215_3 := h1215c.2.2.2
                                      linarith only [h1187, hlam, p1215_0]
                                    · have p1215_0 := h1215c.1
                                      have p1215_1 := h1215c.2.1
                                      have p1215_2 := h1215c.2.2.1
                                      have p1215_3 := h1215c.2.2.2
                                      linarith only [h1186, h1200, h1203, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1215_1, u0elo4]
                                    · have p1215_0 := h1215c.1
                                      have p1215_1 := h1215c.2.1
                                      have p1215_2 := h1215c.2.2.1
                                      have p1215_3 := h1215c.2.2.2
                                      linarith only [hlam, p1215_0]
                      · linarith only [h0, h1185, h1202, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1180, h1186, h1201, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                  · linarith only [h0, h1180, h1186, h1200, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1244 | h1244
                · linarith only [h1186, h1187, h1244, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1246 | h1246
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1247 | h1247
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1248 | h1248
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1249 | h1249
                        · linarith only [h1180, h1249, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                        · linarith only [h1186, h1187, h1249, hc13, hc35, hlam, hphi]
                      · linarith only [h0, h1180, h1186, h1248, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                    · linarith only [h0, h1182, h1186, h1187, h1247, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                  · linarith only [h0, h1182, h1186, h1187, h1246, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1255 | h1255
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1256 | h1256
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1257 | h1257
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1258 | h1258
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1259 | h1259
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1260 | h1260
                        · linarith only [h1180, h1186, h1260, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1262 | h1262
                          · linarith only [h0, h1181, h1262, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h1256, h1262, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                      · linarith only [h0, h1181, h1256, h1259, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · linarith only [h0, h1181, h1256, h1258, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                  · linarith only [h0, h1181, h1256, h1257, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · linarith only [h1186, h1255, h1256, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1269 | h1269
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1270 | h1270
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1271 | h1271
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1272 | h1272
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1273 | h1273
                        · linarith only [h1180, h1186, h1273, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1275 | h1275
                          · linarith only [h1181, h1275, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                          · linarith only [h1269, h1275, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                      · linarith only [h0, h1181, h1271, h1272, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h1181, h1269, h1271, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                  · linarith only [h0, h1181, h1269, h1270, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1281 | h1281
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1282 | h1282
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1283 | h1283
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1284 | h1284
                        · linarith only [h1180, h1186, h1284, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1286 | h1286
                          · linarith only [h1181, h1269, h1286, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1288 | h1288
                            · linarith only [h1180, h1186, h1281, h1288, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1290 | h1290
                              · linarith only [h1182, h1255, h1281, h1284, h1286, h1290, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1292 | h1292
                                · linarith only [h1181, h1269, h1282, h1292, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1294 | h1294
                                  · rcases h0bigk with h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c
                                    · have p1295_0 := h1295c.1
                                      have p1295_1 := h1295c.2.1
                                      have p1295_2 := h1295c.2.2.1
                                      have p1295_3 := h1295c.2.2.2
                                      linarith only [hlam, p1295_0]
                                    · have p1295_0 := h1295c.1
                                      have p1295_1 := h1295c.2.1
                                      have p1295_2 := h1295c.2.2.1
                                      have p1295_3 := h1295c.2.2.2
                                      linarith only [h0, hlam, p1295_1]
                                    · have p1295_0 := h1295c.1
                                      have p1295_1 := h1295c.2.1
                                      have p1295_2 := h1295c.2.2.1
                                      have p1295_3 := h1295c.2.2.2
                                      rcases p1295_3 (m.d 0 1) (by simp) with h1298 | h1298
                                      · rcases p1295_3 (m.d 0 2) (by simp) with h1299 | h1299
                                        · rcases p1295_3 (m.d 0 3) (by simp) with h1300 | h1300
                                          · linarith only [h1180, h1300, hlam]
                                          · rcases p1295_3 (m.d 0 4) (by simp) with h1302 | h1302
                                            · linarith only [h1181, h1302, hlam]
                                            · linarith only [h1186, h1302, hlam]
                                        · linarith only [h1183, h1299, hlam]
                                      · linarith only [h1180, h1298, hlam]
                                    · have p1295_0 := h1295c.1
                                      have p1295_1 := h1295c.2.1
                                      have p1295_2 := h1295c.2.2.1
                                      have p1295_3 := h1295c.2.2.2
                                      linarith only [h0, h1181, h1282, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1295_1, u4ehi2]
                                    · have p1295_0 := h1295c.1
                                      have p1295_1 := h1295c.2.1
                                      have p1295_2 := h1295c.2.2.1
                                      have p1295_3 := h1295c.2.2.2
                                      linarith only [h0, h1182, h1282, h1286, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1295_1, u4ehi2]
                                    · have p1295_0 := h1295c.1
                                      have p1295_1 := h1295c.2.1
                                      have p1295_2 := h1295c.2.2.1
                                      have p1295_3 := h1295c.2.2.2
                                      linarith only [h1180, h1181, h1269, h1281, h1282, h1294, hc23, hc34, hlam, hphi, ht0b, ht45, ht5b, p1295_1, u0elo1, u4ehi2]
                                    · have p1295_0 := h1295c.1
                                      have p1295_1 := h1295c.2.1
                                      have p1295_2 := h1295c.2.2.1
                                      have p1295_3 := h1295c.2.2.2
                                      linarith only [hlam, p1295_0]
                                    · have p1295_0 := h1295c.1
                                      have p1295_1 := h1295c.2.1
                                      have p1295_2 := h1295c.2.2.1
                                      have p1295_3 := h1295c.2.2.2
                                      rcases p1295_3 (m.d 0 1) (by simp) with h1311 | h1311
                                      · linarith only [h0, h1311, hlam]
                                      · linarith only [h1180, h1311, hlam]
                                    · have p1295_0 := h1295c.1
                                      have p1295_1 := h1295c.2.1
                                      have p1295_2 := h1295c.2.2.1
                                      have p1295_3 := h1295c.2.2.2
                                      linarith only [h1181, h1282, hlam, hphi, ht0b, ht45, ht5b, p1295_1, u0elo1, u4ehi2]
                                    · have p1295_0 := h1295c.1
                                      have p1295_1 := h1295c.2.1
                                      have p1295_2 := h1295c.2.2.1
                                      have p1295_3 := h1295c.2.2.2
                                      linarith only [h1182, h1282, h1286, hlam, hphi, ht0b, ht45, ht5b, p1295_1, u0elo1, u4ehi2]
                                    · have p1295_0 := h1295c.1
                                      have p1295_1 := h1295c.2.1
                                      have p1295_2 := h1295c.2.2.1
                                      have p1295_3 := h1295c.2.2.2
                                      linarith only [h1180, hlam, p1295_1]
                                    · have p1295_0 := h1295c.1
                                      have p1295_1 := h1295c.2.1
                                      have p1295_2 := h1295c.2.2.1
                                      have p1295_3 := h1295c.2.2.2
                                      linarith only [h1183, hlam, p1295_1]
                                    · have p1295_0 := h1295c.1
                                      have p1295_1 := h1295c.2.1
                                      have p1295_2 := h1295c.2.2.1
                                      have p1295_3 := h1295c.2.2.2
                                      linarith only [hlam, p1295_0]
                                    · have p1295_0 := h1295c.1
                                      have p1295_1 := h1295c.2.1
                                      have p1295_2 := h1295c.2.2.1
                                      have p1295_3 := h1295c.2.2.2
                                      linarith only [h1186, hlam, p1295_1]
                                    · have p1295_0 := h1295c.1
                                      have p1295_1 := h1295c.2.1
                                      have p1295_2 := h1295c.2.2.1
                                      have p1295_3 := h1295c.2.2.2
                                      linarith only [h1255, hlam, p1295_1]
                                    · have p1295_0 := h1295c.1
                                      have p1295_1 := h1295c.2.1
                                      have p1295_2 := h1295c.2.2.1
                                      have p1295_3 := h1295c.2.2.2
                                      linarith only [h1181, hlam, p1295_0]
                                    · have p1295_0 := h1295c.1
                                      have p1295_1 := h1295c.2.1
                                      have p1295_2 := h1295c.2.2.1
                                      have p1295_3 := h1295c.2.2.2
                                      linarith only [h1184, hlam, p1295_0]
                                    · have p1295_0 := h1295c.1
                                      have p1295_1 := h1295c.2.1
                                      have p1295_2 := h1295c.2.2.1
                                      have p1295_3 := h1295c.2.2.2
                                      linarith only [h1180, h1269, h1281, h1294, hc23, hc34, hlam, hphi, p1295_1]
                                    · have p1295_0 := h1295c.1
                                      have p1295_1 := h1295c.2.1
                                      have p1295_2 := h1295c.2.2.1
                                      have p1295_3 := h1295c.2.2.2
                                      linarith only [hlam, p1295_0]
                                    · have p1295_0 := h1295c.1
                                      have p1295_1 := h1295c.2.1
                                      have p1295_2 := h1295c.2.2.1
                                      have p1295_3 := h1295c.2.2.2
                                      linarith only [h1269, hlam, p1295_0]
                                    · have p1295_0 := h1295c.1
                                      have p1295_1 := h1295c.2.1
                                      have p1295_2 := h1295c.2.2.1
                                      have p1295_3 := h1295c.2.2.2
                                      linarith only [h1182, hlam, p1295_0]
                                    · have p1295_0 := h1295c.1
                                      have p1295_1 := h1295c.2.1
                                      have p1295_2 := h1295c.2.2.1
                                      have p1295_3 := h1295c.2.2.2
                                      linarith only [h1185, hlam, p1295_1]
                                    · have p1295_0 := h1295c.1
                                      have p1295_1 := h1295c.2.1
                                      have p1295_2 := h1295c.2.2.1
                                      have p1295_3 := h1295c.2.2.2
                                      linarith only [h1180, h1269, h1281, h1294, hc23, hc34, hlam, hphi, p1295_1]
                                    · have p1295_0 := h1295c.1
                                      have p1295_1 := h1295c.2.1
                                      have p1295_2 := h1295c.2.2.1
                                      have p1295_3 := h1295c.2.2.2
                                      linarith only [h1181, h1269, h1282, h1294, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1295_1, u4ehi2]
                                    · have p1295_0 := h1295c.1
                                      have p1295_1 := h1295c.2.1
                                      have p1295_2 := h1295c.2.2.1
                                      have p1295_3 := h1295c.2.2.2
                                      linarith only [hlam, p1295_0]
                                  · rcases h0bigk with h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [hlam, p1331_0]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [h0, hlam, p1331_1]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      rcases p1331_3 (m.d 0 1) (by simp) with h1334 | h1334
                                      · rcases p1331_3 (m.d 0 2) (by simp) with h1335 | h1335
                                        · rcases p1331_3 (m.d 0 3) (by simp) with h1336 | h1336
                                          · linarith only [h1180, h1336, hlam]
                                          · rcases p1331_3 (m.d 0 4) (by simp) with h1338 | h1338
                                            · linarith only [h1181, h1338, hlam]
                                            · linarith only [h1186, h1338, hlam]
                                        · linarith only [h1183, h1335, hlam]
                                      · linarith only [h1180, h1334, hlam]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [h0, h1181, h1282, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1331_1, u4ehi2]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [h0, h1182, h1282, h1286, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1331_1, u4ehi2]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [h1180, h1281, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1331_1, u0elo1]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [hlam, p1331_0]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      rcases p1331_3 (m.d 0 1) (by simp) with h1347 | h1347
                                      · linarith only [h0, h1347, hlam]
                                      · linarith only [h1180, h1347, hlam]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [h1181, h1282, hlam, hphi, ht0b, ht45, ht5b, p1331_1, u0elo1, u4ehi2]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [h1182, h1282, h1286, hlam, hphi, ht0b, ht45, ht5b, p1331_1, u0elo1, u4ehi2]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [h1180, hlam, p1331_1]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [h1183, hlam, p1331_1]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [hlam, p1331_0]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [h1186, hlam, p1331_1]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [h1255, hlam, p1331_1]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [h1181, hlam, p1331_0]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [h1184, hlam, p1331_0]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [h1180, h1186, h1281, h1294, hc23, hc45, hlam, hphi, ht34, p1331_1]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [hlam, p1331_0]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [h1269, hlam, p1331_0]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [h1182, hlam, p1331_0]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [h1185, hlam, p1331_1]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      rcases p1331_3 (m.d 0 1) (by simp) with h1364 | h1364
                                      · rcases p1331_3 (m.d 0 2) (by simp) with h1365 | h1365
                                        · rcases p1331_3 (m.d 0 3) (by simp) with h1366 | h1366
                                          · linarith only [h1255, h1366, hlam]
                                          · rcases p1331_3 (m.d 0 4) (by simp) with h1368 | h1368
                                            · linarith only [h1269, h1368, hlam]
                                            · linarith only [h1186, h1368, hlam]
                                        · linarith only [h1183, h1365, hlam]
                                      · linarith only [h1180, h1364, hlam]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [h1182, hlam, hphi, ht0b, ht45, ht5b, p1331_1, u0elo0, u4ehi0]
                                    · have p1331_0 := h1331c.1
                                      have p1331_1 := h1331c.2.1
                                      have p1331_2 := h1331c.2.2.1
                                      have p1331_3 := h1331c.2.2.2
                                      linarith only [hlam, p1331_0]
                      · linarith only [h0, h1181, h1282, h1283, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h1181, h1282, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                  · linarith only [h0, h1181, h1281, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
          · linarith only [h0, h1182, h1185, hlam]
        · linarith only [h0, h1181, h1184, hlam]
      · linarith only [h0, h1180, h1183, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1381 | h1381
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1382 | h1382
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1383 | h1383
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1384 | h1384
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1385 | h1385
              · linarith only [h1180, h1182, h1385, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1387 | h1387
                · linarith only [h1180, h1182, h1384, h1387, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1389 | h1389
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1390 | h1390
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1391 | h1391
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1392 | h1392
                        · linarith only [h1180, h1392, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                        · linarith only [h1384, h1385, h1392, hc13, hc35, hlam, hphi]
                      · linarith only [h0, h1383, h1391, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1180, h1384, h1390, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                  · linarith only [h0, h1180, h1384, h1389, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1398 | h1398
              · linarith only [h1181, h1182, h1384, h1398, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1400 | h1400
                · linarith only [h1181, h1182, h1400, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1402 | h1402
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1403 | h1403
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1404 | h1404
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1405 | h1405
                        · linarith only [h1180, h1182, h1383, h1384, h1405, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1407 | h1407
                          · linarith only [h1181, h1182, h1400, h1407, hlam]
                          · linarith only [h1181, h1182, h1407, hc45, hlam, hphi, u4ehi1]
                      · linarith only [h0, h1181, h1383, h1403, h1404, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
                    · linarith only [h0, h1181, h1403, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                  · linarith only [h0, h1181, h1402, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1413 | h1413
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1414 | h1414
              · linarith only [h1180, h1182, h1414, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1416 | h1416
                · linarith only [h0, h1180, h1383, h1413, h1416, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1418 | h1418
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1419 | h1419
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1420 | h1420
                      · linarith only [h0, h1181, h1383, h1419, h1420, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                      · linarith only [h0, h1181, h1419, h1420, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h1181, h1419, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                  · linarith only [h0, h1180, h1413, h1418, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1425 | h1425
              · linarith only [h0, h1181, h1383, h1413, h1425, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1427 | h1427
                · linarith only [h0, h1181, h1383, h1427, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1429 | h1429
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1430 | h1430
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1431 | h1431
                      · linarith only [h0, h1181, h1383, h1430, h1431, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                      · linarith only [h0, h1181, h1430, h1431, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h1181, h1430, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                  · linarith only [h0, h1181, h1429, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
        · linarith only [h0, h1181, h1382, hlam]
      · linarith only [h0, h1180, h1381, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1438 | h1438
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1439 | h1439
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1440 | h1440
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1441 | h1441
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1442 | h1442
            · linarith only [h1180, h1181, h1442, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1444 | h1444
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1445 | h1445
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1446 | h1446
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1447 | h1447
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1448 | h1448
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1449 | h1449
                        · linarith only [h1180, h1181, h1440, h1442, h1444, h1449, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1451 | h1451
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1452 | h1452
                            · linarith only [h1180, h1181, h1446, h1449, h1452, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1454 | h1454
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1455 | h1455
                                · linarith only [h1440, h1455, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                                · linarith only [h1181, h1438, h1449, h1451, h1455, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                              · linarith only [h1180, h1181, h1444, h1449, h1454, hc23, hc34, hlam, hphi]
                          · linarith only [h1180, h1181, h1446, h1451, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h1441, h1448, hlam]
                    · linarith only [h0, h1440, h1447, hlam]
                  · linarith only [h0, h1439, h1446, hlam]
                · linarith only [h1180, h1181, h1444, h1445, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1464 | h1464
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1465 | h1465
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1466 | h1466
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1467 | h1467
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1468 | h1468
                        · linarith only [h1180, h1468, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1470 | h1470
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1471 | h1471
                            · linarith only [h1180, h1181, h1465, h1468, h1471, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1473 | h1473
                              · linarith only [h1180, h1181, h1444, h1465, h1468, h1473, hc03, hc34, hlam, hphi]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1475 | h1475
                                · linarith only [h1440, h1475, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                                · linarith only [h1464, h1475, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
                          · linarith only [h1181, h1440, h1464, h1470, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h1441, h1467, hlam]
                    · linarith only [h0, h1440, h1466, hlam]
                  · linarith only [h0, h1439, h1465, hlam]
                · linarith only [h1181, h1438, h1464, hlam]
          · linarith only [h0, h1438, h1441, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1484 | h1484
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1485 | h1485
            · linarith only [h0, h1180, h1440, h1485, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1487 | h1487
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1488 | h1488
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1489 | h1489
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1490 | h1490
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1491 | h1491
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1492 | h1492
                        · linarith only [h0, h1180, h1440, h1485, h1490, h1492, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1494 | h1494
                          · linarith only [h0, h1438, h1440, h1490, h1494, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h0, h1440, h1488, h1490, h1494, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h0, h1180, h1440, h1487, h1488, h1490, h1491, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1498 | h1498
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1499 | h1499
                        · linarith only [h1180, h1485, h1499, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1501 | h1501
                          · linarith only [h0, h1438, h1490, h1501, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                          · linarith only [h0, h1180, h1488, h1489, h1490, h1501, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h0, h1180, h1484, h1487, h1488, h1498, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                  · linarith only [h0, h1439, h1489, hlam]
                · linarith only [h0, h1180, h1440, h1487, h1488, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1507 | h1507
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1508 | h1508
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1509 | h1509
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1510 | h1510
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1511 | h1511
                        · linarith only [h1180, h1485, h1507, h1511, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1513 | h1513
                          · linarith only [h0, h1438, h1440, h1509, h1513, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h0, h1180, h1440, h1507, h1508, h1509, h1513, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h0, h1180, h1440, h1508, h1509, h1510, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1517 | h1517
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1518 | h1518
                        · linarith only [h0, h1180, h1485, h1509, h1518, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1520 | h1520
                          · linarith only [h0, h1438, h1509, h1520, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                          · linarith only [h0, h1180, h1507, h1508, h1509, h1520, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h0, h1180, h1484, h1508, h1517, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h1439, h1508, hlam]
                · linarith only [h0, h1438, h1440, h1507, hlam]
          · linarith only [h0, h1438, h1484, hlam]
      · linarith only [h0, h1180, h1439, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1528 | h1528
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1529 | h1529
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1530 | h1530
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1531 | h1531
            · linarith only [h1180, h1181, h1531, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1533 | h1533
              · linarith only [h1180, h1438, h1533, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1535 | h1535
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1536 | h1536
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1537 | h1537
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1538 | h1538
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1539 | h1539
                        · linarith only [h1180, h1531, h1539, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1541 | h1541
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1542 | h1542
                            · linarith only [h1180, h1438, h1536, h1539, h1541, h1542, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1544 | h1544
                              · linarith only [h1180, h1533, h1536, h1544, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1546 | h1546
                                · linarith only [h1529, h1546, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                                · linarith only [h1535, h1546, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
                          · linarith only [h1181, h1535, h1541, hlam]
                      · linarith only [h1181, h1530, h1535, h1537, h1538, hlam, hphi, ht0b, ht45, ht5b, u0elo4, u4ehi4]
                    · linarith only [h0, h1529, h1537, hlam]
                  · linarith only [h0, h1528, h1536, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1553 | h1553
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1554 | h1554
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1555 | h1555
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1556 | h1556
                        · linarith only [h1180, h1556, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1558 | h1558
                          · linarith only [h1180, h1181, h1535, h1553, h1556, h1558, hc23, hc34, hlam, hphi]
                          · linarith only [h1180, h1181, h1553, h1558, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h1180, h1530, h1553, h1555, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1529, h1554, hlam]
                  · linarith only [h0, h1528, h1553, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1564 | h1564
            · linarith only [h1180, h1181, h1564, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1566 | h1566
              · linarith only [h1180, h1438, h1566, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1568 | h1568
                · linarith only [h1529, h1530, h1568, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1570 | h1570
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1571 | h1571
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1572 | h1572
                      · linarith only [h1529, h1530, h1572, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1574 | h1574
                        · linarith only [h1180, h1181, h1564, h1571, h1572, h1574, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1576 | h1576
                          · linarith only [h1181, h1568, h1571, h1572, h1576, hc01, hc25, hlam, hphi, ht12]
                          · linarith only [h1180, h1181, h1570, h1576, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h1180, h1529, h1570, h1571, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h1528, h1570, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1581 | h1581
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1582 | h1582
            · linarith only [h1180, h1181, h1582, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1584 | h1584
              · linarith only [h1180, h1438, h1584, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1586 | h1586
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1587 | h1587
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1588 | h1588
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1589 | h1589
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1590 | h1590
                        · linarith only [h1180, h1438, h1529, h1581, h1582, h1588, h1590, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1592 | h1592
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1593 | h1593
                            · linarith only [h1180, h1529, h1581, h1587, h1588, h1590, h1593, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1595 | h1595
                              · linarith only [h1180, h1438, h1529, h1581, h1584, h1587, h1588, h1595, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1597 | h1597
                                · linarith only [h1529, h1581, h1588, h1597, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                                · linarith only [h1180, h1438, h1529, h1581, h1597, hc13, hc45, hlam, hphi, ht34]
                          · linarith only [h1529, h1581, h1586, h1588, h1592, hlam]
                      · linarith only [h1529, h1581, h1588, h1589, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1602 | h1602
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1603 | h1603
                        · linarith only [h1180, h1603, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1605 | h1605
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1606 | h1606
                            · linarith only [h1180, h1181, h1438, h1587, h1588, h1602, h1603, h1606, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                            · linarith only [h1180, h1438, h1588, h1602, h1606, hc13, hc34, hlam, hphi]
                          · linarith only [h1180, h1438, h1587, h1588, h1602, h1605, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h1180, h1529, h1581, h1587, h1602, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h0, h1528, h1587, hlam]
                · linarith only [h1529, h1581, h1586, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1613 | h1613
            · linarith only [h0, h1180, h1529, h1613, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1615 | h1615
              · linarith only [h0, h1180, h1581, h1615, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1617 | h1617
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1618 | h1618
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1619 | h1619
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1620 | h1620
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1621 | h1621
                        · linarith only [h0, h1180, h1529, h1613, h1619, h1621, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1623 | h1623
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1624 | h1624
                            · linarith only [h0, h1180, h1581, h1618, h1620, h1621, h1623, h1624, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1626 | h1626
                              · linarith only [h0, h1180, h1529, h1615, h1618, h1619, h1626, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1628 | h1628
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1629 | h1629
                                  · rcases h0bigk with h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c
                                    · have p1630_0 := h1630c.1
                                      have p1630_1 := h1630c.2.1
                                      have p1630_2 := h1630c.2.2.1
                                      have p1630_3 := h1630c.2.2.2
                                      linarith only [hlam, p1630_0]
                                    · have p1630_0 := h1630c.1
                                      have p1630_1 := h1630c.2.1
                                      have p1630_2 := h1630c.2.2.1
                                      have p1630_3 := h1630c.2.2.2
                                      linarith only [h0, hlam, p1630_1]
                                    · have p1630_0 := h1630c.1
                                      have p1630_1 := h1630c.2.1
                                      have p1630_2 := h1630c.2.2.1
                                      have p1630_3 := h1630c.2.2.2
                                      linarith only [h0, h1581, h1619, h1628, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1630_1]
                                    · have p1630_0 := h1630c.1
                                      have p1630_1 := h1630c.2.1
                                      have p1630_2 := h1630c.2.2.1
                                      have p1630_3 := h1630c.2.2.2
                                      linarith only [h1181, hlam, p1630_1]
                                    · have p1630_0 := h1630c.1
                                      have p1630_1 := h1630c.2.1
                                      have p1630_2 := h1630c.2.2.1
                                      have p1630_3 := h1630c.2.2.2
                                      linarith only [h1438, hlam, p1630_1]
                                    · have p1630_0 := h1630c.1
                                      have p1630_1 := h1630c.2.1
                                      have p1630_2 := h1630c.2.2.1
                                      have p1630_3 := h1630c.2.2.2
                                      linarith only [h1581, h1619, h1628, hc01, hc12, hlam, hphi, p1630_1]
                                    · have p1630_0 := h1630c.1
                                      have p1630_1 := h1630c.2.1
                                      have p1630_2 := h1630c.2.2.1
                                      have p1630_3 := h1630c.2.2.2
                                      linarith only [hlam, p1630_0]
                                    · have p1630_0 := h1630c.1
                                      have p1630_1 := h1630c.2.1
                                      have p1630_2 := h1630c.2.2.1
                                      have p1630_3 := h1630c.2.2.2
                                      linarith only [h1180, h1581, h1618, h1619, h1628, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1630_1]
                                    · have p1630_0 := h1630c.1
                                      have p1630_1 := h1630c.2.1
                                      have p1630_2 := h1630c.2.2.1
                                      have p1630_3 := h1630c.2.2.2
                                      linarith only [h1529, hlam, p1630_1]
                                    · have p1630_0 := h1630c.1
                                      have p1630_1 := h1630c.2.1
                                      have p1630_2 := h1630c.2.2.1
                                      have p1630_3 := h1630c.2.2.2
                                      linarith only [h1581, hlam, p1630_0]
                                    · have p1630_0 := h1630c.1
                                      have p1630_1 := h1630c.2.1
                                      have p1630_2 := h1630c.2.2.1
                                      have p1630_3 := h1630c.2.2.2
                                      linarith only [h1180, hlam, p1630_1]
                                    · have p1630_0 := h1630c.1
                                      have p1630_1 := h1630c.2.1
                                      have p1630_2 := h1630c.2.2.1
                                      have p1630_3 := h1630c.2.2.2
                                      linarith only [h1528, hlam, p1630_1]
                                    · have p1630_0 := h1630c.1
                                      have p1630_1 := h1630c.2.1
                                      have p1630_2 := h1630c.2.2.1
                                      have p1630_3 := h1630c.2.2.2
                                      linarith only [hlam, p1630_0]
                                    · have p1630_0 := h1630c.1
                                      have p1630_1 := h1630c.2.1
                                      have p1630_2 := h1630c.2.2.1
                                      have p1630_3 := h1630c.2.2.2
                                      linarith only [h1613, hlam, p1630_1]
                                    · have p1630_0 := h1630c.1
                                      have p1630_1 := h1630c.2.1
                                      have p1630_2 := h1630c.2.2.1
                                      have p1630_3 := h1630c.2.2.2
                                      linarith only [h1615, hlam, p1630_1]
                                    · have p1630_0 := h1630c.1
                                      have p1630_1 := h1630c.2.1
                                      have p1630_2 := h1630c.2.2.1
                                      have p1630_3 := h1630c.2.2.2
                                      linarith only [h1180, h1618, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1630_1, u0elo3]
                                    · have p1630_0 := h1630c.1
                                      have p1630_1 := h1630c.2.1
                                      have p1630_2 := h1630c.2.2.1
                                      have p1630_3 := h1630c.2.2.2
                                      linarith only [h0, h1180, h1529, h1618, h1619, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1630_1]
                                    · have p1630_0 := h1630c.1
                                      have p1630_1 := h1630c.2.1
                                      have p1630_2 := h1630c.2.2.1
                                      have p1630_3 := h1630c.2.2.2
                                      rcases p1630_3 (m.d 0 1) (by simp) with h1648 | h1648
                                      · linarith only [h1181, h1648, hlam]
                                      · linarith only [h1180, h1648, hlam]
                                    · have p1630_0 := h1630c.1
                                      have p1630_1 := h1630c.2.1
                                      have p1630_2 := h1630c.2.2.1
                                      have p1630_3 := h1630c.2.2.2
                                      linarith only [hlam, p1630_0]
                                    · have p1630_0 := h1630c.1
                                      have p1630_1 := h1630c.2.1
                                      have p1630_2 := h1630c.2.2.1
                                      have p1630_3 := h1630c.2.2.2
                                      linarith only [h0, h1180, h1529, h1581, h1618, h1619, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1630_1]
                                    · have p1630_0 := h1630c.1
                                      have p1630_1 := h1630c.2.1
                                      have p1630_2 := h1630c.2.2.1
                                      have p1630_3 := h1630c.2.2.2
                                      linarith only [h1180, h1618, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1630_1, u0elo4]
                                    · have p1630_0 := h1630c.1
                                      have p1630_1 := h1630c.2.1
                                      have p1630_2 := h1630c.2.2.1
                                      have p1630_3 := h1630c.2.2.2
                                      linarith only [h0, h1180, h1581, h1618, h1619, h1628, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1630_1]
                                    · have p1630_0 := h1630c.1
                                      have p1630_1 := h1630c.2.1
                                      have p1630_2 := h1630c.2.2.1
                                      have p1630_3 := h1630c.2.2.2
                                      rcases p1630_3 (m.d 0 1) (by simp) with h1655 | h1655
                                      · linarith only [h1438, h1655, hlam]
                                      · linarith only [h1180, h1655, hlam]
                                    · have p1630_0 := h1630c.1
                                      have p1630_1 := h1630c.2.1
                                      have p1630_2 := h1630c.2.2.1
                                      have p1630_3 := h1630c.2.2.2
                                      linarith only [h1617, hlam, p1630_1]
                                    · have p1630_0 := h1630c.1
                                      have p1630_1 := h1630c.2.1
                                      have p1630_2 := h1630c.2.2.1
                                      have p1630_3 := h1630c.2.2.2
                                      linarith only [hlam, p1630_0]
                                  · linarith only [h1180, h1181, h1618, h1621, h1629, hc23, hc45, hlam, hphi, ht34]
                                · linarith only [h1529, h1617, h1628, hlam]
                          · linarith only [h1529, h1617, h1619, h1623, hlam]
                      · linarith only [h0, h1180, h1529, h1618, h1619, h1620, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1664 | h1664
                      · linarith only [h0, h1180, h1581, h1618, h1619, h1664, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1666 | h1666
                        · linarith only [h1180, h1666, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1668 | h1668
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1669 | h1669
                            · linarith only [h0, h1180, h1618, h1664, h1666, h1668, h1669, hlam]
                            · linarith only [h0, h1180, h1619, h1669, hc13, hc34, hlam, hphi]
                          · linarith only [h0, h1180, h1617, h1618, h1619, h1668, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h0, h1180, h1528, h1618, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1674 | h1674
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1675 | h1675
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1676 | h1676
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1677 | h1677
                        · linarith only [h1180, h1677, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1679 | h1679
                          · linarith only [h0, h1180, h1529, h1617, h1677, h1679, hc13, hc34, hlam, hphi]
                          · linarith only [h1180, h1181, h1674, h1679, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h1180, h1529, h1674, h1675, h1676, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1683 | h1683
                      · linarith only [h0, h1180, h1581, h1674, h1675, h1683, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1685 | h1685
                        · linarith only [h1180, h1685, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1687 | h1687
                          · linarith only [h0, h1180, h1529, h1617, h1674, h1685, h1687, hc23, hc34, hlam, hphi]
                          · linarith only [h1180, h1181, h1674, h1687, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h1180, h1528, h1674, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
      · linarith only [h0, h1180, h1528, hlam]

set_option maxHeartbeats 6528000 in
set_option maxHeartbeats 6528000 in
theorem r1l7_20_12_14_M_LI_L_I_L_R_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1180 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1692 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1693 | h1693
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1694 | h1694
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1695 | h1695
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1696 | h1696
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1697 | h1697
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1698 | h1698
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1699 | h1699
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1700 | h1700
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1701 | h1701
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1702 | h1702
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1703 | h1703
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1704 | h1704
                        · linarith only [h1692, h1704, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                        · linarith only [h1180, h1692, h1694, h1699, h1704, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi1]
                      · linarith only [h1180, h1692, h1699, h1703, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                    · linarith only [h1180, h1692, h1699, h1700, h1702, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                  · linarith only [h1180, h1692, h1699, h1700, h1701, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · linarith only [h0, h1692, h1694, h1699, h1700, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1711 | h1711
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1712 | h1712
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1713 | h1713
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1714 | h1714
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1715 | h1715
                        · linarith only [h1692, h1699, h1715, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1717 | h1717
                          · linarith only [h1694, h1717, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1719 | h1719
                            · linarith only [h1180, h1692, h1711, h1714, h1717, h1719, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1721 | h1721
                              · linarith only [h1692, h1695, h1699, h1714, h1717, h1721, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1723 | h1723
                                · linarith only [h1692, h1699, h1714, h1723, hlam]
                                · rcases h0bigk with h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c | h1725c
                                  · have p1725_0 := h1725c.1
                                    have p1725_1 := h1725c.2.1
                                    have p1725_2 := h1725c.2.2.1
                                    have p1725_3 := h1725c.2.2.2
                                    linarith only [hlam, p1725_0]
                                  · have p1725_0 := h1725c.1
                                    have p1725_1 := h1725c.2.1
                                    have p1725_2 := h1725c.2.2.1
                                    have p1725_3 := h1725c.2.2.2
                                    linarith only [h0, hlam, p1725_1]
                                  · have p1725_0 := h1725c.1
                                    have p1725_1 := h1725c.2.1
                                    have p1725_2 := h1725c.2.2.1
                                    have p1725_3 := h1725c.2.2.2
                                    linarith only [h1180, hlam, p1725_0]
                                  · have p1725_0 := h1725c.1
                                    have p1725_1 := h1725c.2.1
                                    have p1725_2 := h1725c.2.2.1
                                    have p1725_3 := h1725c.2.2.2
                                    linarith only [h1180, h1692, h1711, h1714, h1717, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1725_1]
                                  · have p1725_0 := h1725c.1
                                    have p1725_1 := h1725c.2.1
                                    have p1725_2 := h1725c.2.2.1
                                    have p1725_3 := h1725c.2.2.2
                                    linarith only [h1180, h1692, h1699, h1711, h1714, h1717, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1725_1]
                                  · have p1725_0 := h1725c.1
                                    have p1725_1 := h1725c.2.1
                                    have p1725_2 := h1725c.2.2.1
                                    have p1725_3 := h1725c.2.2.2
                                    linarith only [h1692, h1714, h1717, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1725_1, u0elo1]
                                  · have p1725_0 := h1725c.1
                                    have p1725_1 := h1725c.2.1
                                    have p1725_2 := h1725c.2.2.1
                                    have p1725_3 := h1725c.2.2.2
                                    linarith only [hlam, p1725_0]
                                  · have p1725_0 := h1725c.1
                                    have p1725_1 := h1725c.2.1
                                    have p1725_2 := h1725c.2.2.1
                                    have p1725_3 := h1725c.2.2.2
                                    linarith only [h1180, h1692, h1714, h1717, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1725_1, u0elo1]
                                  · have p1725_0 := h1725c.1
                                    have p1725_1 := h1725c.2.1
                                    have p1725_2 := h1725c.2.2.1
                                    have p1725_3 := h1725c.2.2.2
                                    linarith only [h1692, h1714, h1717, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1725_1, u0elo1]
                                  · have p1725_0 := h1725c.1
                                    have p1725_1 := h1725c.2.1
                                    have p1725_2 := h1725c.2.2.1
                                    have p1725_3 := h1725c.2.2.2
                                    linarith only [h1692, h1699, h1714, h1717, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1725_1, u0elo1]
                                  · have p1725_0 := h1725c.1
                                    have p1725_1 := h1725c.2.1
                                    have p1725_2 := h1725c.2.2.1
                                    have p1725_3 := h1725c.2.2.2
                                    linarith only [h1693, h1714, h1715, h1717, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1725_1, u0elo2]
                                  · have p1725_0 := h1725c.1
                                    have p1725_1 := h1725c.2.1
                                    have p1725_2 := h1725c.2.2.1
                                    have p1725_3 := h1725c.2.2.2
                                    linarith only [h1694, hlam, p1725_1]
                                  · have p1725_0 := h1725c.1
                                    have p1725_1 := h1725c.2.1
                                    have p1725_2 := h1725c.2.2.1
                                    have p1725_3 := h1725c.2.2.2
                                    linarith only [hlam, p1725_0]
                                  · have p1725_0 := h1725c.1
                                    have p1725_1 := h1725c.2.1
                                    have p1725_2 := h1725c.2.2.1
                                    have p1725_3 := h1725c.2.2.2
                                    linarith only [h1692, h1694, h1714, h1717, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1725_1, u0elo1]
                                  · have p1725_0 := h1725c.1
                                    have p1725_1 := h1725c.2.1
                                    have p1725_2 := h1725c.2.2.1
                                    have p1725_3 := h1725c.2.2.2
                                    linarith only [h1692, h1694, h1699, h1714, h1717, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1725_1, u0elo1]
                                  · have p1725_0 := h1725c.1
                                    have p1725_1 := h1725c.2.1
                                    have p1725_2 := h1725c.2.2.1
                                    have p1725_3 := h1725c.2.2.2
                                    linarith only [h1692, hlam, p1725_0]
                                  · have p1725_0 := h1725c.1
                                    have p1725_1 := h1725c.2.1
                                    have p1725_2 := h1725c.2.2.1
                                    have p1725_3 := h1725c.2.2.2
                                    linarith only [h1695, hlam, p1725_0]
                                  · have p1725_0 := h1725c.1
                                    have p1725_1 := h1725c.2.1
                                    have p1725_2 := h1725c.2.2.1
                                    have p1725_3 := h1725c.2.2.2
                                    linarith only [h1697, hlam, p1725_0]
                                  · have p1725_0 := h1725c.1
                                    have p1725_1 := h1725c.2.1
                                    have p1725_2 := h1725c.2.2.1
                                    have p1725_3 := h1725c.2.2.2
                                    linarith only [hlam, p1725_0]
                                  · have p1725_0 := h1725c.1
                                    have p1725_1 := h1725c.2.1
                                    have p1725_2 := h1725c.2.2.1
                                    have p1725_3 := h1725c.2.2.2
                                    linarith only [h1699, hlam, p1725_0]
                                  · have p1725_0 := h1725c.1
                                    have p1725_1 := h1725c.2.1
                                    have p1725_2 := h1725c.2.2.1
                                    have p1725_3 := h1725c.2.2.2
                                    linarith only [h1693, hlam, p1725_0]
                                  · have p1725_0 := h1725c.1
                                    have p1725_1 := h1725c.2.1
                                    have p1725_2 := h1725c.2.2.1
                                    have p1725_3 := h1725c.2.2.2
                                    linarith only [h1696, hlam, p1725_1]
                                  · have p1725_0 := h1725c.1
                                    have p1725_1 := h1725c.2.1
                                    have p1725_2 := h1725c.2.2.1
                                    have p1725_3 := h1725c.2.2.2
                                    linarith only [h1698, hlam, p1725_0]
                                  · have p1725_0 := h1725c.1
                                    have p1725_1 := h1725c.2.1
                                    have p1725_2 := h1725c.2.2.1
                                    have p1725_3 := h1725c.2.2.2
                                    linarith only [h1692, h1714, h1717, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1725_1, u0elo4]
                                  · have p1725_0 := h1725c.1
                                    have p1725_1 := h1725c.2.1
                                    have p1725_2 := h1725c.2.2.1
                                    have p1725_3 := h1725c.2.2.2
                                    linarith only [hlam, p1725_0]
                      · linarith only [h1180, h1692, h1714, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
                    · linarith only [h0, h1692, h1713, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                  · linarith only [h1180, h1692, h1711, h1712, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · linarith only [h0, h1692, h1711, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · linarith only [h1180, h1693, h1698, hlam]
          · linarith only [h1180, h1692, h1697, hlam]
        · linarith only [h0, h1693, h1696, hlam]
      · linarith only [h1180, h1692, h1694, h1695, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1759 | h1759
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1760 | h1760
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1761 | h1761
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1762 | h1762
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1763 | h1763
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1764 | h1764
                · linarith only [h1694, h1759, h1764, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · linarith only [h0, h1692, h1763, h1764, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1767 | h1767
                · linarith only [h0, h1692, h1694, h1767, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                · linarith only [h0, h1692, h1767, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · linarith only [h0, h1693, h1694, h1762, hlam]
          · linarith only [h0, h1692, h1694, h1761, hlam]
        · linarith only [h0, h1693, h1760, hlam]
      · linarith only [h0, h1692, h1759, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1774 | h1774
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1775 | h1775
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1776 | h1776
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1777 | h1777
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1778 | h1778
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1779 | h1779
              · linarith only [h1692, h1693, h1779, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1781 | h1781
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1782 | h1782
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1783 | h1783
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1784 | h1784
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1785 | h1785
                        · linarith only [h1692, h1693, h1774, h1778, h1779, h1785, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi0]
                        · linarith only [h1692, h1693, h1785, hc45, hlam, hphi, u4ehi1]
                      · linarith only [h1180, h1692, h1782, h1784, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                    · linarith only [h1180, h1776, h1781, h1783, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h1180, h1692, h1781, h1782, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · linarith only [h0, h1692, h1774, h1781, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1792 | h1792
              · linarith only [h1692, h1693, h1792, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1794 | h1794
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1795 | h1795
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1796 | h1796
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1797 | h1797
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1798 | h1798
                        · linarith only [h1692, h1792, h1798, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi0]
                        · linarith only [h1692, h1693, h1795, h1798, hc45, hlam, hphi, u4ehi2]
                      · linarith only [h1180, h1692, h1795, h1797, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h1692, h1776, h1795, h1796, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
                  · linarith only [h1180, h1692, h1794, h1795, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · linarith only [h0, h1692, h1774, h1794, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi1]
          · linarith only [h1180, h1692, h1777, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1806 | h1806
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1807 | h1807
            · linarith only [h1774, h1776, h1807, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1809 | h1809
              · linarith only [h0, h1692, h1776, h1809, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1811 | h1811
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1812 | h1812
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1813 | h1813
                    · linarith only [h1180, h1692, h1774, h1776, h1812, h1813, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h1692, h1812, h1813, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                  · linarith only [h1180, h1692, h1811, h1812, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · linarith only [h1774, h1776, h1811, hc12, hc25, hlam, hphi]
          · linarith only [h1180, h1692, h1806, hlam]
      · linarith only [h0, h1692, h1775, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1820 | h1820
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1821 | h1821
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1822 | h1822
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1823 | h1823
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1824 | h1824
              · linarith only [h1692, h1693, h1824, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1826 | h1826
                · linarith only [h1774, h1820, h1826, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · linarith only [h0, h1692, h1826, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · linarith only [h1774, h1821, h1823, hlam]
          · linarith only [h1692, h1693, h1774, h1821, h1822, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1831 | h1831
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1832 | h1832
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1833 | h1833
              · linarith only [h0, h1692, h1821, h1833, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1835 | h1835
                · linarith only [h0, h1692, h1774, h1835, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                · linarith only [h0, h1692, h1835, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1838 | h1838
              · linarith only [h1180, h1692, h1832, h1838, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1840 | h1840
                · linarith only [h0, h1692, h1774, h1840, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                · linarith only [h0, h1692, h1840, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
          · linarith only [h0, h1692, h1774, h1831, hlam]
      · linarith only [h0, h1692, h1820, hlam]

set_option maxHeartbeats 6528000 in
set_option maxHeartbeats 6528000 in
theorem r1l7_20_12_14_M_LI_L_I_L_R_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1180 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1692 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1845 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1846 | h1846
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1847 | h1847
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1848 | h1848
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1849 | h1849
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1850 | h1850
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1851 | h1851
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1852 | h1852
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1853 | h1853
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1854 | h1854
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1855 | h1855
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1856 | h1856
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1857 | h1857
                        · linarith only [h1846, h1857, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1859 | h1859
                          · linarith only [h1846, h1849, h1857, h1859, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1861 | h1861
                            · linarith only [h1846, h1849, h1857, h1861, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                            · linarith only [h1845, h1856, h1861, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · linarith only [h1692, h1851, h1856, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h1180, h1845, h1846, h1849, h1851, h1855, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                  · linarith only [h0, h1848, h1854, hlam]
                · linarith only [h0, h1847, h1853, hlam]
              · linarith only [h0, h1846, h1852, hlam]
            · linarith only [h1692, h1845, h1851, hlam]
          · linarith only [h1180, h1845, h1850, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1871 | h1871
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1872 | h1872
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1873 | h1873
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1874 | h1874
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1875 | h1875
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1876 | h1876
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1877 | h1877
                      · linarith only [h1180, h1845, h1849, h1873, h1876, h1877, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h1180, h1847, h1849, h1872, h1876, h1877, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1880 | h1880
                      · linarith only [h1180, h1845, h1876, h1880, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                      · linarith only [h1692, h1845, h1872, h1880, hc15, hlam, hphi, ht0b, ht5b, u0elo4]
                  · linarith only [h0, h1845, h1848, h1872, h1875, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                · linarith only [h0, h1847, h1874, hlam]
              · linarith only [h0, h1846, h1847, h1873, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi2]
            · linarith only [h1180, h1845, h1849, h1872, hlam]
          · linarith only [h1180, h1845, h1871, hlam]
      · linarith only [h0, h1845, h1848, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1889 | h1889
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1890 | h1890
        · linarith only [h1846, h1847, h1890, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1892 | h1892
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1893 | h1893
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1894 | h1894
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1895 | h1895
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1896 | h1896
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1897 | h1897
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1898 | h1898
                      · linarith only [h1180, h1845, h1846, h1847, h1895, h1898, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h1180, h1846, h1847, h1893, h1895, h1898, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1901 | h1901
                      · linarith only [h1180, h1845, h1897, h1901, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                      · linarith only [h1692, h1845, h1893, h1901, hc15, hlam, hphi, ht0b, ht5b, u0elo4]
                  · linarith only [h1847, h1889, h1896, hc12, hc24, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1905 | h1905
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1906 | h1906
                    · linarith only [h1180, h1890, h1894, h1895, h1906, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1908 | h1908
                      · linarith only [h1180, h1845, h1906, h1908, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                      · linarith only [h1692, h1845, h1893, h1908, hc15, hlam, hphi, ht0b, ht5b, u0elo4]
                  · linarith only [h1180, h1845, h1889, h1893, h1894, h1905, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
              · linarith only [h0, h1845, h1846, h1893, h1894, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
            · linarith only [h0, h1845, h1847, h1893, hlam]
          · linarith only [h1180, h1845, h1892, hlam]
      · linarith only [h1180, h1845, h1846, h1889, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1916 | h1916
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1917 | h1917
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1918 | h1918
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1919 | h1919
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1920 | h1920
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1921 | h1921
              · linarith only [h1846, h1916, h1921, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1923 | h1923
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1924 | h1924
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1925 | h1925
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1926 | h1926
                      · linarith only [h1692, h1845, h1921, h1923, h1926, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                      · linarith only [h1692, h1916, h1920, h1926, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h1180, h1918, h1925, hlam]
                  · linarith only [h1692, h1845, h1917, h1920, h1923, h1924, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                · linarith only [h0, h1916, h1923, hlam]
            · linarith only [h1692, h1845, h1920, hlam]
          · linarith only [h1180, h1845, h1919, hlam]
        · linarith only [h1846, h1916, h1918, hlam]
      · linarith only [h0, h1845, h1917, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1936 | h1936
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1937 | h1937
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1938 | h1938
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1939 | h1939
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1940 | h1940
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1941 | h1941
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1942 | h1942
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1943 | h1943
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1944 | h1944
                      · linarith only [h0, h1845, h1846, h1940, h1944, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h0, h1916, h1937, h1939, h1941, h1944, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h1846, h1937, h1940, h1943, hlam]
                  · linarith only [h0, h1845, h1936, h1939, h1942, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                · linarith only [h1846, h1940, h1941, hc02, hc24, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1950 | h1950
                · linarith only [h0, h1845, h1916, h1939, h1940, h1950, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1952 | h1952
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1953 | h1953
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1954 | h1954
                      · linarith only [h0, h1845, h1940, h1954, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                      · linarith only [h0, h1937, h1939, h1950, h1954, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h1180, h1937, h1953, hlam]
                  · linarith only [h0, h1845, h1936, h1939, h1952, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
            · linarith only [h0, h1845, h1916, h1939, hlam]
          · linarith only [h1180, h1845, h1938, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1961 | h1961
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1962 | h1962
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1963 | h1963
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1964 | h1964
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1965 | h1965
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1966 | h1966
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1967 | h1967
                      · linarith only [h0, h1845, h1846, h1937, h1963, h1966, h1967, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h0, h1846, h1937, h1962, h1966, h1967, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1970 | h1970
                      · linarith only [h0, h1845, h1846, h1963, h1970, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h1962, h1970, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                  · linarith only [h0, h1845, h1916, h1962, h1964, h1965, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · linarith only [h0, h1845, h1846, h1962, h1963, h1964, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1975 | h1975
                · linarith only [h0, h1845, h1916, h1962, h1963, h1975, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1977 | h1977
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1978 | h1978
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1979 | h1979
                      · linarith only [h0, h1845, h1963, h1979, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                      · linarith only [h1962, h1979, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1982 | h1982
                      · linarith only [h0, h1845, h1963, h1982, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                      · linarith only [h1692, h1962, h1982, hlam]
                  · linarith only [h0, h1845, h1936, h1962, h1977, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
            · linarith only [h0, h1845, h1846, h1937, h1962, hlam]
          · linarith only [h0, h1845, h1846, h1961, hlam]
      · linarith only [h0, h1845, h1936, hlam]

end R2N4
