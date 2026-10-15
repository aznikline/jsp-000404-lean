import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_41S14

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6760000 in
set_option maxHeartbeats 6760000 in
theorem r1l7_11_13_25_L_I_L_R_M_IR_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1234 | h1234
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1235 | h1235
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1236 | h1236
      · linarith only [h0, h1, h1236, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1238 | h1238
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1239 | h1239
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1240 | h1240
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1241 | h1241
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1242 | h1242
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1243 | h1243
                  · linarith only [h0, h1, h1236, h1243, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1245 | h1245
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1246 | h1246
                      · linarith only [h0, h1, h1243, h1246, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h0, h1, h1239, h1243, h1246, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h1238, h1243, h1245, hc12, hc23, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1250 | h1250
                  · linarith only [h0, h1, h1250, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1252 | h1252
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1253 | h1253
                      · linarith only [h0, h1, h1250, h1253, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h0, h1, h1239, h1250, h1252, h1253, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h1, h1238, h1250, h1252, hc12, hc23, hlam, hphi]
              · linarith only [h1240, h1241, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1, h1234, h1240, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1259 | h1259
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1260 | h1260
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1261 | h1261
                · linarith only [h1238, h1239, h1261, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1263 | h1263
                  · linarith only [h0, h1, h1263, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1265 | h1265
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1266 | h1266
                      · linarith only [h0, h1, h1239, h1263, h1266, hc02, hc23, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1268 | h1268
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1269 | h1269
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1270 | h1270
                            · linarith only [h0, h1, h1261, h1263, h1265, h1270, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1272 | h1272
                              · linarith only [h0, h1, h1263, h1265, h1272, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h1, h1234, h1235, h1263, h1268, h1272, hc04, hlam, hphi, ht0b, ht5b, u5ehi1]
                          · linarith only [h1, h1235, h1266, h1269, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h1235, h1238, h1259, h1268, hc02, hlam, hphi, ht0b, ht5b, u5ehi1]
                    · linarith only [h1, h1235, h1238, h1239, h1263, h1265, hc12, hc23, hlam, hphi]
              · linarith only [h1259, h1260, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1, h1235, h1238, h1239, h1259, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1280 | h1280
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1281 | h1281
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1282 | h1282
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1283 | h1283
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1284 | h1284
                  · linarith only [h0, h1, h1284, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1286 | h1286
                    · linarith only [h0, h1, h1238, h1280, h1284, h1286, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1288 | h1288
                      · linarith only [h1, h1234, h1284, h1286, h1288, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h1238, h1280, h1288, hc12, hc24, hlam, hphi]
                · linarith only [h1238, h1280, h1283, hlam]
              · linarith only [h1281, h1282, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1, h1234, h1281, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1294 | h1294
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1295 | h1295
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1296 | h1296
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1297 | h1297
                  · linarith only [h0, h1, h1297, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1299 | h1299
                    · linarith only [h0, h1, h1238, h1297, h1299, hc02, hc23, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1301 | h1301
                      · linarith only [h0, h1, h1280, h1297, h1301, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1303 | h1303
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1304 | h1304
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1305 | h1305
                            · linarith only [h1, h1234, h1297, h1305, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                            · linarith only [h1, h1234, h1296, h1297, h1299, h1305, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h1304, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h1234, h1296, h1303, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1310 | h1310
                  · linarith only [h0, h1, h1310, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1312 | h1312
                    · linarith only [h0, h1238, h1312, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1314 | h1314
                      · linarith only [h0, h1280, h1314, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1316 | h1316
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1317 | h1317
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1318 | h1318
                            · linarith only [h1, h1234, h1296, h1310, h1318, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1320 | h1320
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1321 | h1321
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1322 | h1322
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1323 | h1323
                                    · linarith only [h1234, h1296, h1316, h1323, hlam]
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
                                        linarith only [h1, h1310, hc12, hc23, hlam, hphi, p1325_1]
                                      · have p1325_0 := h1325c.1
                                        have p1325_1 := h1325c.2.1
                                        have p1325_2 := h1325c.2.2.1
                                        have p1325_3 := h1325c.2.2.2
                                        linarith only [h1, hlam, p1325_0]
                                      · have p1325_0 := h1325c.1
                                        have p1325_1 := h1325c.2.1
                                        have p1325_2 := h1325c.2.2.1
                                        have p1325_3 := h1325c.2.2.2
                                        linarith only [h1, h1310, h1312, hc12, hc23, hlam, hphi, p1325_1]
                                      · have p1325_0 := h1325c.1
                                        have p1325_1 := h1325c.2.1
                                        have p1325_2 := h1325c.2.2.1
                                        have p1325_3 := h1325c.2.2.2
                                        linarith only [h1, h1310, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1325_1, u5ehi1]
                                      · have p1325_0 := h1325c.1
                                        have p1325_1 := h1325c.2.1
                                        have p1325_2 := h1325c.2.2.1
                                        have p1325_3 := h1325c.2.2.2
                                        linarith only [h0, hlam, p1325_0]
                                      · have p1325_0 := h1325c.1
                                        have p1325_1 := h1325c.2.1
                                        have p1325_2 := h1325c.2.2.1
                                        have p1325_3 := h1325c.2.2.2
                                        linarith only [hlam, p1325_0]
                                      · have p1325_0 := h1325c.1
                                        have p1325_1 := h1325c.2.1
                                        have p1325_2 := h1325c.2.2.1
                                        have p1325_3 := h1325c.2.2.2
                                        linarith only [h1310, hlam, p1325_0]
                                      · have p1325_0 := h1325c.1
                                        have p1325_1 := h1325c.2.1
                                        have p1325_2 := h1325c.2.2.1
                                        have p1325_3 := h1325c.2.2.2
                                        linarith only [h1312, hlam, p1325_0]
                                      · have p1325_0 := h1325c.1
                                        have p1325_1 := h1325c.2.1
                                        have p1325_2 := h1325c.2.2.1
                                        have p1325_3 := h1325c.2.2.2
                                        linarith only [h1314, hlam, p1325_0]
                                      · have p1325_0 := h1325c.1
                                        have p1325_1 := h1325c.2.1
                                        have p1325_2 := h1325c.2.2.1
                                        have p1325_3 := h1325c.2.2.2
                                        linarith only [h0, h1310, hc12, hc23, hlam, hphi, p1325_1]
                                      · have p1325_0 := h1325c.1
                                        have p1325_1 := h1325c.2.1
                                        have p1325_2 := h1325c.2.2.1
                                        have p1325_3 := h1325c.2.2.2
                                        rcases p1325_3 (m.d 0 1) (by simp) with h1337 | h1337
                                        · linarith only [h1, h1337, hlam]
                                        · linarith only [h0, h1337, hlam]
                                      · have p1325_0 := h1325c.1
                                        have p1325_1 := h1325c.2.1
                                        have p1325_2 := h1325c.2.2.1
                                        have p1325_3 := h1325c.2.2.2
                                        linarith only [hlam, p1325_0]
                                      · have p1325_0 := h1325c.1
                                        have p1325_1 := h1325c.2.1
                                        have p1325_2 := h1325c.2.2.1
                                        have p1325_3 := h1325c.2.2.2
                                        rcases p1325_3 (m.d 0 1) (by simp) with h1341 | h1341
                                        · linarith only [h1, h1341, hlam]
                                        · linarith only [h1234, h1341, hlam]
                                      · have p1325_0 := h1325c.1
                                        have p1325_1 := h1325c.2.1
                                        have p1325_2 := h1325c.2.2.1
                                        have p1325_3 := h1325c.2.2.2
                                        rcases p1325_3 (m.d 0 1) (by simp) with h1344 | h1344
                                        · linarith only [h1, h1344, hlam]
                                        · linarith only [h1235, h1344, hlam]
                                      · have p1325_0 := h1325c.1
                                        have p1325_1 := h1325c.2.1
                                        have p1325_2 := h1325c.2.2.1
                                        have p1325_3 := h1325c.2.2.2
                                        linarith only [h1234, hlam, p1325_0]
                                      · have p1325_0 := h1325c.1
                                        have p1325_1 := h1325c.2.1
                                        have p1325_2 := h1325c.2.2.1
                                        have p1325_3 := h1325c.2.2.2
                                        linarith only [h1234, h1296, h1322, hc12, hc24, hlam, hphi, p1325_1]
                                      · have p1325_0 := h1325c.1
                                        have p1325_1 := h1325c.2.1
                                        have p1325_2 := h1325c.2.2.1
                                        have p1325_3 := h1325c.2.2.2
                                        linarith only [h1316, hlam, p1325_0]
                                      · have p1325_0 := h1325c.1
                                        have p1325_1 := h1325c.2.1
                                        have p1325_2 := h1325c.2.2.1
                                        have p1325_3 := h1325c.2.2.2
                                        linarith only [hlam, p1325_0]
                                      · have p1325_0 := h1325c.1
                                        have p1325_1 := h1325c.2.1
                                        have p1325_2 := h1325c.2.2.1
                                        have p1325_3 := h1325c.2.2.2
                                        linarith only [h1318, hlam, p1325_1]
                                      · have p1325_0 := h1325c.1
                                        have p1325_1 := h1325c.2.1
                                        have p1325_2 := h1325c.2.2.1
                                        have p1325_3 := h1325c.2.2.2
                                        linarith only [h1235, hlam, p1325_0]
                                      · have p1325_0 := h1325c.1
                                        have p1325_1 := h1325c.2.1
                                        have p1325_2 := h1325c.2.2.1
                                        have p1325_3 := h1325c.2.2.2
                                        linarith only [h1, h1235, h1310, hc12, hc23, hlam, hphi, p1325_1]
                                      · have p1325_0 := h1325c.1
                                        have p1325_1 := h1325c.2.1
                                        have p1325_2 := h1325c.2.2.1
                                        have p1325_3 := h1325c.2.2.2
                                        linarith only [h1317, hlam, p1325_0]
                                      · have p1325_0 := h1325c.1
                                        have p1325_1 := h1325c.2.1
                                        have p1325_2 := h1325c.2.2.1
                                        have p1325_3 := h1325c.2.2.2
                                        linarith only [h1, h1235, h1310, h1316, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1325_1, u3ehi3]
                                      · have p1325_0 := h1325c.1
                                        have p1325_1 := h1325c.2.1
                                        have p1325_2 := h1325c.2.2.1
                                        have p1325_3 := h1325c.2.2.2
                                        linarith only [hlam, p1325_0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1357 | h1357
                                    · linarith only [h0, h1238, h1322, h1357, hc12, hc34, hlam, hphi, ht23]
                                    · rcases h1bigk with h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c | h1359c
                                      · have p1359_0 := h1359c.1
                                        have p1359_1 := h1359c.2.1
                                        have p1359_2 := h1359c.2.2.1
                                        have p1359_3 := h1359c.2.2.2
                                        linarith only [hlam, p1359_0]
                                      · have p1359_0 := h1359c.1
                                        have p1359_1 := h1359c.2.1
                                        have p1359_2 := h1359c.2.2.1
                                        have p1359_3 := h1359c.2.2.2
                                        linarith only [h1, h1310, hc12, hc23, hlam, hphi, p1359_1]
                                      · have p1359_0 := h1359c.1
                                        have p1359_1 := h1359c.2.1
                                        have p1359_2 := h1359c.2.2.1
                                        have p1359_3 := h1359c.2.2.2
                                        linarith only [h1, hlam, p1359_0]
                                      · have p1359_0 := h1359c.1
                                        have p1359_1 := h1359c.2.1
                                        have p1359_2 := h1359c.2.2.1
                                        have p1359_3 := h1359c.2.2.2
                                        linarith only [h1, h1310, h1316, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1359_1, u3ehi3]
                                      · have p1359_0 := h1359c.1
                                        have p1359_1 := h1359c.2.1
                                        have p1359_2 := h1359c.2.2.1
                                        have p1359_3 := h1359c.2.2.2
                                        linarith only [h1, h1310, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1359_1, u5ehi1]
                                      · have p1359_0 := h1359c.1
                                        have p1359_1 := h1359c.2.1
                                        have p1359_2 := h1359c.2.2.1
                                        have p1359_3 := h1359c.2.2.2
                                        linarith only [h0, hlam, p1359_0]
                                      · have p1359_0 := h1359c.1
                                        have p1359_1 := h1359c.2.1
                                        have p1359_2 := h1359c.2.2.1
                                        have p1359_3 := h1359c.2.2.2
                                        linarith only [hlam, p1359_0]
                                      · have p1359_0 := h1359c.1
                                        have p1359_1 := h1359c.2.1
                                        have p1359_2 := h1359c.2.2.1
                                        have p1359_3 := h1359c.2.2.2
                                        linarith only [h1310, hlam, p1359_0]
                                      · have p1359_0 := h1359c.1
                                        have p1359_1 := h1359c.2.1
                                        have p1359_2 := h1359c.2.2.1
                                        have p1359_3 := h1359c.2.2.2
                                        linarith only [h1312, hlam, p1359_0]
                                      · have p1359_0 := h1359c.1
                                        have p1359_1 := h1359c.2.1
                                        have p1359_2 := h1359c.2.2.1
                                        have p1359_3 := h1359c.2.2.2
                                        linarith only [h1314, hlam, p1359_0]
                                      · have p1359_0 := h1359c.1
                                        have p1359_1 := h1359c.2.1
                                        have p1359_2 := h1359c.2.2.1
                                        have p1359_3 := h1359c.2.2.2
                                        linarith only [h0, h1310, hc12, hc23, hlam, hphi, p1359_1]
                                      · have p1359_0 := h1359c.1
                                        have p1359_1 := h1359c.2.1
                                        have p1359_2 := h1359c.2.2.1
                                        have p1359_3 := h1359c.2.2.2
                                        rcases p1359_3 (m.d 0 1) (by simp) with h1371 | h1371
                                        · linarith only [h1, h1371, hlam]
                                        · linarith only [h0, h1371, hlam]
                                      · have p1359_0 := h1359c.1
                                        have p1359_1 := h1359c.2.1
                                        have p1359_2 := h1359c.2.2.1
                                        have p1359_3 := h1359c.2.2.2
                                        linarith only [hlam, p1359_0]
                                      · have p1359_0 := h1359c.1
                                        have p1359_1 := h1359c.2.1
                                        have p1359_2 := h1359c.2.2.1
                                        have p1359_3 := h1359c.2.2.2
                                        rcases p1359_3 (m.d 0 1) (by simp) with h1375 | h1375
                                        · linarith only [h1, h1375, hlam]
                                        · linarith only [h1234, h1375, hlam]
                                      · have p1359_0 := h1359c.1
                                        have p1359_1 := h1359c.2.1
                                        have p1359_2 := h1359c.2.2.1
                                        have p1359_3 := h1359c.2.2.2
                                        rcases p1359_3 (m.d 0 1) (by simp) with h1378 | h1378
                                        · linarith only [h1, h1378, hlam]
                                        · linarith only [h1235, h1378, hlam]
                                      · have p1359_0 := h1359c.1
                                        have p1359_1 := h1359c.2.1
                                        have p1359_2 := h1359c.2.2.1
                                        have p1359_3 := h1359c.2.2.2
                                        linarith only [h1234, hlam, p1359_0]
                                      · have p1359_0 := h1359c.1
                                        have p1359_1 := h1359c.2.1
                                        have p1359_2 := h1359c.2.2.1
                                        have p1359_3 := h1359c.2.2.2
                                        linarith only [h1, h1235, h1310, h1318, hc12, hc23, hlam, hphi, p1359_1]
                                      · have p1359_0 := h1359c.1
                                        have p1359_1 := h1359c.2.1
                                        have p1359_2 := h1359c.2.2.1
                                        have p1359_3 := h1359c.2.2.2
                                        linarith only [h1316, hlam, p1359_0]
                                      · have p1359_0 := h1359c.1
                                        have p1359_1 := h1359c.2.1
                                        have p1359_2 := h1359c.2.2.1
                                        have p1359_3 := h1359c.2.2.2
                                        linarith only [hlam, p1359_0]
                                      · have p1359_0 := h1359c.1
                                        have p1359_1 := h1359c.2.1
                                        have p1359_2 := h1359c.2.2.1
                                        have p1359_3 := h1359c.2.2.2
                                        linarith only [h1318, hlam, p1359_1]
                                      · have p1359_0 := h1359c.1
                                        have p1359_1 := h1359c.2.1
                                        have p1359_2 := h1359c.2.2.1
                                        have p1359_3 := h1359c.2.2.2
                                        linarith only [h1235, hlam, p1359_0]
                                      · have p1359_0 := h1359c.1
                                        have p1359_1 := h1359c.2.1
                                        have p1359_2 := h1359c.2.2.1
                                        have p1359_3 := h1359c.2.2.2
                                        linarith only [h1, h1235, h1310, hc12, hc23, hlam, hphi, p1359_1]
                                      · have p1359_0 := h1359c.1
                                        have p1359_1 := h1359c.2.1
                                        have p1359_2 := h1359c.2.2.1
                                        have p1359_3 := h1359c.2.2.2
                                        linarith only [h1317, hlam, p1359_0]
                                      · have p1359_0 := h1359c.1
                                        have p1359_1 := h1359c.2.1
                                        have p1359_2 := h1359c.2.2.1
                                        have p1359_3 := h1359c.2.2.2
                                        linarith only [h1, h1235, h1310, h1316, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1359_1, u3ehi3]
                                      · have p1359_0 := h1359c.1
                                        have p1359_1 := h1359c.2.1
                                        have p1359_2 := h1359c.2.2.1
                                        have p1359_3 := h1359c.2.2.2
                                        linarith only [hlam, p1359_0]
                                · linarith only [h1, h1235, h1310, h1321, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                              · linarith only [h1, h1235, h1310, h1316, h1318, h1320, hlam]
                          · linarith only [h1, h1235, h1317, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                        · linarith only [h1, h1235, h1316, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
              · linarith only [h1294, h1295, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1, h1234, h1294, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1397 | h1397
      · linarith only [h0, h1, h1397, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1399 | h1399
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1400 | h1400
          · linarith only [h0, h1235, h1400, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1402 | h1402
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1403 | h1403
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1404 | h1404
                · linarith only [h0, h1235, h1399, h1404, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1406 | h1406
                  · linarith only [h0, h1, h1397, h1406, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1408 | h1408
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1409 | h1409
                      · linarith only [h0, h1235, h1400, h1409, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1411 | h1411
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1412 | h1412
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1413 | h1413
                            · linarith only [h1234, h1235, h1404, h1413, hlam]
                            · linarith only [h0, h1235, h1408, h1413, hc24, hc45, hlam, hphi]
                          · linarith only [h0, h1, h1408, h1411, h1412, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h0, h1, h1411, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h1397, h1399, h1408, hc12, hc23, hlam, hphi]
              · linarith only [h1402, h1403, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1, h1234, h1402, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1421 | h1421
          · linarith only [h1234, h1235, h1399, h1421, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1423 | h1423
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1424 | h1424
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1425 | h1425
                · linarith only [h1234, h1235, h1425, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1427 | h1427
                  · linarith only [h0, h1, h1397, h1427, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1429 | h1429
                    · linarith only [h0, h1, h1399, h1427, h1429, hc02, hc23, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1431 | h1431
                      · linarith only [h0, h1235, h1421, h1431, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1433 | h1433
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1434 | h1434
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1435 | h1435
                            · linarith only [h1234, h1235, h1425, h1427, h1434, h1435, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h1234, h1235, h1433, h1435, hc45, hlam, hphi, ht34, u3ehi3]
                          · linarith only [h1, h1234, h1433, h1434, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1, h1234, h1429, h1433, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1423, h1424, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1, h1234, h1423, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1442 | h1442
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1443 | h1443
      · linarith only [h0, h1, h1443, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1445 | h1445
        · linarith only [h0, h1234, h1445, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1447 | h1447
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1448 | h1448
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1449 | h1449
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1450 | h1450
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1451 | h1451
                  · linarith only [h1443, h1447, h1451, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1453 | h1453
                    · linarith only [h1445, h1447, h1453, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1455 | h1455
                      · linarith only [h0, h1, h1455, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                      · linarith only [h0, h1, h1447, h1451, h1455, hc12, hc23, hlam, hphi]
                · linarith only [h1234, h1442, h1450, hlam]
              · linarith only [h1448, h1449, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1460 | h1460
              · linarith only [h1448, h1460, hc34, hlam, hphi, u3ehi4]
              · linarith only [h0, h1, h1447, h1460, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1463 | h1463
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1464 | h1464
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1465 | h1465
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1466 | h1466
                  · linarith only [h0, h1, h1466, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1468 | h1468
                    · linarith only [h0, h1, h1445, h1466, h1468, hc02, hc23, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1470 | h1470
                      · linarith only [h0, h1, h1447, h1466, h1470, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1472 | h1472
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1473 | h1473
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1474 | h1474
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1475 | h1475
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1476 | h1476
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1477 | h1477
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1478 | h1478
                                    · rcases h1bigk with h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c
                                      · have p1479_0 := h1479c.1
                                        have p1479_1 := h1479c.2.1
                                        have p1479_2 := h1479c.2.2.1
                                        have p1479_3 := h1479c.2.2.2
                                        linarith only [hlam, p1479_0]
                                      · have p1479_0 := h1479c.1
                                        have p1479_1 := h1479c.2.1
                                        have p1479_2 := h1479c.2.2.1
                                        have p1479_3 := h1479c.2.2.2
                                        linarith only [h1234, h1466, h1472, hc12, hc23, hlam, hphi, p1479_1]
                                      · have p1479_0 := h1479c.1
                                        have p1479_1 := h1479c.2.1
                                        have p1479_2 := h1479c.2.2.1
                                        have p1479_3 := h1479c.2.2.2
                                        linarith only [h1, hlam, p1479_0]
                                      · have p1479_0 := h1479c.1
                                        have p1479_1 := h1479c.2.1
                                        have p1479_2 := h1479c.2.2.1
                                        have p1479_3 := h1479c.2.2.2
                                        linarith only [h1234, hlam, p1479_0]
                                      · have p1479_0 := h1479c.1
                                        have p1479_1 := h1479c.2.1
                                        have p1479_2 := h1479c.2.2.1
                                        have p1479_3 := h1479c.2.2.2
                                        linarith only [h1234, h1466, h1472, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1479_1, u5ehi1]
                                      · have p1479_0 := h1479c.1
                                        have p1479_1 := h1479c.2.1
                                        have p1479_2 := h1479c.2.2.1
                                        have p1479_3 := h1479c.2.2.2
                                        linarith only [h0, hlam, p1479_0]
                                      · have p1479_0 := h1479c.1
                                        have p1479_1 := h1479c.2.1
                                        have p1479_2 := h1479c.2.2.1
                                        have p1479_3 := h1479c.2.2.2
                                        linarith only [hlam, p1479_0]
                                      · have p1479_0 := h1479c.1
                                        have p1479_1 := h1479c.2.1
                                        have p1479_2 := h1479c.2.2.1
                                        have p1479_3 := h1479c.2.2.2
                                        linarith only [h1466, hlam, p1479_0]
                                      · have p1479_0 := h1479c.1
                                        have p1479_1 := h1479c.2.1
                                        have p1479_2 := h1479c.2.2.1
                                        have p1479_3 := h1479c.2.2.2
                                        linarith only [h1468, hlam, p1479_0]
                                      · have p1479_0 := h1479c.1
                                        have p1479_1 := h1479c.2.1
                                        have p1479_2 := h1479c.2.2.1
                                        have p1479_3 := h1479c.2.2.2
                                        linarith only [h1470, hlam, p1479_0]
                                      · have p1479_0 := h1479c.1
                                        have p1479_1 := h1479c.2.1
                                        have p1479_2 := h1479c.2.2.1
                                        have p1479_3 := h1479c.2.2.2
                                        linarith only [h0, h1466, hc12, hc23, hlam, hphi, p1479_1]
                                      · have p1479_0 := h1479c.1
                                        have p1479_1 := h1479c.2.1
                                        have p1479_2 := h1479c.2.2.1
                                        have p1479_3 := h1479c.2.2.2
                                        rcases p1479_3 (m.d 0 1) (by simp) with h1491 | h1491
                                        · linarith only [h1, h1491, hlam]
                                        · linarith only [h0, h1491, hlam]
                                      · have p1479_0 := h1479c.1
                                        have p1479_1 := h1479c.2.1
                                        have p1479_2 := h1479c.2.2.1
                                        have p1479_3 := h1479c.2.2.2
                                        linarith only [hlam, p1479_0]
                                      · have p1479_0 := h1479c.1
                                        have p1479_1 := h1479c.2.1
                                        have p1479_2 := h1479c.2.2.1
                                        have p1479_3 := h1479c.2.2.2
                                        linarith only [h1234, h1442, h1466, h1473, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1479_1, u3ehi4]
                                      · have p1479_0 := h1479c.1
                                        have p1479_1 := h1479c.2.1
                                        have p1479_2 := h1479c.2.2.1
                                        have p1479_3 := h1479c.2.2.2
                                        rcases p1479_3 (m.d 0 1) (by simp) with h1496 | h1496
                                        · linarith only [h1, h1496, hlam]
                                        · linarith only [h1442, h1496, hlam]
                                      · have p1479_0 := h1479c.1
                                        have p1479_1 := h1479c.2.1
                                        have p1479_2 := h1479c.2.2.1
                                        have p1479_3 := h1479c.2.2.2
                                        linarith only [h1442, h1473, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1479_1, u3ehi4]
                                      · have p1479_0 := h1479c.1
                                        have p1479_1 := h1479c.2.1
                                        have p1479_2 := h1479c.2.2.1
                                        have p1479_3 := h1479c.2.2.2
                                        rcases p1479_3 (m.d 0 1) (by simp) with h1500 | h1500
                                        · linarith only [h1234, h1500, hlam]
                                        · linarith only [h0, h1500, hlam]
                                      · have p1479_0 := h1479c.1
                                        have p1479_1 := h1479c.2.1
                                        have p1479_2 := h1479c.2.2.1
                                        have p1479_3 := h1479c.2.2.2
                                        linarith only [h1472, hlam, p1479_0]
                                      · have p1479_0 := h1479c.1
                                        have p1479_1 := h1479c.2.1
                                        have p1479_2 := h1479c.2.2.1
                                        have p1479_3 := h1479c.2.2.2
                                        linarith only [hlam, p1479_0]
                                      · have p1479_0 := h1479c.1
                                        have p1479_1 := h1479c.2.1
                                        have p1479_2 := h1479c.2.2.1
                                        have p1479_3 := h1479c.2.2.2
                                        rcases p1479_3 (m.d 0 1) (by simp) with h1505 | h1505
                                        · linarith only [h1234, h1505, hlam]
                                        · linarith only [h1442, h1505, hlam]
                                      · have p1479_0 := h1479c.1
                                        have p1479_1 := h1479c.2.1
                                        have p1479_2 := h1479c.2.2.1
                                        have p1479_3 := h1479c.2.2.2
                                        linarith only [h1442, hlam, p1479_0]
                                      · have p1479_0 := h1479c.1
                                        have p1479_1 := h1479c.2.1
                                        have p1479_2 := h1479c.2.2.1
                                        have p1479_3 := h1479c.2.2.2
                                        linarith only [h1, h1442, h1466, hc12, hc23, hlam, hphi, p1479_1]
                                      · have p1479_0 := h1479c.1
                                        have p1479_1 := h1479c.2.1
                                        have p1479_2 := h1479c.2.2.1
                                        have p1479_3 := h1479c.2.2.2
                                        linarith only [h1473, hlam, p1479_0]
                                      · have p1479_0 := h1479c.1
                                        have p1479_1 := h1479c.2.1
                                        have p1479_2 := h1479c.2.2.1
                                        have p1479_3 := h1479c.2.2.2
                                        linarith only [h1474, hlam, p1479_0]
                                      · have p1479_0 := h1479c.1
                                        have p1479_1 := h1479c.2.1
                                        have p1479_2 := h1479c.2.2.1
                                        have p1479_3 := h1479c.2.2.2
                                        linarith only [hlam, p1479_0]
                                    · linarith only [h1234, h1442, h1466, h1472, h1474, h1478, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                                  · linarith only [h0, h1234, h1442, h1445, h1466, h1472, h1474, h1477, hc12, hc23, hlam, hphi]
                                · linarith only [h1234, h1442, h1466, h1472, h1476, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                              · linarith only [h1234, h1442, h1466, h1472, h1473, h1475, hc34, hlam, hphi, u3ehi4]
                            · linarith only [h1234, h1442, h1473, h1474, hc45, hlam, hphi, ht34, u3ehi4]
                          · linarith only [h1234, h1442, h1472, h1473, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                        · linarith only [h1, h1442, h1463, h1472, hc03, hlam, hphi, ht0b, ht5b, u5ehi1]
                · linarith only [h1234, h1442, h1465, hlam]
              · linarith only [h1463, h1464, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1522 | h1522
              · linarith only [h1463, h1522, hc34, hlam, hphi, u3ehi4]
              · linarith only [h1, h1442, h1522, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1525 | h1525
      · linarith only [h0, h1, h1525, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1527 | h1527
        · linarith only [h0, h1234, h1527, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1529 | h1529
          · linarith only [h0, h1442, h1529, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1531 | h1531
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1532 | h1532
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1533 | h1533
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1534 | h1534
                  · linarith only [h0, h1234, h1525, h1534, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1536 | h1536
                    · linarith only [h0, h1442, h1527, h1533, h1536, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1538 | h1538
                      · linarith only [h0, h1442, h1529, h1538, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1540 | h1540
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1541 | h1541
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1542 | h1542
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1543 | h1543
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1544 | h1544
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1545 | h1545
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1546 | h1546
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
                                        linarith only [h1442, h1534, h1540, h1542, hc12, hc23, hlam, hphi, p1547_1]
                                      · have p1547_0 := h1547c.1
                                        have p1547_1 := h1547c.2.1
                                        have p1547_2 := h1547c.2.2.1
                                        have p1547_3 := h1547c.2.2.2
                                        linarith only [h1, hlam, p1547_0]
                                      · have p1547_0 := h1547c.1
                                        have p1547_1 := h1547c.2.1
                                        have p1547_2 := h1547c.2.2.1
                                        have p1547_3 := h1547c.2.2.2
                                        linarith only [h1234, hlam, p1547_0]
                                      · have p1547_0 := h1547c.1
                                        have p1547_1 := h1547c.2.1
                                        have p1547_2 := h1547c.2.2.1
                                        have p1547_3 := h1547c.2.2.2
                                        linarith only [h1442, hlam, p1547_0]
                                      · have p1547_0 := h1547c.1
                                        have p1547_1 := h1547c.2.1
                                        have p1547_2 := h1547c.2.2.1
                                        have p1547_3 := h1547c.2.2.2
                                        linarith only [h0, hlam, p1547_0]
                                      · have p1547_0 := h1547c.1
                                        have p1547_1 := h1547c.2.1
                                        have p1547_2 := h1547c.2.2.1
                                        have p1547_3 := h1547c.2.2.2
                                        linarith only [hlam, p1547_0]
                                      · have p1547_0 := h1547c.1
                                        have p1547_1 := h1547c.2.1
                                        have p1547_2 := h1547c.2.2.1
                                        have p1547_3 := h1547c.2.2.2
                                        linarith only [h1534, hlam, p1547_0]
                                      · have p1547_0 := h1547c.1
                                        have p1547_1 := h1547c.2.1
                                        have p1547_2 := h1547c.2.2.1
                                        have p1547_3 := h1547c.2.2.2
                                        linarith only [h1536, hlam, p1547_0]
                                      · have p1547_0 := h1547c.1
                                        have p1547_1 := h1547c.2.1
                                        have p1547_2 := h1547c.2.2.1
                                        have p1547_3 := h1547c.2.2.2
                                        linarith only [h1538, hlam, p1547_0]
                                      · have p1547_0 := h1547c.1
                                        have p1547_1 := h1547c.2.1
                                        have p1547_2 := h1547c.2.2.1
                                        have p1547_3 := h1547c.2.2.2
                                        linarith only [h0, h1534, hc12, hc23, hlam, hphi, p1547_1]
                                      · have p1547_0 := h1547c.1
                                        have p1547_1 := h1547c.2.1
                                        have p1547_2 := h1547c.2.2.1
                                        have p1547_3 := h1547c.2.2.2
                                        rcases p1547_3 (m.d 0 1) (by simp) with h1559 | h1559
                                        · linarith only [h1, h1559, hlam]
                                        · linarith only [h0, h1559, hlam]
                                      · have p1547_0 := h1547c.1
                                        have p1547_1 := h1547c.2.1
                                        have p1547_2 := h1547c.2.2.1
                                        have p1547_3 := h1547c.2.2.2
                                        linarith only [hlam, p1547_0]
                                      · have p1547_0 := h1547c.1
                                        have p1547_1 := h1547c.2.1
                                        have p1547_2 := h1547c.2.2.1
                                        have p1547_3 := h1547c.2.2.2
                                        linarith only [h0, h1234, h1534, hc12, hc23, hlam, hphi, p1547_1]
                                      · have p1547_0 := h1547c.1
                                        have p1547_1 := h1547c.2.1
                                        have p1547_2 := h1547c.2.2.1
                                        have p1547_3 := h1547c.2.2.2
                                        linarith only [h0, h1442, h1534, hc12, hc23, hlam, hphi, p1547_1]
                                      · have p1547_0 := h1547c.1
                                        have p1547_1 := h1547c.2.1
                                        have p1547_2 := h1547c.2.2.1
                                        have p1547_3 := h1547c.2.2.2
                                        linarith only [h0, h1536, h1543, hc12, hc23, hlam, hphi, p1547_1]
                                      · have p1547_0 := h1547c.1
                                        have p1547_1 := h1547c.2.1
                                        have p1547_2 := h1547c.2.2.1
                                        have p1547_3 := h1547c.2.2.2
                                        rcases p1547_3 (m.d 0 1) (by simp) with h1566 | h1566
                                        · linarith only [h1234, h1566, hlam]
                                        · linarith only [h0, h1566, hlam]
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
                                      · have p1547_0 := h1547c.1
                                        have p1547_1 := h1547c.2.1
                                        have p1547_2 := h1547c.2.2.1
                                        have p1547_3 := h1547c.2.2.2
                                        linarith only [h0, h1442, h1536, h1543, hc12, hc23, hlam, hphi, p1547_1]
                                      · have p1547_0 := h1547c.1
                                        have p1547_1 := h1547c.2.1
                                        have p1547_2 := h1547c.2.2.1
                                        have p1547_3 := h1547c.2.2.2
                                        linarith only [h0, h1538, hc12, hc25, hlam, hphi, p1547_1]
                                      · have p1547_0 := h1547c.1
                                        have p1547_1 := h1547c.2.1
                                        have p1547_2 := h1547c.2.2.1
                                        have p1547_3 := h1547c.2.2.2
                                        rcases p1547_3 (m.d 0 1) (by simp) with h1573 | h1573
                                        · linarith only [h1442, h1573, hlam]
                                        · linarith only [h0, h1573, hlam]
                                      · have p1547_0 := h1547c.1
                                        have p1547_1 := h1547c.2.1
                                        have p1547_2 := h1547c.2.2.1
                                        have p1547_3 := h1547c.2.2.2
                                        linarith only [h1541, hlam, p1547_0]
                                      · have p1547_0 := h1547c.1
                                        have p1547_1 := h1547c.2.1
                                        have p1547_2 := h1547c.2.2.1
                                        have p1547_3 := h1547c.2.2.2
                                        linarith only [h1542, hlam, p1547_0]
                                      · have p1547_0 := h1547c.1
                                        have p1547_1 := h1547c.2.1
                                        have p1547_2 := h1547c.2.2.1
                                        have p1547_3 := h1547c.2.2.2
                                        linarith only [hlam, p1547_0]
                                    · rcases h1bigk with h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c | h1579c
                                      · have p1579_0 := h1579c.1
                                        have p1579_1 := h1579c.2.1
                                        have p1579_2 := h1579c.2.2.1
                                        have p1579_3 := h1579c.2.2.2
                                        linarith only [hlam, p1579_0]
                                      · have p1579_0 := h1579c.1
                                        have p1579_1 := h1579c.2.1
                                        have p1579_2 := h1579c.2.2.1
                                        have p1579_3 := h1579c.2.2.2
                                        linarith only [h1, h1534, hc12, hc23, hlam, hphi, p1579_1]
                                      · have p1579_0 := h1579c.1
                                        have p1579_1 := h1579c.2.1
                                        have p1579_2 := h1579c.2.2.1
                                        have p1579_3 := h1579c.2.2.2
                                        linarith only [h1, hlam, p1579_0]
                                      · have p1579_0 := h1579c.1
                                        have p1579_1 := h1579c.2.1
                                        have p1579_2 := h1579c.2.2.1
                                        have p1579_3 := h1579c.2.2.2
                                        linarith only [h1234, hlam, p1579_0]
                                      · have p1579_0 := h1579c.1
                                        have p1579_1 := h1579c.2.1
                                        have p1579_2 := h1579c.2.2.1
                                        have p1579_3 := h1579c.2.2.2
                                        linarith only [h1442, hlam, p1579_0]
                                      · have p1579_0 := h1579c.1
                                        have p1579_1 := h1579c.2.1
                                        have p1579_2 := h1579c.2.2.1
                                        have p1579_3 := h1579c.2.2.2
                                        linarith only [h0, hlam, p1579_0]
                                      · have p1579_0 := h1579c.1
                                        have p1579_1 := h1579c.2.1
                                        have p1579_2 := h1579c.2.2.1
                                        have p1579_3 := h1579c.2.2.2
                                        linarith only [hlam, p1579_0]
                                      · have p1579_0 := h1579c.1
                                        have p1579_1 := h1579c.2.1
                                        have p1579_2 := h1579c.2.2.1
                                        have p1579_3 := h1579c.2.2.2
                                        linarith only [h1534, hlam, p1579_0]
                                      · have p1579_0 := h1579c.1
                                        have p1579_1 := h1579c.2.1
                                        have p1579_2 := h1579c.2.2.1
                                        have p1579_3 := h1579c.2.2.2
                                        linarith only [h1536, hlam, p1579_0]
                                      · have p1579_0 := h1579c.1
                                        have p1579_1 := h1579c.2.1
                                        have p1579_2 := h1579c.2.2.1
                                        have p1579_3 := h1579c.2.2.2
                                        linarith only [h1538, hlam, p1579_0]
                                      · have p1579_0 := h1579c.1
                                        have p1579_1 := h1579c.2.1
                                        have p1579_2 := h1579c.2.2.1
                                        have p1579_3 := h1579c.2.2.2
                                        linarith only [h0, h1534, hc12, hc23, hlam, hphi, p1579_1]
                                      · have p1579_0 := h1579c.1
                                        have p1579_1 := h1579c.2.1
                                        have p1579_2 := h1579c.2.2.1
                                        have p1579_3 := h1579c.2.2.2
                                        rcases p1579_3 (m.d 0 1) (by simp) with h1591 | h1591
                                        · linarith only [h1, h1591, hlam]
                                        · linarith only [h0, h1591, hlam]
                                      · have p1579_0 := h1579c.1
                                        have p1579_1 := h1579c.2.1
                                        have p1579_2 := h1579c.2.2.1
                                        have p1579_3 := h1579c.2.2.2
                                        linarith only [hlam, p1579_0]
                                      · have p1579_0 := h1579c.1
                                        have p1579_1 := h1579c.2.1
                                        have p1579_2 := h1579c.2.2.1
                                        have p1579_3 := h1579c.2.2.2
                                        linarith only [h0, h1234, h1534, hc12, hc23, hlam, hphi, p1579_1]
                                      · have p1579_0 := h1579c.1
                                        have p1579_1 := h1579c.2.1
                                        have p1579_2 := h1579c.2.2.1
                                        have p1579_3 := h1579c.2.2.2
                                        linarith only [h0, h1442, h1534, hc12, hc23, hlam, hphi, p1579_1]
                                      · have p1579_0 := h1579c.1
                                        have p1579_1 := h1579c.2.1
                                        have p1579_2 := h1579c.2.2.1
                                        have p1579_3 := h1579c.2.2.2
                                        linarith only [h0, h1536, h1543, hc12, hc23, hlam, hphi, p1579_1]
                                      · have p1579_0 := h1579c.1
                                        have p1579_1 := h1579c.2.1
                                        have p1579_2 := h1579c.2.2.1
                                        have p1579_3 := h1579c.2.2.2
                                        rcases p1579_3 (m.d 0 1) (by simp) with h1598 | h1598
                                        · linarith only [h1234, h1598, hlam]
                                        · linarith only [h0, h1598, hlam]
                                      · have p1579_0 := h1579c.1
                                        have p1579_1 := h1579c.2.1
                                        have p1579_2 := h1579c.2.2.1
                                        have p1579_3 := h1579c.2.2.2
                                        linarith only [h1540, hlam, p1579_0]
                                      · have p1579_0 := h1579c.1
                                        have p1579_1 := h1579c.2.1
                                        have p1579_2 := h1579c.2.2.1
                                        have p1579_3 := h1579c.2.2.2
                                        linarith only [hlam, p1579_0]
                                      · have p1579_0 := h1579c.1
                                        have p1579_1 := h1579c.2.1
                                        have p1579_2 := h1579c.2.2.1
                                        have p1579_3 := h1579c.2.2.2
                                        linarith only [h0, h1442, h1536, h1543, hc12, hc23, hlam, hphi, p1579_1]
                                      · have p1579_0 := h1579c.1
                                        have p1579_1 := h1579c.2.1
                                        have p1579_2 := h1579c.2.2.1
                                        have p1579_3 := h1579c.2.2.2
                                        linarith only [h0, h1538, h1543, h1545, hc12, hc23, hlam, hphi, p1579_1]
                                      · have p1579_0 := h1579c.1
                                        have p1579_1 := h1579c.2.1
                                        have p1579_2 := h1579c.2.2.1
                                        have p1579_3 := h1579c.2.2.2
                                        rcases p1579_3 (m.d 0 1) (by simp) with h1605 | h1605
                                        · linarith only [h1442, h1605, hlam]
                                        · linarith only [h0, h1605, hlam]
                                      · have p1579_0 := h1579c.1
                                        have p1579_1 := h1579c.2.1
                                        have p1579_2 := h1579c.2.2.1
                                        have p1579_3 := h1579c.2.2.2
                                        linarith only [h1541, hlam, p1579_0]
                                      · have p1579_0 := h1579c.1
                                        have p1579_1 := h1579c.2.1
                                        have p1579_2 := h1579c.2.2.1
                                        have p1579_3 := h1579c.2.2.2
                                        linarith only [h1542, hlam, p1579_0]
                                      · have p1579_0 := h1579c.1
                                        have p1579_1 := h1579c.2.1
                                        have p1579_2 := h1579c.2.2.1
                                        have p1579_3 := h1579c.2.2.2
                                        linarith only [hlam, p1579_0]
                                  · linarith only [h0, h1234, h1536, h1545, hc12, hc45, hlam, hphi, ht23, ht34]
                                · linarith only [h0, h1, h1534, h1544, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h1, h1532, h1534, h1543, hc34, hlam, hphi, u3ehi4]
                            · linarith only [h0, h1234, h1531, h1533, h1542, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                          · linarith only [h1, h1532, h1541, hlam]
                        · linarith only [h1, h1531, h1540, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1617 | h1617
                  · linarith only [h0, h1234, h1617, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1619 | h1619
                    · linarith only [h0, h1234, h1533, h1619, hc24, hc45, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1621 | h1621
                      · linarith only [h0, h1234, h1533, h1621, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1623 | h1623
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1624 | h1624
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1625 | h1625
                            · linarith only [h0, h1234, h1533, h1619, h1625, hc12, hc24, hlam, hphi]
                            · linarith only [h0, h1234, h1625, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h1, h1532, h1624, hlam]
                        · linarith only [h1, h1532, h1623, hc34, hlam, hphi, u3ehi4]
              · linarith only [h1531, h1532, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1631 | h1631
              · linarith only [h1531, h1631, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1633 | h1633
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1634 | h1634
                  · linarith only [h0, h1, h1634, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1636 | h1636
                    · linarith only [h0, h1527, h1636, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1638 | h1638
                      · linarith only [h0, h1, h1638, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1640 | h1640
                        · linarith only [h0, h1, h1531, h1634, h1640, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h1640, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1643 | h1643
                  · linarith only [h0, h1, h1643, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1645 | h1645
                    · linarith only [h0, h1, h1531, h1633, h1645, hc24, hc45, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1647 | h1647
                      · linarith only [h0, h1, h1531, h1633, h1647, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1649 | h1649
                        · linarith only [h0, h1, h1531, h1643, h1649, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h1649, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 6760000 in
set_option maxHeartbeats 6760000 in
theorem r1l7_11_13_25_L_I_L_R_M_IR_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_11_13_25_L_I_L_R_M_IR_x0_x0 m hb1 hb3 hb5 h0 h1
  · exact r1l7_11_13_25_L_I_L_R_M_IR_x0_x1 m hb1 hb3 hb5 h0 h1

set_option maxHeartbeats 6760000 in
set_option maxHeartbeats 6760000 in
theorem r1l7_11_13_25_L_I_L_R_M_IR_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1652 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1653 | h1653
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1654 | h1654
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1655 | h1655
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1656 | h1656
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1657 | h1657
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1658 | h1658
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1659 | h1659
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1660 | h1660
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1661 | h1661
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1662 | h1662
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1663 | h1663
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1664 | h1664
                        · linarith only [h0, h1652, h1664, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h1652, h1658, h1661, h1664, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h1654, h1663, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h1654, h1662, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h1652, h1661, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1670 | h1670
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1671 | h1671
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1672 | h1672
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1673 | h1673
                        · linarith only [h0, h1652, h1673, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h1652, h1658, h1673, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h0, h1654, h1672, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h1654, h1671, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h1652, h1658, h1670, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
              · linarith only [h1658, h1659, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1680 | h1680
              · linarith only [h1658, h1680, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1682 | h1682
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1683 | h1683
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1684 | h1684
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1685 | h1685
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1686 | h1686
                        · linarith only [h1652, h1658, h1686, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1688 | h1688
                          · linarith only [h1652, h1680, h1688, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1690 | h1690
                            · linarith only [h0, h1653, h1690, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · linarith only [h0, h1653, h1682, h1683, h1686, h1690, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h1652, h1683, h1685, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h1652, h1683, h1684, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h1652, h1683, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1696 | h1696
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1697 | h1697
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1698 | h1698
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1699 | h1699
                        · linarith only [h0, h1652, h1699, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1701 | h1701
                          · linarith only [h0, h1653, h1680, h1699, h1701, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1703 | h1703
                            · linarith only [h0, h1653, h1682, h1703, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1705 | h1705
                              · linarith only [h1652, h1658, h1696, h1705, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1707 | h1707
                                · linarith only [h1652, h1658, h1696, h1707, hc34, hlam, hphi, u3ehi4]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1709 | h1709
                                  · linarith only [h0, h1656, h1658, h1682, h1709, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1711 | h1711
                                    · linarith only [h1652, h1658, h1682, h1696, h1711, hc34, hlam, hphi, u3ehi2]
                                    · linarith only [h1652, h1658, h1696, h1711, hc45, hlam, hphi, ht34, u3ehi2]
                      · linarith only [h0, h1654, h1698, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h1652, h1696, h1697, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h1652, h1696, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · linarith only [h0, h1654, h1657, hlam]
        · linarith only [h0, h1653, h1656, hlam]
      · linarith only [h0, h1652, h1655, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1720 | h1720
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1721 | h1721
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1722 | h1722
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1723 | h1723
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1724 | h1724
              · linarith only [h1652, h1654, h1724, hlam]
              · linarith only [h1723, h1724, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1727 | h1727
              · linarith only [h1723, h1727, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1729 | h1729
                · linarith only [h1653, h1654, h1729, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1731 | h1731
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1732 | h1732
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1733 | h1733
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1734 | h1734
                        · linarith only [h1652, h1654, h1734, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1736 | h1736
                          · linarith only [h1653, h1654, h1733, h1734, h1736, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · linarith only [h1653, h1654, h1734, h1736, hc35, hlam, hphi, u3ehi1]
                      · linarith only [h0, h1722, h1733, hlam]
                    · linarith only [h0, h1652, h1731, h1732, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h1652, h1731, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1742 | h1742
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1743 | h1743
              · linarith only [h1652, h1654, h1743, hlam]
              · linarith only [h1742, h1743, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1746 | h1746
              · linarith only [h1742, h1746, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1748 | h1748
                · linarith only [h0, h1653, h1722, h1748, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1750 | h1750
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1751 | h1751
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1752 | h1752
                      · linarith only [h0, h1652, h1722, h1750, h1752, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h1652, h1750, h1752, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h1652, h1750, h1751, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h1652, h1750, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
        · linarith only [h0, h1653, h1721, hlam]
      · linarith only [h0, h1652, h1720, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1759 | h1759
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1760 | h1760
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1761 | h1761
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1762 | h1762
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1763 | h1763
            · linarith only [h1652, h1653, h1763, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1765 | h1765
              · linarith only [h1763, h1765, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1767 | h1767
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1768 | h1768
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1769 | h1769
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1770 | h1770
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1771 | h1771
                        · linarith only [h1652, h1763, h1771, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h1652, h1653, h1768, h1771, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h1652, h1653, h1768, h1769, h1770, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h1761, h1769, hlam]
                  · linarith only [h0, h1652, h1768, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h1652, h1653, h1767, hc45, hlam, hphi, ht34, u3ehi1]
          · linarith only [h0, h1759, h1762, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1779 | h1779
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1780 | h1780
            · linarith only [h0, h1652, h1761, h1780, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1782 | h1782
              · linarith only [h1780, h1782, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1784 | h1784
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1785 | h1785
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1786 | h1786
                    · linarith only [h0, h1759, h1761, h1786, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                    · linarith only [h0, h1652, h1785, h1786, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h1652, h1785, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h1652, h1653, h1784, hc45, hlam, hphi, ht34, u3ehi1]
          · linarith only [h0, h1759, h1779, hlam]
      · linarith only [h0, h1652, h1760, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1793 | h1793
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1794 | h1794
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1795 | h1795
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1796 | h1796
            · linarith only [h1652, h1653, h1796, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1798 | h1798
              · linarith only [h1796, h1798, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1800 | h1800
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1801 | h1801
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1802 | h1802
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1803 | h1803
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1804 | h1804
                        · linarith only [h1652, h1796, h1804, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h1652, h1653, h1801, h1804, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h1652, h1653, h1795, h1801, h1802, h1803, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h1652, h1801, h1802, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h1652, h1801, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h1652, h1653, h1800, hc45, hlam, hphi, ht34, u3ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1811 | h1811
            · linarith only [h1652, h1653, h1811, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1813 | h1813
              · linarith only [h1811, h1813, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1815 | h1815
                · linarith only [h1794, h1795, h1815, hlam]
                · linarith only [h1652, h1653, h1815, hc45, hlam, hphi, ht34, u3ehi1]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1818 | h1818
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1819 | h1819
            · linarith only [h0, h1652, h1794, h1819, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1821 | h1821
              · linarith only [h1819, h1821, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1823 | h1823
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1824 | h1824
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1825 | h1825
                    · linarith only [h1652, h1759, h1794, h1818, h1825, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h0, h1652, h1824, h1825, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h1652, h1824, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h1652, h1653, h1823, hc45, hlam, hphi, ht34, u3ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1830 | h1830
            · linarith only [h0, h1652, h1794, h1830, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1832 | h1832
              · linarith only [h1830, h1832, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1834 | h1834
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1835 | h1835
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1836 | h1836
                    · linarith only [h0, h1652, h1794, h1835, h1836, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h1652, h1835, h1836, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h1652, h1835, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h1652, h1653, h1834, hc45, hlam, hphi, ht34, u3ehi1]
      · linarith only [h0, h1652, h1793, hlam]

set_option maxHeartbeats 6760000 in
set_option maxHeartbeats 6760000 in
theorem r1l7_11_13_25_L_I_L_R_M_IR_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1652 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1842 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1843 | h1843
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1844 | h1844
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1845 | h1845
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1846 | h1846
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1847 | h1847
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1848 | h1848
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1849 | h1849
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1850 | h1850
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1851 | h1851
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1852 | h1852
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1853 | h1853
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1854 | h1854
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1855 | h1855
                          · linarith only [h1652, h1842, h1850, h1855, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                          · linarith only [h1652, h1842, h1849, h1850, h1853, h1855, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h1652, h1843, h1854, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                      · linarith only [h1652, h1843, h1853, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                    · linarith only [h1652, h1842, h1849, h1850, h1852, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · linarith only [h1652, h1842, h1849, h1850, h1851, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · linarith only [h0, h1842, h1844, h1849, h1850, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1863 | h1863
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1864 | h1864
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1865 | h1865
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1866 | h1866
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1867 | h1867
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1868 | h1868
                          · linarith only [h1652, h1842, h1849, h1868, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1870 | h1870
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1871 | h1871
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1872 | h1872
                                · linarith only [h1842, h1849, h1864, h1872, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1874 | h1874
                                  · linarith only [h1842, h1849, h1864, h1870, h1874, hlam]
                                  · rcases h1bigk with h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c | h1876c
                                    · have p1876_0 := h1876c.1
                                      have p1876_1 := h1876c.2.1
                                      have p1876_2 := h1876c.2.2.1
                                      have p1876_3 := h1876c.2.2.2
                                      linarith only [hlam, p1876_0]
                                    · have p1876_0 := h1876c.1
                                      have p1876_1 := h1876c.2.1
                                      have p1876_2 := h1876c.2.2.1
                                      have p1876_3 := h1876c.2.2.2
                                      linarith only [h0, hlam, p1876_0]
                                    · have p1876_0 := h1876c.1
                                      have p1876_1 := h1876c.2.1
                                      have p1876_2 := h1876c.2.2.1
                                      have p1876_3 := h1876c.2.2.2
                                      linarith only [h1652, hlam, p1876_0]
                                    · have p1876_0 := h1876c.1
                                      have p1876_1 := h1876c.2.1
                                      have p1876_2 := h1876c.2.2.1
                                      have p1876_3 := h1876c.2.2.2
                                      linarith only [h1652, h1863, h1864, h1870, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1876_1, u3ehi3]
                                    · have p1876_0 := h1876c.1
                                      have p1876_1 := h1876c.2.1
                                      have p1876_2 := h1876c.2.2.1
                                      have p1876_3 := h1876c.2.2.2
                                      linarith only [h1652, h1863, h1864, h1868, h1870, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1876_1, u3ehi3]
                                    · have p1876_0 := h1876c.1
                                      have p1876_1 := h1876c.2.1
                                      have p1876_2 := h1876c.2.2.1
                                      have p1876_3 := h1876c.2.2.2
                                      linarith only [h1842, h1864, h1870, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1876_1, u3ehi3]
                                    · have p1876_0 := h1876c.1
                                      have p1876_1 := h1876c.2.1
                                      have p1876_2 := h1876c.2.2.1
                                      have p1876_3 := h1876c.2.2.2
                                      linarith only [hlam, p1876_0]
                                    · have p1876_0 := h1876c.1
                                      have p1876_1 := h1876c.2.1
                                      have p1876_2 := h1876c.2.2.1
                                      have p1876_3 := h1876c.2.2.2
                                      linarith only [h1652, hc01, hc12, hlam, hphi, p1876_1]
                                    · have p1876_0 := h1876c.1
                                      have p1876_1 := h1876c.2.1
                                      have p1876_2 := h1876c.2.2.1
                                      have p1876_3 := h1876c.2.2.2
                                      rcases p1876_3 (m.d 0 1) (by simp) with h1885 | h1885
                                      · linarith only [h0, h1885, hlam]
                                      · linarith only [h1842, h1885, hlam]
                                    · have p1876_0 := h1876c.1
                                      have p1876_1 := h1876c.2.1
                                      have p1876_2 := h1876c.2.2.1
                                      have p1876_3 := h1876c.2.2.2
                                      rcases p1876_3 (m.d 0 1) (by simp) with h1888 | h1888
                                      · linarith only [h0, h1888, hlam]
                                      · linarith only [h1843, h1888, hlam]
                                    · have p1876_0 := h1876c.1
                                      have p1876_1 := h1876c.2.1
                                      have p1876_2 := h1876c.2.2.1
                                      have p1876_3 := h1876c.2.2.2
                                      linarith only [h1843, h1864, h1868, h1870, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1876_1, u3ehi3]
                                    · have p1876_0 := h1876c.1
                                      have p1876_1 := h1876c.2.1
                                      have p1876_2 := h1876c.2.2.1
                                      have p1876_3 := h1876c.2.2.2
                                      linarith only [h1863, hlam, p1876_1]
                                    · have p1876_0 := h1876c.1
                                      have p1876_1 := h1876c.2.1
                                      have p1876_2 := h1876c.2.2.1
                                      have p1876_3 := h1876c.2.2.2
                                      linarith only [hlam, p1876_0]
                                    · have p1876_0 := h1876c.1
                                      have p1876_1 := h1876c.2.1
                                      have p1876_2 := h1876c.2.2.1
                                      have p1876_3 := h1876c.2.2.2
                                      rcases p1876_3 (m.d 0 1) (by simp) with h1894 | h1894
                                      · linarith only [h1652, h1894, hlam]
                                      · linarith only [h1842, h1894, hlam]
                                    · have p1876_0 := h1876c.1
                                      have p1876_1 := h1876c.2.1
                                      have p1876_2 := h1876c.2.2.1
                                      have p1876_3 := h1876c.2.2.2
                                      rcases p1876_3 (m.d 0 1) (by simp) with h1897 | h1897
                                      · linarith only [h1652, h1897, hlam]
                                      · linarith only [h1843, h1897, hlam]
                                    · have p1876_0 := h1876c.1
                                      have p1876_1 := h1876c.2.1
                                      have p1876_2 := h1876c.2.2.1
                                      have p1876_3 := h1876c.2.2.2
                                      linarith only [h1842, hlam, p1876_0]
                                    · have p1876_0 := h1876c.1
                                      have p1876_1 := h1876c.2.1
                                      have p1876_2 := h1876c.2.2.1
                                      have p1876_3 := h1876c.2.2.2
                                      linarith only [h1864, hlam, p1876_1]
                                    · have p1876_0 := h1876c.1
                                      have p1876_1 := h1876c.2.1
                                      have p1876_2 := h1876c.2.2.1
                                      have p1876_3 := h1876c.2.2.2
                                      linarith only [h1866, hlam, p1876_0]
                                    · have p1876_0 := h1876c.1
                                      have p1876_1 := h1876c.2.1
                                      have p1876_2 := h1876c.2.2.1
                                      have p1876_3 := h1876c.2.2.2
                                      linarith only [hlam, p1876_0]
                                    · have p1876_0 := h1876c.1
                                      have p1876_1 := h1876c.2.1
                                      have p1876_2 := h1876c.2.2.1
                                      have p1876_3 := h1876c.2.2.2
                                      linarith only [h1868, hlam, p1876_1]
                                    · have p1876_0 := h1876c.1
                                      have p1876_1 := h1876c.2.1
                                      have p1876_2 := h1876c.2.2.1
                                      have p1876_3 := h1876c.2.2.2
                                      linarith only [h1843, hlam, p1876_0]
                                    · have p1876_0 := h1876c.1
                                      have p1876_1 := h1876c.2.1
                                      have p1876_2 := h1876c.2.2.1
                                      have p1876_3 := h1876c.2.2.2
                                      linarith only [h1865, hlam, p1876_1]
                                    · have p1876_0 := h1876c.1
                                      have p1876_1 := h1876c.2.1
                                      have p1876_2 := h1876c.2.2.1
                                      have p1876_3 := h1876c.2.2.2
                                      linarith only [h1867, hlam, p1876_0]
                                    · have p1876_0 := h1876c.1
                                      have p1876_1 := h1876c.2.1
                                      have p1876_2 := h1876c.2.2.1
                                      have p1876_3 := h1876c.2.2.2
                                      linarith only [h1843, h1864, h1870, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1876_1, u3ehi3]
                                    · have p1876_0 := h1876c.1
                                      have p1876_1 := h1876c.2.1
                                      have p1876_2 := h1876c.2.2.1
                                      have p1876_3 := h1876c.2.2.2
                                      linarith only [hlam, p1876_0]
                              · linarith only [h1652, h1843, h1863, h1867, h1871, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                            · linarith only [h1847, h1849, h1870, hc45, hlam, hphi, ht34, u3ehi2]
                        · linarith only [h1652, h1843, h1867, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                      · linarith only [h1652, h1843, h1865, h1866, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h0, h1843, h1865, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h1652, h1843, h1863, h1864, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h0, h1843, h1863, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h1847, h1848, hc35, hlam, hphi, u3ehi3]
          · linarith only [h1652, h1842, h1847, hlam]
        · linarith only [h0, h1843, h1846, hlam]
      · linarith only [h1652, h1842, h1844, h1845, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1921 | h1921
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1922 | h1922
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1923 | h1923
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1924 | h1924
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1925 | h1925
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1926 | h1926
                · linarith only [h1844, h1922, h1926, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · linarith only [h0, h1842, h1925, h1926, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1929 | h1929
                · linarith only [h0, h1843, h1844, h1929, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                · linarith only [h0, h1843, h1929, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h1923, h1924, hc35, hlam, hphi, u3ehi3]
          · linarith only [h0, h1842, h1844, h1923, hlam]
        · linarith only [h0, h1843, h1922, hlam]
      · linarith only [h0, h1842, h1921, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1936 | h1936
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1937 | h1937
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1938 | h1938
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1939 | h1939
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1940 | h1940
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1941 | h1941
              · linarith only [h1842, h1843, h1941, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1943 | h1943
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1944 | h1944
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1945 | h1945
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1946 | h1946
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1947 | h1947
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1948 | h1948
                          · linarith only [h1842, h1843, h1941, h1943, h1947, h1948, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h1842, h1843, h1946, h1948, hc45, hlam, hphi, ht34, u3ehi3]
                        · linarith only [h0, h1652, h1842, h1936, h1940, h1946, h1947, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1652, h1940, h1946, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h0, h1938, h1945, hlam]
                  · linarith only [h0, h1937, h1944, hlam]
                · linarith only [h0, h1936, h1943, hlam]
            · linarith only [h1939, h1940, hc35, hlam, hphi, u3ehi3]
          · linarith only [h1652, h1842, h1939, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1958 | h1958
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1959 | h1959
            · linarith only [h1936, h1938, h1959, hlam]
            · linarith only [h1958, h1959, hc35, hlam, hphi, u3ehi3]
          · linarith only [h1652, h1842, h1958, hlam]
      · linarith only [h0, h1842, h1937, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1964 | h1964
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1965 | h1965
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1966 | h1966
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1967 | h1967
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1968 | h1968
              · linarith only [h1842, h1843, h1968, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1970 | h1970
                · linarith only [h1936, h1965, h1970, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1972 | h1972
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1973 | h1973
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1974 | h1974
                      · linarith only [h1842, h1843, h1970, h1973, h1974, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1842, h1843, h1966, h1970, h1973, h1974, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h1965, h1973, hlam]
                  · linarith only [h0, h1964, h1972, hlam]
            · linarith only [h1966, h1967, hc35, hlam, hphi, u3ehi3]
          · linarith only [h0, h1842, h1936, h1966, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1981 | h1981
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1982 | h1982
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1983 | h1983
              · linarith only [h0, h1842, h1965, h1983, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1985 | h1985
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1986 | h1986
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1987 | h1987
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1988 | h1988
                      · linarith only [h0, h1842, h1936, h1985, h1988, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1652, h1842, h1981, h1988, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h1936, h1985, h1987, hc02, hc25, hlam, hphi]
                  · linarith only [h0, h1842, h1936, h1981, h1985, h1986, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1993 | h1993
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1994 | h1994
                    · linarith only [h0, h1842, h1965, h1981, h1985, h1994, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1996 | h1996
                      · linarith only [h0, h1842, h1985, h1996, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1652, h1981, h1996, hlam]
                  · linarith only [h0, h1842, h1964, h1981, h1993, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
            · linarith only [h1981, h1982, hc35, hlam, hphi, u3ehi3]
          · linarith only [h0, h1842, h1936, h1981, hlam]
      · linarith only [h0, h1842, h1964, hlam]

set_option maxHeartbeats 6760000 in
set_option maxHeartbeats 6760000 in
theorem r1l7_11_13_25_L_I_L_R_M_IR_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1652 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1842 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2003 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h2004 | h2004
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2005 | h2005
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2006 | h2006
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2007 | h2007
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2008 | h2008
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2009 | h2009
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2010 | h2010
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2011 | h2011
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2012 | h2012
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2013 | h2013
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2014 | h2014
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2015 | h2015
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2016 | h2016
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2017 | h2017
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2018 | h2018
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2019 | h2019
                                · linarith only [h2004, h2016, h2019, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · linarith only [h1842, h2003, h2010, h2013, h2015, h2019, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h1842, h2003, h2010, h2013, h2015, h2016, h2018, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h1842, h2003, h2010, h2013, h2014, h2017, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2024 | h2024
                            · linarith only [h2016, h2024, hc34, hlam, hphi, u3ehi4]
                            · linarith only [h1842, h2003, h2010, h2013, h2014, h2024, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h1842, h2003, h2015, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi1]
                      · linarith only [h1842, h2003, h2013, h2014, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                    · linarith only [h1652, h2007, h2013, hlam]
                  · linarith only [h0, h2003, h2012, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h0, h2003, h2011, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h0, h2003, h2010, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h1842, h2003, h2009, hlam]
          · linarith only [h2007, h2008, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2035 | h2035
          · linarith only [h2007, h2035, hc34, hlam, hphi, u3ehi4]
          · linarith only [h1652, h2003, h2035, hlam]
      · linarith only [h0, h2003, h2006, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2039 | h2039
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2040 | h2040
        · linarith only [h2004, h2005, h2040, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2042 | h2042
          · linarith only [h2040, h2042, hc34, hlam, hphi, u3ehi4]
          · linarith only [h1652, h2003, h2042, hlam]
      · linarith only [h1652, h2003, h2004, h2039, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2046 | h2046
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2047 | h2047
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2048 | h2048
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2049 | h2049
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2050 | h2050
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2051 | h2051
              · linarith only [h1842, h2003, h2004, h2046, h2051, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
              · linarith only [h0, h2003, h2051, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h1842, h2003, h2050, hlam]
          · linarith only [h2048, h2049, hc35, hlam, hphi, u3ehi3]
        · linarith only [h2004, h2046, h2048, hlam]
      · linarith only [h1842, h2003, h2046, h2047, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2058 | h2058
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2059 | h2059
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2060 | h2060
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2061 | h2061
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2062 | h2062
              · linarith only [h2004, h2058, h2062, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · linarith only [h0, h2003, h2062, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h0, h2003, h2046, h2061, hlam]
          · linarith only [h2059, h2060, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2067 | h2067
          · linarith only [h2059, h2067, hc34, hlam, hphi, u3ehi4]
          · linarith only [h1652, h2003, h2067, hlam]
      · linarith only [h0, h2003, h2058, hlam]

end R2N4
