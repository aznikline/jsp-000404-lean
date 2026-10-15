import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_51S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5346000 in
set_option maxHeartbeats 5346000 in
theorem r1l7_11_13_25_L_I_L_I_H_L_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1230 | h1230
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1231 | h1231
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1232 | h1232
      · linarith only [h0, h1, h1232, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1234 | h1234
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1235 | h1235
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1236 | h1236
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1237 | h1237
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1238 | h1238
                · linarith only [h0, h1, h1232, h1238, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1240 | h1240
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1241 | h1241
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1242 | h1242
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1243 | h1243
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1244 | h1244
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1245 | h1245
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1246 | h1246
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1247 | h1247
                                · linarith only [h0, h1, h1238, h1240, h1247, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                · linarith only [h1247, hc24, hlam, hphi, ht45, u5elo4]
                              · linarith only [h0, h1, h1238, h1246, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h1, h1238, h1240, h1245, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h1244, hc14, hlam, hphi, ht45, u5elo4]
                        · linarith only [h0, h1, h1240, h1243, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h1, h1240, h1242, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h1240, h1241, hc24, hlam, hphi, ht45, u5elo2]
                  · linarith only [h0, h1, h1234, h1238, h1240, hc12, hc23, hlam, hphi]
              · linarith only [h1, h1237, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
            · linarith only [h0, h1, h1234, h1236, hlam]
          · linarith only [h1235, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1260 | h1260
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1261 | h1261
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1262 | h1262
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1263 | h1263
                · linarith only [h0, h1232, h1263, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1265 | h1265
                  · linarith only [h0, h1234, h1265, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1267 | h1267
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1268 | h1268
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1269 | h1269
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1270 | h1270
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1271 | h1271
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1272 | h1272
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1273 | h1273
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1274 | h1274
                                  · rcases h1bigk with h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c
                                    · have p1275_0 := h1275c.1
                                      have p1275_1 := h1275c.2.1
                                      have p1275_2 := h1275c.2.2.1
                                      have p1275_3 := h1275c.2.2.2
                                      linarith only [hlam, p1275_0]
                                    · have p1275_0 := h1275c.1
                                      have p1275_1 := h1275c.2.1
                                      have p1275_2 := h1275c.2.2.1
                                      have p1275_3 := h1275c.2.2.2
                                      linarith only [h1, h1267, h1272, h1274, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1275_1]
                                    · have p1275_0 := h1275c.1
                                      have p1275_1 := h1275c.2.1
                                      have p1275_2 := h1275c.2.2.1
                                      have p1275_3 := h1275c.2.2.2
                                      linarith only [h1, hlam, p1275_0]
                                    · have p1275_0 := h1275c.1
                                      have p1275_1 := h1275c.2.1
                                      have p1275_2 := h1275c.2.2.1
                                      have p1275_3 := h1275c.2.2.2
                                      linarith only [h1, h1263, h1265, h1267, h1272, h1274, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1275_1]
                                    · have p1275_0 := h1275c.1
                                      have p1275_1 := h1275c.2.1
                                      have p1275_2 := h1275c.2.2.1
                                      have p1275_3 := h1275c.2.2.2
                                      rcases p1275_3 (m.d 0 1) (by simp) with h1280 | h1280
                                      · rcases p1275_3 (m.d 1 2) (by simp) with h1281 | h1281
                                        · linarith only [h0, h1281, hlam]
                                        · linarith only [h1267, h1281, hlam]
                                      · linarith only [h1280, hlam, p1275_0]
                                    · have p1275_0 := h1275c.1
                                      have p1275_1 := h1275c.2.1
                                      have p1275_2 := h1275c.2.2.1
                                      have p1275_3 := h1275c.2.2.2
                                      linarith only [h0, hlam, p1275_0]
                                    · have p1275_0 := h1275c.1
                                      have p1275_1 := h1275c.2.1
                                      have p1275_2 := h1275c.2.2.1
                                      have p1275_3 := h1275c.2.2.2
                                      linarith only [hlam, p1275_0]
                                    · have p1275_0 := h1275c.1
                                      have p1275_1 := h1275c.2.1
                                      have p1275_2 := h1275c.2.2.1
                                      have p1275_3 := h1275c.2.2.2
                                      linarith only [h1263, hlam, p1275_0]
                                    · have p1275_0 := h1275c.1
                                      have p1275_1 := h1275c.2.1
                                      have p1275_2 := h1275c.2.2.1
                                      have p1275_3 := h1275c.2.2.2
                                      linarith only [h1265, hlam, p1275_0]
                                    · have p1275_0 := h1275c.1
                                      have p1275_1 := h1275c.2.1
                                      have p1275_2 := h1275c.2.2.1
                                      have p1275_3 := h1275c.2.2.2
                                      linarith only [h0, h1, h1263, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1275_1]
                                    · have p1275_0 := h1275c.1
                                      have p1275_1 := h1275c.2.1
                                      have p1275_2 := h1275c.2.2.1
                                      have p1275_3 := h1275c.2.2.2
                                      linarith only [h0, h1263, hc12, hc23, hlam, hphi, p1275_1]
                                    · have p1275_0 := h1275c.1
                                      have p1275_1 := h1275c.2.1
                                      have p1275_2 := h1275c.2.2.1
                                      have p1275_3 := h1275c.2.2.2
                                      rcases p1275_3 (m.d 0 1) (by simp) with h1291 | h1291
                                      · linarith only [h1, h1291, hlam]
                                      · linarith only [h0, h1291, hlam]
                                    · have p1275_0 := h1275c.1
                                      have p1275_1 := h1275c.2.1
                                      have p1275_2 := h1275c.2.2.1
                                      have p1275_3 := h1275c.2.2.2
                                      linarith only [hlam, p1275_0]
                                    · have p1275_0 := h1275c.1
                                      have p1275_1 := h1275c.2.1
                                      have p1275_2 := h1275c.2.2.1
                                      have p1275_3 := h1275c.2.2.2
                                      rcases p1275_3 (m.d 0 1) (by simp) with h1295 | h1295
                                      · linarith only [h1, h1295, hlam]
                                      · linarith only [h1230, h1295, hlam]
                                    · have p1275_0 := h1275c.1
                                      have p1275_1 := h1275c.2.1
                                      have p1275_2 := h1275c.2.2.1
                                      have p1275_3 := h1275c.2.2.2
                                      rcases p1275_3 (m.d 0 1) (by simp) with h1298 | h1298
                                      · linarith only [h1, h1298, hlam]
                                      · linarith only [h1231, h1298, hlam]
                                    · have p1275_0 := h1275c.1
                                      have p1275_1 := h1275c.2.1
                                      have p1275_2 := h1275c.2.2.1
                                      have p1275_3 := h1275c.2.2.2
                                      linarith only [h1230, hlam, p1275_0]
                                    · have p1275_0 := h1275c.1
                                      have p1275_1 := h1275c.2.1
                                      have p1275_2 := h1275c.2.2.1
                                      have p1275_3 := h1275c.2.2.2
                                      linarith only [h1230, h1267, h1272, h1274, hc01, hc45, hlam, hphi, ht0b, ht5b, p1275_1]
                                    · have p1275_0 := h1275c.1
                                      have p1275_1 := h1275c.2.1
                                      have p1275_2 := h1275c.2.2.1
                                      have p1275_3 := h1275c.2.2.2
                                      linarith only [h1268, hlam, p1275_0]
                                    · have p1275_0 := h1275c.1
                                      have p1275_1 := h1275c.2.1
                                      have p1275_2 := h1275c.2.2.1
                                      have p1275_3 := h1275c.2.2.2
                                      linarith only [hlam, p1275_0]
                                    · have p1275_0 := h1275c.1
                                      have p1275_1 := h1275c.2.1
                                      have p1275_2 := h1275c.2.2.1
                                      have p1275_3 := h1275c.2.2.2
                                      linarith only [h1, h1230, h1263, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1275_1]
                                    · have p1275_0 := h1275c.1
                                      have p1275_1 := h1275c.2.1
                                      have p1275_2 := h1275c.2.2.1
                                      have p1275_3 := h1275c.2.2.2
                                      linarith only [h1231, hlam, p1275_0]
                                    · have p1275_0 := h1275c.1
                                      have p1275_1 := h1275c.2.1
                                      have p1275_2 := h1275c.2.2.1
                                      have p1275_3 := h1275c.2.2.2
                                      linarith only [h1267, hlam, p1275_1]
                                    · have p1275_0 := h1275c.1
                                      have p1275_1 := h1275c.2.1
                                      have p1275_2 := h1275c.2.2.1
                                      have p1275_3 := h1275c.2.2.2
                                      linarith only [h1269, hlam, p1275_0]
                                    · have p1275_0 := h1275c.1
                                      have p1275_1 := h1275c.2.1
                                      have p1275_2 := h1275c.2.2.1
                                      have p1275_3 := h1275c.2.2.2
                                      linarith only [h1270, hlam, p1275_0]
                                    · have p1275_0 := h1275c.1
                                      have p1275_1 := h1275c.2.1
                                      have p1275_2 := h1275c.2.2.1
                                      have p1275_3 := h1275c.2.2.2
                                      linarith only [hlam, p1275_0]
                                  · linarith only [h1274, hc34, hlam, hphi, ht45, u5elo4]
                                · linarith only [h1, h1230, h1234, h1263, h1270, h1273, hc02, hc23, hlam, hphi]
                              · linarith only [h1, h1230, h1263, h1270, h1272, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h1, h1230, h1263, h1265, h1267, h1271, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h1265, h1267, h1270, hc25, hlam, hphi, u5elo4]
                        · linarith only [h1, h1230, h1265, h1267, h1269, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h1, h1230, h1265, h1267, h1268, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h1267, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h1262, hc03, hlam, hphi, ht34, ht45, u5elo3]
            · linarith only [h1, h1230, h1261, hlam]
          · linarith only [h1260, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
    · linarith only [h1231, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1323 | h1323
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1324 | h1324
      · linarith only [h0, h1, h1324, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1326 | h1326
        · linarith only [h0, h1230, h1326, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1328 | h1328
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1329 | h1329
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1330 | h1330
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1331 | h1331
                · linarith only [h0, h1, h1324, h1331, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1333 | h1333
                  · linarith only [h0, h1230, h1326, h1333, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1335 | h1335
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1336 | h1336
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1337 | h1337
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1338 | h1338
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1339 | h1339
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1340 | h1340
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1341 | h1341
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1342 | h1342
                                  · rcases h1bigk with h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c
                                    · have p1343_0 := h1343c.1
                                      have p1343_1 := h1343c.2.1
                                      have p1343_2 := h1343c.2.2.1
                                      have p1343_3 := h1343c.2.2.2
                                      linarith only [hlam, p1343_0]
                                    · have p1343_0 := h1343c.1
                                      have p1343_1 := h1343c.2.1
                                      have p1343_2 := h1343c.2.2.1
                                      have p1343_3 := h1343c.2.2.2
                                      linarith only [h1230, h1331, h1336, hc12, hc23, hlam, hphi, p1343_1]
                                    · have p1343_0 := h1343c.1
                                      have p1343_1 := h1343c.2.1
                                      have p1343_2 := h1343c.2.2.1
                                      have p1343_3 := h1343c.2.2.2
                                      linarith only [h1, hlam, p1343_0]
                                    · have p1343_0 := h1343c.1
                                      have p1343_1 := h1343c.2.1
                                      have p1343_2 := h1343c.2.2.1
                                      have p1343_3 := h1343c.2.2.2
                                      linarith only [h1230, hlam, p1343_0]
                                    · have p1343_0 := h1343c.1
                                      have p1343_1 := h1343c.2.1
                                      have p1343_2 := h1343c.2.2.1
                                      have p1343_3 := h1343c.2.2.2
                                      rcases p1343_3 (m.d 0 1) (by simp) with h1348 | h1348
                                      · rcases p1343_3 (m.d 1 2) (by simp) with h1349 | h1349
                                        · linarith only [h0, h1349, hlam]
                                        · linarith only [h1335, h1349, hlam]
                                      · linarith only [h1348, hlam, p1343_0]
                                    · have p1343_0 := h1343c.1
                                      have p1343_1 := h1343c.2.1
                                      have p1343_2 := h1343c.2.2.1
                                      have p1343_3 := h1343c.2.2.2
                                      linarith only [h0, hlam, p1343_0]
                                    · have p1343_0 := h1343c.1
                                      have p1343_1 := h1343c.2.1
                                      have p1343_2 := h1343c.2.2.1
                                      have p1343_3 := h1343c.2.2.2
                                      linarith only [hlam, p1343_0]
                                    · have p1343_0 := h1343c.1
                                      have p1343_1 := h1343c.2.1
                                      have p1343_2 := h1343c.2.2.1
                                      have p1343_3 := h1343c.2.2.2
                                      linarith only [h1331, hlam, p1343_0]
                                    · have p1343_0 := h1343c.1
                                      have p1343_1 := h1343c.2.1
                                      have p1343_2 := h1343c.2.2.1
                                      have p1343_3 := h1343c.2.2.2
                                      linarith only [h1333, hlam, p1343_0]
                                    · have p1343_0 := h1343c.1
                                      have p1343_1 := h1343c.2.1
                                      have p1343_2 := h1343c.2.2.1
                                      have p1343_3 := h1343c.2.2.2
                                      linarith only [h0, h1230, h1331, h1336, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1343_1]
                                    · have p1343_0 := h1343c.1
                                      have p1343_1 := h1343c.2.1
                                      have p1343_2 := h1343c.2.2.1
                                      have p1343_3 := h1343c.2.2.2
                                      linarith only [h0, h1331, hc12, hc23, hlam, hphi, p1343_1]
                                    · have p1343_0 := h1343c.1
                                      have p1343_1 := h1343c.2.1
                                      have p1343_2 := h1343c.2.2.1
                                      have p1343_3 := h1343c.2.2.2
                                      rcases p1343_3 (m.d 0 1) (by simp) with h1359 | h1359
                                      · linarith only [h1, h1359, hlam]
                                      · linarith only [h0, h1359, hlam]
                                    · have p1343_0 := h1343c.1
                                      have p1343_1 := h1343c.2.1
                                      have p1343_2 := h1343c.2.2.1
                                      have p1343_3 := h1343c.2.2.2
                                      linarith only [hlam, p1343_0]
                                    · have p1343_0 := h1343c.1
                                      have p1343_1 := h1343c.2.1
                                      have p1343_2 := h1343c.2.2.1
                                      have p1343_3 := h1343c.2.2.2
                                      linarith only [h0, h1230, h1331, h1335, h1340, h1342, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1343_1]
                                    · have p1343_0 := h1343c.1
                                      have p1343_1 := h1343c.2.1
                                      have p1343_2 := h1343c.2.2.1
                                      have p1343_3 := h1343c.2.2.2
                                      rcases p1343_3 (m.d 0 1) (by simp) with h1364 | h1364
                                      · linarith only [h1, h1364, hlam]
                                      · linarith only [h1323, h1364, hlam]
                                    · have p1343_0 := h1343c.1
                                      have p1343_1 := h1343c.2.1
                                      have p1343_2 := h1343c.2.2.1
                                      have p1343_3 := h1343c.2.2.2
                                      linarith only [h0, h1335, h1336, h1340, h1342, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1343_1]
                                    · have p1343_0 := h1343c.1
                                      have p1343_1 := h1343c.2.1
                                      have p1343_2 := h1343c.2.2.1
                                      have p1343_3 := h1343c.2.2.2
                                      rcases p1343_3 (m.d 0 1) (by simp) with h1368 | h1368
                                      · linarith only [h1230, h1368, hlam]
                                      · linarith only [h0, h1368, hlam]
                                    · have p1343_0 := h1343c.1
                                      have p1343_1 := h1343c.2.1
                                      have p1343_2 := h1343c.2.2.1
                                      have p1343_3 := h1343c.2.2.2
                                      linarith only [h1336, hlam, p1343_0]
                                    · have p1343_0 := h1343c.1
                                      have p1343_1 := h1343c.2.1
                                      have p1343_2 := h1343c.2.2.1
                                      have p1343_3 := h1343c.2.2.2
                                      linarith only [hlam, p1343_0]
                                    · have p1343_0 := h1343c.1
                                      have p1343_1 := h1343c.2.1
                                      have p1343_2 := h1343c.2.2.1
                                      have p1343_3 := h1343c.2.2.2
                                      rcases p1343_3 (m.d 0 1) (by simp) with h1373 | h1373
                                      · linarith only [h1230, h1373, hlam]
                                      · linarith only [h1323, h1373, hlam]
                                    · have p1343_0 := h1343c.1
                                      have p1343_1 := h1343c.2.1
                                      have p1343_2 := h1343c.2.2.1
                                      have p1343_3 := h1343c.2.2.2
                                      linarith only [h1323, hlam, p1343_0]
                                    · have p1343_0 := h1343c.1
                                      have p1343_1 := h1343c.2.1
                                      have p1343_2 := h1343c.2.2.1
                                      have p1343_3 := h1343c.2.2.2
                                      linarith only [h1335, hlam, p1343_1]
                                    · have p1343_0 := h1343c.1
                                      have p1343_1 := h1343c.2.1
                                      have p1343_2 := h1343c.2.2.1
                                      have p1343_3 := h1343c.2.2.2
                                      linarith only [h1337, hlam, p1343_0]
                                    · have p1343_0 := h1343c.1
                                      have p1343_1 := h1343c.2.1
                                      have p1343_2 := h1343c.2.2.1
                                      have p1343_3 := h1343c.2.2.2
                                      linarith only [h1338, hlam, p1343_0]
                                    · have p1343_0 := h1343c.1
                                      have p1343_1 := h1343c.2.1
                                      have p1343_2 := h1343c.2.2.1
                                      have p1343_3 := h1343c.2.2.2
                                      linarith only [hlam, p1343_0]
                                  · linarith only [h1342, hc34, hlam, hphi, ht45, u5elo4]
                                · linarith only [h1338, h1341, hc24, hlam, hphi, ht45, u5elo1]
                              · linarith only [h0, h1230, h1331, h1336, h1340, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h1230, h1331, h1335, h1336, h1339, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h0, h1230, h1335, h1338, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                        · linarith only [h0, h1230, h1335, h1336, h1337, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h0, h1, h1329, h1335, h1336, hc03, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h1335, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h1330, hc03, hlam, hphi, ht34, ht45, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1390 | h1390
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1391 | h1391
                · linarith only [h0, h1, h1329, h1391, hc23, hc34, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1393 | h1393
                  · linarith only [h0, h1, h1326, h1329, h1393, hc02, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1395 | h1395
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1396 | h1396
                      · linarith only [h0, h1, h1329, h1391, h1395, h1396, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h1, h1395, h1396, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h1395, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h1, h1390, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
          · linarith only [h1328, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
    · linarith only [h0, h1323, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]

set_option maxHeartbeats 5346000 in
set_option maxHeartbeats 5346000 in
theorem r1l7_11_13_25_L_I_L_I_H_L_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_11_13_25_L_I_L_I_H_L_x0_x0 m hb1 hb3 hb5 h0 h1
  · exact r1l7_11_13_25_L_I_L_I_H_L_x0_x1 m hb1 hb3 hb5 h0 h1

set_option maxHeartbeats 5346000 in
set_option maxHeartbeats 5346000 in
theorem r1l7_11_13_25_L_I_L_I_H_L_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1403 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1404 | h1404
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1405 | h1405
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1406 | h1406
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1407 | h1407
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1408 | h1408
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1409 | h1409
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1410 | h1410
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1411 | h1411
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1412 | h1412
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1413 | h1413
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1414 | h1414
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1415 | h1415
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1416 | h1416
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1417 | h1417
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1418 | h1418
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1419 | h1419
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1420 | h1420
                                  · linarith only [h0, h1403, h1411, h1417, h1420, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                  · linarith only [h1420, hc34, hlam, hphi, ht45, u5elo4]
                                · linarith only [h0, h1403, h1414, h1416, h1419, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h1418, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h0, h1403, h1414, h1417, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h1416, hc14, hlam, hphi, ht45, u5elo4]
                        · linarith only [h1415, hc13, hlam, hphi, ht34, ht45, u5elo3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1428 | h1428
                        · linarith only [h0, h1403, h1409, h1414, h1428, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h1428, hc13, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h0, h1413, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h1405, h1407, h1412, hc02, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h1406, h1411, hlam]
              · linarith only [h1410, hc03, hlam, hphi, ht34, ht45, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1435 | h1435
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1436 | h1436
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1437 | h1437
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1438 | h1438
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1439 | h1439
                      · linarith only [h1403, h1409, h1435, h1439, hc01, hc35, hlam, hphi, ht0b, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1441 | h1441
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1442 | h1442
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1443 | h1443
                            · linarith only [h1403, h1406, h1409, h1441, h1443, hc02, hc35, hlam, hphi, ht0b, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1445 | h1445
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1446 | h1446
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1447 | h1447
                                  · rcases h1bigk with h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c | h1448c
                                    · have p1448_0 := h1448c.1
                                      have p1448_1 := h1448c.2.1
                                      have p1448_2 := h1448c.2.2.1
                                      have p1448_3 := h1448c.2.2.2
                                      linarith only [hlam, p1448_0]
                                    · have p1448_0 := h1448c.1
                                      have p1448_1 := h1448c.2.1
                                      have p1448_2 := h1448c.2.2.1
                                      have p1448_3 := h1448c.2.2.2
                                      linarith only [h0, hlam, p1448_0]
                                    · have p1448_0 := h1448c.1
                                      have p1448_1 := h1448c.2.1
                                      have p1448_2 := h1448c.2.2.1
                                      have p1448_3 := h1448c.2.2.2
                                      linarith only [h0, h1436, h1445, h1447, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1448_1]
                                    · have p1448_0 := h1448c.1
                                      have p1448_1 := h1448c.2.1
                                      have p1448_2 := h1448c.2.2.1
                                      have p1448_3 := h1448c.2.2.2
                                      linarith only [h0, h1436, h1439, h1445, h1447, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1448_1]
                                    · have p1448_0 := h1448c.1
                                      have p1448_1 := h1448c.2.1
                                      have p1448_2 := h1448c.2.2.1
                                      have p1448_3 := h1448c.2.2.2
                                      rcases p1448_3 (m.d 0 1) (by simp) with h1453 | h1453
                                      · rcases p1448_3 (m.d 1 2) (by simp) with h1454 | h1454
                                        · rcases p1448_3 (m.d 1 3) (by simp) with h1455 | h1455
                                          · linarith only [h1403, h1455, hlam]
                                          · linarith only [h1441, h1455, hlam]
                                        · linarith only [h1438, h1454, hlam]
                                      · linarith only [h1453, hlam, p1448_0]
                                    · have p1448_0 := h1448c.1
                                      have p1448_1 := h1448c.2.1
                                      have p1448_2 := h1448c.2.2.1
                                      have p1448_3 := h1448c.2.2.2
                                      linarith only [h1403, h1436, h1445, h1447, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1448_1]
                                    · have p1448_0 := h1448c.1
                                      have p1448_1 := h1448c.2.1
                                      have p1448_2 := h1448c.2.2.1
                                      have p1448_3 := h1448c.2.2.2
                                      linarith only [hlam, p1448_0]
                                    · have p1448_0 := h1448c.1
                                      have p1448_1 := h1448c.2.1
                                      have p1448_2 := h1448c.2.2.1
                                      have p1448_3 := h1448c.2.2.2
                                      rcases p1448_3 (m.d 0 1) (by simp) with h1462 | h1462
                                      · linarith only [h0, h1462, hlam]
                                      · linarith only [h1403, h1462, hlam]
                                    · have p1448_0 := h1448c.1
                                      have p1448_1 := h1448c.2.1
                                      have p1448_2 := h1448c.2.2.1
                                      have p1448_3 := h1448c.2.2.2
                                      rcases p1448_3 (m.d 0 1) (by simp) with h1465 | h1465
                                      · linarith only [h0, h1465, hlam]
                                      · linarith only [h1404, h1465, hlam]
                                    · have p1448_0 := h1448c.1
                                      have p1448_1 := h1448c.2.1
                                      have p1448_2 := h1448c.2.2.1
                                      have p1448_3 := h1448c.2.2.2
                                      rcases p1448_3 (m.d 0 1) (by simp) with h1468 | h1468
                                      · linarith only [h0, h1468, hlam]
                                      · linarith only [h1405, h1468, hlam]
                                    · have p1448_0 := h1448c.1
                                      have p1448_1 := h1448c.2.1
                                      have p1448_2 := h1448c.2.2.1
                                      have p1448_3 := h1448c.2.2.2
                                      linarith only [h1403, hlam, p1448_0]
                                    · have p1448_0 := h1448c.1
                                      have p1448_1 := h1448c.2.1
                                      have p1448_2 := h1448c.2.2.1
                                      have p1448_3 := h1448c.2.2.2
                                      linarith only [h1436, hlam, p1448_1]
                                    · have p1448_0 := h1448c.1
                                      have p1448_1 := h1448c.2.1
                                      have p1448_2 := h1448c.2.2.1
                                      have p1448_3 := h1448c.2.2.2
                                      linarith only [hlam, p1448_0]
                                    · have p1448_0 := h1448c.1
                                      have p1448_1 := h1448c.2.1
                                      have p1448_2 := h1448c.2.2.1
                                      have p1448_3 := h1448c.2.2.2
                                      linarith only [h1439, hlam, p1448_1]
                                    · have p1448_0 := h1448c.1
                                      have p1448_1 := h1448c.2.1
                                      have p1448_2 := h1448c.2.2.1
                                      have p1448_3 := h1448c.2.2.2
                                      linarith only [h0, h1404, h1439, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p1448_1]
                                    · have p1448_0 := h1448c.1
                                      have p1448_1 := h1448c.2.1
                                      have p1448_2 := h1448c.2.2.1
                                      have p1448_3 := h1448c.2.2.2
                                      linarith only [h1404, hlam, p1448_0]
                                    · have p1448_0 := h1448c.1
                                      have p1448_1 := h1448c.2.1
                                      have p1448_2 := h1448c.2.2.1
                                      have p1448_3 := h1448c.2.2.2
                                      linarith only [h1437, hlam, p1448_1]
                                    · have p1448_0 := h1448c.1
                                      have p1448_1 := h1448c.2.1
                                      have p1448_2 := h1448c.2.2.1
                                      have p1448_3 := h1448c.2.2.2
                                      linarith only [h0, h1404, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1448_1]
                                    · have p1448_0 := h1448c.1
                                      have p1448_1 := h1448c.2.1
                                      have p1448_2 := h1448c.2.2.1
                                      have p1448_3 := h1448c.2.2.2
                                      linarith only [hlam, p1448_0]
                                    · have p1448_0 := h1448c.1
                                      have p1448_1 := h1448c.2.1
                                      have p1448_2 := h1448c.2.2.1
                                      have p1448_3 := h1448c.2.2.2
                                      linarith only [h0, h1404, h1438, h1445, h1447, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1448_1]
                                    · have p1448_0 := h1448c.1
                                      have p1448_1 := h1448c.2.1
                                      have p1448_2 := h1448c.2.2.1
                                      have p1448_3 := h1448c.2.2.2
                                      linarith only [h1405, hlam, p1448_0]
                                    · have p1448_0 := h1448c.1
                                      have p1448_1 := h1448c.2.1
                                      have p1448_2 := h1448c.2.2.1
                                      have p1448_3 := h1448c.2.2.2
                                      linarith only [h1438, hlam, p1448_1]
                                    · have p1448_0 := h1448c.1
                                      have p1448_1 := h1448c.2.1
                                      have p1448_2 := h1448c.2.2.1
                                      have p1448_3 := h1448c.2.2.2
                                      linarith only [h1441, hlam, p1448_0]
                                    · have p1448_0 := h1448c.1
                                      have p1448_1 := h1448c.2.1
                                      have p1448_2 := h1448c.2.2.1
                                      have p1448_3 := h1448c.2.2.2
                                      linarith only [h1442, hlam, p1448_0]
                                    · have p1448_0 := h1448c.1
                                      have p1448_1 := h1448c.2.1
                                      have p1448_2 := h1448c.2.2.1
                                      have p1448_3 := h1448c.2.2.2
                                      linarith only [hlam, p1448_0]
                                  · linarith only [h1403, h1409, h1436, h1445, h1447, hc35, hlam, hphi, u5elo4]
                                · linarith only [h1442, h1446, hc24, hlam, hphi, ht45, u5elo1]
                              · linarith only [h1445, hc23, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h1439, h1442, hc13, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h1436, h1441, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h0, h1438, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h1404, h1407, h1437, hlam]
                · linarith only [h0, h1406, h1436, hlam]
              · linarith only [h1435, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · linarith only [h1408, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h0, h1404, h1407, hlam]
      · linarith only [h0, h1403, h1406, hlam]
    · linarith only [h1405, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1499 | h1499
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1500 | h1500
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1501 | h1501
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1502 | h1502
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1503 | h1503
            · linarith only [h1403, h1404, h1503, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1505 | h1505
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1506 | h1506
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1507 | h1507
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1508 | h1508
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1509 | h1509
                      · linarith only [h1403, h1404, h1503, h1509, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1511 | h1511
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1512 | h1512
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1513 | h1513
                            · linarith only [h1403, h1404, h1509, h1511, h1513, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1515 | h1515
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1516 | h1516
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1517 | h1517
                                  · rcases h1bigk with h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c
                                    · have p1518_0 := h1518c.1
                                      have p1518_1 := h1518c.2.1
                                      have p1518_2 := h1518c.2.2.1
                                      have p1518_3 := h1518c.2.2.2
                                      linarith only [hlam, p1518_0]
                                    · have p1518_0 := h1518c.1
                                      have p1518_1 := h1518c.2.1
                                      have p1518_2 := h1518c.2.2.1
                                      have p1518_3 := h1518c.2.2.2
                                      linarith only [h0, hlam, p1518_0]
                                    · have p1518_0 := h1518c.1
                                      have p1518_1 := h1518c.2.1
                                      have p1518_2 := h1518c.2.2.1
                                      have p1518_3 := h1518c.2.2.2
                                      linarith only [h1404, h1506, h1507, h1515, h1517, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1518_1]
                                    · have p1518_0 := h1518c.1
                                      have p1518_1 := h1518c.2.1
                                      have p1518_2 := h1518c.2.2.1
                                      have p1518_3 := h1518c.2.2.2
                                      linarith only [h1404, hlam, p1518_0]
                                    · have p1518_0 := h1518c.1
                                      have p1518_1 := h1518c.2.1
                                      have p1518_2 := h1518c.2.2.1
                                      have p1518_3 := h1518c.2.2.2
                                      rcases p1518_3 (m.d 0 1) (by simp) with h1523 | h1523
                                      · rcases p1518_3 (m.d 1 2) (by simp) with h1524 | h1524
                                        · rcases p1518_3 (m.d 1 3) (by simp) with h1525 | h1525
                                          · linarith only [h1403, h1525, hlam]
                                          · linarith only [h1511, h1525, hlam]
                                        · linarith only [h1508, h1524, hlam]
                                      · linarith only [h1523, hlam, p1518_0]
                                    · have p1518_0 := h1518c.1
                                      have p1518_1 := h1518c.2.1
                                      have p1518_2 := h1518c.2.2.1
                                      have p1518_3 := h1518c.2.2.2
                                      linarith only [h1403, h1506, h1515, h1517, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1518_1]
                                    · have p1518_0 := h1518c.1
                                      have p1518_1 := h1518c.2.1
                                      have p1518_2 := h1518c.2.2.1
                                      have p1518_3 := h1518c.2.2.2
                                      linarith only [hlam, p1518_0]
                                    · have p1518_0 := h1518c.1
                                      have p1518_1 := h1518c.2.1
                                      have p1518_2 := h1518c.2.2.1
                                      have p1518_3 := h1518c.2.2.2
                                      rcases p1518_3 (m.d 0 1) (by simp) with h1532 | h1532
                                      · linarith only [h0, h1532, hlam]
                                      · linarith only [h1403, h1532, hlam]
                                    · have p1518_0 := h1518c.1
                                      have p1518_1 := h1518c.2.1
                                      have p1518_2 := h1518c.2.2.1
                                      have p1518_3 := h1518c.2.2.2
                                      linarith only [h1403, h1404, h1506, h1515, h1517, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1518_1]
                                    · have p1518_0 := h1518c.1
                                      have p1518_1 := h1518c.2.1
                                      have p1518_2 := h1518c.2.2.1
                                      have p1518_3 := h1518c.2.2.2
                                      rcases p1518_3 (m.d 0 1) (by simp) with h1536 | h1536
                                      · linarith only [h0, h1536, hlam]
                                      · linarith only [h1499, h1536, hlam]
                                    · have p1518_0 := h1518c.1
                                      have p1518_1 := h1518c.2.1
                                      have p1518_2 := h1518c.2.2.1
                                      have p1518_3 := h1518c.2.2.2
                                      linarith only [h1403, hlam, p1518_0]
                                    · have p1518_0 := h1518c.1
                                      have p1518_1 := h1518c.2.1
                                      have p1518_2 := h1518c.2.2.1
                                      have p1518_3 := h1518c.2.2.2
                                      linarith only [h1506, hlam, p1518_1]
                                    · have p1518_0 := h1518c.1
                                      have p1518_1 := h1518c.2.1
                                      have p1518_2 := h1518c.2.2.1
                                      have p1518_3 := h1518c.2.2.2
                                      linarith only [hlam, p1518_0]
                                    · have p1518_0 := h1518c.1
                                      have p1518_1 := h1518c.2.1
                                      have p1518_2 := h1518c.2.2.1
                                      have p1518_3 := h1518c.2.2.2
                                      linarith only [h1509, hlam, p1518_1]
                                    · have p1518_0 := h1518c.1
                                      have p1518_1 := h1518c.2.1
                                      have p1518_2 := h1518c.2.2.1
                                      have p1518_3 := h1518c.2.2.2
                                      linarith only [h1403, h1404, h1507, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p1518_1]
                                    · have p1518_0 := h1518c.1
                                      have p1518_1 := h1518c.2.1
                                      have p1518_2 := h1518c.2.2.1
                                      have p1518_3 := h1518c.2.2.2
                                      linarith only [h1403, h1506, h1507, h1515, h1517, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1518_1]
                                    · have p1518_0 := h1518c.1
                                      have p1518_1 := h1518c.2.1
                                      have p1518_2 := h1518c.2.2.1
                                      have p1518_3 := h1518c.2.2.2
                                      linarith only [h1507, hlam, p1518_1]
                                    · have p1518_0 := h1518c.1
                                      have p1518_1 := h1518c.2.1
                                      have p1518_2 := h1518c.2.2.1
                                      have p1518_3 := h1518c.2.2.2
                                      rcases p1518_3 (m.d 0 1) (by simp) with h1546 | h1546
                                      · linarith only [h1404, h1546, hlam]
                                      · linarith only [h1403, h1546, hlam]
                                    · have p1518_0 := h1518c.1
                                      have p1518_1 := h1518c.2.1
                                      have p1518_2 := h1518c.2.2.1
                                      have p1518_3 := h1518c.2.2.2
                                      linarith only [hlam, p1518_0]
                                    · have p1518_0 := h1518c.1
                                      have p1518_1 := h1518c.2.1
                                      have p1518_2 := h1518c.2.2.1
                                      have p1518_3 := h1518c.2.2.2
                                      rcases p1518_3 (m.d 0 1) (by simp) with h1550 | h1550
                                      · linarith only [h1404, h1550, hlam]
                                      · linarith only [h1499, h1550, hlam]
                                    · have p1518_0 := h1518c.1
                                      have p1518_1 := h1518c.2.1
                                      have p1518_2 := h1518c.2.2.1
                                      have p1518_3 := h1518c.2.2.2
                                      linarith only [h1499, hlam, p1518_0]
                                    · have p1518_0 := h1518c.1
                                      have p1518_1 := h1518c.2.1
                                      have p1518_2 := h1518c.2.2.1
                                      have p1518_3 := h1518c.2.2.2
                                      linarith only [h1508, hlam, p1518_1]
                                    · have p1518_0 := h1518c.1
                                      have p1518_1 := h1518c.2.1
                                      have p1518_2 := h1518c.2.2.1
                                      have p1518_3 := h1518c.2.2.2
                                      linarith only [h1511, hlam, p1518_0]
                                    · have p1518_0 := h1518c.1
                                      have p1518_1 := h1518c.2.1
                                      have p1518_2 := h1518c.2.2.1
                                      have p1518_3 := h1518c.2.2.2
                                      linarith only [h1512, hlam, p1518_0]
                                    · have p1518_0 := h1518c.1
                                      have p1518_1 := h1518c.2.1
                                      have p1518_2 := h1518c.2.2.1
                                      have p1518_3 := h1518c.2.2.2
                                      linarith only [hlam, p1518_0]
                                  · linarith only [h1517, hc34, hlam, hphi, ht45, u5elo4]
                                · linarith only [h1499, h1512, h1516, hc24, hlam, hphi, ht45, u5elo0]
                              · linarith only [h1515, hc23, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h1403, h1404, h1512, hc13, hc45, hlam, hphi, ht34]
                        · linarith only [h1506, h1511, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h1403, h1404, h1506, h1507, h1508, hc23, hlam, hphi, ht34, ht45, u5elo2]
                  · linarith only [h0, h1403, h1501, h1506, h1507, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h1500, h1506, hlam]
              · linarith only [h1505, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · linarith only [h1502, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1568 | h1568
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1569 | h1569
            · linarith only [h0, h1403, h1501, h1569, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1571 | h1571
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1572 | h1572
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1573 | h1573
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1574 | h1574
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1575 | h1575
                      · linarith only [h0, h1403, h1501, h1569, h1573, h1575, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1577 | h1577
                        · linarith only [h0, h1403, h1501, h1573, h1577, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h1577, hc13, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h0, h1501, h1573, h1574, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1581 | h1581
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1582 | h1582
                      · linarith only [h0, h1403, h1569, h1573, h1582, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1584 | h1584
                        · linarith only [h0, h1403, h1573, h1584, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h1572, h1584, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h0, h1403, h1572, h1581, hc23, hlam, hphi, ht34, ht45, u5elo2]
                · linarith only [h0, h1403, h1500, h1501, h1572, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h1571, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · linarith only [h1568, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
      · linarith only [h0, h1403, h1500, hlam]
    · linarith only [h1403, h1499, hc13, hlam, hphi, ht34, ht45, u5elo1]

set_option maxHeartbeats 5346000 in
set_option maxHeartbeats 5346000 in
theorem r1l7_11_13_25_L_I_L_I_H_L_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1403 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1593 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1594 | h1594
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1595 | h1595
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1596 | h1596
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1597 | h1597
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1598 | h1598
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1599 | h1599
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1600 | h1600
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1601 | h1601
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1602 | h1602
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1603 | h1603
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1604 | h1604
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1605 | h1605
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1606 | h1606
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1607 | h1607
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1608 | h1608
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1609 | h1609
                                · rcases h1bigk with h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [hlam, p1610_0]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [h0, hlam, p1610_0]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [h1403, hlam, p1610_0]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [h1403, h1601, h1606, h1609, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1610_1]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    rcases p1610_3 (m.d 0 1) (by simp) with h1615 | h1615
                                    · rcases p1610_3 (m.d 1 2) (by simp) with h1616 | h1616
                                      · rcases p1610_3 (m.d 1 3) (by simp) with h1617 | h1617
                                        · rcases p1610_3 (m.d 1 4) (by simp) with h1618 | h1618
                                          · linarith only [h1593, h1618, hlam]
                                          · linarith only [h1605, h1618, hlam]
                                        · linarith only [h1604, h1617, hlam]
                                      · linarith only [h1602, h1616, hlam]
                                    · linarith only [h1615, hlam, p1610_0]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [h1593, h1601, h1606, h1609, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1610_1]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [hlam, p1610_0]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [h1403, hc01, hc12, hlam, hphi, p1610_1]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    rcases p1610_3 (m.d 0 1) (by simp) with h1627 | h1627
                                    · linarith only [h0, h1627, hlam]
                                    · linarith only [h1593, h1627, hlam]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    rcases p1610_3 (m.d 0 1) (by simp) with h1630 | h1630
                                    · linarith only [h0, h1630, hlam]
                                    · linarith only [h1594, h1630, hlam]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [h1593, h1600, h1601, h1606, h1609, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1610_1]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [h1600, hlam, p1610_1]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [hlam, p1610_0]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    rcases p1610_3 (m.d 0 1) (by simp) with h1636 | h1636
                                    · linarith only [h1403, h1636, hlam]
                                    · linarith only [h1593, h1636, hlam]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    rcases p1610_3 (m.d 0 1) (by simp) with h1639 | h1639
                                    · linarith only [h1403, h1639, hlam]
                                    · linarith only [h1594, h1639, hlam]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [h1593, hlam, p1610_0]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [h1601, hlam, p1610_1]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [h1603, hlam, p1610_0]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [hlam, p1610_0]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [h0, h1593, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p1610_1]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [h1594, hlam, p1610_0]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [h1602, hlam, p1610_1]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [h1604, hlam, p1610_0]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [h1605, hlam, p1610_0]
                                  · have p1610_0 := h1610c.1
                                    have p1610_1 := h1610c.2.1
                                    have p1610_2 := h1610c.2.2.1
                                    have p1610_3 := h1610c.2.2.2
                                    linarith only [hlam, p1610_0]
                                · linarith only [h1609, hc34, hlam, hphi, ht45, u5elo4]
                              · linarith only [h1605, h1608, hc24, hlam, hphi, ht45, u5elo1]
                            · linarith only [h1607, hc23, hlam, hphi, ht34, ht45, u5elo3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1655 | h1655
                            · linarith only [h1403, h1593, h1600, h1603, h1606, h1655, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h1655, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h1605, hc14, hlam, hphi, ht45, u5elo4]
                      · linarith only [h1403, h1604, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                    · linarith only [h1403, h1594, h1595, h1598, h1603, hc02, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h1403, h1600, h1602, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                · linarith only [h0, h1596, h1601, hlam]
              · linarith only [h0, h1595, h1600, hlam]
            · linarith only [h1599, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · linarith only [h1403, h1593, h1598, hlam]
        · linarith only [h1597, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
      · linarith only [h1403, h1593, h1595, h1596, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1668 | h1668
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1669 | h1669
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1670 | h1670
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1671 | h1671
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1672 | h1672
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1673 | h1673
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1674 | h1674
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1675 | h1675
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1676 | h1676
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1677 | h1677
                        · linarith only [h0, h1593, h1595, h1672, h1677, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h1677, hc14, hlam, hphi, ht45, u5elo4]
                      · linarith only [h0, h1593, h1595, h1672, h1673, h1676, hc24, hlam, hphi, ht45, u5elo3]
                    · linarith only [h1403, h1670, h1675, hlam]
                  · linarith only [h0, h1595, h1672, h1674, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h1595, h1672, h1673, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1684 | h1684
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1685 | h1685
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1686 | h1686
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1687 | h1687
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1688 | h1688
                        · linarith only [h0, h1593, h1672, h1688, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h1688, hc14, hlam, hphi, ht45, u5elo4]
                      · linarith only [h1403, h1687, hc03, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h1403, h1670, h1686, hlam]
                  · linarith only [h0, h1685, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                · linarith only [h0, h1668, h1684, hlam]
            · linarith only [h1671, hc03, hlam, hphi, ht34, ht45, u5elo3]
          · linarith only [h0, h1593, h1595, h1670, hlam]
        · linarith only [h1669, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
      · linarith only [h0, h1593, h1668, hlam]
  · linarith only [h1593, h1594, hc14, hlam, hphi, ht45, u5elo1]

end R2N4
