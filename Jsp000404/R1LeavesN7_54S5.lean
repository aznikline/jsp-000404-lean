import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4588000 in
set_option maxHeartbeats 4588000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_R_L_I_x1_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h868 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1079 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1211 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1293 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h1294 | h1294
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1295 | h1295
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1296 | h1296
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1297 | h1297
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1298 | h1298
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1299 | h1299
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1300 | h1300
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1301 | h1301
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1302 | h1302
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1303 | h1303
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1304 | h1304
                      · linarith only [h1293, h1304, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                      · linarith only [h1296, h1304, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                    · linarith only [h1079, h1293, h1296, h1298, h1303, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h1297, h1302, h868, hlam]
                · linarith only [h1296, h1301, h868, hlam]
              · linarith only [h0, h1295, h1300, hlam]
            · linarith only [h0, h1293, h1299, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1312 | h1312
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1313 | h1313
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1314 | h1314
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1315 | h1315
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1316 | h1316
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1317 | h1317
                      · linarith only [h1293, h1317, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                      · linarith only [h1296, h1317, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1320 | h1320
                      · linarith only [h1293, h1320, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                      · linarith only [h1079, h1296, h1316, h1320, hc45, hlam, hphi, ht34, u3ehi2]
                  · linarith only [h1296, h1315, h868, hc35, hlam, hphi, u3ehi3]
                · linarith only [h1296, h1314, h868, hlam]
              · linarith only [h0, h1295, h1313, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h1293, h1312, hlam]
        · linarith only [h1296, h1297, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1328 | h1328
        · linarith only [h1296, h1328, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1330 | h1330
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1331 | h1331
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1332 | h1332
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1333 | h1333
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1334 | h1334
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1335 | h1335
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1336 | h1336
                      · linarith only [h1293, h1296, h1336, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1338 | h1338
                        · linarith only [h1293, h1338, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
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
                                linarith only [h868, hlam, p1342_0]
                              · have p1342_0 := h1342c.1
                                have p1342_1 := h1342c.2.1
                                have p1342_2 := h1342c.2.2.1
                                have p1342_3 := h1342c.2.2.2
                                linarith only [h1079, hlam, p1342_1]
                              · have p1342_0 := h1342c.1
                                have p1342_1 := h1342c.2.1
                                have p1342_2 := h1342c.2.2.1
                                have p1342_3 := h1342c.2.2.2
                                linarith only [h1211, hlam, p1342_1]
                              · have p1342_0 := h1342c.1
                                have p1342_1 := h1342c.2.1
                                have p1342_2 := h1342c.2.2.1
                                have p1342_3 := h1342c.2.2.2
                                rcases p1342_3 (m.d 0 1) (by simp) with h1348 | h1348
                                · linarith only [h0, h1348, hlam]
                                · rcases p1342_3 (m.d 0 2) (by simp) with h1350 | h1350
                                  · rcases p1342_3 (m.d 0 3) (by simp) with h1351 | h1351
                                    · linarith only [h1293, h1351, hlam]
                                    · linarith only [h1351, h868, hlam]
                                  · linarith only [h0, h1350, hlam]
                              · have p1342_0 := h1342c.1
                                have p1342_1 := h1342c.2.1
                                have p1342_2 := h1342c.2.2.1
                                have p1342_3 := h1342c.2.2.2
                                linarith only [hlam, p1342_0]
                              · have p1342_0 := h1342c.1
                                have p1342_1 := h1342c.2.1
                                have p1342_2 := h1342c.2.2.1
                                have p1342_3 := h1342c.2.2.2
                                linarith only [h1293, hlam, hphi, ht0b, ht34, ht45, ht5b, p1342_1, u0elo1, u3ehi2]
                              · have p1342_0 := h1342c.1
                                have p1342_1 := h1342c.2.1
                                have p1342_2 := h1342c.2.2.1
                                have p1342_3 := h1342c.2.2.2
                                linarith only [h1294, h1340, hc45, hlam, hphi, ht0b, ht5b, p1342_1, u0elo1]
                              · have p1342_0 := h1342c.1
                                have p1342_1 := h1342c.2.1
                                have p1342_2 := h1342c.2.2.1
                                have p1342_3 := h1342c.2.2.2
                                linarith only [h1293, h1328, hlam, hphi, ht0b, ht34, ht45, ht5b, p1342_1, u0elo1, u3ehi2]
                              · have p1342_0 := h1342c.1
                                have p1342_1 := h1342c.2.1
                                have p1342_2 := h1342c.2.2.1
                                have p1342_3 := h1342c.2.2.2
                                linarith only [h1328, hc01, hc35, hlam, hphi, ht12, ht23, p1342_1]
                              · have p1342_0 := h1342c.1
                                have p1342_1 := h1342c.2.1
                                have p1342_2 := h1342c.2.2.1
                                have p1342_3 := h1342c.2.2.2
                                linarith only [h1293, hlam, p1342_1]
                              · have p1342_0 := h1342c.1
                                have p1342_1 := h1342c.2.1
                                have p1342_2 := h1342c.2.2.1
                                have p1342_3 := h1342c.2.2.2
                                linarith only [hlam, p1342_0]
                              · have p1342_0 := h1342c.1
                                have p1342_1 := h1342c.2.1
                                have p1342_2 := h1342c.2.2.1
                                have p1342_3 := h1342c.2.2.2
                                linarith only [h1296, hlam, p1342_1]
                              · have p1342_0 := h1342c.1
                                have p1342_1 := h1342c.2.1
                                have p1342_2 := h1342c.2.2.1
                                have p1342_3 := h1342c.2.2.2
                                linarith only [h1328, hlam, p1342_1]
                              · have p1342_0 := h1342c.1
                                have p1342_1 := h1342c.2.1
                                have p1342_2 := h1342c.2.2.1
                                have p1342_3 := h1342c.2.2.2
                                linarith only [h1296, h1331, h1333, hc01, hc12, hlam, hphi, p1342_1]
                              · have p1342_0 := h1342c.1
                                have p1342_1 := h1342c.2.1
                                have p1342_2 := h1342c.2.2.1
                                have p1342_3 := h1342c.2.2.2
                                linarith only [h1294, hlam, p1342_0]
                              · have p1342_0 := h1342c.1
                                have p1342_1 := h1342c.2.1
                                have p1342_2 := h1342c.2.2.1
                                have p1342_3 := h1342c.2.2.2
                                linarith only [h1293, h1296, h1331, h1333, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1342_1, u3ehi2]
                              · have p1342_0 := h1342c.1
                                have p1342_1 := h1342c.2.1
                                have p1342_2 := h1342c.2.2.1
                                have p1342_3 := h1342c.2.2.2
                                linarith only [hlam, p1342_0]
                              · have p1342_0 := h1342c.1
                                have p1342_1 := h1342c.2.1
                                have p1342_2 := h1342c.2.2.1
                                have p1342_3 := h1342c.2.2.2
                                linarith only [h1293, h1296, h1328, h1331, h1333, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1342_1, u3ehi2]
                              · have p1342_0 := h1342c.1
                                have p1342_1 := h1342c.2.1
                                have p1342_2 := h1342c.2.2.1
                                have p1342_3 := h1342c.2.2.2
                                linarith only [h1296, h1330, h1331, h1333, hc01, hc12, hlam, hphi, p1342_1]
                              · have p1342_0 := h1342c.1
                                have p1342_1 := h1342c.2.1
                                have p1342_2 := h1342c.2.2.1
                                have p1342_3 := h1342c.2.2.2
                                linarith only [h1295, hlam, p1342_1]
                              · have p1342_0 := h1342c.1
                                have p1342_1 := h1342c.2.1
                                have p1342_2 := h1342c.2.2.1
                                have p1342_3 := h1342c.2.2.2
                                linarith only [h1293, h1295, hlam, hphi, ht0b, ht34, ht45, ht5b, p1342_1, u0elo1, u3ehi2]
                              · have p1342_0 := h1342c.1
                                have p1342_1 := h1342c.2.1
                                have p1342_2 := h1342c.2.2.1
                                have p1342_3 := h1342c.2.2.2
                                linarith only [h1330, hlam, p1342_1]
                              · have p1342_0 := h1342c.1
                                have p1342_1 := h1342c.2.1
                                have p1342_2 := h1342c.2.2.1
                                have p1342_3 := h1342c.2.2.2
                                linarith only [hlam, p1342_0]
                            · linarith only [h1293, h1296, h1341, hc45, hlam, hphi, ht34, u3ehi2]
                          · linarith only [h1330, h1336, h1340, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi2]
                    · linarith only [h1079, h1296, h1330, h1331, h1333, h1335, hc01, hc12, hlam, hphi]
                  · linarith only [h1296, h1333, h1334, hc35, hlam, hphi, u3ehi0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1378 | h1378
                  · linarith only [h1333, h1378, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1380 | h1380
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1381 | h1381
                      · linarith only [h1293, h1333, h1381, h868, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1383 | h1383
                        · linarith only [h1293, h1333, h1383, h868, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1385 | h1385
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1386 | h1386
                            · rcases h0bigk with h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [hlam, p1387_0]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h0, hlam, p1387_1]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h868, hlam, p1387_0]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1079, hlam, p1387_1]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1211, hlam, p1387_1]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                rcases p1387_3 (m.d 0 1) (by simp) with h1393 | h1393
                                · linarith only [h0, h1393, hlam]
                                · rcases p1387_3 (m.d 0 2) (by simp) with h1395 | h1395
                                  · rcases p1387_3 (m.d 0 3) (by simp) with h1396 | h1396
                                    · linarith only [h1293, h1396, hlam]
                                    · linarith only [h1396, h868, hlam]
                                  · linarith only [h0, h1395, hlam]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [hlam, p1387_0]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht34, ht45, ht5b, p1387_1, u0elo1, u3ehi0]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1294, h1383, h1385, hlam, hphi, ht0b, ht34, ht45, ht5b, p1387_1, u0elo1, u3ehi2]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1295, h1383, hlam, hphi, ht0b, ht34, ht45, ht5b, p1387_1, u0elo1, u3ehi2]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1378, h1386, h868, hc01, hc34, hlam, hphi, ht12, ht23, p1387_1]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1293, hlam, p1387_1]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [hlam, p1387_0]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1296, hlam, p1387_1]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1328, hlam, p1387_1]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                rcases p1387_3 (m.d 0 1) (by simp) with h1409 | h1409
                                · linarith only [h1079, h1409, hlam]
                                · rcases p1387_3 (m.d 0 2) (by simp) with h1411 | h1411
                                  · rcases p1387_3 (m.d 0 3) (by simp) with h1412 | h1412
                                    · linarith only [h1296, h1412, hlam]
                                    · linarith only [h1412, h868, hlam]
                                  · linarith only [h0, h1411, hlam]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1294, hlam, p1387_0]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht34, ht45, ht5b, p1387_1, u0elo3, u3ehi0]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [hlam, p1387_0]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1294, h1295, h1383, hlam, hphi, ht0b, ht34, ht45, ht5b, p1387_1, u0elo1, u3ehi2]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                rcases p1387_3 (m.d 0 1) (by simp) with h1420 | h1420
                                · linarith only [h1211, h1420, hlam]
                                · rcases p1387_3 (m.d 0 2) (by simp) with h1422 | h1422
                                  · rcases p1387_3 (m.d 0 3) (by simp) with h1423 | h1423
                                    · linarith only [h1328, h1423, hlam]
                                    · linarith only [h1423, h868, hlam]
                                  · linarith only [h0, h1422, hlam]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1295, hlam, p1387_1]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1293, hlam, hphi, ht0b, ht34, ht45, ht5b, p1387_1, u0elo4, u3ehi2]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1330, hlam, p1387_1]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [hlam, p1387_0]
                            · linarith only [h1079, h1333, h1385, h1386, hc01, hc24, hlam, hphi, ht12]
                          · linarith only [h1294, h1330, h1381, h1385, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
                    · linarith only [h1079, h1330, h1380, hlam]
              · linarith only [h0, h1295, h1332, hlam]
            · linarith only [h0, h1293, h1331, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1436 | h1436
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1437 | h1437
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1438 | h1438
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1439 | h1439
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1440 | h1440
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1441 | h1441
                      · linarith only [h1293, h1296, h1441, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1443 | h1443
                        · linarith only [h1293, h1328, h1443, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1445 | h1445
                          · linarith only [h1294, h1330, h1445, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1447 | h1447
                            · linarith only [h1293, h1296, h1330, h1447, hc34, hlam, hphi, u3ehi2]
                            · linarith only [h1293, h1296, h1436, h1438, h1440, h1447, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h1293, h1296, h1438, h1440, hc45, hlam, hphi, ht34, u3ehi2]
                  · linarith only [h1293, h1296, h1438, h1439, hc35, hlam, hphi, u3ehi2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1452 | h1452
                  · linarith only [h1438, h1452, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1454 | h1454
                    · linarith only [h1293, h1296, h1330, h1438, h1454, hc34, hlam, hphi, u3ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1456 | h1456
                      · linarith only [h1293, h1438, h1454, h1456, h868, hc45, hlam, hphi, ht34, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1458 | h1458
                        · linarith only [h1293, h1438, h1454, h1458, h868, hc45, hlam, hphi, ht34, u3ehi4]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1460 | h1460
                          · linarith only [h1079, h1294, h1454, h1460, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1462 | h1462
                            · linarith only [h1438, h1454, h1462, h868, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h1296, h1462, hc45, hlam, hphi, ht34, u3ehi0]
              · linarith only [h0, h1295, h1437, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h1293, h1296, h1436, hc01, hc34, hlam, hphi, ht12, ht23]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1467 | h1467
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1468 | h1468
        · linarith only [h1293, h1295, h1468, hlam]
        · linarith only [h1467, h1468, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1471 | h1471
        · linarith only [h1467, h1471, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1473 | h1473
          · linarith only [h1294, h1295, h1473, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1475 | h1475
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1476 | h1476
              · linarith only [h1293, h1295, h1476, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1478 | h1478
                · linarith only [h1467, h1475, h1476, h1478, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1480 | h1480
                  · linarith only [h1293, h1295, h1471, h1478, h1480, hc34, hlam, hphi, u3ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1482 | h1482
                    · linarith only [h1293, h1467, h1473, h1478, h1482, hc34, hlam, hphi, u3ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1484 | h1484
                      · linarith only [h1293, h1484, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1486 | h1486
                        · linarith only [h0, h1294, h1476, h1484, h1486, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                        · linarith only [h0, h1294, h1476, h1484, h1486, hc35, hlam, hphi, u3ehi2]
            · linarith only [h0, h1293, h1475, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1490 | h1490
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1491 | h1491
      · linarith only [h1293, h1294, h1491, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1493 | h1493
        · linarith only [h1491, h1493, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1495 | h1495
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1496 | h1496
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1497 | h1497
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1498 | h1498
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1499 | h1499
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1500 | h1500
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1501 | h1501
                      · linarith only [h1293, h1491, h1501, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
                      · linarith only [h1293, h1294, h1496, h1498, h1501, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h1495, h1498, h1500, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi3]
                  · linarith only [h1498, h1499, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1506 | h1506
                  · linarith only [h1498, h1506, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1508 | h1508
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1509 | h1509
                      · linarith only [h1293, h1498, h1509, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                      · linarith only [h1293, h1294, h1509, hc34, hlam, hphi, u3ehi2]
                    · linarith only [h1079, h1293, h1294, h1495, h1508, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4, u3ehi2]
              · linarith only [h0, h1490, h1497, hlam]
            · linarith only [h0, h1293, h1496, hlam]
          · linarith only [h1293, h1294, h1495, hc45, hlam, hphi, ht34, u3ehi2]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1516 | h1516
      · linarith only [h1293, h1294, h1516, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1518 | h1518
        · linarith only [h1516, h1518, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1520 | h1520
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1521 | h1521
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1522 | h1522
              · linarith only [h1293, h1490, h1522, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1524 | h1524
                · linarith only [h1516, h1521, h1522, h1524, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1526 | h1526
                  · linarith only [h1293, h1490, h1518, h1524, h1526, hc34, hlam, hphi, u3ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1528 | h1528
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1529 | h1529
                      · linarith only [h1293, h1524, h1529, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                      · linarith only [h1293, h1294, h1529, hc34, hlam, hphi, u3ehi2]
                    · linarith only [h1079, h1520, h1528, hlam]
            · linarith only [h0, h1293, h1521, hlam]
          · linarith only [h1293, h1294, h1520, hc45, hlam, hphi, ht34, u3ehi2]

end R2N4
