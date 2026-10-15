import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4696000 in
set_option maxHeartbeats 4696000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_R_L_I_x1_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h869 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1088 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1242 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1334 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h1bigk := hb1.1
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h1335 | h1335
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1336 | h1336
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1337 | h1337
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1338 | h1338
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1339 | h1339
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1340 | h1340
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1341 | h1341
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1342 | h1342
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1343 | h1343
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1344 | h1344
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1345 | h1345
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1346 | h1346
                        · linarith only [h1334, h1346, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                        · linarith only [h1334, h1337, h1346, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
                      · linarith only [h1088, h1334, h1337, h1339, h1345, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h1338, h1344, h869, hlam]
                  · linarith only [h1337, h1343, h869, hlam]
                · linarith only [h0, h1336, h1342, hlam]
              · linarith only [h0, h1335, h1341, hlam]
            · linarith only [h0, h1334, h1340, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1355 | h1355
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1356 | h1356
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1357 | h1357
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1358 | h1358
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1359 | h1359
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1360 | h1360
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1361 | h1361
                        · linarith only [h1334, h1361, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                        · linarith only [h1337, h1339, h1355, h1358, h1360, h1361, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1364 | h1364
                        · linarith only [h1334, h1364, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                        · linarith only [h1334, h1337, h1364, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
                    · linarith only [h1334, h1338, h1359, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                  · linarith only [h1337, h1338, h1358, h869, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi4]
                · linarith only [h0, h1336, h1357, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h1335, h1356, hlam]
            · linarith only [h0, h1334, h1355, hlam]
        · linarith only [h1337, h1338, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1373 | h1373
        · linarith only [h1337, h1373, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1375 | h1375
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1376 | h1376
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1377 | h1377
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1378 | h1378
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1379 | h1379
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1380 | h1380
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1381 | h1381
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1382 | h1382
                        · linarith only [h1334, h1337, h1382, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1384 | h1384
                          · linarith only [h1334, h1373, h1384, hlam]
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
                                linarith only [h869, hlam, p1387_0]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1088, hlam, p1387_1]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1242, hlam, p1387_1]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                rcases p1387_3 (m.d 0 1) (by simp) with h1393 | h1393
                                · linarith only [h0, h1393, hlam]
                                · rcases p1387_3 (m.d 0 2) (by simp) with h1395 | h1395
                                  · rcases p1387_3 (m.d 0 3) (by simp) with h1396 | h1396
                                    · linarith only [h1334, h1396, hlam]
                                    · linarith only [h1396, h869, hlam]
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
                                linarith only [h1375, hc45, hlam, hphi, ht0b, ht5b, p1387_1, u0elo1]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1334, h1373, hlam, hphi, ht0b, ht34, ht45, ht5b, p1387_1, u0elo1, u3ehi2]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1337, h1376, h1379, hc01, hc12, hlam, hphi, p1387_1]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1334, hlam, p1387_1]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [hlam, p1387_0]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1337, hlam, p1387_1]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1373, hlam, p1387_1]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1337, h1376, h1379, hc01, hc12, hlam, hphi, p1387_1]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1335, hlam, p1387_0]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1337, h1376, h1379, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1387_1, u3ehi0]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [hlam, p1387_0]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1334, h1337, h1373, h1376, h1379, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1387_1, u3ehi2]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1373, h1376, h1379, h1386, hc01, hc12, hlam, hphi, p1387_1]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1336, hlam, p1387_1]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1334, h1373, h1376, h1379, h1386, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1387_1, u3ehi2]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [h1375, hlam, p1387_1]
                              · have p1387_0 := h1387c.1
                                have p1387_1 := h1387c.2.1
                                have p1387_2 := h1387c.2.2.1
                                have p1387_3 := h1387c.2.2.2
                                linarith only [hlam, p1387_0]
                            · linarith only [h1334, h1337, h1386, hc45, hlam, hphi, ht34, u3ehi2]
                      · linarith only [h1337, h1375, h1379, h1381, hlam]
                    · linarith only [h1379, h1380, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1422 | h1422
                    · linarith only [h1379, h1422, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1424 | h1424
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1425 | h1425
                        · linarith only [h1334, h1379, h1425, h869, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1427 | h1427
                          · linarith only [h1242, h1334, h1422, h1427, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1429 | h1429
                            · rcases h0bigk with h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c
                              · have p1430_0 := h1430c.1
                                have p1430_1 := h1430c.2.1
                                have p1430_2 := h1430c.2.2.1
                                have p1430_3 := h1430c.2.2.2
                                linarith only [hlam, p1430_0]
                              · have p1430_0 := h1430c.1
                                have p1430_1 := h1430c.2.1
                                have p1430_2 := h1430c.2.2.1
                                have p1430_3 := h1430c.2.2.2
                                linarith only [h0, hlam, p1430_1]
                              · have p1430_0 := h1430c.1
                                have p1430_1 := h1430c.2.1
                                have p1430_2 := h1430c.2.2.1
                                have p1430_3 := h1430c.2.2.2
                                linarith only [h869, hlam, p1430_0]
                              · have p1430_0 := h1430c.1
                                have p1430_1 := h1430c.2.1
                                have p1430_2 := h1430c.2.2.1
                                have p1430_3 := h1430c.2.2.2
                                linarith only [h1088, hlam, p1430_1]
                              · have p1430_0 := h1430c.1
                                have p1430_1 := h1430c.2.1
                                have p1430_2 := h1430c.2.2.1
                                have p1430_3 := h1430c.2.2.2
                                linarith only [h1242, hlam, p1430_1]
                              · have p1430_0 := h1430c.1
                                have p1430_1 := h1430c.2.1
                                have p1430_2 := h1430c.2.2.1
                                have p1430_3 := h1430c.2.2.2
                                rcases p1430_3 (m.d 0 1) (by simp) with h1436 | h1436
                                · linarith only [h0, h1436, hlam]
                                · rcases p1430_3 (m.d 0 2) (by simp) with h1438 | h1438
                                  · rcases p1430_3 (m.d 0 3) (by simp) with h1439 | h1439
                                    · linarith only [h1334, h1439, hlam]
                                    · linarith only [h1439, h869, hlam]
                                  · linarith only [h0, h1438, hlam]
                              · have p1430_0 := h1430c.1
                                have p1430_1 := h1430c.2.1
                                have p1430_2 := h1430c.2.2.1
                                have p1430_3 := h1430c.2.2.2
                                linarith only [hlam, p1430_0]
                              · have p1430_0 := h1430c.1
                                have p1430_1 := h1430c.2.1
                                have p1430_2 := h1430c.2.2.1
                                have p1430_3 := h1430c.2.2.2
                                linarith only [h1334, hlam, hphi, ht0b, ht34, ht45, ht5b, p1430_1, u0elo1, u3ehi2]
                              · have p1430_0 := h1430c.1
                                have p1430_1 := h1430c.2.1
                                have p1430_2 := h1430c.2.2.1
                                have p1430_3 := h1430c.2.2.2
                                linarith only [h1334, h1337, hlam, hphi, ht0b, ht34, ht45, ht5b, p1430_1, u0elo1, u3ehi2]
                              · have p1430_0 := h1430c.1
                                have p1430_1 := h1430c.2.1
                                have p1430_2 := h1430c.2.2.1
                                have p1430_3 := h1430c.2.2.2
                                linarith only [h1334, h1373, hlam, hphi, ht0b, ht34, ht45, ht5b, p1430_1, u0elo1, u3ehi2]
                              · have p1430_0 := h1430c.1
                                have p1430_1 := h1430c.2.1
                                have p1430_2 := h1430c.2.2.1
                                have p1430_3 := h1430c.2.2.2
                                linarith only [h1422, h1429, h869, hc01, hc34, hlam, hphi, ht12, ht23, p1430_1]
                              · have p1430_0 := h1430c.1
                                have p1430_1 := h1430c.2.1
                                have p1430_2 := h1430c.2.2.1
                                have p1430_3 := h1430c.2.2.2
                                linarith only [h1334, hlam, p1430_1]
                              · have p1430_0 := h1430c.1
                                have p1430_1 := h1430c.2.1
                                have p1430_2 := h1430c.2.2.1
                                have p1430_3 := h1430c.2.2.2
                                linarith only [hlam, p1430_0]
                              · have p1430_0 := h1430c.1
                                have p1430_1 := h1430c.2.1
                                have p1430_2 := h1430c.2.2.1
                                have p1430_3 := h1430c.2.2.2
                                linarith only [h1337, hlam, p1430_1]
                              · have p1430_0 := h1430c.1
                                have p1430_1 := h1430c.2.1
                                have p1430_2 := h1430c.2.2.1
                                have p1430_3 := h1430c.2.2.2
                                linarith only [h1373, hlam, p1430_1]
                              · have p1430_0 := h1430c.1
                                have p1430_1 := h1430c.2.1
                                have p1430_2 := h1430c.2.2.1
                                have p1430_3 := h1430c.2.2.2
                                rcases p1430_3 (m.d 0 1) (by simp) with h1452 | h1452
                                · linarith only [h1088, h1452, hlam]
                                · rcases p1430_3 (m.d 0 2) (by simp) with h1454 | h1454
                                  · rcases p1430_3 (m.d 0 3) (by simp) with h1455 | h1455
                                    · linarith only [h1337, h1455, hlam]
                                    · linarith only [h1455, h869, hlam]
                                  · linarith only [h0, h1454, hlam]
                              · have p1430_0 := h1430c.1
                                have p1430_1 := h1430c.2.1
                                have p1430_2 := h1430c.2.2.1
                                have p1430_3 := h1430c.2.2.2
                                linarith only [h1335, hlam, p1430_0]
                              · have p1430_0 := h1430c.1
                                have p1430_1 := h1430c.2.1
                                have p1430_2 := h1430c.2.2.1
                                have p1430_3 := h1430c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht34, ht45, ht5b, p1430_1, u0elo3, u3ehi0]
                              · have p1430_0 := h1430c.1
                                have p1430_1 := h1430c.2.1
                                have p1430_2 := h1430c.2.2.1
                                have p1430_3 := h1430c.2.2.2
                                linarith only [hlam, p1430_0]
                              · have p1430_0 := h1430c.1
                                have p1430_1 := h1430c.2.1
                                have p1430_2 := h1430c.2.2.1
                                have p1430_3 := h1430c.2.2.2
                                linarith only [h1334, h1335, h1373, hlam, hphi, ht0b, ht34, ht45, ht5b, p1430_1, u0elo1, u3ehi2]
                              · have p1430_0 := h1430c.1
                                have p1430_1 := h1430c.2.1
                                have p1430_2 := h1430c.2.2.1
                                have p1430_3 := h1430c.2.2.2
                                rcases p1430_3 (m.d 0 1) (by simp) with h1463 | h1463
                                · linarith only [h1242, h1463, hlam]
                                · rcases p1430_3 (m.d 0 2) (by simp) with h1465 | h1465
                                  · rcases p1430_3 (m.d 0 3) (by simp) with h1466 | h1466
                                    · linarith only [h1373, h1466, hlam]
                                    · linarith only [h1466, h869, hlam]
                                  · linarith only [h0, h1465, hlam]
                              · have p1430_0 := h1430c.1
                                have p1430_1 := h1430c.2.1
                                have p1430_2 := h1430c.2.2.1
                                have p1430_3 := h1430c.2.2.2
                                linarith only [h1336, hlam, p1430_1]
                              · have p1430_0 := h1430c.1
                                have p1430_1 := h1430c.2.1
                                have p1430_2 := h1430c.2.2.1
                                have p1430_3 := h1430c.2.2.2
                                linarith only [h1334, hlam, hphi, ht0b, ht34, ht45, ht5b, p1430_1, u0elo4, u3ehi2]
                              · have p1430_0 := h1430c.1
                                have p1430_1 := h1430c.2.1
                                have p1430_2 := h1430c.2.2.1
                                have p1430_3 := h1430c.2.2.2
                                linarith only [h1375, hlam, p1430_1]
                              · have p1430_0 := h1430c.1
                                have p1430_1 := h1430c.2.1
                                have p1430_2 := h1430c.2.2.1
                                have p1430_3 := h1430c.2.2.2
                                linarith only [hlam, p1430_0]
                            · linarith only [h1335, h1375, h1429, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                      · linarith only [h1088, h1375, h1424, hlam]
                · linarith only [h0, h1336, h1378, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h1335, h1377, hlam]
            · linarith only [h0, h1334, h1376, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1479 | h1479
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1480 | h1480
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1481 | h1481
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1482 | h1482
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1483 | h1483
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1484 | h1484
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1485 | h1485
                        · linarith only [h1334, h1337, h1485, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1487 | h1487
                          · linarith only [h1334, h1373, h1487, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1489 | h1489
                            · linarith only [h1335, h1375, h1485, h1489, hc34, hlam, hphi, u3ehi2]
                            · linarith only [h1334, h1337, h1489, hc45, hlam, hphi, ht34, u3ehi2]
                      · linarith only [h1334, h1337, h1482, h1484, hc45, hlam, hphi, ht34, u3ehi2]
                    · linarith only [h1334, h1337, h1482, h1483, hc35, hlam, hphi, u3ehi2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1494 | h1494
                    · linarith only [h1482, h1494, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1496 | h1496
                      · linarith only [h1334, h1337, h1375, h1482, h1496, hc34, hlam, hphi, u3ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1498 | h1498
                        · linarith only [h1334, h1482, h1496, h1498, h869, hc45, hlam, hphi, ht34, u3ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1500 | h1500
                          · linarith only [h1334, h1482, h1496, h1500, h869, hc45, hlam, hphi, ht34, u3ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1502 | h1502
                            · linarith only [h1482, h1496, h1502, h869, hc34, hlam, hphi, u3ehi0]
                            · linarith only [h1334, h1337, h1502, hc45, hlam, hphi, ht34, u3ehi2]
                · linarith only [h0, h1336, h1481, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h1334, h1335, h1480, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi2]
            · linarith only [h0, h1334, h1479, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1508 | h1508
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1509 | h1509
        · linarith only [h1334, h1336, h1509, hlam]
        · linarith only [h1508, h1509, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1512 | h1512
        · linarith only [h1508, h1512, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1514 | h1514
          · linarith only [h1335, h1336, h1514, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1516 | h1516
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1517 | h1517
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1518 | h1518
                · linarith only [h1334, h1336, h1518, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1520 | h1520
                  · linarith only [h1334, h1508, h1516, h1518, h1520, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1522 | h1522
                    · linarith only [h1334, h1336, h1512, h1516, h1518, h1522, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1524 | h1524
                      · linarith only [h1088, h1514, h1517, h1518, h1524, hc01, hc25, hlam, hphi, ht12]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1526 | h1526
                        · linarith only [h1334, h1526, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1528 | h1528
                          · linarith only [h0, h1335, h1518, h1526, h1528, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                          · linarith only [h0, h1335, h1518, h1526, h1528, hc35, hlam, hphi, u3ehi2]
              · linarith only [h0, h1335, h1517, hlam]
            · linarith only [h0, h1334, h1516, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1533 | h1533
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1534 | h1534
      · linarith only [h1334, h1335, h1534, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1536 | h1536
        · linarith only [h1534, h1536, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1538 | h1538
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1539 | h1539
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1540 | h1540
              · linarith only [h1334, h1335, h1540, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1542 | h1542
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1543 | h1543
                  · linarith only [h1534, h1539, h1540, h1543, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1545 | h1545
                    · linarith only [h1334, h1536, h1543, h1545, hc34, hlam, hphi, u3ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1547 | h1547
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1548 | h1548
                        · linarith only [h1334, h1543, h1548, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                        · linarith only [h0, h1334, h1540, h1548, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h1088, h1538, h1547, hlam]
                · linarith only [h0, h1533, h1542, hlam]
            · linarith only [h0, h1334, h1539, hlam]
          · linarith only [h1334, h1335, h1538, hc45, hlam, hphi, ht34, u3ehi2]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1555 | h1555
      · linarith only [h1334, h1335, h1555, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1557 | h1557
        · linarith only [h1555, h1557, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1559 | h1559
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1560 | h1560
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1561 | h1561
              · linarith only [h1334, h1335, h1561, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1563 | h1563
                · linarith only [h1334, h1533, h1561, h1563, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1565 | h1565
                  · linarith only [h1555, h1560, h1561, h1565, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1567 | h1567
                    · linarith only [h1334, h1533, h1557, h1565, h1567, hc34, hlam, hphi, u3ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1569 | h1569
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1570 | h1570
                        · linarith only [h1334, h1565, h1570, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                        · linarith only [h0, h1334, h1561, h1570, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h1088, h1559, h1569, hlam]
            · linarith only [h0, h1334, h1560, hlam]
          · linarith only [h1334, h1335, h1559, hc45, hlam, hphi, ht34, u3ehi2]

end R2N4
