import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_57S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3886000 in
theorem r1l7_10_12_23_L_I_L_0_M_LI_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h0emin := hb0.2.1
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1373 | h1373
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1374 | h1374
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1375 | h1375
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1376 | h1376
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1377 | h1377
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1378 | h1378
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1379 | h1379
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1380 | h1380
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1381 | h1381
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1382 | h1382
                    · linarith only [h0, h1373, h1382, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h1378, h1381, h1382, hc23, hlam, hphi, u3elo0]
                  · linarith only [h0, h1381, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1386 | h1386
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1387 | h1387
                    · linarith only [h0, h1373, h1387, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h1378, h1387, hc13, hlam, hphi, u3elo0]
                  · linarith only [h0, h1386, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1391 | h1391
                · linarith only [h1378, h1379, h1391, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1393 | h1393
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1394 | h1394
                    · linarith only [h0, h1373, h1394, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h1378, h1379, h1394, hc13, hlam, hphi, u3elo4]
                  · linarith only [h0, h1393, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1398 | h1398
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1399 | h1399
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1400 | h1400
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1401 | h1401
                    · linarith only [h0, h1373, h1378, h1401, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1403 | h1403
                      · linarith only [h0, h1374, h1401, h1403, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · linarith only [h1378, h1398, h1400, h1403, hc23, hlam, hphi, u3elo3]
                  · linarith only [h0, h1400, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h1378, h1398, h1399, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1408 | h1408
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1409 | h1409
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1410 | h1410
                    · linarith only [h0, h1373, h1410, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1412 | h1412
                      · linarith only [h0, h1374, h1398, h1410, h1412, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1414 | h1414
                        · linarith only [h0, h1373, h1378, h1409, h1414, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1416 | h1416
                          · linarith only [h1373, h1398, h1409, h1416, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1418 | h1418
                            · rcases h0bigk with h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [hlam, p1419_0]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [h0, hlam, p1419_1]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1419_1, u2elo1]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [h0, h1408, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1419_1, u2elo1]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1419_1, u2elo1]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht12, p1419_1, u2elo1]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [hlam, p1419_0]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                rcases p1419_3 (m.d 0 1) (by simp) with h1427 | h1427
                                · linarith only [h0, h1427, hlam]
                                · linarith only [h1373, h1427, hlam]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [h0, h1408, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1419_1, u2elo1]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                rcases p1419_3 (m.d 0 1) (by simp) with h1431 | h1431
                                · linarith only [h0, h1431, hlam]
                                · linarith only [h0, h1374, h1409, h1410, h1431, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1419_1, u2elo1]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [h1373, hlam, p1419_1]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [h1375, hlam, p1419_1]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [hlam, p1419_0]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [h1378, hlam, p1419_1]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [h1398, hlam, p1419_1]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [h1374, hlam, p1419_0]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [h1376, hlam, p1419_0]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [h0, h1373, h1374, h1409, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1419_1, u2elo1]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [hlam, p1419_0]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [h0, h1374, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1419_1, u2elo1]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [h0, h1377, hc01, hlam, hphi, ht12, p1419_1, u2elo1]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [h1377, hlam, p1419_1]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [h1373, h1398, h1409, hc23, hlam, hphi, p1419_1, u3elo4]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [h1408, hlam, p1419_1]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [hlam, p1419_0]
                            · linarith only [h1378, h1408, h1418, hlam]
                  · linarith only [h0, h1409, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1451 | h1451
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1452 | h1452
                    · linarith only [h0, h1373, h1452, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1454 | h1454
                      · linarith only [h0, h1374, h1452, h1454, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1456 | h1456
                        · linarith only [h0, h1374, h1378, h1451, h1452, h1456, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1458 | h1458
                          · linarith only [h0, h1373, h1398, h1408, h1451, h1458, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1460 | h1460
                            · linarith only [h1374, h1408, h1451, h1452, h1460, hc23, hlam, hphi, u3elo3]
                            · rcases h0bigk with h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c | h1462c
                              · have p1462_0 := h1462c.1
                                have p1462_1 := h1462c.2.1
                                have p1462_2 := h1462c.2.2.1
                                have p1462_3 := h1462c.2.2.2
                                linarith only [hlam, p1462_0]
                              · have p1462_0 := h1462c.1
                                have p1462_1 := h1462c.2.1
                                have p1462_2 := h1462c.2.2.1
                                have p1462_3 := h1462c.2.2.2
                                linarith only [h0, hlam, p1462_1]
                              · have p1462_0 := h1462c.1
                                have p1462_1 := h1462c.2.1
                                have p1462_2 := h1462c.2.2.1
                                have p1462_3 := h1462c.2.2.2
                                linarith only [h0, h1373, h1451, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1462_1, u2elo1]
                              · have p1462_0 := h1462c.1
                                have p1462_1 := h1462c.2.1
                                have p1462_2 := h1462c.2.2.1
                                have p1462_3 := h1462c.2.2.2
                                linarith only [h0, h1374, h1451, h1452, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1462_1, u2elo1]
                              · have p1462_0 := h1462c.1
                                have p1462_1 := h1462c.2.1
                                have p1462_2 := h1462c.2.2.1
                                have p1462_3 := h1462c.2.2.2
                                linarith only [h0, h1374, h1408, h1451, h1452, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1462_1, u2elo1]
                              · have p1462_0 := h1462c.1
                                have p1462_1 := h1462c.2.1
                                have p1462_2 := h1462c.2.2.1
                                have p1462_3 := h1462c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, p1462_1, u2elo0]
                              · have p1462_0 := h1462c.1
                                have p1462_1 := h1462c.2.1
                                have p1462_2 := h1462c.2.2.1
                                have p1462_3 := h1462c.2.2.2
                                linarith only [hlam, p1462_0]
                              · have p1462_0 := h1462c.1
                                have p1462_1 := h1462c.2.1
                                have p1462_2 := h1462c.2.2.1
                                have p1462_3 := h1462c.2.2.2
                                rcases p1462_3 (m.d 0 1) (by simp) with h1470 | h1470
                                · linarith only [h0, h1470, hlam]
                                · linarith only [h1373, h1470, hlam]
                              · have p1462_0 := h1462c.1
                                have p1462_1 := h1462c.2.1
                                have p1462_2 := h1462c.2.2.1
                                have p1462_3 := h1462c.2.2.2
                                rcases p1462_3 (m.d 0 1) (by simp) with h1473 | h1473
                                · linarith only [h0, h1473, hlam]
                                · linarith only [h1374, h1473, hlam]
                              · have p1462_0 := h1462c.1
                                have p1462_1 := h1462c.2.1
                                have p1462_2 := h1462c.2.2.1
                                have p1462_3 := h1462c.2.2.2
                                rcases p1462_3 (m.d 0 1) (by simp) with h1476 | h1476
                                · linarith only [h0, h1476, hlam]
                                · linarith only [h0, h1374, h1451, h1452, h1476, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1462_1, u2elo1]
                              · have p1462_0 := h1462c.1
                                have p1462_1 := h1462c.2.1
                                have p1462_2 := h1462c.2.2.1
                                have p1462_3 := h1462c.2.2.2
                                linarith only [h1373, hlam, p1462_1]
                              · have p1462_0 := h1462c.1
                                have p1462_1 := h1462c.2.1
                                have p1462_2 := h1462c.2.2.1
                                have p1462_3 := h1462c.2.2.2
                                linarith only [h1375, hlam, p1462_1]
                              · have p1462_0 := h1462c.1
                                have p1462_1 := h1462c.2.1
                                have p1462_2 := h1462c.2.2.1
                                have p1462_3 := h1462c.2.2.2
                                linarith only [hlam, p1462_0]
                              · have p1462_0 := h1462c.1
                                have p1462_1 := h1462c.2.1
                                have p1462_2 := h1462c.2.2.1
                                have p1462_3 := h1462c.2.2.2
                                linarith only [h1378, hlam, p1462_1]
                              · have p1462_0 := h1462c.1
                                have p1462_1 := h1462c.2.1
                                have p1462_2 := h1462c.2.2.1
                                have p1462_3 := h1462c.2.2.2
                                linarith only [h1398, hlam, p1462_1]
                              · have p1462_0 := h1462c.1
                                have p1462_1 := h1462c.2.1
                                have p1462_2 := h1462c.2.2.1
                                have p1462_3 := h1462c.2.2.2
                                linarith only [h1374, hlam, p1462_0]
                              · have p1462_0 := h1462c.1
                                have p1462_1 := h1462c.2.1
                                have p1462_2 := h1462c.2.2.1
                                have p1462_3 := h1462c.2.2.2
                                linarith only [h1376, hlam, p1462_0]
                              · have p1462_0 := h1462c.1
                                have p1462_1 := h1462c.2.1
                                have p1462_2 := h1462c.2.2.1
                                have p1462_3 := h1462c.2.2.2
                                linarith only [h0, h1373, h1374, h1451, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1462_1, u2elo1]
                              · have p1462_0 := h1462c.1
                                have p1462_1 := h1462c.2.1
                                have p1462_2 := h1462c.2.2.1
                                have p1462_3 := h1462c.2.2.2
                                linarith only [hlam, p1462_0]
                              · have p1462_0 := h1462c.1
                                have p1462_1 := h1462c.2.1
                                have p1462_2 := h1462c.2.2.1
                                have p1462_3 := h1462c.2.2.2
                                linarith only [h1408, hlam, p1462_0]
                              · have p1462_0 := h1462c.1
                                have p1462_1 := h1462c.2.1
                                have p1462_2 := h1462c.2.2.1
                                have p1462_3 := h1462c.2.2.2
                                linarith only [h1398, hc01, hlam, hphi, ht12, ht23, p1462_1, u3elo4]
                              · have p1462_0 := h1462c.1
                                have p1462_1 := h1462c.2.1
                                have p1462_2 := h1462c.2.2.1
                                have p1462_3 := h1462c.2.2.2
                                linarith only [h1377, hlam, p1462_1]
                              · have p1462_0 := h1462c.1
                                have p1462_1 := h1462c.2.1
                                have p1462_2 := h1462c.2.2.1
                                have p1462_3 := h1462c.2.2.2
                                linarith only [h1398, hc03, hlam, hphi, p1462_1, u3elo4]
                              · have p1462_0 := h1462c.1
                                have p1462_1 := h1462c.2.1
                                have p1462_2 := h1462c.2.2.1
                                have p1462_3 := h1462c.2.2.2
                                linarith only [h1374, h1398, h1451, h1452, hc23, hlam, hphi, p1462_1, u3elo4]
                              · have p1462_0 := h1462c.1
                                have p1462_1 := h1462c.2.1
                                have p1462_2 := h1462c.2.2.1
                                have p1462_3 := h1462c.2.2.2
                                linarith only [hlam, p1462_0]
                  · linarith only [h0, h1373, h1451, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1495 | h1495
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1496 | h1496
              · linarith only [h0, h1373, h1377, h1496, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1498 | h1498
                · linarith only [h0, h1374, h1377, h1498, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1500 | h1500
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1501 | h1501
                    · linarith only [h0, h1373, h1501, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h1495, h1496, h1501, hc13, hlam, hphi, u3elo4]
                  · linarith only [h0, h1373, h1500, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1505 | h1505
              · linarith only [h0, h1374, h1377, h1495, h1505, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1507 | h1507
                · linarith only [h0, h1374, h1377, h1507, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1509 | h1509
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1510 | h1510
                    · linarith only [h0, h1373, h1495, h1510, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1512 | h1512
                      · linarith only [h0, h1373, h1377, h1505, h1512, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1514 | h1514
                        · linarith only [h0, h1374, h1495, h1509, h1510, h1514, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1516 | h1516
                          · linarith only [h0, h1373, h1377, h1505, h1509, h1516, hlam]
                          · linarith only [h0, h1374, h1377, h1510, h1516, hc13, hlam, hphi, u3elo4]
                  · linarith only [h0, h1373, h1509, hc13, hlam, hphi, u3elo2]
        · linarith only [h0, h1374, h1376, hlam]
      · linarith only [h0, h1373, h1375, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1522 | h1522
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1523 | h1523
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1524 | h1524
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1525 | h1525
            · linarith only [h1373, h1374, h1525, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1527 | h1527
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1528 | h1528
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1529 | h1529
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1530 | h1530
                    · linarith only [h0, h1373, h1525, h1530, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h1373, h1374, h1529, h1530, hc23, hlam, hphi, u3elo3]
                  · linarith only [h0, h1529, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h1373, h1374, h1527, h1528, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1535 | h1535
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1536 | h1536
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1537 | h1537
                    · linarith only [h0, h1373, h1537, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h1373, h1374, h1536, h1537, hc23, hlam, hphi, u3elo3]
                  · linarith only [h0, h1536, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1541 | h1541
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1542 | h1542
                    · linarith only [h0, h1373, h1542, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h1373, h1374, h1541, h1542, hc23, hlam, hphi, u3elo3]
                  · linarith only [h0, h1541, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1546 | h1546
            · linarith only [h1373, h1374, h1546, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1548 | h1548
              · linarith only [h1522, h1524, h1546, h1548, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1550 | h1550
                · linarith only [h1523, h1524, h1550, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1552 | h1552
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1553 | h1553
                    · linarith only [h0, h1373, h1546, h1553, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h1373, h1374, h1552, h1553, hc23, hlam, hphi, u3elo3]
                  · linarith only [h0, h1552, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1557 | h1557
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1558 | h1558
            · linarith only [h0, h1373, h1523, h1558, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1560 | h1560
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1561 | h1561
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1562 | h1562
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1563 | h1563
                    · linarith only [h1558, h1563, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1373, h1374, h1563, hc13, hlam, hphi, u3elo3]
                  · linarith only [h0, h1373, h1562, hc13, hlam, hphi, u3elo2]
                · linarith only [h0, h1373, h1523, h1560, h1561, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1568 | h1568
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1569 | h1569
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1570 | h1570
                    · linarith only [h0, h1373, h1570, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h1373, h1374, h1570, hc13, hlam, hphi, u3elo3]
                  · linarith only [h0, h1373, h1569, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                · linarith only [h1523, h1557, h1568, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1575 | h1575
            · linarith only [h0, h1373, h1523, h1575, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1577 | h1577
              · linarith only [h0, h1373, h1557, h1575, h1577, hc13, hlam, hphi, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1579 | h1579
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1580 | h1580
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1581 | h1581
                    · linarith only [h1373, h1374, h1575, h1581, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h1373, h1374, h1580, h1581, hc23, hlam, hphi, u3elo3]
                  · linarith only [h0, h1580, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1585 | h1585
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1586 | h1586
                    · linarith only [h0, h1373, h1586, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h1373, h1374, h1585, h1586, hc23, hlam, hphi, u3elo3]
                  · linarith only [h0, h1373, h1585, hc13, hlam, hphi, u3elo2]
      · linarith only [h0, h1373, h1522, hc13, hlam, hphi, u3elo2]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1591 | h1591
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1592 | h1592
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1593 | h1593
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1594 | h1594
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1595 | h1595
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1596 | h1596
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1597 | h1597
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1598 | h1598
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1599 | h1599
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1600 | h1600
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1601 | h1601
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1602 | h1602
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1603 | h1603
                            · linarith only [h1373, h1591, h1599, h1603, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                            · linarith only [h1373, h1591, h1597, h1603, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                          · linarith only [h1596, h1601, h1602, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                        · linarith only [h1595, h1601, hc23, hlam, hphi, u3elo0]
                      · linarith only [h1373, h1591, h1596, h1597, h1600, hlam]
                    · linarith only [h1373, h1599, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h1591, h1598, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1611 | h1611
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1612 | h1612
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1613 | h1613
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1614 | h1614
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1615 | h1615
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1616 | h1616
                            · linarith only [h1592, h1597, h1614, h1616, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                            · rcases h0bigk with h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c
                              · have p1618_0 := h1618c.1
                                have p1618_1 := h1618c.2.1
                                have p1618_2 := h1618c.2.2.1
                                have p1618_3 := h1618c.2.2.2
                                linarith only [hlam, p1618_0]
                              · have p1618_0 := h1618c.1
                                have p1618_1 := h1618c.2.1
                                have p1618_2 := h1618c.2.2.1
                                have p1618_3 := h1618c.2.2.2
                                linarith only [h0, hlam, p1618_1]
                              · have p1618_0 := h1618c.1
                                have p1618_1 := h1618c.2.1
                                have p1618_2 := h1618c.2.2.1
                                have p1618_3 := h1618c.2.2.2
                                linarith only [h1373, hlam, p1618_0]
                              · have p1618_0 := h1618c.1
                                have p1618_1 := h1618c.2.1
                                have p1618_2 := h1618c.2.2.1
                                have p1618_3 := h1618c.2.2.2
                                linarith only [h1373, h1591, h1611, h1612, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1618_1, u2elo1]
                              · have p1618_0 := h1618c.1
                                have p1618_1 := h1618c.2.1
                                have p1618_2 := h1618c.2.2.1
                                have p1618_3 := h1618c.2.2.2
                                linarith only [h1373, h1591, h1597, h1611, h1612, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1618_1, u2elo1]
                              · have p1618_0 := h1618c.1
                                have p1618_1 := h1618c.2.1
                                have p1618_2 := h1618c.2.2.1
                                have p1618_3 := h1618c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht12, p1618_1, u2elo1]
                              · have p1618_0 := h1618c.1
                                have p1618_1 := h1618c.2.1
                                have p1618_2 := h1618c.2.2.1
                                have p1618_3 := h1618c.2.2.2
                                linarith only [hlam, p1618_0]
                              · have p1618_0 := h1618c.1
                                have p1618_1 := h1618c.2.1
                                have p1618_2 := h1618c.2.2.1
                                have p1618_3 := h1618c.2.2.2
                                linarith only [h0, h1373, h1591, h1612, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1618_1, u2elo1]
                              · have p1618_0 := h1618c.1
                                have p1618_1 := h1618c.2.1
                                have p1618_2 := h1618c.2.2.1
                                have p1618_3 := h1618c.2.2.2
                                rcases p1618_3 (m.d 0 1) (by simp) with h1627 | h1627
                                · linarith only [h0, h1627, hlam]
                                · linarith only [h1591, h1627, hlam]
                              · have p1618_0 := h1618c.1
                                have p1618_1 := h1618c.2.1
                                have p1618_2 := h1618c.2.2.1
                                have p1618_3 := h1618c.2.2.2
                                rcases p1618_3 (m.d 0 1) (by simp) with h1630 | h1630
                                · linarith only [h0, h1630, hlam]
                                · linarith only [h0, h1591, h1612, h1630, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1618_1, u2elo1]
                              · have p1618_0 := h1618c.1
                                have p1618_1 := h1618c.2.1
                                have p1618_2 := h1618c.2.2.1
                                have p1618_3 := h1618c.2.2.2
                                linarith only [h1591, h1612, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1618_1, u3elo0]
                              · have p1618_0 := h1618c.1
                                have p1618_1 := h1618c.2.1
                                have p1618_2 := h1618c.2.2.1
                                have p1618_3 := h1618c.2.2.2
                                linarith only [h1592, hlam, p1618_1]
                              · have p1618_0 := h1618c.1
                                have p1618_1 := h1618c.2.1
                                have p1618_2 := h1618c.2.2.1
                                have p1618_3 := h1618c.2.2.2
                                linarith only [hlam, p1618_0]
                              · have p1618_0 := h1618c.1
                                have p1618_1 := h1618c.2.1
                                have p1618_2 := h1618c.2.2.1
                                have p1618_3 := h1618c.2.2.2
                                rcases p1618_3 (m.d 0 1) (by simp) with h1636 | h1636
                                · linarith only [h1373, h1636, hlam]
                                · linarith only [h1591, h1636, hlam]
                              · have p1618_0 := h1618c.1
                                have p1618_1 := h1618c.2.1
                                have p1618_2 := h1618c.2.2.1
                                have p1618_3 := h1618c.2.2.2
                                rcases p1618_3 (m.d 0 1) (by simp) with h1639 | h1639
                                · linarith only [h1373, h1639, hlam]
                                · linarith only [h1373, h1591, h1611, h1612, h1639, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1618_1, u2elo1]
                              · have p1618_0 := h1618c.1
                                have p1618_1 := h1618c.2.1
                                have p1618_2 := h1618c.2.2.1
                                have p1618_3 := h1618c.2.2.2
                                linarith only [h1591, hlam, p1618_0]
                              · have p1618_0 := h1618c.1
                                have p1618_1 := h1618c.2.1
                                have p1618_2 := h1618c.2.2.1
                                have p1618_3 := h1618c.2.2.2
                                linarith only [h1593, hlam, p1618_0]
                              · have p1618_0 := h1618c.1
                                have p1618_1 := h1618c.2.1
                                have p1618_2 := h1618c.2.2.1
                                have p1618_3 := h1618c.2.2.2
                                linarith only [h1595, hlam, p1618_0]
                              · have p1618_0 := h1618c.1
                                have p1618_1 := h1618c.2.1
                                have p1618_2 := h1618c.2.2.1
                                have p1618_3 := h1618c.2.2.2
                                linarith only [hlam, p1618_0]
                              · have p1618_0 := h1618c.1
                                have p1618_1 := h1618c.2.1
                                have p1618_2 := h1618c.2.2.1
                                have p1618_3 := h1618c.2.2.2
                                linarith only [h1597, hlam, p1618_0]
                              · have p1618_0 := h1618c.1
                                have p1618_1 := h1618c.2.1
                                have p1618_2 := h1618c.2.2.1
                                have p1618_3 := h1618c.2.2.2
                                linarith only [h0, h1591, h1594, h1612, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1618_1, u2elo1]
                              · have p1618_0 := h1618c.1
                                have p1618_1 := h1618c.2.1
                                have p1618_2 := h1618c.2.2.1
                                have p1618_3 := h1618c.2.2.2
                                linarith only [h1594, hlam, p1618_1]
                              · have p1618_0 := h1618c.1
                                have p1618_1 := h1618c.2.1
                                have p1618_2 := h1618c.2.2.1
                                have p1618_3 := h1618c.2.2.2
                                linarith only [h1596, hlam, p1618_0]
                              · have p1618_0 := h1618c.1
                                have p1618_1 := h1618c.2.1
                                have p1618_2 := h1618c.2.2.1
                                have p1618_3 := h1618c.2.2.2
                                rcases p1618_3 (m.d 0 1) (by simp) with h1650 | h1650
                                · linarith only [h1373, h1591, h1611, h1612, h1650, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1618_1, u2elo1]
                                · linarith only [h1591, h1650, hlam]
                              · have p1618_0 := h1618c.1
                                have p1618_1 := h1618c.2.1
                                have p1618_2 := h1618c.2.2.1
                                have p1618_3 := h1618c.2.2.2
                                linarith only [hlam, p1618_0]
                          · linarith only [h1596, h1615, hc23, hlam, hphi, u3elo0]
                        · linarith only [h1373, h1591, h1612, h1614, hc23, hlam, hphi, u3elo1]
                      · linarith only [h1373, h1596, h1613, hlam]
                    · linarith only [h1373, h1612, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h1611, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1659 | h1659
                · linarith only [h1373, h1591, h1596, h1659, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1661 | h1661
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1662 | h1662
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1663 | h1663
                      · linarith only [h1373, h1591, h1596, h1661, h1662, h1663, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h1373, h1591, h1662, h1663, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · linarith only [h1373, h1662, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h1661, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h1373, h1591, h1595, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1669 | h1669
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1670 | h1670
              · linarith only [h1592, h1594, h1670, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1672 | h1672
                · linarith only [h0, h1591, h1594, h1672, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1674 | h1674
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1675 | h1675
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1676 | h1676
                      · linarith only [h1373, h1670, h1676, hc01, hlam, hphi, ht12, ht23, u3elo1]
                      · linarith only [h1373, h1591, h1675, h1676, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · linarith only [h1373, h1591, h1675, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                  · linarith only [h1592, h1674, hc12, hlam, hphi, u2elo0]
            · linarith only [h1373, h1591, h1669, hlam]
        · linarith only [h1373, h1591, h1592, h1593, hc23, hlam, hphi, u3elo1]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1683 | h1683
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1684 | h1684
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1685 | h1685
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1686 | h1686
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1687 | h1687
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1688 | h1688
                  · linarith only [h0, h1591, h1592, h1688, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h1591, h1688, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1691 | h1691
                  · linarith only [h0, h1591, h1592, h1691, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h1591, h1691, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · linarith only [h1592, h1684, h1686, hlam]
            · linarith only [h0, h1591, h1592, h1685, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1696 | h1696
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1697 | h1697
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1698 | h1698
                · linarith only [h0, h1591, h1684, h1698, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1700 | h1700
                  · linarith only [h0, h1591, h1592, h1700, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h1591, h1700, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1703 | h1703
                · linarith only [h1373, h1591, h1697, h1703, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1705 | h1705
                  · linarith only [h0, h1591, h1592, h1705, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h1591, h1705, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · linarith only [h0, h1591, h1592, h1696, hlam]
        · linarith only [h0, h1591, h1683, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1710 | h1710
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1711 | h1711
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1712 | h1712
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1713 | h1713
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1714 | h1714
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1715 | h1715
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1716 | h1716
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1717 | h1717
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1718 | h1718
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1719 | h1719
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1720 | h1720
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1721 | h1721
                            · linarith only [h1710, h1719, h1721, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                            · rcases h0bigk with h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c
                              · have p1723_0 := h1723c.1
                                have p1723_1 := h1723c.2.1
                                have p1723_2 := h1723c.2.2.1
                                have p1723_3 := h1723c.2.2.2
                                linarith only [hlam, p1723_0]
                              · have p1723_0 := h1723c.1
                                have p1723_1 := h1723c.2.1
                                have p1723_2 := h1723c.2.2.1
                                have p1723_3 := h1723c.2.2.2
                                linarith only [h0, hlam, p1723_1]
                              · have p1723_0 := h1723c.1
                                have p1723_1 := h1723c.2.1
                                have p1723_2 := h1723c.2.2.1
                                have p1723_3 := h1723c.2.2.2
                                linarith only [h1373, hlam, p1723_0]
                              · have p1723_0 := h1723c.1
                                have p1723_1 := h1723c.2.1
                                have p1723_2 := h1723c.2.2.1
                                have p1723_3 := h1723c.2.2.2
                                linarith only [h1591, hlam, p1723_1]
                              · have p1723_0 := h1723c.1
                                have p1723_1 := h1723c.2.1
                                have p1723_2 := h1723c.2.2.1
                                have p1723_3 := h1723c.2.2.2
                                linarith only [h1591, h1716, h1717, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1723_1, u2elo1]
                              · have p1723_0 := h1723c.1
                                have p1723_1 := h1723c.2.1
                                have p1723_2 := h1723c.2.2.1
                                have p1723_3 := h1723c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht12, p1723_1, u2elo1]
                              · have p1723_0 := h1723c.1
                                have p1723_1 := h1723c.2.1
                                have p1723_2 := h1723c.2.2.1
                                have p1723_3 := h1723c.2.2.2
                                linarith only [hlam, p1723_0]
                              · have p1723_0 := h1723c.1
                                have p1723_1 := h1723c.2.1
                                have p1723_2 := h1723c.2.2.1
                                have p1723_3 := h1723c.2.2.2
                                linarith only [h0, h1713, h1715, h1721, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1723_1, u2elo1]
                              · have p1723_0 := h1723c.1
                                have p1723_1 := h1723c.2.1
                                have p1723_2 := h1723c.2.2.1
                                have p1723_3 := h1723c.2.2.2
                                linarith only [h0, h1715, h1721, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1723_1, u2elo1]
                              · have p1723_0 := h1723c.1
                                have p1723_1 := h1723c.2.1
                                have p1723_2 := h1723c.2.2.1
                                have p1723_3 := h1723c.2.2.2
                                linarith only [h0, h1715, h1721, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1723_1, u2elo1]
                              · have p1723_0 := h1723c.1
                                have p1723_1 := h1723c.2.1
                                have p1723_2 := h1723c.2.2.1
                                have p1723_3 := h1723c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, p1723_1, u3elo0]
                              · have p1723_0 := h1723c.1
                                have p1723_1 := h1723c.2.1
                                have p1723_2 := h1723c.2.2.1
                                have p1723_3 := h1723c.2.2.2
                                linarith only [h1710, hlam, p1723_1]
                              · have p1723_0 := h1723c.1
                                have p1723_1 := h1723c.2.1
                                have p1723_2 := h1723c.2.2.1
                                have p1723_3 := h1723c.2.2.2
                                linarith only [hlam, p1723_0]
                              · have p1723_0 := h1723c.1
                                have p1723_1 := h1723c.2.1
                                have p1723_2 := h1723c.2.2.1
                                have p1723_3 := h1723c.2.2.2
                                linarith only [h1373, h1715, h1716, h1721, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1723_1, u2elo1]
                              · have p1723_0 := h1723c.1
                                have p1723_1 := h1723c.2.1
                                have p1723_2 := h1723c.2.2.1
                                have p1723_3 := h1723c.2.2.2
                                linarith only [h1373, h1715, h1716, h1721, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1723_1, u2elo1]
                              · have p1723_0 := h1723c.1
                                have p1723_1 := h1723c.2.1
                                have p1723_2 := h1723c.2.2.1
                                have p1723_3 := h1723c.2.2.2
                                linarith only [h1591, h1716, h1717, hc01, hlam, hphi, ht12, p1723_1, u2elo1]
                              · have p1723_0 := h1723c.1
                                have p1723_1 := h1723c.2.1
                                have p1723_2 := h1723c.2.2.1
                                have p1723_3 := h1723c.2.2.2
                                linarith only [h1711, hlam, p1723_0]
                              · have p1723_0 := h1723c.1
                                have p1723_1 := h1723c.2.1
                                have p1723_2 := h1723c.2.2.1
                                have p1723_3 := h1723c.2.2.2
                                linarith only [h1713, hlam, p1723_0]
                              · have p1723_0 := h1723c.1
                                have p1723_1 := h1723c.2.1
                                have p1723_2 := h1723c.2.2.1
                                have p1723_3 := h1723c.2.2.2
                                linarith only [hlam, p1723_0]
                              · have p1723_0 := h1723c.1
                                have p1723_1 := h1723c.2.1
                                have p1723_2 := h1723c.2.2.1
                                have p1723_3 := h1723c.2.2.2
                                linarith only [h1591, h1715, h1716, h1717, h1721, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1723_1, u2elo1]
                              · have p1723_0 := h1723c.1
                                have p1723_1 := h1723c.2.1
                                have p1723_2 := h1723c.2.2.1
                                have p1723_3 := h1723c.2.2.2
                                linarith only [h0, h1712, hc01, hlam, hphi, ht12, p1723_1, u2elo1]
                              · have p1723_0 := h1723c.1
                                have p1723_1 := h1723c.2.1
                                have p1723_2 := h1723c.2.2.1
                                have p1723_3 := h1723c.2.2.2
                                linarith only [h1712, hlam, p1723_1]
                              · have p1723_0 := h1723c.1
                                have p1723_1 := h1723c.2.1
                                have p1723_2 := h1723c.2.2.1
                                have p1723_3 := h1723c.2.2.2
                                linarith only [h1714, hlam, p1723_0]
                              · have p1723_0 := h1723c.1
                                have p1723_1 := h1723c.2.1
                                have p1723_2 := h1723c.2.2.1
                                have p1723_3 := h1723c.2.2.2
                                linarith only [h1715, hlam, p1723_1]
                              · have p1723_0 := h1723c.1
                                have p1723_1 := h1723c.2.1
                                have p1723_2 := h1723c.2.2.1
                                have p1723_3 := h1723c.2.2.2
                                linarith only [hlam, p1723_0]
                          · linarith only [h1714, h1720, hc23, hlam, hphi, u3elo0]
                        · linarith only [h1373, h1713, h1719, hc23, hlam, hphi, u3elo1]
                      · linarith only [h1373, h1714, h1718, hlam]
                    · linarith only [h1373, h1713, h1717, hlam]
                  · linarith only [h0, h1716, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1754 | h1754
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1755 | h1755
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1756 | h1756
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1757 | h1757
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1758 | h1758
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1759 | h1759
                            · linarith only [h0, h1710, h1715, h1757, h1759, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · rcases h0bigk with h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c | h1761c
                              · have p1761_0 := h1761c.1
                                have p1761_1 := h1761c.2.1
                                have p1761_2 := h1761c.2.2.1
                                have p1761_3 := h1761c.2.2.2
                                linarith only [hlam, p1761_0]
                              · have p1761_0 := h1761c.1
                                have p1761_1 := h1761c.2.1
                                have p1761_2 := h1761c.2.2.1
                                have p1761_3 := h1761c.2.2.2
                                linarith only [h0, hlam, p1761_1]
                              · have p1761_0 := h1761c.1
                                have p1761_1 := h1761c.2.1
                                have p1761_2 := h1761c.2.2.1
                                have p1761_3 := h1761c.2.2.2
                                linarith only [h1373, hlam, p1761_0]
                              · have p1761_0 := h1761c.1
                                have p1761_1 := h1761c.2.1
                                have p1761_2 := h1761c.2.2.1
                                have p1761_3 := h1761c.2.2.2
                                linarith only [h1591, hlam, p1761_1]
                              · have p1761_0 := h1761c.1
                                have p1761_1 := h1761c.2.1
                                have p1761_2 := h1761c.2.2.1
                                have p1761_3 := h1761c.2.2.2
                                linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1761_1, u2elo1]
                              · have p1761_0 := h1761c.1
                                have p1761_1 := h1761c.2.1
                                have p1761_2 := h1761c.2.2.1
                                have p1761_3 := h1761c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht12, p1761_1, u2elo1]
                              · have p1761_0 := h1761c.1
                                have p1761_1 := h1761c.2.1
                                have p1761_2 := h1761c.2.2.1
                                have p1761_3 := h1761c.2.2.2
                                linarith only [hlam, p1761_0]
                              · have p1761_0 := h1761c.1
                                have p1761_1 := h1761c.2.1
                                have p1761_2 := h1761c.2.2.1
                                have p1761_3 := h1761c.2.2.2
                                linarith only [h0, h1373, hc01, hlam, hphi, ht12, p1761_1, u2elo1]
                              · have p1761_0 := h1761c.1
                                have p1761_1 := h1761c.2.1
                                have p1761_2 := h1761c.2.2.1
                                have p1761_3 := h1761c.2.2.2
                                linarith only [h0, h1591, hc01, hlam, hphi, ht12, p1761_1, u2elo1]
                              · have p1761_0 := h1761c.1
                                have p1761_1 := h1761c.2.1
                                have p1761_2 := h1761c.2.2.1
                                have p1761_3 := h1761c.2.2.2
                                linarith only [h0, h1591, h1715, hc01, hlam, hphi, ht12, p1761_1, u2elo1]
                              · have p1761_0 := h1761c.1
                                have p1761_1 := h1761c.2.1
                                have p1761_2 := h1761c.2.2.1
                                have p1761_3 := h1761c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, p1761_1, u3elo0]
                              · have p1761_0 := h1761c.1
                                have p1761_1 := h1761c.2.1
                                have p1761_2 := h1761c.2.2.1
                                have p1761_3 := h1761c.2.2.2
                                linarith only [h1710, hlam, p1761_1]
                              · have p1761_0 := h1761c.1
                                have p1761_1 := h1761c.2.1
                                have p1761_2 := h1761c.2.2.1
                                have p1761_3 := h1761c.2.2.2
                                linarith only [hlam, p1761_0]
                              · have p1761_0 := h1761c.1
                                have p1761_1 := h1761c.2.1
                                have p1761_2 := h1761c.2.2.1
                                have p1761_3 := h1761c.2.2.2
                                linarith only [h1373, h1591, hc01, hlam, hphi, ht12, ht23, p1761_1, u3elo1]
                              · have p1761_0 := h1761c.1
                                have p1761_1 := h1761c.2.1
                                have p1761_2 := h1761c.2.2.1
                                have p1761_3 := h1761c.2.2.2
                                linarith only [h1373, h1591, h1715, hc01, hlam, hphi, ht12, ht23, p1761_1, u3elo1]
                              · have p1761_0 := h1761c.1
                                have p1761_1 := h1761c.2.1
                                have p1761_2 := h1761c.2.2.1
                                have p1761_3 := h1761c.2.2.2
                                linarith only [h1715, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1761_1]
                              · have p1761_0 := h1761c.1
                                have p1761_1 := h1761c.2.1
                                have p1761_2 := h1761c.2.2.1
                                have p1761_3 := h1761c.2.2.2
                                linarith only [h1711, hlam, p1761_0]
                              · have p1761_0 := h1761c.1
                                have p1761_1 := h1761c.2.1
                                have p1761_2 := h1761c.2.2.1
                                have p1761_3 := h1761c.2.2.2
                                linarith only [h1713, hlam, p1761_0]
                              · have p1761_0 := h1761c.1
                                have p1761_1 := h1761c.2.1
                                have p1761_2 := h1761c.2.2.1
                                have p1761_3 := h1761c.2.2.2
                                linarith only [hlam, p1761_0]
                              · have p1761_0 := h1761c.1
                                have p1761_1 := h1761c.2.1
                                have p1761_2 := h1761c.2.2.1
                                have p1761_3 := h1761c.2.2.2
                                linarith only [h1715, hlam, p1761_0]
                              · have p1761_0 := h1761c.1
                                have p1761_1 := h1761c.2.1
                                have p1761_2 := h1761c.2.2.1
                                have p1761_3 := h1761c.2.2.2
                                linarith only [h0, h1712, hc01, hlam, hphi, ht12, p1761_1, u2elo1]
                              · have p1761_0 := h1761c.1
                                have p1761_1 := h1761c.2.1
                                have p1761_2 := h1761c.2.2.1
                                have p1761_3 := h1761c.2.2.2
                                linarith only [h1712, hlam, p1761_1]
                              · have p1761_0 := h1761c.1
                                have p1761_1 := h1761c.2.1
                                have p1761_2 := h1761c.2.2.1
                                have p1761_3 := h1761c.2.2.2
                                linarith only [h1714, hlam, p1761_0]
                              · have p1761_0 := h1761c.1
                                have p1761_1 := h1761c.2.1
                                have p1761_2 := h1761c.2.2.1
                                have p1761_3 := h1761c.2.2.2
                                linarith only [h0, h1591, h1712, hc01, hlam, hphi, ht12, p1761_1, u2elo1]
                              · have p1761_0 := h1761c.1
                                have p1761_1 := h1761c.2.1
                                have p1761_2 := h1761c.2.2.1
                                have p1761_3 := h1761c.2.2.2
                                linarith only [hlam, p1761_0]
                          · linarith only [h1373, h1714, h1758, hc23, hlam, hphi, u3elo1]
                        · linarith only [h1373, h1713, h1757, hc23, hlam, hphi, u3elo1]
                      · linarith only [h1373, h1714, h1756, hlam]
                    · linarith only [h1373, h1755, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h1754, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1792 | h1792
                · linarith only [h1713, h1714, h1792, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1794 | h1794
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1795 | h1795
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1796 | h1796
                      · linarith only [h1713, h1714, h1794, h1796, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h1373, h1796, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h1373, h1795, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h1710, h1794, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1801 | h1801
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1802 | h1802
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1803 | h1803
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1804 | h1804
                    · linarith only [h1713, h1804, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1373, h1804, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h1803, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h1713, h1801, h1802, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1809 | h1809
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1810 | h1810
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1811 | h1811
                    · linarith only [h1713, h1811, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1373, h1811, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h1710, h1810, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1815 | h1815
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1816 | h1816
                    · linarith only [h1373, h1713, h1815, h1816, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h1373, h1816, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h1710, h1801, h1815, hc02, hlam, hphi, ht23, u3elo4]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1820 | h1820
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1821 | h1821
              · linarith only [h1710, h1712, h1821, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1823 | h1823
                · linarith only [h1711, h1712, h1823, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1825 | h1825
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1826 | h1826
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1827 | h1827
                      · linarith only [h1821, h1827, hc03, hlam, hphi, u3elo1]
                      · linarith only [h1373, h1827, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h1373, h1826, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h1710, h1712, h1825, hc12, hlam, hphi, u2elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1832 | h1832
              · linarith only [h1711, h1712, h1820, h1832, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1834 | h1834
                · linarith only [h1711, h1712, h1834, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1836 | h1836
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1837 | h1837
                    · linarith only [h1820, h1837, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1373, h1837, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h1710, h1712, h1836, hc12, hlam, hphi, u2elo4]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1841 | h1841
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1842 | h1842
            · linarith only [h1710, h1711, h1842, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1844 | h1844
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1845 | h1845
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1846 | h1846
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1847 | h1847
                    · linarith only [h1842, h1844, h1846, h1847, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · linarith only [h1373, h1847, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h1710, h1711, h1846, hc12, hlam, hphi, u2elo3]
                · linarith only [h1710, h1711, h1844, h1845, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1852 | h1852
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1853 | h1853
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1854 | h1854
                    · linarith only [h1842, h1854, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1373, h1854, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h1710, h1711, h1853, hc12, hlam, hphi, u2elo3]
                · linarith only [h1711, h1841, h1852, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1859 | h1859
            · linarith only [h1710, h1711, h1859, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1861 | h1861
              · linarith only [h1710, h1841, h1861, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1863 | h1863
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1864 | h1864
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1865 | h1865
                    · linarith only [h1859, h1865, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1373, h1865, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h1710, h1711, h1864, hc12, hlam, hphi, u2elo3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1869 | h1869
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1870 | h1870
                    · linarith only [h1373, h1859, h1869, h1870, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h1373, h1870, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h1710, h1711, h1869, hc12, hlam, hphi, u2elo3]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1874 | h1874
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1875 | h1875
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1876 | h1876
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1877 | h1877
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1878 | h1878
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1879 | h1879
                  · linarith only [h1710, h1879, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h1879, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1882 | h1882
                  · linarith only [h1710, h1874, h1882, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h1882, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h1710, h1875, h1877, hlam]
            · linarith only [h1710, h1874, h1876, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1887 | h1887
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1888 | h1888
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1889 | h1889
                · linarith only [h1874, h1875, h1889, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1891 | h1891
                  · linarith only [h1710, h1874, h1891, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h1891, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1894 | h1894
                · linarith only [h1710, h1874, h1888, h1894, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1896 | h1896
                  · linarith only [h1710, h1874, h1896, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h1896, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h1710, h1874, h1887, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1900 | h1900
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1901 | h1901
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1902 | h1902
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1903 | h1903
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1904 | h1904
                  · linarith only [h1710, h1904, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h1904, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h1874, h1900, h1903, hlam]
              · linarith only [h1874, h1900, h1901, h1902, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1909 | h1909
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1910 | h1910
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1911 | h1911
                  · linarith only [h1710, h1900, h1911, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                  · linarith only [h0, h1911, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h1710, h1900, h1901, h1910, hlam]
              · linarith only [h1710, h1900, h1909, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1916 | h1916
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1917 | h1917
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1918 | h1918
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1919 | h1919
                  · linarith only [h1710, h1919, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h1919, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1922 | h1922
                  · linarith only [h0, h1710, h1922, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h1922, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1925 | h1925
                · linarith only [h1916, h1917, h1925, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1927 | h1927
                  · linarith only [h0, h1710, h1927, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h1927, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1930 | h1930
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1931 | h1931
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1932 | h1932
                  · linarith only [h0, h1710, h1932, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h1932, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h1916, h1930, h1931, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1936 | h1936
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1937 | h1937
                  · linarith only [h0, h1710, h1937, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h1937, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1940 | h1940
                  · linarith only [h0, h1710, h1940, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h1940, hc01, hlam, hphi, ht12, ht23, u3elo2]

set_option maxHeartbeats 3886000 in
theorem r1l7_10_12_23_L_I_L_0_M_LI (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0emin := hb0.2.1
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_12_23_L_I_L_0_M_LI_x0 m hb0 hb2 hb3 h0
  · exact r1l7_10_12_23_L_I_L_0_M_LI_x1 m hb0 hb2 hb3 h0

end R2N4
