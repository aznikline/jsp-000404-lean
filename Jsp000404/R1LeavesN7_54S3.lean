import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_54S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4472000 in
theorem r1l7_11_23_L_I_M_LI_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h1bigk := hb1.1
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1397 | h1397
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1398 | h1398
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1399 | h1399
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1400 | h1400
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1401 | h1401
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1402 | h1402
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1403 | h1403
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1404 | h1404
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1405 | h1405
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1406 | h1406
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1407 | h1407
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1408 | h1408
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1409 | h1409
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1410 | h1410
                            · linarith only [h0, h1397, h1401, h1407, h1410, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h0, h1397, h1404, h1406, h1410, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h0, h1397, h1404, h1406, h1409, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h1400, h1408, hc23, hlam, hphi, u3elo0]
                      · linarith only [h0, h1397, h1404, h1407, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1416 | h1416
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1417 | h1417
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1418 | h1418
                          · linarith only [h1402, h1406, h1418, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1420 | h1420
                            · linarith only [h1402, h1406, h1416, h1420, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                            · rcases h1bigk with h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c
                              · have p1422_0 := h1422c.1
                                have p1422_1 := h1422c.2.1
                                have p1422_2 := h1422c.2.2.1
                                have p1422_3 := h1422c.2.2.2
                                linarith only [hlam, p1422_0]
                              · have p1422_0 := h1422c.1
                                have p1422_1 := h1422c.2.1
                                have p1422_2 := h1422c.2.2.1
                                have p1422_3 := h1422c.2.2.2
                                linarith only [h0, hlam, p1422_0]
                              · have p1422_0 := h1422c.1
                                have p1422_1 := h1422c.2.1
                                have p1422_2 := h1422c.2.2.1
                                have p1422_3 := h1422c.2.2.2
                                linarith only [h0, h1401, h1417, h1420, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1422_1]
                              · have p1422_0 := h1422c.1
                                have p1422_1 := h1422c.2.1
                                have p1422_2 := h1422c.2.2.1
                                have p1422_3 := h1422c.2.2.2
                                rcases p1422_3 (m.d 0 1) (by simp) with h1426 | h1426
                                · rcases p1422_3 (m.d 1 2) (by simp) with h1427 | h1427
                                  · rcases p1422_3 (m.d 1 3) (by simp) with h1428 | h1428
                                    · linarith only [h1397, h1428, hlam]
                                    · linarith only [h1404, h1428, hlam]
                                  · linarith only [h1402, h1427, hlam]
                                · linarith only [h1426, hlam, p1422_0]
                              · have p1422_0 := h1422c.1
                                have p1422_1 := h1422c.2.1
                                have p1422_2 := h1422c.2.2.1
                                have p1422_3 := h1422c.2.2.2
                                rcases p1422_3 (m.d 0 1) (by simp) with h1433 | h1433
                                · rcases p1422_3 (m.d 1 2) (by simp) with h1434 | h1434
                                  · rcases p1422_3 (m.d 1 3) (by simp) with h1435 | h1435
                                    · linarith only [h1397, h1435, hlam]
                                    · linarith only [h1405, h1435, hlam]
                                  · linarith only [h1403, h1434, hlam]
                                · linarith only [h1433, hlam, p1422_0]
                              · have p1422_0 := h1422c.1
                                have p1422_1 := h1422c.2.1
                                have p1422_2 := h1422c.2.2.1
                                have p1422_3 := h1422c.2.2.2
                                linarith only [h1397, h1401, h1417, h1420, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1422_1]
                              · have p1422_0 := h1422c.1
                                have p1422_1 := h1422c.2.1
                                have p1422_2 := h1422c.2.2.1
                                have p1422_3 := h1422c.2.2.2
                                linarith only [hlam, p1422_0]
                              · have p1422_0 := h1422c.1
                                have p1422_1 := h1422c.2.1
                                have p1422_2 := h1422c.2.2.1
                                have p1422_3 := h1422c.2.2.2
                                rcases p1422_3 (m.d 0 1) (by simp) with h1442 | h1442
                                · linarith only [h0, h1442, hlam]
                                · linarith only [h1397, h1442, hlam]
                              · have p1422_0 := h1422c.1
                                have p1422_1 := h1422c.2.1
                                have p1422_2 := h1422c.2.2.1
                                have p1422_3 := h1422c.2.2.2
                                rcases p1422_3 (m.d 0 1) (by simp) with h1445 | h1445
                                · linarith only [h0, h1445, hlam]
                                · linarith only [h1398, h1445, hlam]
                              · have p1422_0 := h1422c.1
                                have p1422_1 := h1422c.2.1
                                have p1422_2 := h1422c.2.2.1
                                have p1422_3 := h1422c.2.2.2
                                rcases p1422_3 (m.d 0 1) (by simp) with h1448 | h1448
                                · linarith only [h0, h1448, hlam]
                                · linarith only [h1399, h1448, hlam]
                              · have p1422_0 := h1422c.1
                                have p1422_1 := h1422c.2.1
                                have p1422_2 := h1422c.2.2.1
                                have p1422_3 := h1422c.2.2.2
                                linarith only [h1397, hlam, p1422_0]
                              · have p1422_0 := h1422c.1
                                have p1422_1 := h1422c.2.1
                                have p1422_2 := h1422c.2.2.1
                                have p1422_3 := h1422c.2.2.2
                                linarith only [h1401, hlam, p1422_1]
                              · have p1422_0 := h1422c.1
                                have p1422_1 := h1422c.2.1
                                have p1422_2 := h1422c.2.2.1
                                have p1422_3 := h1422c.2.2.2
                                linarith only [hlam, p1422_0]
                              · have p1422_0 := h1422c.1
                                have p1422_1 := h1422c.2.1
                                have p1422_2 := h1422c.2.2.1
                                have p1422_3 := h1422c.2.2.2
                                linarith only [h0, h1397, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1422_1]
                              · have p1422_0 := h1422c.1
                                have p1422_1 := h1422c.2.1
                                have p1422_2 := h1422c.2.2.1
                                have p1422_3 := h1422c.2.2.2
                                linarith only [h0, h1397, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p1422_1]
                              · have p1422_0 := h1422c.1
                                have p1422_1 := h1422c.2.1
                                have p1422_2 := h1422c.2.2.1
                                have p1422_3 := h1422c.2.2.2
                                linarith only [h1398, hlam, p1422_0]
                              · have p1422_0 := h1422c.1
                                have p1422_1 := h1422c.2.1
                                have p1422_2 := h1422c.2.2.1
                                have p1422_3 := h1422c.2.2.2
                                linarith only [h1402, hlam, p1422_1]
                              · have p1422_0 := h1422c.1
                                have p1422_1 := h1422c.2.1
                                have p1422_2 := h1422c.2.2.1
                                have p1422_3 := h1422c.2.2.2
                                linarith only [h1404, hlam, p1422_0]
                              · have p1422_0 := h1422c.1
                                have p1422_1 := h1422c.2.1
                                have p1422_2 := h1422c.2.2.1
                                have p1422_3 := h1422c.2.2.2
                                linarith only [hlam, p1422_0]
                              · have p1422_0 := h1422c.1
                                have p1422_1 := h1422c.2.1
                                have p1422_2 := h1422c.2.2.1
                                have p1422_3 := h1422c.2.2.2
                                linarith only [h1406, hlam, p1422_1]
                              · have p1422_0 := h1422c.1
                                have p1422_1 := h1422c.2.1
                                have p1422_2 := h1422c.2.2.1
                                have p1422_3 := h1422c.2.2.2
                                linarith only [h1399, hlam, p1422_0]
                              · have p1422_0 := h1422c.1
                                have p1422_1 := h1422c.2.1
                                have p1422_2 := h1422c.2.2.1
                                have p1422_3 := h1422c.2.2.2
                                linarith only [h1403, hlam, p1422_1]
                              · have p1422_0 := h1422c.1
                                have p1422_1 := h1422c.2.1
                                have p1422_2 := h1422c.2.2.1
                                have p1422_3 := h1422c.2.2.2
                                linarith only [h1405, hlam, p1422_0]
                              · have p1422_0 := h1422c.1
                                have p1422_1 := h1422c.2.1
                                have p1422_2 := h1422c.2.2.1
                                have p1422_3 := h1422c.2.2.2
                                linarith only [h0, h1399, h1402, h1416, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1422_1]
                              · have p1422_0 := h1422c.1
                                have p1422_1 := h1422c.2.1
                                have p1422_2 := h1422c.2.2.1
                                have p1422_3 := h1422c.2.2.2
                                linarith only [hlam, p1422_0]
                        · linarith only [h1400, h1417, hc23, hlam, hphi, u3elo0]
                      · linarith only [h0, h1397, h1404, h1416, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h1397, h1400, h1404, h1405, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1469 | h1469
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1470 | h1470
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1471 | h1471
                      · linarith only [h1404, h1469, h1471, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1473 | h1473
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1474 | h1474
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1475 | h1475
                            · rcases h1bigk with h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [hlam, p1476_0]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [h0, hlam, p1476_0]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [h0, h1401, h1473, h1475, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1476_1]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [h0, h1401, h1404, h1473, h1475, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1476_1]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                rcases p1476_3 (m.d 0 1) (by simp) with h1481 | h1481
                                · rcases p1476_3 (m.d 1 2) (by simp) with h1482 | h1482
                                  · rcases p1476_3 (m.d 1 3) (by simp) with h1483 | h1483
                                    · linarith only [h1397, h1483, hlam]
                                    · linarith only [h1469, h1483, hlam]
                                  · linarith only [h1403, h1482, hlam]
                                · linarith only [h1481, hlam, p1476_0]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [h1397, h1401, h1473, h1475, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1476_1]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [hlam, p1476_0]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                rcases p1476_3 (m.d 0 1) (by simp) with h1490 | h1490
                                · linarith only [h0, h1490, hlam]
                                · linarith only [h1397, h1490, hlam]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                rcases p1476_3 (m.d 0 1) (by simp) with h1493 | h1493
                                · linarith only [h0, h1493, hlam]
                                · linarith only [h1398, h1493, hlam]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                rcases p1476_3 (m.d 0 1) (by simp) with h1496 | h1496
                                · linarith only [h0, h1496, hlam]
                                · linarith only [h1399, h1496, hlam]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [h1397, hlam, p1476_0]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [h1401, hlam, p1476_1]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [hlam, p1476_0]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [h1404, hlam, p1476_1]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [h1404, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1476_1, u3elo3]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [h1398, hlam, p1476_0]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [h1402, hlam, p1476_1]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [h0, h1398, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1476_1]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [hlam, p1476_0]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [h0, h1398, h1403, h1473, h1475, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1476_1]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [h1399, hlam, p1476_0]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [h1403, hlam, p1476_1]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [h1469, hlam, p1476_0]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [h1470, hlam, p1476_0]
                              · have p1476_0 := h1476c.1
                                have p1476_1 := h1476c.2.1
                                have p1476_2 := h1476c.2.2.1
                                have p1476_3 := h1476c.2.2.2
                                linarith only [hlam, p1476_0]
                            · linarith only [h0, h1398, h1401, h1404, h1470, h1473, h1475, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h0, h1398, h1470, h1471, h1473, h1474, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h1400, h1473, hc23, hlam, hphi, u3elo0]
                    · linarith only [h1404, h1469, h1470, hlam]
                  · linarith only [h1400, h1469, hc13, hlam, hphi, u3elo0]
              · linarith only [h0, h1399, h1403, hlam]
            · linarith only [h0, h1398, h1402, hlam]
          · linarith only [h0, h1401, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1522 | h1522
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1523 | h1523
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1524 | h1524
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1525 | h1525
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1526 | h1526
                  · linarith only [h0, h1397, h1400, h1526, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1528 | h1528
                    · linarith only [h1525, h1526, h1528, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1530 | h1530
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1531 | h1531
                        · linarith only [h1397, h1400, h1522, h1531, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1533 | h1533
                          · linarith only [h1523, h1528, h1533, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1535 | h1535
                            · linarith only [h1397, h1400, h1525, h1528, h1535, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                            · rcases h1bigk with h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [hlam, p1537_0]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [h0, hlam, p1537_0]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [h0, h1525, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1537_1]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                rcases p1537_3 (m.d 0 1) (by simp) with h1541 | h1541
                                · rcases p1537_3 (m.d 1 2) (by simp) with h1542 | h1542
                                  · rcases p1537_3 (m.d 1 3) (by simp) with h1543 | h1543
                                    · linarith only [h1397, h1543, hlam]
                                    · linarith only [h1525, h1543, hlam]
                                  · linarith only [h1523, h1542, hlam]
                                · linarith only [h1541, hlam, p1537_0]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [h0, h1522, h1526, h1530, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1537_1]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [h1397, h1522, h1530, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1537_1]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [hlam, p1537_0]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                rcases p1537_3 (m.d 0 1) (by simp) with h1551 | h1551
                                · linarith only [h0, h1551, hlam]
                                · linarith only [h1397, h1551, hlam]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                rcases p1537_3 (m.d 0 1) (by simp) with h1554 | h1554
                                · linarith only [h0, h1554, hlam]
                                · linarith only [h1398, h1554, hlam]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                rcases p1537_3 (m.d 0 1) (by simp) with h1557 | h1557
                                · linarith only [h0, h1557, hlam]
                                · linarith only [h1399, h1557, hlam]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [h1397, hlam, p1537_0]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [h1522, hlam, p1537_1]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [hlam, p1537_0]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [h0, h1399, h1526, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1537_1]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [h1526, hlam, p1537_1]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [h1398, hlam, p1537_0]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [h1523, hlam, p1537_1]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [h1525, hlam, p1537_0]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [hlam, p1537_0]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [h1528, hlam, p1537_1]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [h1399, hlam, p1537_0]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [h1524, hlam, p1537_1]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [h0, h1399, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1537_1]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [h0, h1399, h1523, h1530, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1537_1]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [hlam, p1537_0]
                      · linarith only [h1397, h1400, h1525, h1530, hc23, hlam, hphi, u3elo4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1576 | h1576
                  · linarith only [h1397, h1400, h1576, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1578 | h1578
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1579 | h1579
                      · linarith only [h1525, h1579, hc13, hlam, hphi, u3elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1581 | h1581
                        · linarith only [h1400, h1522, h1525, h1581, hc03, hlam, hphi, u3elo3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1583 | h1583
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1584 | h1584
                            · rcases h1bigk with h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c | h1585c
                              · have p1585_0 := h1585c.1
                                have p1585_1 := h1585c.2.1
                                have p1585_2 := h1585c.2.2.1
                                have p1585_3 := h1585c.2.2.2
                                linarith only [hlam, p1585_0]
                              · have p1585_0 := h1585c.1
                                have p1585_1 := h1585c.2.1
                                have p1585_2 := h1585c.2.2.1
                                have p1585_3 := h1585c.2.2.2
                                linarith only [h0, hlam, p1585_0]
                              · have p1585_0 := h1585c.1
                                have p1585_1 := h1585c.2.1
                                have p1585_2 := h1585c.2.2.1
                                have p1585_3 := h1585c.2.2.2
                                rcases p1585_3 (m.d 0 1) (by simp) with h1588 | h1588
                                · rcases p1585_3 (m.d 1 2) (by simp) with h1589 | h1589
                                  · rcases p1585_3 (m.d 1 3) (by simp) with h1590 | h1590
                                    · linarith only [h1590, hlam, p1585_0]
                                    · rcases p1585_3 (m.d 1 4) (by simp) with h1592 | h1592
                                      · linarith only [h1398, h1592, hlam]
                                      · linarith only [h1525, h1592, hlam]
                                  · linarith only [h1522, h1589, hlam]
                                · linarith only [h1588, hlam, p1585_0]
                              · have p1585_0 := h1585c.1
                                have p1585_1 := h1585c.2.1
                                have p1585_2 := h1585c.2.2.1
                                have p1585_3 := h1585c.2.2.2
                                linarith only [h0, h1578, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1585_1]
                              · have p1585_0 := h1585c.1
                                have p1585_1 := h1585c.2.1
                                have p1585_2 := h1585c.2.2.1
                                have p1585_3 := h1585c.2.2.2
                                rcases p1585_3 (m.d 0 1) (by simp) with h1598 | h1598
                                · rcases p1585_3 (m.d 1 2) (by simp) with h1599 | h1599
                                  · rcases p1585_3 (m.d 1 3) (by simp) with h1600 | h1600
                                    · linarith only [h1397, h1600, hlam]
                                    · rcases p1585_3 (m.d 1 4) (by simp) with h1602 | h1602
                                      · linarith only [h1398, h1602, hlam]
                                      · linarith only [h1578, h1602, hlam]
                                  · linarith only [h1524, h1599, hlam]
                                · linarith only [h1598, hlam, p1585_0]
                              · have p1585_0 := h1585c.1
                                have p1585_1 := h1585c.2.1
                                have p1585_2 := h1585c.2.2.1
                                have p1585_3 := h1585c.2.2.2
                                linarith only [h1398, h1523, h1583, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1585_1]
                              · have p1585_0 := h1585c.1
                                have p1585_1 := h1585c.2.1
                                have p1585_2 := h1585c.2.2.1
                                have p1585_3 := h1585c.2.2.2
                                linarith only [hlam, p1585_0]
                              · have p1585_0 := h1585c.1
                                have p1585_1 := h1585c.2.1
                                have p1585_2 := h1585c.2.2.1
                                have p1585_3 := h1585c.2.2.2
                                rcases p1585_3 (m.d 0 1) (by simp) with h1609 | h1609
                                · linarith only [h0, h1609, hlam]
                                · linarith only [h1397, h1609, hlam]
                              · have p1585_0 := h1585c.1
                                have p1585_1 := h1585c.2.1
                                have p1585_2 := h1585c.2.2.1
                                have p1585_3 := h1585c.2.2.2
                                rcases p1585_3 (m.d 0 1) (by simp) with h1612 | h1612
                                · linarith only [h0, h1612, hlam]
                                · linarith only [h1398, h1612, hlam]
                              · have p1585_0 := h1585c.1
                                have p1585_1 := h1585c.2.1
                                have p1585_2 := h1585c.2.2.1
                                have p1585_3 := h1585c.2.2.2
                                rcases p1585_3 (m.d 0 1) (by simp) with h1615 | h1615
                                · linarith only [h0, h1615, hlam]
                                · linarith only [h1399, h1615, hlam]
                              · have p1585_0 := h1585c.1
                                have p1585_1 := h1585c.2.1
                                have p1585_2 := h1585c.2.2.1
                                have p1585_3 := h1585c.2.2.2
                                linarith only [h1397, hlam, p1585_0]
                              · have p1585_0 := h1585c.1
                                have p1585_1 := h1585c.2.1
                                have p1585_2 := h1585c.2.2.1
                                have p1585_3 := h1585c.2.2.2
                                linarith only [h1522, hlam, p1585_1]
                              · have p1585_0 := h1585c.1
                                have p1585_1 := h1585c.2.1
                                have p1585_2 := h1585c.2.2.1
                                have p1585_3 := h1585c.2.2.2
                                linarith only [hlam, p1585_0]
                              · have p1585_0 := h1585c.1
                                have p1585_1 := h1585c.2.1
                                have p1585_2 := h1585c.2.2.1
                                have p1585_3 := h1585c.2.2.2
                                linarith only [h1525, hlam, p1585_1]
                              · have p1585_0 := h1585c.1
                                have p1585_1 := h1585c.2.1
                                have p1585_2 := h1585c.2.2.1
                                have p1585_3 := h1585c.2.2.2
                                linarith only [h1576, hlam, p1585_1]
                              · have p1585_0 := h1585c.1
                                have p1585_1 := h1585c.2.1
                                have p1585_2 := h1585c.2.2.1
                                have p1585_3 := h1585c.2.2.2
                                linarith only [h1398, hlam, p1585_0]
                              · have p1585_0 := h1585c.1
                                have p1585_1 := h1585c.2.1
                                have p1585_2 := h1585c.2.2.1
                                have p1585_3 := h1585c.2.2.2
                                linarith only [h1523, hlam, p1585_1]
                              · have p1585_0 := h1585c.1
                                have p1585_1 := h1585c.2.1
                                have p1585_2 := h1585c.2.2.1
                                have p1585_3 := h1585c.2.2.2
                                linarith only [h0, h1398, h1522, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1585_1]
                              · have p1585_0 := h1585c.1
                                have p1585_1 := h1585c.2.1
                                have p1585_2 := h1585c.2.2.1
                                have p1585_3 := h1585c.2.2.2
                                linarith only [hlam, p1585_0]
                              · have p1585_0 := h1585c.1
                                have p1585_1 := h1585c.2.1
                                have p1585_2 := h1585c.2.2.1
                                have p1585_3 := h1585c.2.2.2
                                linarith only [h0, h1398, h1522, h1576, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1585_1]
                              · have p1585_0 := h1585c.1
                                have p1585_1 := h1585c.2.1
                                have p1585_2 := h1585c.2.2.1
                                have p1585_3 := h1585c.2.2.2
                                linarith only [h1399, hlam, p1585_0]
                              · have p1585_0 := h1585c.1
                                have p1585_1 := h1585c.2.1
                                have p1585_2 := h1585c.2.2.1
                                have p1585_3 := h1585c.2.2.2
                                linarith only [h1524, hlam, p1585_1]
                              · have p1585_0 := h1585c.1
                                have p1585_1 := h1585c.2.1
                                have p1585_2 := h1585c.2.2.1
                                have p1585_3 := h1585c.2.2.2
                                linarith only [h0, h1399, h1522, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1585_1]
                              · have p1585_0 := h1585c.1
                                have p1585_1 := h1585c.2.1
                                have p1585_2 := h1585c.2.2.1
                                have p1585_3 := h1585c.2.2.2
                                linarith only [h1578, hlam, p1585_0]
                              · have p1585_0 := h1585c.1
                                have p1585_1 := h1585c.2.1
                                have p1585_2 := h1585c.2.2.1
                                have p1585_3 := h1585c.2.2.2
                                linarith only [hlam, p1585_0]
                            · linarith only [h0, h1398, h1523, h1583, h1584, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h0, h1398, h1578, h1583, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1635 | h1635
                      · linarith only [h1522, h1525, h1635, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1637 | h1637
                        · linarith only [h1397, h1400, h1522, h1637, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1639 | h1639
                          · linarith only [h1523, h1578, h1639, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1641 | h1641
                            · linarith only [h1522, h1525, h1578, h1641, hc23, hlam, hphi, u3elo3]
                            · rcases h1bigk with h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c
                              · have p1643_0 := h1643c.1
                                have p1643_1 := h1643c.2.1
                                have p1643_2 := h1643c.2.2.1
                                have p1643_3 := h1643c.2.2.2
                                linarith only [hlam, p1643_0]
                              · have p1643_0 := h1643c.1
                                have p1643_1 := h1643c.2.1
                                have p1643_2 := h1643c.2.2.1
                                have p1643_3 := h1643c.2.2.2
                                linarith only [h0, hlam, p1643_0]
                              · have p1643_0 := h1643c.1
                                have p1643_1 := h1643c.2.1
                                have p1643_2 := h1643c.2.2.1
                                have p1643_3 := h1643c.2.2.2
                                rcases p1643_3 (m.d 0 1) (by simp) with h1646 | h1646
                                · rcases p1643_3 (m.d 1 2) (by simp) with h1647 | h1647
                                  · rcases p1643_3 (m.d 1 3) (by simp) with h1648 | h1648
                                    · linarith only [h1648, hlam, p1643_0]
                                    · rcases p1643_3 (m.d 1 4) (by simp) with h1650 | h1650
                                      · linarith only [h1398, h1650, hlam]
                                      · linarith only [h1525, h1650, hlam]
                                  · linarith only [h1522, h1647, hlam]
                                · linarith only [h1646, hlam, p1643_0]
                              · have p1643_0 := h1643c.1
                                have p1643_1 := h1643c.2.1
                                have p1643_2 := h1643c.2.2.1
                                have p1643_3 := h1643c.2.2.2
                                rcases p1643_3 (m.d 0 1) (by simp) with h1655 | h1655
                                · rcases p1643_3 (m.d 1 2) (by simp) with h1656 | h1656
                                  · rcases p1643_3 (m.d 1 3) (by simp) with h1657 | h1657
                                    · linarith only [h1397, h1657, hlam]
                                    · rcases p1643_3 (m.d 1 4) (by simp) with h1659 | h1659
                                      · linarith only [h1659, hlam, p1643_0]
                                      · rcases p1643_3 (m.d 1 5) (by simp) with h1661 | h1661
                                        · linarith only [h1399, h1661, hlam]
                                        · linarith only [h1578, h1661, hlam]
                                  · linarith only [h1523, h1656, hlam]
                                · linarith only [h1655, hlam, p1643_0]
                              · have p1643_0 := h1643c.1
                                have p1643_1 := h1643c.2.1
                                have p1643_2 := h1643c.2.2.1
                                have p1643_3 := h1643c.2.2.2
                                rcases p1643_3 (m.d 0 1) (by simp) with h1666 | h1666
                                · rcases p1643_3 (m.d 1 2) (by simp) with h1667 | h1667
                                  · rcases p1643_3 (m.d 1 3) (by simp) with h1668 | h1668
                                    · linarith only [h1397, h1668, hlam]
                                    · rcases p1643_3 (m.d 1 4) (by simp) with h1670 | h1670
                                      · linarith only [h1398, h1670, hlam]
                                      · rcases p1643_3 (m.d 1 5) (by simp) with h1672 | h1672
                                        · linarith only [h1672, hlam, p1643_0]
                                        · rcases h1emin with h1674 | h1674 | h1674 | h1674 | h1674
                                          · linarith only [h0, h1674, hc12, hlam]
                                          · rcases h3bigk with h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c
                                            · have p1676_0 := h1676c.1
                                              have p1676_1 := h1676c.2.1
                                              have p1676_2 := h1676c.2.2.1
                                              have p1676_3 := h1676c.2.2.2
                                              linarith only [hlam, p1676_0]
                                            · have p1676_0 := h1676c.1
                                              have p1676_1 := h1676c.2.1
                                              have p1676_2 := h1676c.2.2.1
                                              have p1676_3 := h1676c.2.2.2
                                              linarith only [h1400, h1522, hc23, hlam, hphi, p1676_1, u3elo4]
                                            · have p1676_0 := h1676c.1
                                              have p1676_1 := h1676c.2.1
                                              have p1676_2 := h1676c.2.2.1
                                              have p1676_3 := h1676c.2.2.2
                                              linarith only [h1400, hc23, hlam, hphi, p1676_1, u3elo4]
                                            · have p1676_0 := h1676c.1
                                              have p1676_1 := h1676c.2.1
                                              have p1676_2 := h1676c.2.2.1
                                              have p1676_3 := h1676c.2.2.2
                                              linarith only [h1400, h1522, h1525, hc23, hlam, hphi, p1676_1, u3elo4]
                                            · have p1676_0 := h1676c.1
                                              have p1676_1 := h1676c.2.1
                                              have p1676_2 := h1676c.2.2.1
                                              have p1676_3 := h1676c.2.2.2
                                              linarith only [h1400, hlam, p1676_0]
                                            · have p1676_0 := h1676c.1
                                              have p1676_1 := h1676c.2.1
                                              have p1676_2 := h1676c.2.2.1
                                              have p1676_3 := h1676c.2.2.2
                                              linarith only [h1397, hlam, p1676_0]
                                            · have p1676_0 := h1676c.1
                                              have p1676_1 := h1676c.2.1
                                              have p1676_2 := h1676c.2.2.1
                                              have p1676_3 := h1676c.2.2.2
                                              linarith only [hlam, p1676_0]
                                            · have p1676_0 := h1676c.1
                                              have p1676_1 := h1676c.2.1
                                              have p1676_2 := h1676c.2.2.1
                                              have p1676_3 := h1676c.2.2.2
                                              linarith only [h1525, hc23, hlam, hphi, p1676_1, u3elo3]
                                            · have p1676_0 := h1676c.1
                                              have p1676_1 := h1676c.2.1
                                              have p1676_2 := h1676c.2.2.1
                                              have p1676_3 := h1676c.2.2.2
                                              linarith only [h1525, hlam, p1676_0]
                                            · have p1676_0 := h1676c.1
                                              have p1676_1 := h1676c.2.1
                                              have p1676_2 := h1676c.2.2.1
                                              have p1676_3 := h1676c.2.2.2
                                              linarith only [h1576, hlam, p1676_0]
                                            · have p1676_0 := h1676c.1
                                              have p1676_1 := h1676c.2.1
                                              have p1676_2 := h1676c.2.2.1
                                              have p1676_3 := h1676c.2.2.2
                                              linarith only [hc03, hlam, hphi, p1676_1, u3elo2]
                                            · have p1676_0 := h1676c.1
                                              have p1676_1 := h1676c.2.1
                                              have p1676_2 := h1676c.2.2.1
                                              have p1676_3 := h1676c.2.2.2
                                              linarith only [h1522, hlam, p1676_0]
                                            · have p1676_0 := h1676c.1
                                              have p1676_1 := h1676c.2.1
                                              have p1676_2 := h1676c.2.2.1
                                              have p1676_3 := h1676c.2.2.2
                                              linarith only [hlam, p1676_0]
                                            · have p1676_0 := h1676c.1
                                              have p1676_1 := h1676c.2.1
                                              have p1676_2 := h1676c.2.2.1
                                              have p1676_3 := h1676c.2.2.2
                                              linarith only [h1635, hlam, p1676_0]
                                            · have p1676_0 := h1676c.1
                                              have p1676_1 := h1676c.2.1
                                              have p1676_2 := h1676c.2.2.1
                                              have p1676_3 := h1676c.2.2.2
                                              linarith only [h1637, hlam, p1676_0]
                                            · have p1676_0 := h1676c.1
                                              have p1676_1 := h1676c.2.1
                                              have p1676_2 := h1676c.2.2.1
                                              have p1676_3 := h1676c.2.2.2
                                              linarith only [h1641, hc03, hc45, hlam, hphi, ht34, p1676_1]
                                            · have p1676_0 := h1676c.1
                                              have p1676_1 := h1676c.2.1
                                              have p1676_2 := h1676c.2.2.1
                                              have p1676_3 := h1676c.2.2.2
                                              linarith only [h1522, h1641, hc23, hc45, hlam, hphi, ht34, p1676_1]
                                            · have p1676_0 := h1676c.1
                                              have p1676_1 := h1676c.2.1
                                              have p1676_2 := h1676c.2.2.1
                                              have p1676_3 := h1676c.2.2.2
                                              linarith only [h1641, hc23, hc45, hlam, hphi, ht34, p1676_1]
                                            · have p1676_0 := h1676c.1
                                              have p1676_1 := h1676c.2.1
                                              have p1676_2 := h1676c.2.2.1
                                              have p1676_3 := h1676c.2.2.2
                                              linarith only [hlam, p1676_0]
                                            · have p1676_0 := h1676c.1
                                              have p1676_1 := h1676c.2.1
                                              have p1676_2 := h1676c.2.2.1
                                              have p1676_3 := h1676c.2.2.2
                                              linarith only [h1641, hlam, p1676_1]
                                            · have p1676_0 := h1676c.1
                                              have p1676_1 := h1676c.2.1
                                              have p1676_2 := h1676c.2.2.1
                                              have p1676_3 := h1676c.2.2.2
                                              linarith only [h1397, h1522, hc23, hlam, hphi, p1676_1, u3elo4]
                                            · have p1676_0 := h1676c.1
                                              have p1676_1 := h1676c.2.1
                                              have p1676_2 := h1676c.2.2.1
                                              have p1676_3 := h1676c.2.2.2
                                              linarith only [h1522, hc23, hlam, hphi, p1676_1, u3elo4]
                                            · have p1676_0 := h1676c.1
                                              have p1676_1 := h1676c.2.1
                                              have p1676_2 := h1676c.2.2.1
                                              have p1676_3 := h1676c.2.2.2
                                              linarith only [hc23, hlam, hphi, p1676_1, u3elo4]
                                            · have p1676_0 := h1676c.1
                                              have p1676_1 := h1676c.2.1
                                              have p1676_2 := h1676c.2.2.1
                                              have p1676_3 := h1676c.2.2.2
                                              linarith only [h1522, h1525, hc23, hlam, hphi, p1676_1, u3elo4]
                                            · have p1676_0 := h1676c.1
                                              have p1676_1 := h1676c.2.1
                                              have p1676_2 := h1676c.2.2.1
                                              have p1676_3 := h1676c.2.2.2
                                              linarith only [hlam, p1676_0]
                                          · linarith only [h1397, h1674, hlam, ht12, ht23, u3elo0]
                                          · linarith only [h0, h1578, h1674, hc12, hlam, p1643_1]
                                          · linarith only [h0, h1674, hc12, hlam, p1643_1]
                                  · linarith only [h1524, h1667, hlam]
                                · linarith only [h1666, hlam, p1643_0]
                              · have p1643_0 := h1643c.1
                                have p1643_1 := h1643c.2.1
                                have p1643_2 := h1643c.2.2.1
                                have p1643_3 := h1643c.2.2.2
                                rcases p1643_3 (m.d 0 1) (by simp) with h1707 | h1707
                                · linarith only [h1707, hlam, p1643_0]
                                · rcases p1643_3 (m.d 1 2) (by simp) with h1709 | h1709
                                  · rcases p1643_3 (m.d 1 3) (by simp) with h1710 | h1710
                                    · linarith only [h1522, h1710, hlam]
                                    · rcases p1643_3 (m.d 1 4) (by simp) with h1712 | h1712
                                      · linarith only [h1523, h1712, hlam]
                                      · rcases p1643_3 (m.d 1 5) (by simp) with h1714 | h1714
                                        · linarith only [h1524, h1714, hlam]
                                        · rcases h1emin with h1716 | h1716 | h1716 | h1716 | h1716
                                          · linarith only [h1716, hc12, hlam, p1643_1]
                                          · rcases h3bigk with h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c
                                            · have p1718_0 := h1718c.1
                                              have p1718_1 := h1718c.2.1
                                              have p1718_2 := h1718c.2.2.1
                                              have p1718_3 := h1718c.2.2.2
                                              linarith only [hlam, p1718_0]
                                            · have p1718_0 := h1718c.1
                                              have p1718_1 := h1718c.2.1
                                              have p1718_2 := h1718c.2.2.1
                                              have p1718_3 := h1718c.2.2.2
                                              linarith only [h1400, h1522, hc23, hlam, hphi, p1718_1, u3elo4]
                                            · have p1718_0 := h1718c.1
                                              have p1718_1 := h1718c.2.1
                                              have p1718_2 := h1718c.2.2.1
                                              have p1718_3 := h1718c.2.2.2
                                              linarith only [h1400, hc23, hlam, hphi, p1718_1, u3elo4]
                                            · have p1718_0 := h1718c.1
                                              have p1718_1 := h1718c.2.1
                                              have p1718_2 := h1718c.2.2.1
                                              have p1718_3 := h1718c.2.2.2
                                              linarith only [h1400, h1522, h1525, hc23, hlam, hphi, p1718_1, u3elo4]
                                            · have p1718_0 := h1718c.1
                                              have p1718_1 := h1718c.2.1
                                              have p1718_2 := h1718c.2.2.1
                                              have p1718_3 := h1718c.2.2.2
                                              linarith only [h1400, hlam, p1718_0]
                                            · have p1718_0 := h1718c.1
                                              have p1718_1 := h1718c.2.1
                                              have p1718_2 := h1718c.2.2.1
                                              have p1718_3 := h1718c.2.2.2
                                              linarith only [h1397, hlam, p1718_0]
                                            · have p1718_0 := h1718c.1
                                              have p1718_1 := h1718c.2.1
                                              have p1718_2 := h1718c.2.2.1
                                              have p1718_3 := h1718c.2.2.2
                                              linarith only [hlam, p1718_0]
                                            · have p1718_0 := h1718c.1
                                              have p1718_1 := h1718c.2.1
                                              have p1718_2 := h1718c.2.2.1
                                              have p1718_3 := h1718c.2.2.2
                                              linarith only [h1525, hc23, hlam, hphi, p1718_1, u3elo3]
                                            · have p1718_0 := h1718c.1
                                              have p1718_1 := h1718c.2.1
                                              have p1718_2 := h1718c.2.2.1
                                              have p1718_3 := h1718c.2.2.2
                                              linarith only [h1525, hlam, p1718_0]
                                            · have p1718_0 := h1718c.1
                                              have p1718_1 := h1718c.2.1
                                              have p1718_2 := h1718c.2.2.1
                                              have p1718_3 := h1718c.2.2.2
                                              linarith only [h1576, hlam, p1718_0]
                                            · have p1718_0 := h1718c.1
                                              have p1718_1 := h1718c.2.1
                                              have p1718_2 := h1718c.2.2.1
                                              have p1718_3 := h1718c.2.2.2
                                              linarith only [hc03, hlam, hphi, p1718_1, u3elo2]
                                            · have p1718_0 := h1718c.1
                                              have p1718_1 := h1718c.2.1
                                              have p1718_2 := h1718c.2.2.1
                                              have p1718_3 := h1718c.2.2.2
                                              linarith only [h1522, hlam, p1718_0]
                                            · have p1718_0 := h1718c.1
                                              have p1718_1 := h1718c.2.1
                                              have p1718_2 := h1718c.2.2.1
                                              have p1718_3 := h1718c.2.2.2
                                              linarith only [hlam, p1718_0]
                                            · have p1718_0 := h1718c.1
                                              have p1718_1 := h1718c.2.1
                                              have p1718_2 := h1718c.2.2.1
                                              have p1718_3 := h1718c.2.2.2
                                              linarith only [h1635, hlam, p1718_0]
                                            · have p1718_0 := h1718c.1
                                              have p1718_1 := h1718c.2.1
                                              have p1718_2 := h1718c.2.2.1
                                              have p1718_3 := h1718c.2.2.2
                                              linarith only [h1637, hlam, p1718_0]
                                            · have p1718_0 := h1718c.1
                                              have p1718_1 := h1718c.2.1
                                              have p1718_2 := h1718c.2.2.1
                                              have p1718_3 := h1718c.2.2.2
                                              linarith only [h1641, hc03, hc45, hlam, hphi, ht34, p1718_1]
                                            · have p1718_0 := h1718c.1
                                              have p1718_1 := h1718c.2.1
                                              have p1718_2 := h1718c.2.2.1
                                              have p1718_3 := h1718c.2.2.2
                                              linarith only [h1522, h1641, hc23, hc45, hlam, hphi, ht34, p1718_1]
                                            · have p1718_0 := h1718c.1
                                              have p1718_1 := h1718c.2.1
                                              have p1718_2 := h1718c.2.2.1
                                              have p1718_3 := h1718c.2.2.2
                                              linarith only [h1641, hc23, hc45, hlam, hphi, ht34, p1718_1]
                                            · have p1718_0 := h1718c.1
                                              have p1718_1 := h1718c.2.1
                                              have p1718_2 := h1718c.2.2.1
                                              have p1718_3 := h1718c.2.2.2
                                              linarith only [hlam, p1718_0]
                                            · have p1718_0 := h1718c.1
                                              have p1718_1 := h1718c.2.1
                                              have p1718_2 := h1718c.2.2.1
                                              have p1718_3 := h1718c.2.2.2
                                              linarith only [h1641, hlam, p1718_1]
                                            · have p1718_0 := h1718c.1
                                              have p1718_1 := h1718c.2.1
                                              have p1718_2 := h1718c.2.2.1
                                              have p1718_3 := h1718c.2.2.2
                                              linarith only [h1397, h1522, hc23, hlam, hphi, p1718_1, u3elo4]
                                            · have p1718_0 := h1718c.1
                                              have p1718_1 := h1718c.2.1
                                              have p1718_2 := h1718c.2.2.1
                                              have p1718_3 := h1718c.2.2.2
                                              linarith only [h1522, hc23, hlam, hphi, p1718_1, u3elo4]
                                            · have p1718_0 := h1718c.1
                                              have p1718_1 := h1718c.2.1
                                              have p1718_2 := h1718c.2.2.1
                                              have p1718_3 := h1718c.2.2.2
                                              linarith only [hc23, hlam, hphi, p1718_1, u3elo4]
                                            · have p1718_0 := h1718c.1
                                              have p1718_1 := h1718c.2.1
                                              have p1718_2 := h1718c.2.2.1
                                              have p1718_3 := h1718c.2.2.2
                                              linarith only [h1522, h1525, hc23, hlam, hphi, p1718_1, u3elo4]
                                            · have p1718_0 := h1718c.1
                                              have p1718_1 := h1718c.2.1
                                              have p1718_2 := h1718c.2.2.1
                                              have p1718_3 := h1718c.2.2.2
                                              linarith only [hlam, p1718_0]
                                          · linarith only [h1397, h1716, hlam, ht12, ht23, u3elo0]
                                          · linarith only [h1399, h1578, h1716, hc12, hlam, p1643_1]
                                          · linarith only [h1399, h1716, hc12, hlam, p1643_1]
                                  · linarith only [h1709, hlam, p1643_0]
                              · have p1643_0 := h1643c.1
                                have p1643_1 := h1643c.2.1
                                have p1643_2 := h1643c.2.2.1
                                have p1643_3 := h1643c.2.2.2
                                linarith only [hlam, p1643_0]
                              · have p1643_0 := h1643c.1
                                have p1643_1 := h1643c.2.1
                                have p1643_2 := h1643c.2.2.1
                                have p1643_3 := h1643c.2.2.2
                                rcases p1643_3 (m.d 0 1) (by simp) with h1749 | h1749
                                · linarith only [h0, h1749, hlam]
                                · linarith only [h1397, h1749, hlam]
                              · have p1643_0 := h1643c.1
                                have p1643_1 := h1643c.2.1
                                have p1643_2 := h1643c.2.2.1
                                have p1643_3 := h1643c.2.2.2
                                rcases p1643_3 (m.d 0 1) (by simp) with h1752 | h1752
                                · linarith only [h0, h1752, hlam]
                                · linarith only [h1398, h1752, hlam]
                              · have p1643_0 := h1643c.1
                                have p1643_1 := h1643c.2.1
                                have p1643_2 := h1643c.2.2.1
                                have p1643_3 := h1643c.2.2.2
                                rcases p1643_3 (m.d 0 1) (by simp) with h1755 | h1755
                                · linarith only [h0, h1755, hlam]
                                · linarith only [h1399, h1755, hlam]
                              · have p1643_0 := h1643c.1
                                have p1643_1 := h1643c.2.1
                                have p1643_2 := h1643c.2.2.1
                                have p1643_3 := h1643c.2.2.2
                                linarith only [h1397, hlam, p1643_0]
                              · have p1643_0 := h1643c.1
                                have p1643_1 := h1643c.2.1
                                have p1643_2 := h1643c.2.2.1
                                have p1643_3 := h1643c.2.2.2
                                linarith only [h1522, hlam, p1643_1]
                              · have p1643_0 := h1643c.1
                                have p1643_1 := h1643c.2.1
                                have p1643_2 := h1643c.2.2.1
                                have p1643_3 := h1643c.2.2.2
                                linarith only [hlam, p1643_0]
                              · have p1643_0 := h1643c.1
                                have p1643_1 := h1643c.2.1
                                have p1643_2 := h1643c.2.2.1
                                have p1643_3 := h1643c.2.2.2
                                linarith only [h1525, hlam, p1643_1]
                              · have p1643_0 := h1643c.1
                                have p1643_1 := h1643c.2.1
                                have p1643_2 := h1643c.2.2.1
                                have p1643_3 := h1643c.2.2.2
                                linarith only [h1576, hlam, p1643_1]
                              · have p1643_0 := h1643c.1
                                have p1643_1 := h1643c.2.1
                                have p1643_2 := h1643c.2.2.1
                                have p1643_3 := h1643c.2.2.2
                                linarith only [h1398, hlam, p1643_0]
                              · have p1643_0 := h1643c.1
                                have p1643_1 := h1643c.2.1
                                have p1643_2 := h1643c.2.2.1
                                have p1643_3 := h1643c.2.2.2
                                linarith only [h1523, hlam, p1643_1]
                              · have p1643_0 := h1643c.1
                                have p1643_1 := h1643c.2.1
                                have p1643_2 := h1643c.2.2.1
                                have p1643_3 := h1643c.2.2.2
                                linarith only [h0, h1399, h1578, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1643_1]
                              · have p1643_0 := h1643c.1
                                have p1643_1 := h1643c.2.1
                                have p1643_2 := h1643c.2.2.1
                                have p1643_3 := h1643c.2.2.2
                                linarith only [hlam, p1643_0]
                              · have p1643_0 := h1643c.1
                                have p1643_1 := h1643c.2.1
                                have p1643_2 := h1643c.2.2.1
                                have p1643_3 := h1643c.2.2.2
                                linarith only [h1578, hlam, p1643_1]
                              · have p1643_0 := h1643c.1
                                have p1643_1 := h1643c.2.1
                                have p1643_2 := h1643c.2.2.1
                                have p1643_3 := h1643c.2.2.2
                                linarith only [h1399, hlam, p1643_0]
                              · have p1643_0 := h1643c.1
                                have p1643_1 := h1643c.2.1
                                have p1643_2 := h1643c.2.2.1
                                have p1643_3 := h1643c.2.2.2
                                linarith only [h1524, hlam, p1643_1]
                              · have p1643_0 := h1643c.1
                                have p1643_1 := h1643c.2.1
                                have p1643_2 := h1643c.2.2.1
                                have p1643_3 := h1643c.2.2.2
                                linarith only [h0, h1399, h1522, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1643_1]
                              · have p1643_0 := h1643c.1
                                have p1643_1 := h1643c.2.1
                                have p1643_2 := h1643c.2.2.1
                                have p1643_3 := h1643c.2.2.2
                                linarith only [h0, h1399, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1643_1]
                              · have p1643_0 := h1643c.1
                                have p1643_1 := h1643c.2.1
                                have p1643_2 := h1643c.2.2.1
                                have p1643_3 := h1643c.2.2.2
                                linarith only [hlam, p1643_0]
              · linarith only [h0, h1399, h1524, hlam]
            · linarith only [h0, h1398, h1523, hlam]
          · linarith only [h0, h1522, hc01, hlam, hphi, ht12, ht23, u3elo2]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1776 | h1776
        · linarith only [h1397, h1399, h1776, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1778 | h1778
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1779 | h1779
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1780 | h1780
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1781 | h1781
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1782 | h1782
                  · linarith only [h1397, h1399, h1776, h1780, h1782, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h1397, h1399, h1782, hc13, hlam, hphi, u3elo4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1785 | h1785
                  · linarith only [h1398, h1399, h1776, h1781, h1785, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h1398, h1399, h1781, h1785, hc13, hlam, hphi, u3elo4]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1788 | h1788
                · linarith only [h0, h1397, h1780, h1788, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1790 | h1790
                  · linarith only [h0, h1398, h1776, h1780, h1788, h1790, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h0, h1397, h1778, h1780, h1790, hc23, hlam, hphi, u3elo4]
            · linarith only [h0, h1398, h1779, hlam]
          · linarith only [h0, h1778, hc01, hlam, hphi, ht12, ht23, u3elo2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1795 | h1795
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1796 | h1796
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1797 | h1797
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1798 | h1798
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1799 | h1799
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1800 | h1800
                · linarith only [h1397, h1398, h1800, hlam]
                · linarith only [h1397, h1398, h1800, hc13, hlam, hphi, u3elo3]
              · linarith only [h1398, h1795, h1798, h1799, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1804 | h1804
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1805 | h1805
                · linarith only [h0, h1397, h1798, h1805, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h1397, h1798, h1805, hc13, hlam, hphi, u3elo3]
              · linarith only [h0, h1795, h1804, hlam]
          · linarith only [h0, h1797, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1810 | h1810
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1811 | h1811
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1812 | h1812
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1813 | h1813
                · linarith only [h1397, h1398, h1813, hlam]
                · linarith only [h1397, h1398, h1813, hc13, hlam, hphi, u3elo3]
              · linarith only [h1398, h1795, h1811, h1812, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1817 | h1817
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1818 | h1818
                · linarith only [h0, h1397, h1811, h1818, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h1397, h1810, h1811, h1818, hc23, hlam, hphi, u3elo3]
              · linarith only [h0, h1795, h1817, hlam]
          · linarith only [h0, h1810, hc01, hlam, hphi, ht12, ht23, u3elo2]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1823 | h1823
        · linarith only [h1397, h1795, h1823, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1825 | h1825
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1826 | h1826
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1827 | h1827
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1828 | h1828
                · linarith only [h1397, h1398, h1828, hlam]
                · linarith only [h1397, h1398, h1828, hc13, hlam, hphi, u3elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1831 | h1831
                · linarith only [h1397, h1398, h1826, h1827, h1831, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h1397, h1398, h1825, h1831, hc23, hlam, hphi, u3elo3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1834 | h1834
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1835 | h1835
                · linarith only [h0, h1397, h1826, h1835, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h1397, h1795, h1825, h1826, h1834, h1835, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1838 | h1838
                · linarith only [h0, h1397, h1826, h1838, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h1397, h1825, h1826, h1838, hc23, hlam, hphi, u3elo3]
          · linarith only [h0, h1825, hc01, hlam, hphi, ht12, ht23, u3elo2]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1842 | h1842
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1843 | h1843
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1844 | h1844
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1845 | h1845
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1846 | h1846
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1847 | h1847
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1848 | h1848
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1849 | h1849
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1850 | h1850
                    · linarith only [h1397, h1842, h1850, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1852 | h1852
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1853 | h1853
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1854 | h1854
                          · linarith only [h1846, h1850, h1854, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1856 | h1856
                            · linarith only [h1846, h1850, h1852, h1856, hlam]
                            · rcases h1bigk with h1858c | h1858c | h1858c | h1858c | h1858c | h1858c | h1858c | h1858c | h1858c | h1858c | h1858c | h1858c | h1858c | h1858c | h1858c | h1858c | h1858c | h1858c | h1858c | h1858c | h1858c | h1858c | h1858c | h1858c | h1858c
                              · have p1858_0 := h1858c.1
                                have p1858_1 := h1858c.2.1
                                have p1858_2 := h1858c.2.2.1
                                have p1858_3 := h1858c.2.2.2
                                linarith only [hlam, p1858_0]
                              · have p1858_0 := h1858c.1
                                have p1858_1 := h1858c.2.1
                                have p1858_2 := h1858c.2.2.1
                                have p1858_3 := h1858c.2.2.2
                                linarith only [h0, hlam, p1858_0]
                              · have p1858_0 := h1858c.1
                                have p1858_1 := h1858c.2.1
                                have p1858_2 := h1858c.2.2.1
                                have p1858_3 := h1858c.2.2.2
                                linarith only [h1397, hlam, p1858_0]
                              · have p1858_0 := h1858c.1
                                have p1858_1 := h1858c.2.1
                                have p1858_2 := h1858c.2.2.1
                                have p1858_3 := h1858c.2.2.2
                                linarith only [h1397, h1846, h1852, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1858_1, u3elo1]
                              · have p1858_0 := h1858c.1
                                have p1858_1 := h1858c.2.1
                                have p1858_2 := h1858c.2.2.1
                                have p1858_3 := h1858c.2.2.2
                                linarith only [h1397, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1858_1, u3elo1]
                              · have p1858_0 := h1858c.1
                                have p1858_1 := h1858c.2.1
                                have p1858_2 := h1858c.2.2.1
                                have p1858_3 := h1858c.2.2.2
                                rcases p1858_3 (m.d 0 1) (by simp) with h1864 | h1864
                                · linarith only [h1864, hlam, p1858_0]
                                · rcases p1858_3 (m.d 1 2) (by simp) with h1866 | h1866
                                  · rcases p1858_3 (m.d 1 3) (by simp) with h1867 | h1867
                                    · linarith only [h1845, h1867, hlam]
                                    · linarith only [h1397, h1867, hlam]
                                  · linarith only [h1866, hlam, p1858_0]
                              · have p1858_0 := h1858c.1
                                have p1858_1 := h1858c.2.1
                                have p1858_2 := h1858c.2.2.1
                                have p1858_3 := h1858c.2.2.2
                                linarith only [hlam, p1858_0]
                              · have p1858_0 := h1858c.1
                                have p1858_1 := h1858c.2.1
                                have p1858_2 := h1858c.2.2.1
                                have p1858_3 := h1858c.2.2.2
                                linarith only [h1397, hc01, hc12, hlam, hphi, p1858_1]
                              · have p1858_0 := h1858c.1
                                have p1858_1 := h1858c.2.1
                                have p1858_2 := h1858c.2.2.1
                                have p1858_3 := h1858c.2.2.2
                                rcases p1858_3 (m.d 0 1) (by simp) with h1873 | h1873
                                · linarith only [h0, h1873, hlam]
                                · linarith only [h1842, h1873, hlam]
                              · have p1858_0 := h1858c.1
                                have p1858_1 := h1858c.2.1
                                have p1858_2 := h1858c.2.2.1
                                have p1858_3 := h1858c.2.2.2
                                rcases p1858_3 (m.d 0 1) (by simp) with h1876 | h1876
                                · linarith only [h0, h1876, hlam]
                                · linarith only [h1843, h1876, hlam]
                              · have p1858_0 := h1858c.1
                                have p1858_1 := h1858c.2.1
                                have p1858_2 := h1858c.2.2.1
                                have p1858_3 := h1858c.2.2.2
                                linarith only [h1843, h1846, h1850, h1852, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1858_1, u3elo1]
                              · have p1858_0 := h1858c.1
                                have p1858_1 := h1858c.2.1
                                have p1858_2 := h1858c.2.2.1
                                have p1858_3 := h1858c.2.2.2
                                linarith only [h1845, hlam, p1858_1]
                              · have p1858_0 := h1858c.1
                                have p1858_1 := h1858c.2.1
                                have p1858_2 := h1858c.2.2.1
                                have p1858_3 := h1858c.2.2.2
                                linarith only [hlam, p1858_0]
                              · have p1858_0 := h1858c.1
                                have p1858_1 := h1858c.2.1
                                have p1858_2 := h1858c.2.2.1
                                have p1858_3 := h1858c.2.2.2
                                rcases p1858_3 (m.d 0 1) (by simp) with h1882 | h1882
                                · linarith only [h1397, h1882, hlam]
                                · linarith only [h1842, h1882, hlam]
                              · have p1858_0 := h1858c.1
                                have p1858_1 := h1858c.2.1
                                have p1858_2 := h1858c.2.2.1
                                have p1858_3 := h1858c.2.2.2
                                rcases p1858_3 (m.d 0 1) (by simp) with h1885 | h1885
                                · linarith only [h1397, h1885, hlam]
                                · linarith only [h1843, h1885, hlam]
                              · have p1858_0 := h1858c.1
                                have p1858_1 := h1858c.2.1
                                have p1858_2 := h1858c.2.2.1
                                have p1858_3 := h1858c.2.2.2
                                linarith only [h1842, hlam, p1858_0]
                              · have p1858_0 := h1858c.1
                                have p1858_1 := h1858c.2.1
                                have p1858_2 := h1858c.2.2.1
                                have p1858_3 := h1858c.2.2.2
                                linarith only [h1846, hlam, p1858_1]
                              · have p1858_0 := h1858c.1
                                have p1858_1 := h1858c.2.1
                                have p1858_2 := h1858c.2.2.1
                                have p1858_3 := h1858c.2.2.2
                                linarith only [h1848, hlam, p1858_0]
                              · have p1858_0 := h1858c.1
                                have p1858_1 := h1858c.2.1
                                have p1858_2 := h1858c.2.2.1
                                have p1858_3 := h1858c.2.2.2
                                linarith only [hlam, p1858_0]
                              · have p1858_0 := h1858c.1
                                have p1858_1 := h1858c.2.1
                                have p1858_2 := h1858c.2.2.1
                                have p1858_3 := h1858c.2.2.2
                                linarith only [h1850, hlam, p1858_1]
                              · have p1858_0 := h1858c.1
                                have p1858_1 := h1858c.2.1
                                have p1858_2 := h1858c.2.2.1
                                have p1858_3 := h1858c.2.2.2
                                linarith only [h1843, hlam, p1858_0]
                              · have p1858_0 := h1858c.1
                                have p1858_1 := h1858c.2.1
                                have p1858_2 := h1858c.2.2.1
                                have p1858_3 := h1858c.2.2.2
                                linarith only [h1847, hlam, p1858_1]
                              · have p1858_0 := h1858c.1
                                have p1858_1 := h1858c.2.1
                                have p1858_2 := h1858c.2.2.1
                                have p1858_3 := h1858c.2.2.2
                                linarith only [h1849, hlam, p1858_0]
                              · have p1858_0 := h1858c.1
                                have p1858_1 := h1858c.2.1
                                have p1858_2 := h1858c.2.2.1
                                have p1858_3 := h1858c.2.2.2
                                linarith only [h1397, h1843, h1846, h1852, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1858_1, u3elo0]
                              · have p1858_0 := h1858c.1
                                have p1858_1 := h1858c.2.1
                                have p1858_2 := h1858c.2.2.1
                                have p1858_3 := h1858c.2.2.2
                                linarith only [hlam, p1858_0]
                        · linarith only [h1397, h1844, h1853, hc23, hlam, hphi, u3elo1]
                      · linarith only [h1848, h1852, hc23, hlam, hphi, u3elo1]
                  · linarith only [h1397, h1842, h1846, h1849, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                · linarith only [h1397, h1842, h1846, h1848, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
              · linarith only [h1397, h1843, h1845, h1847, hlam]
            · linarith only [h1397, h1842, h1845, h1846, hlam]
          · linarith only [h0, h1845, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · linarith only [h1397, h1843, h1844, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1906 | h1906
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1907 | h1907
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1908 | h1908
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1909 | h1909
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1910 | h1910
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1911 | h1911
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1912 | h1912
                    · linarith only [h1842, h1843, h1911, h1912, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1914 | h1914
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1915 | h1915
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1916 | h1916
                          · linarith only [h1842, h1843, h1908, h1912, h1916, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1918 | h1918
                            · linarith only [h1842, h1843, h1908, h1912, h1914, h1918, hlam]
                            · rcases h1bigk with h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c | h1920c
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [hlam, p1920_0]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [h0, hlam, p1920_0]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [h1397, hlam, p1920_0]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [h1843, h1911, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1920_1, u3elo1]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [h1843, hlam, p1920_0]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                rcases p1920_3 (m.d 0 1) (by simp) with h1926 | h1926
                                · linarith only [h1926, hlam, p1920_0]
                                · rcases p1920_3 (m.d 1 2) (by simp) with h1928 | h1928
                                  · rcases p1920_3 (m.d 1 3) (by simp) with h1929 | h1929
                                    · linarith only [h1907, h1929, hlam]
                                    · linarith only [h1397, h1929, hlam]
                                  · linarith only [h1928, hlam, p1920_0]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [hlam, p1920_0]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [h1843, h1911, hc01, hc12, hlam, hphi, p1920_1]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                rcases p1920_3 (m.d 0 1) (by simp) with h1935 | h1935
                                · linarith only [h0, h1935, hlam]
                                · linarith only [h1842, h1935, hlam]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [h1842, h1843, h1908, h1914, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1920_1]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [h1842, h1908, h1914, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1920_1, u3elo1]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [h1907, hlam, p1920_1]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [hlam, p1920_0]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                rcases p1920_3 (m.d 0 1) (by simp) with h1942 | h1942
                                · linarith only [h1397, h1942, hlam]
                                · linarith only [h1842, h1942, hlam]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [h1842, h1843, h1908, h1914, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1920_1, u3elo1]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [h1842, hlam, p1920_0]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [h1908, hlam, p1920_1]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [h1910, hlam, p1920_0]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [hlam, p1920_0]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [h1912, hlam, p1920_1]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [h1842, h1908, h1912, h1914, hc34, hc45, hlam, hphi, p1920_1]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [h1909, hlam, p1920_1]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [h1911, hlam, p1920_0]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                rcases p1920_3 (m.d 0 1) (by simp) with h1954 | h1954
                                · linarith only [h1843, h1954, hlam]
                                · linarith only [h1842, h1954, hlam]
                              · have p1920_0 := h1920c.1
                                have p1920_1 := h1920c.2.1
                                have p1920_2 := h1920c.2.2.1
                                have p1920_3 := h1920c.2.2.2
                                linarith only [hlam, p1920_0]
                        · linarith only [h1906, h1915, hc23, hlam, hphi, u3elo0]
                      · linarith only [h1910, h1914, hc23, hlam, hphi, u3elo1]
                  · linarith only [h1397, h1906, h1911, hlam]
                · linarith only [h1397, h1842, h1908, h1910, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1962 | h1962
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1963 | h1963
                  · linarith only [h1907, h1909, h1963, hlam]
                  · linarith only [h1397, h1906, h1963, hlam]
                · linarith only [h1397, h1842, h1908, h1962, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
            · linarith only [h1397, h1842, h1907, h1908, hlam]
          · linarith only [h0, h1907, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1969 | h1969
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1970 | h1970
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1971 | h1971
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1972 | h1972
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1973 | h1973
                  · linarith only [h1906, h1973, hc03, hlam, hphi, u3elo1]
                  · linarith only [h1397, h1842, h1970, h1973, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                · linarith only [h1397, h1842, h1970, h1972, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1977 | h1977
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1978 | h1978
                  · linarith only [h1397, h1842, h1906, h1969, h1970, h1971, h1978, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h1397, h1842, h1970, h1978, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                · linarith only [h1397, h1842, h1970, h1977, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
            · linarith only [h1397, h1842, h1969, h1970, hc23, hlam, hphi, u3elo0]
          · linarith only [h0, h1969, hc01, hlam, hphi, ht12, ht23, u3elo2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1984 | h1984
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1985 | h1985
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1986 | h1986
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1987 | h1987
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1988 | h1988
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1989 | h1989
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1990 | h1990
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1991 | h1991
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1992 | h1992
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1993 | h1993
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1994 | h1994
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1995 | h1995
                            · rcases h1bigk with h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c | h1996c
                              · have p1996_0 := h1996c.1
                                have p1996_1 := h1996c.2.1
                                have p1996_2 := h1996c.2.2.1
                                have p1996_3 := h1996c.2.2.2
                                linarith only [hlam, p1996_0]
                              · have p1996_0 := h1996c.1
                                have p1996_1 := h1996c.2.1
                                have p1996_2 := h1996c.2.2.1
                                have p1996_3 := h1996c.2.2.2
                                linarith only [h0, hlam, p1996_0]
                              · have p1996_0 := h1996c.1
                                have p1996_1 := h1996c.2.1
                                have p1996_2 := h1996c.2.2.1
                                have p1996_3 := h1996c.2.2.2
                                linarith only [h1397, hlam, p1996_0]
                              · have p1996_0 := h1996c.1
                                have p1996_1 := h1996c.2.1
                                have p1996_2 := h1996c.2.2.1
                                have p1996_3 := h1996c.2.2.2
                                linarith only [h1842, hlam, p1996_0]
                              · have p1996_0 := h1996c.1
                                have p1996_1 := h1996c.2.1
                                have p1996_2 := h1996c.2.2.1
                                have p1996_3 := h1996c.2.2.2
                                linarith only [h1397, h1988, h1993, h1995, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1996_1, u3elo1]
                              · have p1996_0 := h1996c.1
                                have p1996_1 := h1996c.2.1
                                have p1996_2 := h1996c.2.2.1
                                have p1996_3 := h1996c.2.2.2
                                rcases p1996_3 (m.d 0 1) (by simp) with h2002 | h2002
                                · linarith only [h2002, hlam, p1996_0]
                                · rcases p1996_3 (m.d 1 2) (by simp) with h2004 | h2004
                                  · rcases p1996_3 (m.d 1 3) (by simp) with h2005 | h2005
                                    · linarith only [h1986, h2005, hlam]
                                    · linarith only [h1397, h2005, hlam]
                                  · linarith only [h2004, hlam, p1996_0]
                              · have p1996_0 := h1996c.1
                                have p1996_1 := h1996c.2.1
                                have p1996_2 := h1996c.2.2.1
                                have p1996_3 := h1996c.2.2.2
                                linarith only [hlam, p1996_0]
                              · have p1996_0 := h1996c.1
                                have p1996_1 := h1996c.2.1
                                have p1996_2 := h1996c.2.2.1
                                have p1996_3 := h1996c.2.2.2
                                linarith only [h1842, h1989, hc01, hc12, hlam, hphi, p1996_1]
                              · have p1996_0 := h1996c.1
                                have p1996_1 := h1996c.2.1
                                have p1996_2 := h1996c.2.2.1
                                have p1996_3 := h1996c.2.2.2
                                linarith only [h1842, h1984, h1988, h1993, h1995, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1996_1]
                              · have p1996_0 := h1996c.1
                                have p1996_1 := h1996c.2.1
                                have p1996_2 := h1996c.2.2.1
                                have p1996_3 := h1996c.2.2.2
                                rcases p1996_3 (m.d 0 1) (by simp) with h2012 | h2012
                                · linarith only [h0, h2012, hlam]
                                · linarith only [h1984, h2012, hlam]
                              · have p1996_0 := h1996c.1
                                have p1996_1 := h1996c.2.1
                                have p1996_2 := h1996c.2.2.1
                                have p1996_3 := h1996c.2.2.2
                                linarith only [h1984, h1988, h1993, h1995, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1996_1, u3elo1]
                              · have p1996_0 := h1996c.1
                                have p1996_1 := h1996c.2.1
                                have p1996_2 := h1996c.2.2.1
                                have p1996_3 := h1996c.2.2.2
                                linarith only [h1986, hlam, p1996_1]
                              · have p1996_0 := h1996c.1
                                have p1996_1 := h1996c.2.1
                                have p1996_2 := h1996c.2.2.1
                                have p1996_3 := h1996c.2.2.2
                                linarith only [hlam, p1996_0]
                              · have p1996_0 := h1996c.1
                                have p1996_1 := h1996c.2.1
                                have p1996_2 := h1996c.2.2.1
                                have p1996_3 := h1996c.2.2.2
                                linarith only [h1842, h1984, h1988, h1993, h1995, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1996_1, u3elo1]
                              · have p1996_0 := h1996c.1
                                have p1996_1 := h1996c.2.1
                                have p1996_2 := h1996c.2.2.1
                                have p1996_3 := h1996c.2.2.2
                                rcases p1996_3 (m.d 0 1) (by simp) with h2019 | h2019
                                · linarith only [h1397, h2019, hlam]
                                · linarith only [h1984, h2019, hlam]
                              · have p1996_0 := h1996c.1
                                have p1996_1 := h1996c.2.1
                                have p1996_2 := h1996c.2.2.1
                                have p1996_3 := h1996c.2.2.2
                                linarith only [h1984, h1988, h1989, h1993, h1995, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1996_1, u3elo1]
                              · have p1996_0 := h1996c.1
                                have p1996_1 := h1996c.2.1
                                have p1996_2 := h1996c.2.2.1
                                have p1996_3 := h1996c.2.2.2
                                linarith only [h1987, hlam, p1996_1]
                              · have p1996_0 := h1996c.1
                                have p1996_1 := h1996c.2.1
                                have p1996_2 := h1996c.2.2.1
                                have p1996_3 := h1996c.2.2.2
                                linarith only [h1989, hlam, p1996_0]
                              · have p1996_0 := h1996c.1
                                have p1996_1 := h1996c.2.1
                                have p1996_2 := h1996c.2.2.1
                                have p1996_3 := h1996c.2.2.2
                                linarith only [hlam, p1996_0]
                              · have p1996_0 := h1996c.1
                                have p1996_1 := h1996c.2.1
                                have p1996_2 := h1996c.2.2.1
                                have p1996_3 := h1996c.2.2.2
                                rcases p1996_3 (m.d 0 1) (by simp) with h2026 | h2026
                                · linarith only [h1842, h2026, hlam]
                                · linarith only [h1984, h2026, hlam]
                              · have p1996_0 := h1996c.1
                                have p1996_1 := h1996c.2.1
                                have p1996_2 := h1996c.2.2.1
                                have p1996_3 := h1996c.2.2.2
                                linarith only [h1984, hlam, p1996_0]
                              · have p1996_0 := h1996c.1
                                have p1996_1 := h1996c.2.1
                                have p1996_2 := h1996c.2.2.1
                                have p1996_3 := h1996c.2.2.2
                                linarith only [h1988, hlam, p1996_1]
                              · have p1996_0 := h1996c.1
                                have p1996_1 := h1996c.2.1
                                have p1996_2 := h1996c.2.2.1
                                have p1996_3 := h1996c.2.2.2
                                linarith only [h1990, hlam, p1996_0]
                              · have p1996_0 := h1996c.1
                                have p1996_1 := h1996c.2.1
                                have p1996_2 := h1996c.2.2.1
                                have p1996_3 := h1996c.2.2.2
                                linarith only [h1991, hlam, p1996_0]
                              · have p1996_0 := h1996c.1
                                have p1996_1 := h1996c.2.1
                                have p1996_2 := h1996c.2.2.1
                                have p1996_3 := h1996c.2.2.2
                                linarith only [hlam, p1996_0]
                            · linarith only [h1397, h1984, h1991, h1995, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                          · linarith only [h1842, h1984, h1989, h1991, h1994, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                        · linarith only [h1985, h1993, hc23, hlam, hphi, u3elo0]
                      · linarith only [h1989, h1992, hc23, hlam, hphi, u3elo1]
                    · linarith only [h1842, h1984, h1991, hlam]
                  · linarith only [h1842, h1989, h1990, hc01, hlam, hphi, ht12, ht23, u3elo4]
                · linarith only [h1397, h1989, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h1397, h1984, h1988, hc12, hlam, hphi, ht23, u3elo1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2042 | h2042
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2043 | h2043
                · linarith only [h1986, h1987, h2043, hlam]
                · linarith only [h1397, h2043, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h1397, h1984, h1986, h2042, hlam]
          · linarith only [h0, h1984, h1986, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
        · linarith only [h1397, h1984, h1985, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2049 | h2049
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2050 | h2050
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2051 | h2051
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2052 | h2052
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2053 | h2053
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2054 | h2054
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2055 | h2055
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2056 | h2056
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2057 | h2057
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2058 | h2058
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2059 | h2059
                            · rcases h1bigk with h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c
                              · have p2060_0 := h2060c.1
                                have p2060_1 := h2060c.2.1
                                have p2060_2 := h2060c.2.2.1
                                have p2060_3 := h2060c.2.2.2
                                linarith only [hlam, p2060_0]
                              · have p2060_0 := h2060c.1
                                have p2060_1 := h2060c.2.1
                                have p2060_2 := h2060c.2.2.1
                                have p2060_3 := h2060c.2.2.2
                                linarith only [h0, hlam, p2060_0]
                              · have p2060_0 := h2060c.1
                                have p2060_1 := h2060c.2.1
                                have p2060_2 := h2060c.2.2.1
                                have p2060_3 := h2060c.2.2.2
                                linarith only [h1397, hlam, p2060_0]
                              · have p2060_0 := h2060c.1
                                have p2060_1 := h2060c.2.1
                                have p2060_2 := h2060c.2.2.1
                                have p2060_3 := h2060c.2.2.2
                                linarith only [h1842, hlam, p2060_0]
                              · have p2060_0 := h2060c.1
                                have p2060_1 := h2060c.2.1
                                have p2060_2 := h2060c.2.2.1
                                have p2060_3 := h2060c.2.2.2
                                linarith only [h1984, hlam, p2060_0]
                              · have p2060_0 := h2060c.1
                                have p2060_1 := h2060c.2.1
                                have p2060_2 := h2060c.2.2.1
                                have p2060_3 := h2060c.2.2.2
                                rcases p2060_3 (m.d 0 1) (by simp) with h2066 | h2066
                                · linarith only [h2066, hlam, p2060_0]
                                · rcases p2060_3 (m.d 1 2) (by simp) with h2068 | h2068
                                  · rcases p2060_3 (m.d 1 3) (by simp) with h2069 | h2069
                                    · linarith only [h2050, h2069, hlam]
                                    · linarith only [h1397, h2069, hlam]
                                  · linarith only [h2068, hlam, p2060_0]
                              · have p2060_0 := h2060c.1
                                have p2060_1 := h2060c.2.1
                                have p2060_2 := h2060c.2.2.1
                                have p2060_3 := h2060c.2.2.2
                                linarith only [hlam, p2060_0]
                              · have p2060_0 := h2060c.1
                                have p2060_1 := h2060c.2.1
                                have p2060_2 := h2060c.2.2.1
                                have p2060_3 := h2060c.2.2.2
                                linarith only [h2050, h2056, h2059, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2060_1]
                              · have p2060_0 := h2060c.1
                                have p2060_1 := h2060c.2.1
                                have p2060_2 := h2060c.2.2.1
                                have p2060_3 := h2060c.2.2.2
                                linarith only [h1984, h2055, hc01, hc12, hlam, hphi, p2060_1]
                              · have p2060_0 := h2060c.1
                                have p2060_1 := h2060c.2.1
                                have p2060_2 := h2060c.2.2.1
                                have p2060_3 := h2060c.2.2.2
                                linarith only [h1984, hc01, hc12, hlam, hphi, p2060_1]
                              · have p2060_0 := h2060c.1
                                have p2060_1 := h2060c.2.1
                                have p2060_2 := h2060c.2.2.1
                                have p2060_3 := h2060c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, p2060_1, u3elo1]
                              · have p2060_0 := h2060c.1
                                have p2060_1 := h2060c.2.1
                                have p2060_2 := h2060c.2.2.1
                                have p2060_3 := h2060c.2.2.2
                                linarith only [h2050, hlam, p2060_1]
                              · have p2060_0 := h2060c.1
                                have p2060_1 := h2060c.2.1
                                have p2060_2 := h2060c.2.2.1
                                have p2060_3 := h2060c.2.2.2
                                linarith only [hlam, p2060_0]
                              · have p2060_0 := h2060c.1
                                have p2060_1 := h2060c.2.1
                                have p2060_2 := h2060c.2.2.1
                                have p2060_3 := h2060c.2.2.2
                                linarith only [h1842, hc01, hlam, hphi, ht12, ht23, p2060_1, u3elo1]
                              · have p2060_0 := h2060c.1
                                have p2060_1 := h2060c.2.1
                                have p2060_2 := h2060c.2.2.1
                                have p2060_3 := h2060c.2.2.2
                                linarith only [h1984, hc01, hlam, hphi, ht12, ht23, p2060_1, u3elo1]
                              · have p2060_0 := h2060c.1
                                have p2060_1 := h2060c.2.1
                                have p2060_2 := h2060c.2.2.1
                                have p2060_3 := h2060c.2.2.2
                                linarith only [h2053, hc01, hlam, hphi, ht12, ht23, p2060_1, u3elo1]
                              · have p2060_0 := h2060c.1
                                have p2060_1 := h2060c.2.1
                                have p2060_2 := h2060c.2.2.1
                                have p2060_3 := h2060c.2.2.2
                                linarith only [h2051, hlam, p2060_1]
                              · have p2060_0 := h2060c.1
                                have p2060_1 := h2060c.2.1
                                have p2060_2 := h2060c.2.2.1
                                have p2060_3 := h2060c.2.2.2
                                linarith only [h2053, hlam, p2060_0]
                              · have p2060_0 := h2060c.1
                                have p2060_1 := h2060c.2.1
                                have p2060_2 := h2060c.2.2.1
                                have p2060_3 := h2060c.2.2.2
                                linarith only [hlam, p2060_0]
                              · have p2060_0 := h2060c.1
                                have p2060_1 := h2060c.2.1
                                have p2060_2 := h2060c.2.2.1
                                have p2060_3 := h2060c.2.2.2
                                linarith only [h1984, h2053, hc01, hlam, hphi, ht12, ht23, p2060_1, u3elo1]
                              · have p2060_0 := h2060c.1
                                have p2060_1 := h2060c.2.1
                                have p2060_2 := h2060c.2.2.1
                                have p2060_3 := h2060c.2.2.2
                                linarith only [h2054, hc01, hlam, hphi, ht12, ht23, p2060_1, u3elo1]
                              · have p2060_0 := h2060c.1
                                have p2060_1 := h2060c.2.1
                                have p2060_2 := h2060c.2.2.1
                                have p2060_3 := h2060c.2.2.2
                                linarith only [h2052, hlam, p2060_1]
                              · have p2060_0 := h2060c.1
                                have p2060_1 := h2060c.2.1
                                have p2060_2 := h2060c.2.2.1
                                have p2060_3 := h2060c.2.2.2
                                linarith only [h2054, hlam, p2060_0]
                              · have p2060_0 := h2060c.1
                                have p2060_1 := h2060c.2.1
                                have p2060_2 := h2060c.2.2.1
                                have p2060_3 := h2060c.2.2.2
                                linarith only [h2055, hlam, p2060_0]
                              · have p2060_0 := h2060c.1
                                have p2060_1 := h2060c.2.1
                                have p2060_2 := h2060c.2.2.1
                                have p2060_3 := h2060c.2.2.2
                                linarith only [hlam, p2060_0]
                            · rcases h1bigk with h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c | h2092c
                              · have p2092_0 := h2092c.1
                                have p2092_1 := h2092c.2.1
                                have p2092_2 := h2092c.2.2.1
                                have p2092_3 := h2092c.2.2.2
                                linarith only [hlam, p2092_0]
                              · have p2092_0 := h2092c.1
                                have p2092_1 := h2092c.2.1
                                have p2092_2 := h2092c.2.2.1
                                have p2092_3 := h2092c.2.2.2
                                linarith only [h0, hlam, p2092_0]
                              · have p2092_0 := h2092c.1
                                have p2092_1 := h2092c.2.1
                                have p2092_2 := h2092c.2.2.1
                                have p2092_3 := h2092c.2.2.2
                                linarith only [h1397, hlam, p2092_0]
                              · have p2092_0 := h2092c.1
                                have p2092_1 := h2092c.2.1
                                have p2092_2 := h2092c.2.2.1
                                have p2092_3 := h2092c.2.2.2
                                linarith only [h1842, hlam, p2092_0]
                              · have p2092_0 := h2092c.1
                                have p2092_1 := h2092c.2.1
                                have p2092_2 := h2092c.2.2.1
                                have p2092_3 := h2092c.2.2.2
                                linarith only [h1984, hlam, p2092_0]
                              · have p2092_0 := h2092c.1
                                have p2092_1 := h2092c.2.1
                                have p2092_2 := h2092c.2.2.1
                                have p2092_3 := h2092c.2.2.2
                                rcases p2092_3 (m.d 0 1) (by simp) with h2098 | h2098
                                · linarith only [h2098, hlam, p2092_0]
                                · rcases p2092_3 (m.d 1 2) (by simp) with h2100 | h2100
                                  · rcases p2092_3 (m.d 1 3) (by simp) with h2101 | h2101
                                    · linarith only [h2050, h2101, hlam]
                                    · linarith only [h1397, h2101, hlam]
                                  · linarith only [h2100, hlam, p2092_0]
                              · have p2092_0 := h2092c.1
                                have p2092_1 := h2092c.2.1
                                have p2092_2 := h2092c.2.2.1
                                have p2092_3 := h2092c.2.2.2
                                linarith only [hlam, p2092_0]
                              · have p2092_0 := h2092c.1
                                have p2092_1 := h2092c.2.1
                                have p2092_2 := h2092c.2.2.1
                                have p2092_3 := h2092c.2.2.2
                                linarith only [h1397, hc01, hc12, hlam, hphi, p2092_1]
                              · have p2092_0 := h2092c.1
                                have p2092_1 := h2092c.2.1
                                have p2092_2 := h2092c.2.2.1
                                have p2092_3 := h2092c.2.2.2
                                linarith only [h1984, h2055, hc01, hc12, hlam, hphi, p2092_1]
                              · have p2092_0 := h2092c.1
                                have p2092_1 := h2092c.2.1
                                have p2092_2 := h2092c.2.2.1
                                have p2092_3 := h2092c.2.2.2
                                linarith only [h1984, hc01, hc12, hlam, hphi, p2092_1]
                              · have p2092_0 := h2092c.1
                                have p2092_1 := h2092c.2.1
                                have p2092_2 := h2092c.2.2.1
                                have p2092_3 := h2092c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, p2092_1, u3elo1]
                              · have p2092_0 := h2092c.1
                                have p2092_1 := h2092c.2.1
                                have p2092_2 := h2092c.2.2.1
                                have p2092_3 := h2092c.2.2.2
                                linarith only [h2050, hlam, p2092_1]
                              · have p2092_0 := h2092c.1
                                have p2092_1 := h2092c.2.1
                                have p2092_2 := h2092c.2.2.1
                                have p2092_3 := h2092c.2.2.2
                                linarith only [hlam, p2092_0]
                              · have p2092_0 := h2092c.1
                                have p2092_1 := h2092c.2.1
                                have p2092_2 := h2092c.2.2.1
                                have p2092_3 := h2092c.2.2.2
                                linarith only [h2051, h2058, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2092_1, u3elo1]
                              · have p2092_0 := h2092c.1
                                have p2092_1 := h2092c.2.1
                                have p2092_2 := h2092c.2.2.1
                                have p2092_3 := h2092c.2.2.2
                                linarith only [h1984, hc01, hlam, hphi, ht12, ht23, p2092_1, u3elo1]
                              · have p2092_0 := h2092c.1
                                have p2092_1 := h2092c.2.1
                                have p2092_2 := h2092c.2.2.1
                                have p2092_3 := h2092c.2.2.2
                                linarith only [h2053, hc01, hlam, hphi, ht12, ht23, p2092_1, u3elo1]
                              · have p2092_0 := h2092c.1
                                have p2092_1 := h2092c.2.1
                                have p2092_2 := h2092c.2.2.1
                                have p2092_3 := h2092c.2.2.2
                                linarith only [h2051, hlam, p2092_1]
                              · have p2092_0 := h2092c.1
                                have p2092_1 := h2092c.2.1
                                have p2092_2 := h2092c.2.2.1
                                have p2092_3 := h2092c.2.2.2
                                linarith only [h2053, hlam, p2092_0]
                              · have p2092_0 := h2092c.1
                                have p2092_1 := h2092c.2.1
                                have p2092_2 := h2092c.2.2.1
                                have p2092_3 := h2092c.2.2.2
                                linarith only [hlam, p2092_0]
                              · have p2092_0 := h2092c.1
                                have p2092_1 := h2092c.2.1
                                have p2092_2 := h2092c.2.2.1
                                have p2092_3 := h2092c.2.2.2
                                linarith only [h1984, h2053, hc01, hlam, hphi, ht12, ht23, p2092_1, u3elo1]
                              · have p2092_0 := h2092c.1
                                have p2092_1 := h2092c.2.1
                                have p2092_2 := h2092c.2.2.1
                                have p2092_3 := h2092c.2.2.2
                                linarith only [h2054, hc01, hlam, hphi, ht12, ht23, p2092_1, u3elo1]
                              · have p2092_0 := h2092c.1
                                have p2092_1 := h2092c.2.1
                                have p2092_2 := h2092c.2.2.1
                                have p2092_3 := h2092c.2.2.2
                                linarith only [h2052, hlam, p2092_1]
                              · have p2092_0 := h2092c.1
                                have p2092_1 := h2092c.2.1
                                have p2092_2 := h2092c.2.2.1
                                have p2092_3 := h2092c.2.2.2
                                linarith only [h2054, hlam, p2092_0]
                              · have p2092_0 := h2092c.1
                                have p2092_1 := h2092c.2.1
                                have p2092_2 := h2092c.2.2.1
                                have p2092_3 := h2092c.2.2.2
                                linarith only [h2055, hlam, p2092_0]
                              · have p2092_0 := h2092c.1
                                have p2092_1 := h2092c.2.1
                                have p2092_2 := h2092c.2.2.1
                                have p2092_3 := h2092c.2.2.2
                                linarith only [hlam, p2092_0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2124 | h2124
                            · linarith only [h2053, h2058, h2124, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · rcases h1bigk with h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c | h2126c
                              · have p2126_0 := h2126c.1
                                have p2126_1 := h2126c.2.1
                                have p2126_2 := h2126c.2.2.1
                                have p2126_3 := h2126c.2.2.2
                                linarith only [hlam, p2126_0]
                              · have p2126_0 := h2126c.1
                                have p2126_1 := h2126c.2.1
                                have p2126_2 := h2126c.2.2.1
                                have p2126_3 := h2126c.2.2.2
                                linarith only [h0, hlam, p2126_0]
                              · have p2126_0 := h2126c.1
                                have p2126_1 := h2126c.2.1
                                have p2126_2 := h2126c.2.2.1
                                have p2126_3 := h2126c.2.2.2
                                linarith only [h1397, hlam, p2126_0]
                              · have p2126_0 := h2126c.1
                                have p2126_1 := h2126c.2.1
                                have p2126_2 := h2126c.2.2.1
                                have p2126_3 := h2126c.2.2.2
                                linarith only [h1842, hlam, p2126_0]
                              · have p2126_0 := h2126c.1
                                have p2126_1 := h2126c.2.1
                                have p2126_2 := h2126c.2.2.1
                                have p2126_3 := h2126c.2.2.2
                                linarith only [h1984, hlam, p2126_0]
                              · have p2126_0 := h2126c.1
                                have p2126_1 := h2126c.2.1
                                have p2126_2 := h2126c.2.2.1
                                have p2126_3 := h2126c.2.2.2
                                rcases p2126_3 (m.d 0 1) (by simp) with h2132 | h2132
                                · linarith only [h2132, hlam, p2126_0]
                                · rcases p2126_3 (m.d 1 2) (by simp) with h2134 | h2134
                                  · rcases p2126_3 (m.d 1 3) (by simp) with h2135 | h2135
                                    · linarith only [h2050, h2135, hlam]
                                    · linarith only [h1397, h2135, hlam]
                                  · linarith only [h2134, hlam, p2126_0]
                              · have p2126_0 := h2126c.1
                                have p2126_1 := h2126c.2.1
                                have p2126_2 := h2126c.2.2.1
                                have p2126_3 := h2126c.2.2.2
                                linarith only [hlam, p2126_0]
                              · have p2126_0 := h2126c.1
                                have p2126_1 := h2126c.2.1
                                have p2126_2 := h2126c.2.2.1
                                have p2126_3 := h2126c.2.2.2
                                linarith only [h1397, hc01, hc12, hlam, hphi, p2126_1]
                              · have p2126_0 := h2126c.1
                                have p2126_1 := h2126c.2.1
                                have p2126_2 := h2126c.2.2.1
                                have p2126_3 := h2126c.2.2.2
                                linarith only [h1984, h2055, hc01, hc12, hlam, hphi, p2126_1]
                              · have p2126_0 := h2126c.1
                                have p2126_1 := h2126c.2.1
                                have p2126_2 := h2126c.2.2.1
                                have p2126_3 := h2126c.2.2.2
                                linarith only [h1984, hc01, hc12, hlam, hphi, p2126_1]
                              · have p2126_0 := h2126c.1
                                have p2126_1 := h2126c.2.1
                                have p2126_2 := h2126c.2.2.1
                                have p2126_3 := h2126c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, p2126_1, u3elo1]
                              · have p2126_0 := h2126c.1
                                have p2126_1 := h2126c.2.1
                                have p2126_2 := h2126c.2.2.1
                                have p2126_3 := h2126c.2.2.2
                                linarith only [h2050, hlam, p2126_1]
                              · have p2126_0 := h2126c.1
                                have p2126_1 := h2126c.2.1
                                have p2126_2 := h2126c.2.2.1
                                have p2126_3 := h2126c.2.2.2
                                linarith only [hlam, p2126_0]
                              · have p2126_0 := h2126c.1
                                have p2126_1 := h2126c.2.1
                                have p2126_2 := h2126c.2.2.1
                                have p2126_3 := h2126c.2.2.2
                                linarith only [h1984, h2055, hc01, hlam, hphi, ht12, ht23, p2126_1, u3elo1]
                              · have p2126_0 := h2126c.1
                                have p2126_1 := h2126c.2.1
                                have p2126_2 := h2126c.2.2.1
                                have p2126_3 := h2126c.2.2.2
                                linarith only [h1984, hc01, hlam, hphi, ht12, ht23, p2126_1, u3elo1]
                              · have p2126_0 := h2126c.1
                                have p2126_1 := h2126c.2.1
                                have p2126_2 := h2126c.2.2.1
                                have p2126_3 := h2126c.2.2.2
                                linarith only [h2053, hc01, hlam, hphi, ht12, ht23, p2126_1, u3elo1]
                              · have p2126_0 := h2126c.1
                                have p2126_1 := h2126c.2.1
                                have p2126_2 := h2126c.2.2.1
                                have p2126_3 := h2126c.2.2.2
                                linarith only [h2051, hlam, p2126_1]
                              · have p2126_0 := h2126c.1
                                have p2126_1 := h2126c.2.1
                                have p2126_2 := h2126c.2.2.1
                                have p2126_3 := h2126c.2.2.2
                                linarith only [h2053, hlam, p2126_0]
                              · have p2126_0 := h2126c.1
                                have p2126_1 := h2126c.2.1
                                have p2126_2 := h2126c.2.2.1
                                have p2126_3 := h2126c.2.2.2
                                linarith only [hlam, p2126_0]
                              · have p2126_0 := h2126c.1
                                have p2126_1 := h2126c.2.1
                                have p2126_2 := h2126c.2.2.1
                                have p2126_3 := h2126c.2.2.2
                                linarith only [h1984, h2053, hc01, hlam, hphi, ht12, ht23, p2126_1, u3elo1]
                              · have p2126_0 := h2126c.1
                                have p2126_1 := h2126c.2.1
                                have p2126_2 := h2126c.2.2.1
                                have p2126_3 := h2126c.2.2.2
                                linarith only [h2054, hc01, hlam, hphi, ht12, ht23, p2126_1, u3elo1]
                              · have p2126_0 := h2126c.1
                                have p2126_1 := h2126c.2.1
                                have p2126_2 := h2126c.2.2.1
                                have p2126_3 := h2126c.2.2.2
                                linarith only [h2052, hlam, p2126_1]
                              · have p2126_0 := h2126c.1
                                have p2126_1 := h2126c.2.1
                                have p2126_2 := h2126c.2.2.1
                                have p2126_3 := h2126c.2.2.2
                                linarith only [h2054, hlam, p2126_0]
                              · have p2126_0 := h2126c.1
                                have p2126_1 := h2126c.2.1
                                have p2126_2 := h2126c.2.2.1
                                have p2126_3 := h2126c.2.2.2
                                linarith only [h2055, hlam, p2126_0]
                              · have p2126_0 := h2126c.1
                                have p2126_1 := h2126c.2.1
                                have p2126_2 := h2126c.2.2.1
                                have p2126_3 := h2126c.2.2.2
                                linarith only [hlam, p2126_0]
                        · linarith only [h2049, h2057, hc23, hlam, hphi, u3elo0]
                      · linarith only [h2053, h2056, hc23, hlam, hphi, u3elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2160 | h2160
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2161 | h2161
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2162 | h2162
                          · linarith only [h1842, h2055, h2162, hc01, hc24, hlam, hphi, ht12]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2164 | h2164
                            · linarith only [h1842, h2055, h2160, h2164, hc01, hc23, hlam, hphi, ht12]
                            · rcases h1bigk with h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [hlam, p2166_0]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [h0, hlam, p2166_0]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [h1397, hlam, p2166_0]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [h1842, hlam, p2166_0]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [h1984, hlam, p2166_0]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                rcases p2166_3 (m.d 0 1) (by simp) with h2172 | h2172
                                · linarith only [h2172, hlam, p2166_0]
                                · rcases p2166_3 (m.d 1 2) (by simp) with h2174 | h2174
                                  · rcases p2166_3 (m.d 1 3) (by simp) with h2175 | h2175
                                    · linarith only [h2050, h2175, hlam]
                                    · linarith only [h1397, h2175, hlam]
                                  · linarith only [h2174, hlam, p2166_0]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [hlam, p2166_0]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [h1397, hc01, hc12, hlam, hphi, p2166_1]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [h1842, hc01, hc12, hlam, hphi, p2166_1]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [h1842, h2055, hc01, hc12, hlam, hphi, p2166_1]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, p2166_1, u3elo1]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [h2050, hlam, p2166_1]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [hlam, p2166_0]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [h1842, hc01, hlam, hphi, ht12, ht23, p2166_1, u3elo1]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [h1842, h2055, hc01, hlam, hphi, ht12, ht23, p2166_1, u3elo1]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [h2055, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2166_1]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [h2051, hlam, p2166_1]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [h2053, hlam, p2166_0]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [hlam, p2166_0]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [h2055, hlam, p2166_1]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [h2054, hc01, hlam, hphi, ht12, ht23, p2166_1, u3elo1]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [h2052, hlam, p2166_1]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [h2054, hlam, p2166_0]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [h1842, h2054, hc01, hlam, hphi, ht12, ht23, p2166_1, u3elo1]
                              · have p2166_0 := h2166c.1
                                have p2166_1 := h2166c.2.1
                                have p2166_2 := h2166c.2.2.1
                                have p2166_3 := h2166c.2.2.2
                                linarith only [hlam, p2166_0]
                        · linarith only [h1397, h2049, h2161, hc23, hlam, hphi, u3elo1]
                      · linarith only [h2053, h2160, hc23, hlam, hphi, u3elo1]
                  · linarith only [h1397, h2049, h2054, hlam]
                · linarith only [h1397, h2053, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2202 | h2202
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2203 | h2203
                  · linarith only [h2050, h2052, h2203, hlam]
                  · linarith only [h2049, h2203, hc13, hlam, hphi, u3elo0]
                · linarith only [h1397, h2202, hc01, hlam, hphi, ht12, ht23, u3elo3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2207 | h2207
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2208 | h2208
                · linarith only [h2050, h2051, h2208, hlam]
                · linarith only [h1397, h2208, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2211 | h2211
                · linarith only [h2050, h2051, h2211, hlam]
                · linarith only [h1397, h2211, hc01, hlam, hphi, ht12, ht23, u3elo3]
          · linarith only [h0, h2050, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2215 | h2215
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2216 | h2216
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2217 | h2217
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2218 | h2218
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2219 | h2219
                  · linarith only [h2049, h2219, hc03, hlam, hphi, u3elo1]
                  · linarith only [h1842, h2218, h2219, hc01, hlam, hphi, ht12, ht23, u3elo4]
                · linarith only [h1397, h2218, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2223 | h2223
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2224 | h2224
                  · linarith only [h1397, h2049, h2224, hc01, hlam, hphi, ht12, ht23, u3elo1]
                  · linarith only [h1397, h2224, hc01, hlam, hphi, ht12, ht23, u3elo4]
                · linarith only [h1397, h2223, hc01, hlam, hphi, ht12, ht23, u3elo3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2228 | h2228
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2229 | h2229
                · linarith only [h2215, h2216, h2229, hlam]
                · linarith only [h1397, h2229, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2232 | h2232
                · linarith only [h2215, h2216, h2232, hlam]
                · linarith only [h1397, h2232, hc01, hlam, hphi, ht12, ht23, u3elo3]
          · linarith only [h0, h2215, hc01, hlam, hphi, ht12, ht23, u3elo2]

set_option maxHeartbeats 4472000 in
theorem r1l7_11_23_L_I_M_LI (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h1bigk := hb1.1
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_23_L_I_M_LI_x0 m hb1 hb3 h0
  · exact r1l7_11_23_L_I_M_LI_x1 m hb1 hb3 h0

end R2N4
