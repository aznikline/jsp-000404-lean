import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_52S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5002000 in
set_option maxHeartbeats 5002000 in
theorem r1l7_11_13_25_L_0_L_I_M_IR_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1198 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1459 | h1459
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1460 | h1460
    · linarith only [h1198, h1460, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1462 | h1462
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1463 | h1463
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1464 | h1464
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1465 | h1465
            · linarith only [h1198, h1459, h1465, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1467 | h1467
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1468 | h1468
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1469 | h1469
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1470 | h1470
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1471 | h1471
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1472 | h1472
                        · linarith only [h1459, h1460, h1465, h1467, h1471, h1472, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1474 | h1474
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1475 | h1475
                            · linarith only [h0, h1462, h1475, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                            · linarith only [h1198, h1464, h1467, h1474, h1475, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · linarith only [h1459, h1460, h1467, h1470, h1471, h1474, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · linarith only [h1198, h1464, h1471, hlam]
                    · linarith only [h1198, h1463, h1470, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1481 | h1481
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1482 | h1482
                      · linarith only [h1467, h1469, h1482, hlam]
                      · linarith only [h1198, h1464, h1482, hlam]
                    · linarith only [h1198, h1463, h1481, hlam]
                · linarith only [h1198, h1459, h1467, h1468, hlam]
              · linarith only [h0, h1462, h1467, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1488 | h1488
            · linarith only [h1198, h1459, h1488, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1490 | h1490
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1491 | h1491
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1492 | h1492
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1493 | h1493
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1494 | h1494
                      · linarith only [h1198, h1464, h1490, h1494, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1496 | h1496
                        · linarith only [h1459, h1488, h1496, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1498 | h1498
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1499 | h1499
                            · linarith only [h1198, h1459, h1462, h1464, h1494, h1499, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1501 | h1501
                              · linarith only [h1198, h1459, h1491, h1494, h1496, h1501, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1503 | h1503
                                · linarith only [h1198, h1459, h1491, h1494, h1496, h1498, h1503, hlam]
                                · linarith only [h1198, h1459, h1491, h1494, h1498, h1503, hc34, hc45, hlam, hphi]
                          · linarith only [h1198, h1463, h1494, h1498, hc23, hc35, hlam, hphi]
                    · linarith only [h1198, h1459, h1463, h1493, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1508 | h1508
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1509 | h1509
                      · linarith only [h1198, h1459, h1464, h1490, h1491, h1509, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1511 | h1511
                        · linarith only [h1198, h1459, h1509, h1511, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1513 | h1513
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1514 | h1514
                            · linarith only [h1198, h1509, h1514, hc01, hc23, hlam, hphi, ht12]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1516 | h1516
                              · linarith only [h1198, h1459, h1460, h1490, h1491, h1492, h1511, h1514, h1516, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                              · linarith only [h1198, h1459, h1490, h1491, h1492, h1513, h1516, hc34, hc45, hlam, hphi]
                          · linarith only [h1463, h1464, h1513, hc23, hc35, hlam, hphi]
                    · linarith only [h1198, h1463, h1464, h1508, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h0, h1459, h1491, hlam]
              · linarith only [h0, h1459, h1462, h1490, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h1198, h1459, h1463, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1524 | h1524
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1525 | h1525
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1526 | h1526
            · linarith only [h1459, h1460, h1526, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1528 | h1528
              · linarith only [h0, h1462, h1528, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1530 | h1530
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1531 | h1531
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1532 | h1532
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1533 | h1533
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1534 | h1534
                        · linarith only [h1459, h1460, h1526, h1528, h1531, h1534, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1536 | h1536
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1537 | h1537
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1538 | h1538
                              · linarith only [h1459, h1460, h1530, h1534, h1538, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1540 | h1540
                                · linarith only [h1459, h1460, h1530, h1534, h1536, h1540, hlam]
                                · rcases h3bigk with h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c | h1542c
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [hlam, p1542_0]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [h1198, hlam, p1542_1]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [h1462, hlam, p1542_1]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    rcases p1542_3 (m.d 0 3) (by simp) with h1546 | h1546
                                    · rcases p1542_3 (m.d 1 3) (by simp) with h1547 | h1547
                                      · rcases p1542_3 (m.d 2 3) (by simp) with h1548 | h1548
                                        · rcases p1542_3 (m.d 3 4) (by simp) with h1549 | h1549
                                          · linarith only [h1549, hlam, p1542_0]
                                          · rcases p1542_3 (m.d 3 5) (by simp) with h1551 | h1551
                                            · linarith only [h1525, h1551, hlam]
                                            · linarith only [h1540, h1551, hlam]
                                        · linarith only [h1536, h1548, hlam]
                                      · linarith only [h1532, h1547, hlam]
                                    · linarith only [h1546, hlam, p1542_0]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [h1198, hlam, hphi, ht01, ht0b, ht5b, p1542_1, u1elo2, u5ehi3]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [h1198, hc01, hlam, hphi, p1542_1, u1elo2]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [hlam, p1542_0]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [h1528, hlam, p1542_1]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    rcases p1542_3 (m.d 0 3) (by simp) with h1561 | h1561
                                    · linarith only [h1198, h1561, hlam]
                                    · linarith only [h1524, h1561, hlam]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [hlam, hphi, ht01, ht0b, ht5b, p1542_1, u1elo2, u5ehi3]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [h1525, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1542_1, u5ehi3]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [h1198, h1459, h1530, h1536, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1542_1]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [hlam, p1542_0]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [h1459, h1460, h1528, h1530, h1531, h1536, hlam, p1542_2]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    rcases p1542_3 (m.d 0 3) (by simp) with h1569 | h1569
                                    · linarith only [h1462, h1569, hlam]
                                    · linarith only [h1525, h1569, hlam]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [h1524, hlam, p1542_0]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [h1532, hlam, p1542_0]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [h1536, hlam, p1542_0]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [hlam, p1542_0]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [h1540, hlam, p1542_1]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [h1525, hlam, p1542_0]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [h1533, hlam, p1542_0]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [h1537, hlam, p1542_0]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [h1198, h1525, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1542_1, u1elo2]
                                  · have p1542_0 := h1542c.1
                                    have p1542_1 := h1542c.2.1
                                    have p1542_2 := h1542c.2.2.1
                                    have p1542_3 := h1542c.2.2.2
                                    linarith only [hlam, p1542_0]
                            · linarith only [h1198, h1459, h1460, h1525, h1528, h1530, h1531, h1536, h1537, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                          · linarith only [h1459, h1460, h1528, h1530, h1531, h1536, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h1198, h1525, h1533, hlam]
                    · linarith only [h1198, h1524, h1532, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1586 | h1586
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1587 | h1587
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1588 | h1588
                        · linarith only [h1459, h1588, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1590 | h1590
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1591 | h1591
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1592 | h1592
                              · linarith only [h0, h1459, h1530, h1531, h1588, h1592, hlam]
                              · linarith only [h0, h1459, h1530, h1531, h1590, h1592, hc34, hc45, hlam, hphi]
                            · linarith only [h0, h1459, h1462, h1525, h1530, h1590, h1591, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h0, h1459, h1528, h1530, h1590, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h1198, h1525, h1587, hlam]
                    · linarith only [h1198, h1524, h1586, hlam]
                · linarith only [h0, h1459, h1530, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1600 | h1600
            · linarith only [h0, h1459, h1600, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1602 | h1602
              · linarith only [h0, h1462, h1602, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1604 | h1604
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1605 | h1605
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1606 | h1606
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1607 | h1607
                      · linarith only [h0, h1459, h1462, h1525, h1604, h1607, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · linarith only [h1602, h1605, h1607, hlam]
                    · linarith only [h1524, h1602, h1605, h1606, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1611 | h1611
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1612 | h1612
                      · linarith only [h1198, h1459, h1525, h1604, h1612, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1614 | h1614
                        · linarith only [h0, h1459, h1600, h1614, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1616 | h1616
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1617 | h1617
                            · linarith only [h0, h1459, h1602, h1604, h1612, h1616, h1617, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h1459, h1602, h1604, h1616, h1617, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1459, h1602, h1604, h1616, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h1459, h1524, h1602, h1604, h1611, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h1459, h1604, hlam]
        · linarith only [h1198, h1459, h1524, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1624 | h1624
    · linarith only [h0, h1624, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1626 | h1626
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1627 | h1627
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1628 | h1628
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1629 | h1629
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1630 | h1630
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1631 | h1631
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1632 | h1632
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1633 | h1633
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1634 | h1634
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1635 | h1635
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1636 | h1636
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1637 | h1637
                            · linarith only [h0, h1626, h1637, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                            · linarith only [h1198, h1628, h1630, h1636, h1637, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1640 | h1640
                            · linarith only [h0, h1626, h1640, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1642 | h1642
                              · linarith only [h1631, h1642, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1644 | h1644
                                · linarith only [h1198, h1627, h1630, h1636, h1642, h1644, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                                · linarith only [h1459, h1629, h1630, h1633, h1636, h1644, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                        · linarith only [h1459, h1629, h1635, hlam]
                      · linarith only [h1198, h1628, h1634, hlam]
                    · linarith only [h1198, h1627, h1633, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1650 | h1650
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1651 | h1651
                      · linarith only [h1630, h1632, h1651, hlam]
                      · linarith only [h1198, h1628, h1651, hlam]
                    · linarith only [h1198, h1627, h1650, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1655 | h1655
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1656 | h1656
                    · linarith only [h1630, h1631, h1656, hlam]
                    · linarith only [h1198, h1627, h1656, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1659 | h1659
                    · linarith only [h1630, h1631, h1659, hlam]
                    · linarith only [h1198, h1627, h1659, hlam]
              · linarith only [h0, h1626, h1630, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1663 | h1663
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1664 | h1664
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1665 | h1665
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1666 | h1666
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1667 | h1667
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1668 | h1668
                        · linarith only [h1459, h1629, h1666, h1668, hc01, hlam, hphi, u1elo2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1670 | h1670
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1671 | h1671
                            · linarith only [h0, h1626, h1671, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                            · linarith only [h0, h1626, h1628, h1670, h1671, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1674 | h1674
                            · linarith only [h1459, h1627, h1668, h1670, h1674, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1676 | h1676
                              · linarith only [h1459, h1668, h1676, hc01, hc24, hlam, hphi, ht12]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1678 | h1678
                                · linarith only [h0, h1459, h1626, h1627, h1668, h1678, hc01, hlam, hphi, u1elo1]
                                · rcases h3bigk with h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c
                                  · have p1680_0 := h1680c.1
                                    have p1680_1 := h1680c.2.1
                                    have p1680_2 := h1680c.2.2.1
                                    have p1680_3 := h1680c.2.2.2
                                    linarith only [hlam, p1680_0]
                                  · have p1680_0 := h1680c.1
                                    have p1680_1 := h1680c.2.1
                                    have p1680_2 := h1680c.2.2.1
                                    have p1680_3 := h1680c.2.2.2
                                    linarith only [h1198, hlam, p1680_1]
                                  · have p1680_0 := h1680c.1
                                    have p1680_1 := h1680c.2.1
                                    have p1680_2 := h1680c.2.2.1
                                    have p1680_3 := h1680c.2.2.2
                                    rcases p1680_3 (m.d 0 3) (by simp) with h1683 | h1683
                                    · rcases p1680_3 (m.d 1 3) (by simp) with h1684 | h1684
                                      · rcases p1680_3 (m.d 2 3) (by simp) with h1685 | h1685
                                        · linarith only [h1626, h1685, hlam]
                                        · rcases p1680_3 (m.d 3 4) (by simp) with h1687 | h1687
                                          · linarith only [h1627, h1687, hlam]
                                          · linarith only [h1670, h1687, hlam]
                                      · linarith only [h1663, h1684, hlam]
                                    · linarith only [h1626, h1683, hlam]
                                  · have p1680_0 := h1680c.1
                                    have p1680_1 := h1680c.2.1
                                    have p1680_2 := h1680c.2.2.1
                                    have p1680_3 := h1680c.2.2.2
                                    linarith only [h0, h1626, h1670, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1680_1, u1elo1]
                                  · have p1680_0 := h1680c.1
                                    have p1680_1 := h1680c.2.1
                                    have p1680_2 := h1680c.2.2.1
                                    have p1680_3 := h1680c.2.2.2
                                    linarith only [h0, h1626, h1674, hlam, hphi, ht01, ht0b, ht5b, p1680_1, u1elo1, u5ehi2]
                                  · have p1680_0 := h1680c.1
                                    have p1680_1 := h1680c.2.1
                                    have p1680_2 := h1680c.2.2.1
                                    have p1680_3 := h1680c.2.2.2
                                    linarith only [h1628, hlam, hphi, ht01, ht0b, ht5b, p1680_1, u1elo2, u5ehi0]
                                  · have p1680_0 := h1680c.1
                                    have p1680_1 := h1680c.2.1
                                    have p1680_2 := h1680c.2.2.1
                                    have p1680_3 := h1680c.2.2.2
                                    linarith only [hlam, p1680_0]
                                  · have p1680_0 := h1680c.1
                                    have p1680_1 := h1680c.2.1
                                    have p1680_2 := h1680c.2.2.1
                                    have p1680_3 := h1680c.2.2.2
                                    rcases p1680_3 (m.d 0 3) (by simp) with h1696 | h1696
                                    · linarith only [h1198, h1696, hlam]
                                    · linarith only [h1626, h1696, hlam]
                                  · have p1680_0 := h1680c.1
                                    have p1680_1 := h1680c.2.1
                                    have p1680_2 := h1680c.2.2.1
                                    have p1680_3 := h1680c.2.2.2
                                    linarith only [h1663, h1670, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1680_1, u1elo1]
                                  · have p1680_0 := h1680c.1
                                    have p1680_1 := h1680c.2.1
                                    have p1680_2 := h1680c.2.2.1
                                    have p1680_3 := h1680c.2.2.2
                                    linarith only [h1663, h1670, h1678, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1680_1, u1elo1]
                                  · have p1680_0 := h1680c.1
                                    have p1680_1 := h1680c.2.1
                                    have p1680_2 := h1680c.2.2.1
                                    have p1680_3 := h1680c.2.2.2
                                    linarith only [h1626, hlam, p1680_0]
                                  · have p1680_0 := h1680c.1
                                    have p1680_1 := h1680c.2.1
                                    have p1680_2 := h1680c.2.2.1
                                    have p1680_3 := h1680c.2.2.2
                                    linarith only [h1663, hlam, p1680_0]
                                  · have p1680_0 := h1680c.1
                                    have p1680_1 := h1680c.2.1
                                    have p1680_2 := h1680c.2.2.1
                                    have p1680_3 := h1680c.2.2.2
                                    linarith only [hlam, p1680_0]
                                  · have p1680_0 := h1680c.1
                                    have p1680_1 := h1680c.2.1
                                    have p1680_2 := h1680c.2.2.1
                                    have p1680_3 := h1680c.2.2.2
                                    linarith only [h1670, hlam, p1680_0]
                                  · have p1680_0 := h1680c.1
                                    have p1680_1 := h1680c.2.1
                                    have p1680_2 := h1680c.2.2.1
                                    have p1680_3 := h1680c.2.2.2
                                    linarith only [h1674, hlam, p1680_0]
                                  · have p1680_0 := h1680c.1
                                    have p1680_1 := h1680c.2.1
                                    have p1680_2 := h1680c.2.2.1
                                    have p1680_3 := h1680c.2.2.2
                                    linarith only [h1627, hlam, p1680_0]
                                  · have p1680_0 := h1680c.1
                                    have p1680_1 := h1680c.2.1
                                    have p1680_2 := h1680c.2.2.1
                                    have p1680_3 := h1680c.2.2.2
                                    linarith only [h1666, hlam, p1680_0]
                                  · have p1680_0 := h1680c.1
                                    have p1680_1 := h1680c.2.1
                                    have p1680_2 := h1680c.2.2.1
                                    have p1680_3 := h1680c.2.2.2
                                    linarith only [h1198, h1628, h1663, h1678, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1680_1, u1elo1]
                                  · have p1680_0 := h1680c.1
                                    have p1680_1 := h1680c.2.1
                                    have p1680_2 := h1680c.2.2.1
                                    have p1680_3 := h1680c.2.2.2
                                    linarith only [hlam, p1680_0]
                                  · have p1680_0 := h1680c.1
                                    have p1680_1 := h1680c.2.1
                                    have p1680_2 := h1680c.2.2.1
                                    have p1680_3 := h1680c.2.2.2
                                    linarith only [h1678, hlam, p1680_1]
                                  · have p1680_0 := h1680c.1
                                    have p1680_1 := h1680c.2.1
                                    have p1680_2 := h1680c.2.2.1
                                    have p1680_3 := h1680c.2.2.2
                                    linarith only [h1628, hlam, p1680_0]
                                  · have p1680_0 := h1680c.1
                                    have p1680_1 := h1680c.2.1
                                    have p1680_2 := h1680c.2.2.1
                                    have p1680_3 := h1680c.2.2.2
                                    linarith only [h1667, hlam, p1680_0]
                                  · have p1680_0 := h1680c.1
                                    have p1680_1 := h1680c.2.1
                                    have p1680_2 := h1680c.2.2.1
                                    have p1680_3 := h1680c.2.2.2
                                    linarith only [h1198, h1628, h1663, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1680_1, u1elo1]
                                  · have p1680_0 := h1680c.1
                                    have p1680_1 := h1680c.2.1
                                    have p1680_2 := h1680c.2.2.1
                                    have p1680_3 := h1680c.2.2.2
                                    linarith only [h1198, h1628, h1663, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1680_1, u1elo1]
                                  · have p1680_0 := h1680c.1
                                    have p1680_1 := h1680c.2.1
                                    have p1680_2 := h1680c.2.2.1
                                    have p1680_3 := h1680c.2.2.2
                                    linarith only [hlam, p1680_0]
                      · linarith only [h1198, h1628, h1667, hlam]
                    · linarith only [h1198, h1627, h1666, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1718 | h1718
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1719 | h1719
                      · linarith only [h1663, h1665, h1719, hlam]
                      · linarith only [h0, h1198, h1626, h1628, h1665, h1719, hc01, hlam, hphi, u1elo4]
                    · linarith only [h1198, h1627, h1718, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1723 | h1723
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1724 | h1724
                    · linarith only [h1663, h1664, h1724, hlam]
                    · linarith only [h0, h1198, h1626, h1627, h1664, h1724, hc01, hlam, hphi, u1elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1727 | h1727
                    · linarith only [h1663, h1664, h1727, hlam]
                    · linarith only [h0, h1198, h1626, h1627, h1664, h1727, hc01, hlam, hphi, u1elo3]
              · linarith only [h0, h1626, h1663, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1731 | h1731
            · linarith only [h1627, h1628, h1731, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1733 | h1733
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1734 | h1734
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1735 | h1735
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1736 | h1736
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1737 | h1737
                      · linarith only [h1627, h1628, h1733, h1737, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1739 | h1739
                        · linarith only [h1459, h1731, h1736, h1737, h1739, hc01, hc35, hlam, hphi, ht12, ht23]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1741 | h1741
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1742 | h1742
                            · linarith only [h1198, h1737, h1742, hc01, hc23, hlam, hphi, ht12]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1744 | h1744
                              · linarith only [h0, h1459, h1626, h1739, h1741, h1744, hc01, hlam, hphi, u1elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1746 | h1746
                                · linarith only [h0, h1459, h1626, h1739, h1741, h1746, hc01, hlam, hphi, u1elo1]
                                · rcases h3bigk with h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c | h1748c
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [hlam, p1748_0]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [h1198, hlam, p1748_1]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [h1198, h1741, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1748_1, u1elo2]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [h1198, h1737, h1746, hc34, hc45, hlam, hphi, p1748_1]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [h1628, hlam, p1748_0]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [h1737, h1746, hc03, hc45, hlam, hphi, ht34, p1748_1]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [hlam, p1748_0]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [h1737, h1741, h1746, hc34, hc45, hlam, hphi, p1748_1]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [h1737, h1746, hc34, hc45, hlam, hphi, p1748_1]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [h1737, hlam, p1748_0]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [h1626, hlam, p1748_0]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [h1733, hlam, p1748_0]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [hlam, p1748_0]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [h1198, h1626, h1737, h1746, hc34, hc45, hlam, hphi, p1748_1]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [h1742, hlam, p1748_0]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [h1627, hlam, p1748_0]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [h1736, hlam, p1748_0]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [h1741, hlam, p1748_0]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [hlam, p1748_0]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [h1746, hlam, p1748_1]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [h1627, h1746, hc34, hc45, hlam, hphi, p1748_1]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [h1198, h1746, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1748_1]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [h1741, h1746, hc34, hc45, hlam, hphi, p1748_1]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    rcases p1748_3 (m.d 0 3) (by simp) with h1772 | h1772
                                    · linarith only [h1628, h1772, hlam]
                                    · linarith only [h1627, h1772, hlam]
                                  · have p1748_0 := h1748c.1
                                    have p1748_1 := h1748c.2.1
                                    have p1748_2 := h1748c.2.2.1
                                    have p1748_3 := h1748c.2.2.2
                                    linarith only [hlam, p1748_0]
                          · linarith only [h1627, h1628, h1741, hc23, hc35, hlam, hphi]
                    · linarith only [h1627, h1628, h1736, hc13, hc35, hlam, hphi]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1778 | h1778
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1779 | h1779
                      · linarith only [h1627, h1628, h1779, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1781 | h1781
                        · linarith only [h1459, h1731, h1781, hc01, hlam, hphi, u1elo3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1783 | h1783
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1784 | h1784
                            · linarith only [h1198, h1779, h1784, hc01, hc23, hlam, hphi, ht12]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1786 | h1786
                              · linarith only [h0, h1626, h1735, h1781, h1783, h1784, h1786, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · linarith only [h0, h1626, h1735, h1783, h1786, hc34, hc45, hlam, hphi]
                          · linarith only [h1627, h1628, h1783, hc23, hc35, hlam, hphi]
                    · linarith only [h1627, h1628, h1778, hc13, hc35, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1791 | h1791
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1792 | h1792
                    · linarith only [h1733, h1734, h1792, hlam]
                    · linarith only [h1627, h1628, h1792, hc13, hc35, hlam, hphi]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1795 | h1795
                    · linarith only [h1733, h1734, h1795, hlam]
                    · linarith only [h1627, h1628, h1795, hc13, hc35, hlam, hphi]
              · linarith only [h0, h1626, h1733, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1799 | h1799
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1800 | h1800
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1801 | h1801
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1802 | h1802
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1803 | h1803
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1804 | h1804
                    · linarith only [h1627, h1799, h1804, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1806 | h1806
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1807 | h1807
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1808 | h1808
                          · linarith only [h1626, h1804, h1806, h1808, hc02, hlam, hphi, ht0b, ht5b, u5ehi1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1810 | h1810
                            · linarith only [h0, h1626, h1810, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                            · linarith only [h1198, h1799, h1804, h1810, hc23, hc34, hlam, hphi]
                        · linarith only [h1459, h1624, h1800, h1804, h1806, h1807, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h1198, h1799, h1806, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1815 | h1815
                    · linarith only [h1627, h1799, h1815, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1817 | h1817
                      · linarith only [h1802, h1803, h1815, h1817, hlam]
                      · linarith only [h1198, h1799, h1817, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1820 | h1820
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1821 | h1821
                    · linarith only [h1627, h1799, h1821, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1823 | h1823
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1824 | h1824
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1825 | h1825
                          · linarith only [h1198, h1821, h1825, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1827 | h1827
                            · linarith only [h0, h1626, h1827, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                            · linarith only [h0, h1626, h1799, h1802, h1825, h1827, hc23, hc34, hlam, hphi]
                        · linarith only [h1624, h1800, h1802, h1820, h1824, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi2]
                      · linarith only [h1198, h1799, h1823, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1832 | h1832
                    · linarith only [h1627, h1799, h1832, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1834 | h1834
                      · linarith only [h1801, h1820, h1834, hlam]
                      · linarith only [h0, h1198, h1626, h1799, h1802, h1834, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h1626, h1801, hlam]
            · linarith only [h1627, h1799, h1800, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1839 | h1839
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1840 | h1840
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1841 | h1841
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1842 | h1842
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1843 | h1843
                    · linarith only [h1198, h1627, h1843, hc01, hlam, hphi, u1elo2]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1845 | h1845
                      · linarith only [h1198, h1799, h1841, h1843, h1845, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1847 | h1847
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1848 | h1848
                          · linarith only [h0, h1626, h1843, h1848, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1850 | h1850
                            · linarith only [h1198, h1845, h1850, hc01, hc23, hlam, hphi, ht12]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1852 | h1852
                              · linarith only [h1841, h1852, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1854 | h1854
                                · rcases h3bigk with h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c | h1855c
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [hlam, p1855_0]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [h1198, hlam, p1855_1]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [h1198, h1845, h1854, hc23, hc34, hlam, hphi, p1855_1]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [h1627, hlam, p1855_0]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [h1799, hlam, p1855_0]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [h1845, h1854, hc03, hc34, hlam, hphi, p1855_1]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [hlam, p1855_0]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [h1845, h1854, hc23, hc34, hlam, hphi, p1855_1]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [h1843, hlam, p1855_0]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [h1845, hlam, p1855_0]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [h1626, hlam, p1855_0]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [h1840, hlam, p1855_0]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [hlam, p1855_0]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [h1848, hlam, p1855_0]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [h1850, hlam, p1855_0]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    rcases p1855_3 (m.d 0 3) (by simp) with h1871 | h1871
                                    · linarith only [h1871, hlam, p1855_0]
                                    · rcases p1855_3 (m.d 1 3) (by simp) with h1873 | h1873
                                      · linarith only [h1843, h1873, hlam]
                                      · linarith only [h1198, h1873, hlam]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [h1198, hc01, hc34, hlam, hphi, ht12, ht23, p1855_1]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    rcases p1855_3 (m.d 0 3) (by simp) with h1877 | h1877
                                    · linarith only [h1627, h1877, hlam]
                                    · linarith only [h1626, h1877, hlam]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [hlam, p1855_0]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [h1198, h1459, h1799, h1839, h1841, h1848, h1852, hc01, hc23, hc34, hlam, hphi, p1855_1, u1elo1]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    rcases p1855_3 (m.d 0 3) (by simp) with h1882 | h1882
                                    · linarith only [h1882, hlam, p1855_0]
                                    · rcases p1855_3 (m.d 1 3) (by simp) with h1884 | h1884
                                      · linarith only [h1845, h1884, hlam]
                                      · linarith only [h1198, h1884, hlam]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [h1198, h1459, h1839, h1841, h1848, h1852, hc01, hc23, hc35, hlam, hphi, p1855_1, u1elo1]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    rcases p1855_3 (m.d 0 3) (by simp) with h1888 | h1888
                                    · linarith only [h1799, h1888, hlam]
                                    · linarith only [h1626, h1888, hlam]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [h1854, hlam, p1855_0]
                                  · have p1855_0 := h1855c.1
                                    have p1855_1 := h1855c.2.1
                                    have p1855_2 := h1855c.2.2.1
                                    have p1855_3 := h1855c.2.2.2
                                    linarith only [hlam, p1855_0]
                                · linarith only [h1198, h1459, h1627, h1839, h1841, h1854, hc01, hlam, hphi, u1elo1]
                        · linarith only [h1459, h1839, h1847, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1895 | h1895
                    · linarith only [h1198, h1627, h1895, hc01, hlam, hphi, u1elo2]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1897 | h1897
                      · linarith only [h1198, h1799, h1895, h1897, hc01, hc34, hlam, hphi, ht12, ht23]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1899 | h1899
                        · linarith only [h1841, h1842, h1899, hlam]
                        · linarith only [h1459, h1839, h1899, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1902 | h1902
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1903 | h1903
                    · linarith only [h1198, h1627, h1903, hc01, hlam, hphi, u1elo2]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1905 | h1905
                      · linarith only [h1198, h1799, h1840, h1905, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1907 | h1907
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1908 | h1908
                          · linarith only [h1198, h1903, h1908, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1910 | h1910
                            · linarith only [h1198, h1905, h1910, hc01, hc23, hlam, hphi, ht12]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1912 | h1912
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1913 | h1913
                                · rcases h3bigk with h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c | h1914c
                                  · have p1914_0 := h1914c.1
                                    have p1914_1 := h1914c.2.1
                                    have p1914_2 := h1914c.2.2.1
                                    have p1914_3 := h1914c.2.2.2
                                    linarith only [hlam, p1914_0]
                                  · have p1914_0 := h1914c.1
                                    have p1914_1 := h1914c.2.1
                                    have p1914_2 := h1914c.2.2.1
                                    have p1914_3 := h1914c.2.2.2
                                    linarith only [h1198, hlam, p1914_1]
                                  · have p1914_0 := h1914c.1
                                    have p1914_1 := h1914c.2.1
                                    have p1914_2 := h1914c.2.2.1
                                    have p1914_3 := h1914c.2.2.2
                                    linarith only [h1624, h1799, h1841, h1902, h1908, hc23, hc34, hlam, hphi, p1914_1]
                                  · have p1914_0 := h1914c.1
                                    have p1914_1 := h1914c.2.1
                                    have p1914_2 := h1914c.2.2.1
                                    have p1914_3 := h1914c.2.2.2
                                    linarith only [h1627, hlam, p1914_0]
                                  · have p1914_0 := h1914c.1
                                    have p1914_1 := h1914c.2.1
                                    have p1914_2 := h1914c.2.2.1
                                    have p1914_3 := h1914c.2.2.2
                                    linarith only [h1799, hlam, p1914_0]
                                  · have p1914_0 := h1914c.1
                                    have p1914_1 := h1914c.2.1
                                    have p1914_2 := h1914c.2.2.1
                                    have p1914_3 := h1914c.2.2.2
                                    linarith only [h1841, h1902, h1905, h1908, hc03, hc34, hlam, hphi, p1914_1]
                                  · have p1914_0 := h1914c.1
                                    have p1914_1 := h1914c.2.1
                                    have p1914_2 := h1914c.2.2.1
                                    have p1914_3 := h1914c.2.2.2
                                    linarith only [hlam, p1914_0]
                                  · have p1914_0 := h1914c.1
                                    have p1914_1 := h1914c.2.1
                                    have p1914_2 := h1914c.2.2.1
                                    have p1914_3 := h1914c.2.2.2
                                    linarith only [h1841, h1902, h1905, h1908, hc23, hc34, hlam, hphi, p1914_1]
                                  · have p1914_0 := h1914c.1
                                    have p1914_1 := h1914c.2.1
                                    have p1914_2 := h1914c.2.2.1
                                    have p1914_3 := h1914c.2.2.2
                                    linarith only [h1903, hlam, p1914_0]
                                  · have p1914_0 := h1914c.1
                                    have p1914_1 := h1914c.2.1
                                    have p1914_2 := h1914c.2.2.1
                                    have p1914_3 := h1914c.2.2.2
                                    linarith only [h1905, hlam, p1914_0]
                                  · have p1914_0 := h1914c.1
                                    have p1914_1 := h1914c.2.1
                                    have p1914_2 := h1914c.2.2.1
                                    have p1914_3 := h1914c.2.2.2
                                    linarith only [h1626, hlam, p1914_0]
                                  · have p1914_0 := h1914c.1
                                    have p1914_1 := h1914c.2.1
                                    have p1914_2 := h1914c.2.2.1
                                    have p1914_3 := h1914c.2.2.2
                                    linarith only [h1840, hlam, p1914_0]
                                  · have p1914_0 := h1914c.1
                                    have p1914_1 := h1914c.2.1
                                    have p1914_2 := h1914c.2.2.1
                                    have p1914_3 := h1914c.2.2.2
                                    linarith only [hlam, p1914_0]
                                  · have p1914_0 := h1914c.1
                                    have p1914_1 := h1914c.2.1
                                    have p1914_2 := h1914c.2.2.1
                                    have p1914_3 := h1914c.2.2.2
                                    linarith only [h1908, hlam, p1914_0]
                                  · have p1914_0 := h1914c.1
                                    have p1914_1 := h1914c.2.1
                                    have p1914_2 := h1914c.2.2.1
                                    have p1914_3 := h1914c.2.2.2
                                    linarith only [h1910, hlam, p1914_0]
                                  · have p1914_0 := h1914c.1
                                    have p1914_1 := h1914c.2.1
                                    have p1914_2 := h1914c.2.2.1
                                    have p1914_3 := h1914c.2.2.2
                                    rcases p1914_3 (m.d 0 3) (by simp) with h1930 | h1930
                                    · linarith only [h1930, hlam, p1914_0]
                                    · rcases p1914_3 (m.d 1 3) (by simp) with h1932 | h1932
                                      · linarith only [h1903, h1932, hlam]
                                      · linarith only [h1198, h1932, hlam]
                                  · have p1914_0 := h1914c.1
                                    have p1914_1 := h1914c.2.1
                                    have p1914_2 := h1914c.2.2.1
                                    have p1914_3 := h1914c.2.2.2
                                    linarith only [h1198, hc01, hc34, hlam, hphi, ht12, ht23, p1914_1]
                                  · have p1914_0 := h1914c.1
                                    have p1914_1 := h1914c.2.1
                                    have p1914_2 := h1914c.2.2.1
                                    have p1914_3 := h1914c.2.2.2
                                    rcases p1914_3 (m.d 0 3) (by simp) with h1936 | h1936
                                    · linarith only [h1627, h1936, hlam]
                                    · linarith only [h1626, h1936, hlam]
                                  · have p1914_0 := h1914c.1
                                    have p1914_1 := h1914c.2.1
                                    have p1914_2 := h1914c.2.2.1
                                    have p1914_3 := h1914c.2.2.2
                                    linarith only [hlam, p1914_0]
                                  · have p1914_0 := h1914c.1
                                    have p1914_1 := h1914c.2.1
                                    have p1914_2 := h1914c.2.2.1
                                    have p1914_3 := h1914c.2.2.2
                                    linarith only [h1198, h1799, hc01, hc34, hlam, hphi, ht12, ht23, p1914_1]
                                  · have p1914_0 := h1914c.1
                                    have p1914_1 := h1914c.2.1
                                    have p1914_2 := h1914c.2.2.1
                                    have p1914_3 := h1914c.2.2.2
                                    rcases p1914_3 (m.d 0 3) (by simp) with h1941 | h1941
                                    · linarith only [h1941, hlam, p1914_0]
                                    · rcases p1914_3 (m.d 1 3) (by simp) with h1943 | h1943
                                      · linarith only [h1905, h1943, hlam]
                                      · linarith only [h1198, h1943, hlam]
                                  · have p1914_0 := h1914c.1
                                    have p1914_1 := h1914c.2.1
                                    have p1914_2 := h1914c.2.2.1
                                    have p1914_3 := h1914c.2.2.2
                                    linarith only [h1198, hc01, hc35, hlam, hphi, ht12, ht23, p1914_1]
                                  · have p1914_0 := h1914c.1
                                    have p1914_1 := h1914c.2.1
                                    have p1914_2 := h1914c.2.2.1
                                    have p1914_3 := h1914c.2.2.2
                                    rcases p1914_3 (m.d 0 3) (by simp) with h1947 | h1947
                                    · linarith only [h1799, h1947, hlam]
                                    · linarith only [h1626, h1947, hlam]
                                  · have p1914_0 := h1914c.1
                                    have p1914_1 := h1914c.2.1
                                    have p1914_2 := h1914c.2.2.1
                                    have p1914_3 := h1914c.2.2.2
                                    linarith only [h1913, hlam, p1914_0]
                                  · have p1914_0 := h1914c.1
                                    have p1914_1 := h1914c.2.1
                                    have p1914_2 := h1914c.2.2.1
                                    have p1914_3 := h1914c.2.2.2
                                    linarith only [hlam, p1914_0]
                                · linarith only [h1841, h1902, h1908, h1913, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                              · linarith only [h1459, h1839, h1841, h1902, h1912, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi2]
                        · linarith only [h1459, h1839, h1907, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1955 | h1955
                    · linarith only [h1198, h1627, h1955, hc01, hlam, hphi, u1elo2]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1957 | h1957
                      · linarith only [h1198, h1799, h1840, h1957, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1959 | h1959
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1960 | h1960
                          · linarith only [h1198, h1955, h1960, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1962 | h1962
                            · linarith only [h1198, h1957, h1962, hc01, hc23, hlam, hphi, ht12]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1964 | h1964
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1965 | h1965
                                · rcases h3bigk with h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c | h1966c
                                  · have p1966_0 := h1966c.1
                                    have p1966_1 := h1966c.2.1
                                    have p1966_2 := h1966c.2.2.1
                                    have p1966_3 := h1966c.2.2.2
                                    linarith only [hlam, p1966_0]
                                  · have p1966_0 := h1966c.1
                                    have p1966_1 := h1966c.2.1
                                    have p1966_2 := h1966c.2.2.1
                                    have p1966_3 := h1966c.2.2.2
                                    linarith only [h1198, hlam, p1966_1]
                                  · have p1966_0 := h1966c.1
                                    have p1966_1 := h1966c.2.1
                                    have p1966_2 := h1966c.2.2.1
                                    have p1966_3 := h1966c.2.2.2
                                    linarith only [h0, h1626, h1902, h1960, h1964, hc23, hc34, hlam, hphi, p1966_1]
                                  · have p1966_0 := h1966c.1
                                    have p1966_1 := h1966c.2.1
                                    have p1966_2 := h1966c.2.2.1
                                    have p1966_3 := h1966c.2.2.2
                                    linarith only [h1627, hlam, p1966_0]
                                  · have p1966_0 := h1966c.1
                                    have p1966_1 := h1966c.2.1
                                    have p1966_2 := h1966c.2.2.1
                                    have p1966_3 := h1966c.2.2.2
                                    linarith only [h1799, hlam, p1966_0]
                                  · have p1966_0 := h1966c.1
                                    have p1966_1 := h1966c.2.1
                                    have p1966_2 := h1966c.2.2.1
                                    have p1966_3 := h1966c.2.2.2
                                    linarith only [h1198, hc01, hlam, hphi, p1966_1, u1elo2]
                                  · have p1966_0 := h1966c.1
                                    have p1966_1 := h1966c.2.1
                                    have p1966_2 := h1966c.2.2.1
                                    have p1966_3 := h1966c.2.2.2
                                    linarith only [hlam, p1966_0]
                                  · have p1966_0 := h1966c.1
                                    have p1966_1 := h1966c.2.1
                                    have p1966_2 := h1966c.2.2.1
                                    have p1966_3 := h1966c.2.2.2
                                    linarith only [h1840, h1902, h1960, h1964, hc23, hc34, hlam, hphi, p1966_1]
                                  · have p1966_0 := h1966c.1
                                    have p1966_1 := h1966c.2.1
                                    have p1966_2 := h1966c.2.2.1
                                    have p1966_3 := h1966c.2.2.2
                                    linarith only [h1955, hlam, p1966_0]
                                  · have p1966_0 := h1966c.1
                                    have p1966_1 := h1966c.2.1
                                    have p1966_2 := h1966c.2.2.1
                                    have p1966_3 := h1966c.2.2.2
                                    linarith only [h1957, hlam, p1966_0]
                                  · have p1966_0 := h1966c.1
                                    have p1966_1 := h1966c.2.1
                                    have p1966_2 := h1966c.2.2.1
                                    have p1966_3 := h1966c.2.2.2
                                    linarith only [h1626, hlam, p1966_0]
                                  · have p1966_0 := h1966c.1
                                    have p1966_1 := h1966c.2.1
                                    have p1966_2 := h1966c.2.2.1
                                    have p1966_3 := h1966c.2.2.2
                                    linarith only [h1840, hlam, p1966_0]
                                  · have p1966_0 := h1966c.1
                                    have p1966_1 := h1966c.2.1
                                    have p1966_2 := h1966c.2.2.1
                                    have p1966_3 := h1966c.2.2.2
                                    linarith only [hlam, p1966_0]
                                  · have p1966_0 := h1966c.1
                                    have p1966_1 := h1966c.2.1
                                    have p1966_2 := h1966c.2.2.1
                                    have p1966_3 := h1966c.2.2.2
                                    linarith only [h1960, hlam, p1966_0]
                                  · have p1966_0 := h1966c.1
                                    have p1966_1 := h1966c.2.1
                                    have p1966_2 := h1966c.2.2.1
                                    have p1966_3 := h1966c.2.2.2
                                    linarith only [h1962, hlam, p1966_0]
                                  · have p1966_0 := h1966c.1
                                    have p1966_1 := h1966c.2.1
                                    have p1966_2 := h1966c.2.2.1
                                    have p1966_3 := h1966c.2.2.2
                                    rcases p1966_3 (m.d 0 3) (by simp) with h1982 | h1982
                                    · linarith only [h1982, hlam, p1966_0]
                                    · rcases p1966_3 (m.d 1 3) (by simp) with h1984 | h1984
                                      · linarith only [h1955, h1984, hlam]
                                      · linarith only [h1198, h1984, hlam]
                                  · have p1966_0 := h1966c.1
                                    have p1966_1 := h1966c.2.1
                                    have p1966_2 := h1966c.2.2.1
                                    have p1966_3 := h1966c.2.2.2
                                    linarith only [h1198, hc01, hc34, hlam, hphi, ht12, ht23, p1966_1]
                                  · have p1966_0 := h1966c.1
                                    have p1966_1 := h1966c.2.1
                                    have p1966_2 := h1966c.2.2.1
                                    have p1966_3 := h1966c.2.2.2
                                    rcases p1966_3 (m.d 0 3) (by simp) with h1988 | h1988
                                    · linarith only [h1627, h1988, hlam]
                                    · linarith only [h1626, h1988, hlam]
                                  · have p1966_0 := h1966c.1
                                    have p1966_1 := h1966c.2.1
                                    have p1966_2 := h1966c.2.2.1
                                    have p1966_3 := h1966c.2.2.2
                                    linarith only [hlam, p1966_0]
                                  · have p1966_0 := h1966c.1
                                    have p1966_1 := h1966c.2.1
                                    have p1966_2 := h1966c.2.2.1
                                    have p1966_3 := h1966c.2.2.2
                                    linarith only [h0, h1902, h1962, hc02, hc34, hlam, hphi, ht23, p1966_1]
                                  · have p1966_0 := h1966c.1
                                    have p1966_1 := h1966c.2.1
                                    have p1966_2 := h1966c.2.2.1
                                    have p1966_3 := h1966c.2.2.2
                                    rcases p1966_3 (m.d 0 3) (by simp) with h1993 | h1993
                                    · linarith only [h1993, hlam, p1966_0]
                                    · rcases p1966_3 (m.d 1 3) (by simp) with h1995 | h1995
                                      · linarith only [h1957, h1995, hlam]
                                      · linarith only [h1198, h1995, hlam]
                                  · have p1966_0 := h1966c.1
                                    have p1966_1 := h1966c.2.1
                                    have p1966_2 := h1966c.2.2.1
                                    have p1966_3 := h1966c.2.2.2
                                    linarith only [h1198, hc01, hc35, hlam, hphi, ht12, ht23, p1966_1]
                                  · have p1966_0 := h1966c.1
                                    have p1966_1 := h1966c.2.1
                                    have p1966_2 := h1966c.2.2.1
                                    have p1966_3 := h1966c.2.2.2
                                    rcases p1966_3 (m.d 0 3) (by simp) with h1999 | h1999
                                    · linarith only [h1799, h1999, hlam]
                                    · linarith only [h1626, h1999, hlam]
                                  · have p1966_0 := h1966c.1
                                    have p1966_1 := h1966c.2.1
                                    have p1966_2 := h1966c.2.2.1
                                    have p1966_3 := h1966c.2.2.2
                                    linarith only [h1965, hlam, p1966_0]
                                  · have p1966_0 := h1966c.1
                                    have p1966_1 := h1966c.2.1
                                    have p1966_2 := h1966c.2.2.1
                                    have p1966_3 := h1966c.2.2.2
                                    linarith only [hlam, p1966_0]
                                · linarith only [h1198, h1459, h1627, h1839, h1965, hc01, hlam, hphi, u1elo3]
                              · linarith only [h1198, h1459, h1839, h1840, h1841, h1964, hc01, hlam, hphi, u1elo3]
                        · linarith only [h1459, h1839, h1959, hlam]
              · linarith only [h0, h1626, h1840, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2008 | h2008
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2009 | h2009
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2010 | h2010
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2011 | h2011
                    · linarith only [h1198, h1627, h2011, hc01, hlam, hphi, u1elo2]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2013 | h2013
                      · linarith only [h1198, h1799, h2011, h2013, hc01, hc34, hlam, hphi, ht12, ht23]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2015 | h2015
                        · linarith only [h1459, h1839, h2009, h2015, hc01, hlam, hphi, u1elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2017 | h2017
                          · linarith only [h1626, h1627, h2017, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2019 | h2019
                            · linarith only [h1198, h2013, h2019, hc01, hc23, hlam, hphi, ht12]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2021 | h2021
                              · linarith only [h1459, h2009, h2015, h2021, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2023 | h2023
                                · linarith only [h1198, h2011, h2015, h2023, hc01, hc34, hlam, hphi, ht12, ht23]
                                · linarith only [h1198, h2011, h2023, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2026 | h2026
                    · linarith only [h1198, h1627, h2026, hc01, hlam, hphi, u1elo2]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2028 | h2028
                      · linarith only [h1799, h2026, h2028, hc03, hc34, hlam, hphi]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2030 | h2030
                        · linarith only [h1459, h1839, h2030, hc01, hlam, hphi, u1elo3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2032 | h2032
                          · linarith only [h1626, h1627, h2032, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2034 | h2034
                            · linarith only [h1198, h2028, h2034, hc01, hc23, hlam, hphi, ht12]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2036 | h2036
                              · linarith only [h1459, h2030, h2036, hc01, hc24, hlam, hphi, ht12]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2038 | h2038
                                · linarith only [h0, h1626, h2010, h2036, h2038, hc23, hc34, hlam, hphi]
                                · linarith only [h1198, h2026, h2038, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2041 | h2041
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2042 | h2042
                    · linarith only [h1198, h1627, h2042, hc01, hlam, hphi, u1elo2]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2044 | h2044
                      · linarith only [h1198, h1799, h2008, h2009, h2044, hc01, hlam, hphi, u1elo3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2046 | h2046
                        · linarith only [h1459, h1839, h2046, hc01, hlam, hphi, u1elo3]
                        · linarith only [h2009, h2041, h2046, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2049 | h2049
                    · linarith only [h1198, h1627, h2049, hc01, hlam, hphi, u1elo2]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2051 | h2051
                      · linarith only [h1198, h1799, h2008, h2009, h2051, hc01, hlam, hphi, u1elo3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2053 | h2053
                        · linarith only [h1198, h1627, h1839, h2053, hc01, hlam, hphi, u1elo3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2055 | h2055
                          · linarith only [h1198, h2049, h2055, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2057 | h2057
                            · linarith only [h1198, h2051, h2057, hc01, hc23, hlam, hphi, ht12]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2059 | h2059
                              · linarith only [h0, h1626, h2009, h2053, h2055, h2059, hc23, hc34, hlam, hphi]
                              · linarith only [h1198, h2008, h2009, h2059, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · linarith only [h0, h1626, h2008, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2063 | h2063
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2064 | h2064
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2065 | h2065
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2066 | h2066
              · linarith only [h0, h1626, h2066, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2068 | h2068
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2069 | h2069
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2070 | h2070
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2071 | h2071
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2072 | h2072
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2073 | h2073
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2074 | h2074
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2075 | h2075
                              · linarith only [h2068, h2075, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2077 | h2077
                                · linarith only [h2073, h2075, h2077, hlam]
                                · rcases h3bigk with h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c | h2079c
                                  · have p2079_0 := h2079c.1
                                    have p2079_1 := h2079c.2.1
                                    have p2079_2 := h2079c.2.2.1
                                    have p2079_3 := h2079c.2.2.2
                                    linarith only [hlam, p2079_0]
                                  · have p2079_0 := h2079c.1
                                    have p2079_1 := h2079c.2.1
                                    have p2079_2 := h2079c.2.2.1
                                    have p2079_3 := h2079c.2.2.2
                                    linarith only [h1198, hlam, p2079_1]
                                  · have p2079_0 := h2079c.1
                                    have p2079_1 := h2079c.2.1
                                    have p2079_2 := h2079c.2.2.1
                                    have p2079_3 := h2079c.2.2.2
                                    linarith only [h1626, hlam, p2079_1]
                                  · have p2079_0 := h2079c.1
                                    have p2079_1 := h2079c.2.1
                                    have p2079_2 := h2079c.2.2.1
                                    have p2079_3 := h2079c.2.2.2
                                    rcases p2079_3 (m.d 0 3) (by simp) with h2083 | h2083
                                    · rcases p2079_3 (m.d 1 3) (by simp) with h2084 | h2084
                                      · rcases p2079_3 (m.d 2 3) (by simp) with h2085 | h2085
                                        · rcases p2079_3 (m.d 3 4) (by simp) with h2086 | h2086
                                          · linarith only [h2086, hlam, p2079_0]
                                          · rcases p2079_3 (m.d 3 5) (by simp) with h2088 | h2088
                                            · linarith only [h2064, h2088, hlam]
                                            · linarith only [h2077, h2088, hlam]
                                        · linarith only [h2073, h2085, hlam]
                                      · linarith only [h2070, h2084, hlam]
                                    · linarith only [h2083, hlam, p2079_0]
                                  · have p2079_0 := h2079c.1
                                    have p2079_1 := h2079c.2.1
                                    have p2079_2 := h2079c.2.2.1
                                    have p2079_3 := h2079c.2.2.2
                                    linarith only [h1198, hlam, hphi, ht01, ht0b, ht5b, p2079_1, u1elo2, u5ehi3]
                                  · have p2079_0 := h2079c.1
                                    have p2079_1 := h2079c.2.1
                                    have p2079_2 := h2079c.2.2.1
                                    have p2079_3 := h2079c.2.2.2
                                    linarith only [h1198, hc01, hlam, hphi, p2079_1, u1elo2]
                                  · have p2079_0 := h2079c.1
                                    have p2079_1 := h2079c.2.1
                                    have p2079_2 := h2079c.2.2.1
                                    have p2079_3 := h2079c.2.2.2
                                    linarith only [hlam, p2079_0]
                                  · have p2079_0 := h2079c.1
                                    have p2079_1 := h2079c.2.1
                                    have p2079_2 := h2079c.2.2.1
                                    have p2079_3 := h2079c.2.2.2
                                    linarith only [h2066, hlam, p2079_1]
                                  · have p2079_0 := h2079c.1
                                    have p2079_1 := h2079c.2.1
                                    have p2079_2 := h2079c.2.2.1
                                    have p2079_3 := h2079c.2.2.2
                                    rcases p2079_3 (m.d 0 3) (by simp) with h2098 | h2098
                                    · linarith only [h1198, h2098, hlam]
                                    · linarith only [h2063, h2098, hlam]
                                  · have p2079_0 := h2079c.1
                                    have p2079_1 := h2079c.2.1
                                    have p2079_2 := h2079c.2.2.1
                                    have p2079_3 := h2079c.2.2.2
                                    linarith only [hlam, hphi, ht01, ht0b, ht5b, p2079_1, u1elo2, u5ehi3]
                                  · have p2079_0 := h2079c.1
                                    have p2079_1 := h2079c.2.1
                                    have p2079_2 := h2079c.2.2.1
                                    have p2079_3 := h2079c.2.2.2
                                    linarith only [h2063, h2065, h2073, h2075, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2079_1]
                                  · have p2079_0 := h2079c.1
                                    have p2079_1 := h2079c.2.1
                                    have p2079_2 := h2079c.2.2.1
                                    have p2079_3 := h2079c.2.2.2
                                    linarith only [h0, h2066, hc01, hc23, hlam, hphi, ht12, p2079_1]
                                  · have p2079_0 := h2079c.1
                                    have p2079_1 := h2079c.2.1
                                    have p2079_2 := h2079c.2.2.1
                                    have p2079_3 := h2079c.2.2.2
                                    linarith only [hlam, p2079_0]
                                  · have p2079_0 := h2079c.1
                                    have p2079_1 := h2079c.2.1
                                    have p2079_2 := h2079c.2.2.1
                                    have p2079_3 := h2079c.2.2.2
                                    linarith only [h1459, h2065, h2066, h2068, h2073, h2075, hlam, p2079_2]
                                  · have p2079_0 := h2079c.1
                                    have p2079_1 := h2079c.2.1
                                    have p2079_2 := h2079c.2.2.1
                                    have p2079_3 := h2079c.2.2.2
                                    rcases p2079_3 (m.d 0 3) (by simp) with h2106 | h2106
                                    · linarith only [h1626, h2106, hlam]
                                    · linarith only [h2064, h2106, hlam]
                                  · have p2079_0 := h2079c.1
                                    have p2079_1 := h2079c.2.1
                                    have p2079_2 := h2079c.2.2.1
                                    have p2079_3 := h2079c.2.2.2
                                    linarith only [h2063, hlam, p2079_0]
                                  · have p2079_0 := h2079c.1
                                    have p2079_1 := h2079c.2.1
                                    have p2079_2 := h2079c.2.2.1
                                    have p2079_3 := h2079c.2.2.2
                                    linarith only [h2070, hlam, p2079_0]
                                  · have p2079_0 := h2079c.1
                                    have p2079_1 := h2079c.2.1
                                    have p2079_2 := h2079c.2.2.1
                                    have p2079_3 := h2079c.2.2.2
                                    linarith only [h2073, hlam, p2079_0]
                                  · have p2079_0 := h2079c.1
                                    have p2079_1 := h2079c.2.1
                                    have p2079_2 := h2079c.2.2.1
                                    have p2079_3 := h2079c.2.2.2
                                    linarith only [hlam, p2079_0]
                                  · have p2079_0 := h2079c.1
                                    have p2079_1 := h2079c.2.1
                                    have p2079_2 := h2079c.2.2.1
                                    have p2079_3 := h2079c.2.2.2
                                    linarith only [h2077, hlam, p2079_1]
                                  · have p2079_0 := h2079c.1
                                    have p2079_1 := h2079c.2.1
                                    have p2079_2 := h2079c.2.2.1
                                    have p2079_3 := h2079c.2.2.2
                                    linarith only [h2064, hlam, p2079_0]
                                  · have p2079_0 := h2079c.1
                                    have p2079_1 := h2079c.2.1
                                    have p2079_2 := h2079c.2.2.1
                                    have p2079_3 := h2079c.2.2.2
                                    linarith only [h2071, hlam, p2079_0]
                                  · have p2079_0 := h2079c.1
                                    have p2079_1 := h2079c.2.1
                                    have p2079_2 := h2079c.2.2.1
                                    have p2079_3 := h2079c.2.2.2
                                    linarith only [h2074, hlam, p2079_0]
                                  · have p2079_0 := h2079c.1
                                    have p2079_1 := h2079c.2.1
                                    have p2079_2 := h2079c.2.2.1
                                    have p2079_3 := h2079c.2.2.2
                                    linarith only [h1198, h2064, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2079_1, u1elo2]
                                  · have p2079_0 := h2079c.1
                                    have p2079_1 := h2079c.2.1
                                    have p2079_2 := h2079c.2.2.1
                                    have p2079_3 := h2079c.2.2.2
                                    linarith only [hlam, p2079_0]
                            · linarith only [h1198, h1459, h2064, h2066, h2068, h2074, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                          · linarith only [h1459, h2065, h2066, h2068, h2073, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                        · linarith only [h1459, h2065, h2072, hlam]
                      · linarith only [h1198, h2064, h2071, hlam]
                    · linarith only [h1198, h2063, h2070, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2124 | h2124
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2125 | h2125
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2126 | h2126
                        · linarith only [h2068, h2069, h2126, hlam]
                        · linarith only [h1459, h2065, h2126, hlam]
                      · linarith only [h1198, h2064, h2125, hlam]
                    · linarith only [h1198, h2063, h2124, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2131 | h2131
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2132 | h2132
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2133 | h2133
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2134 | h2134
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2135 | h2135
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2136 | h2136
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2137 | h2137
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2138 | h2138
                                · linarith only [h1198, h2063, h2138, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
                                · rcases h3bigk with h2140c | h2140c | h2140c | h2140c | h2140c | h2140c | h2140c | h2140c | h2140c | h2140c | h2140c | h2140c | h2140c | h2140c | h2140c | h2140c | h2140c | h2140c | h2140c | h2140c | h2140c | h2140c | h2140c | h2140c | h2140c
                                  · have p2140_0 := h2140c.1
                                    have p2140_1 := h2140c.2.1
                                    have p2140_2 := h2140c.2.2.1
                                    have p2140_3 := h2140c.2.2.2
                                    linarith only [hlam, p2140_0]
                                  · have p2140_0 := h2140c.1
                                    have p2140_1 := h2140c.2.1
                                    have p2140_2 := h2140c.2.2.1
                                    have p2140_3 := h2140c.2.2.2
                                    linarith only [h1198, hlam, p2140_1]
                                  · have p2140_0 := h2140c.1
                                    have p2140_1 := h2140c.2.1
                                    have p2140_2 := h2140c.2.2.1
                                    have p2140_3 := h2140c.2.2.2
                                    linarith only [h1626, hlam, p2140_1]
                                  · have p2140_0 := h2140c.1
                                    have p2140_1 := h2140c.2.1
                                    have p2140_2 := h2140c.2.2.1
                                    have p2140_3 := h2140c.2.2.2
                                    rcases p2140_3 (m.d 0 3) (by simp) with h2144 | h2144
                                    · rcases p2140_3 (m.d 1 3) (by simp) with h2145 | h2145
                                      · rcases p2140_3 (m.d 2 3) (by simp) with h2146 | h2146
                                        · rcases p2140_3 (m.d 3 4) (by simp) with h2147 | h2147
                                          · linarith only [h2147, hlam, p2140_0]
                                          · rcases p2140_3 (m.d 3 5) (by simp) with h2149 | h2149
                                            · linarith only [h2064, h2149, hlam]
                                            · linarith only [h2138, h2149, hlam]
                                        · linarith only [h2135, h2146, hlam]
                                      · linarith only [h2132, h2145, hlam]
                                    · linarith only [h2144, hlam, p2140_0]
                                  · have p2140_0 := h2140c.1
                                    have p2140_1 := h2140c.2.1
                                    have p2140_2 := h2140c.2.2.1
                                    have p2140_3 := h2140c.2.2.2
                                    linarith only [h1198, hlam, hphi, ht01, ht0b, ht5b, p2140_1, u1elo2, u5ehi3]
                                  · have p2140_0 := h2140c.1
                                    have p2140_1 := h2140c.2.1
                                    have p2140_2 := h2140c.2.2.1
                                    have p2140_3 := h2140c.2.2.2
                                    linarith only [h1198, hc01, hlam, hphi, p2140_1, u1elo2]
                                  · have p2140_0 := h2140c.1
                                    have p2140_1 := h2140c.2.1
                                    have p2140_2 := h2140c.2.2.1
                                    have p2140_3 := h2140c.2.2.2
                                    linarith only [hlam, p2140_0]
                                  · have p2140_0 := h2140c.1
                                    have p2140_1 := h2140c.2.1
                                    have p2140_2 := h2140c.2.2.1
                                    have p2140_3 := h2140c.2.2.2
                                    linarith only [h2066, hlam, p2140_1]
                                  · have p2140_0 := h2140c.1
                                    have p2140_1 := h2140c.2.1
                                    have p2140_2 := h2140c.2.2.1
                                    have p2140_3 := h2140c.2.2.2
                                    rcases p2140_3 (m.d 0 3) (by simp) with h2159 | h2159
                                    · linarith only [h1198, h2159, hlam]
                                    · linarith only [h2063, h2159, hlam]
                                  · have p2140_0 := h2140c.1
                                    have p2140_1 := h2140c.2.1
                                    have p2140_2 := h2140c.2.2.1
                                    have p2140_3 := h2140c.2.2.2
                                    linarith only [hlam, hphi, ht01, ht0b, ht5b, p2140_1, u1elo2, u5ehi3]
                                  · have p2140_0 := h2140c.1
                                    have p2140_1 := h2140c.2.1
                                    have p2140_2 := h2140c.2.2.1
                                    have p2140_3 := h2140c.2.2.2
                                    linarith only [h2063, h2065, h2138, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2140_1]
                                  · have p2140_0 := h2140c.1
                                    have p2140_1 := h2140c.2.1
                                    have p2140_2 := h2140c.2.2.1
                                    have p2140_3 := h2140c.2.2.2
                                    linarith only [h1198, hc01, hc23, hlam, hphi, ht12, p2140_1]
                                  · have p2140_0 := h2140c.1
                                    have p2140_1 := h2140c.2.1
                                    have p2140_2 := h2140c.2.2.1
                                    have p2140_3 := h2140c.2.2.2
                                    linarith only [hlam, p2140_0]
                                  · have p2140_0 := h2140c.1
                                    have p2140_1 := h2140c.2.1
                                    have p2140_2 := h2140c.2.2.1
                                    have p2140_3 := h2140c.2.2.2
                                    linarith only [h2066, h2131, h2137, h2138, hlam, p2140_2]
                                  · have p2140_0 := h2140c.1
                                    have p2140_1 := h2140c.2.1
                                    have p2140_2 := h2140c.2.2.1
                                    have p2140_3 := h2140c.2.2.2
                                    rcases p2140_3 (m.d 0 3) (by simp) with h2167 | h2167
                                    · linarith only [h1626, h2167, hlam]
                                    · linarith only [h2064, h2167, hlam]
                                  · have p2140_0 := h2140c.1
                                    have p2140_1 := h2140c.2.1
                                    have p2140_2 := h2140c.2.2.1
                                    have p2140_3 := h2140c.2.2.2
                                    linarith only [h2063, hlam, p2140_0]
                                  · have p2140_0 := h2140c.1
                                    have p2140_1 := h2140c.2.1
                                    have p2140_2 := h2140c.2.2.1
                                    have p2140_3 := h2140c.2.2.2
                                    linarith only [h2132, hlam, p2140_0]
                                  · have p2140_0 := h2140c.1
                                    have p2140_1 := h2140c.2.1
                                    have p2140_2 := h2140c.2.2.1
                                    have p2140_3 := h2140c.2.2.2
                                    linarith only [h2135, hlam, p2140_0]
                                  · have p2140_0 := h2140c.1
                                    have p2140_1 := h2140c.2.1
                                    have p2140_2 := h2140c.2.2.1
                                    have p2140_3 := h2140c.2.2.2
                                    linarith only [hlam, p2140_0]
                                  · have p2140_0 := h2140c.1
                                    have p2140_1 := h2140c.2.1
                                    have p2140_2 := h2140c.2.2.1
                                    have p2140_3 := h2140c.2.2.2
                                    linarith only [h2138, hlam, p2140_1]
                                  · have p2140_0 := h2140c.1
                                    have p2140_1 := h2140c.2.1
                                    have p2140_2 := h2140c.2.2.1
                                    have p2140_3 := h2140c.2.2.2
                                    linarith only [h2064, hlam, p2140_0]
                                  · have p2140_0 := h2140c.1
                                    have p2140_1 := h2140c.2.1
                                    have p2140_2 := h2140c.2.2.1
                                    have p2140_3 := h2140c.2.2.2
                                    linarith only [h2133, hlam, p2140_0]
                                  · have p2140_0 := h2140c.1
                                    have p2140_1 := h2140c.2.1
                                    have p2140_2 := h2140c.2.2.1
                                    have p2140_3 := h2140c.2.2.2
                                    linarith only [h2136, hlam, p2140_0]
                                  · have p2140_0 := h2140c.1
                                    have p2140_1 := h2140c.2.1
                                    have p2140_2 := h2140c.2.2.1
                                    have p2140_3 := h2140c.2.2.2
                                    linarith only [h1198, h2064, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2140_1, u1elo2]
                                  · have p2140_0 := h2140c.1
                                    have p2140_1 := h2140c.2.1
                                    have p2140_2 := h2140c.2.2.1
                                    have p2140_3 := h2140c.2.2.2
                                    linarith only [hlam, p2140_0]
                              · linarith only [h2065, h2068, h2131, h2137, hc04, hlam, hphi, ht0b, ht5b, u5ehi1]
                            · linarith only [h2068, h2131, h2135, h2136, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                          · linarith only [h1626, h2063, h2135, hlam]
                        · linarith only [h1198, h1459, h2063, h2065, h2134, hc01, hlam, hphi, u1elo2]
                      · linarith only [h1198, h2064, h2133, hlam]
                    · linarith only [h1198, h2063, h2132, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2186 | h2186
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2187 | h2187
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2188 | h2188
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2189 | h2189
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2190 | h2190
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2191 | h2191
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2192 | h2192
                                · linarith only [h1198, h2063, h2192, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
                                · rcases h3bigk with h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c | h2194c
                                  · have p2194_0 := h2194c.1
                                    have p2194_1 := h2194c.2.1
                                    have p2194_2 := h2194c.2.2.1
                                    have p2194_3 := h2194c.2.2.2
                                    linarith only [hlam, p2194_0]
                                  · have p2194_0 := h2194c.1
                                    have p2194_1 := h2194c.2.1
                                    have p2194_2 := h2194c.2.2.1
                                    have p2194_3 := h2194c.2.2.2
                                    linarith only [h1198, hlam, p2194_1]
                                  · have p2194_0 := h2194c.1
                                    have p2194_1 := h2194c.2.1
                                    have p2194_2 := h2194c.2.2.1
                                    have p2194_3 := h2194c.2.2.2
                                    linarith only [h1626, hlam, p2194_1]
                                  · have p2194_0 := h2194c.1
                                    have p2194_1 := h2194c.2.1
                                    have p2194_2 := h2194c.2.2.1
                                    have p2194_3 := h2194c.2.2.2
                                    rcases p2194_3 (m.d 0 3) (by simp) with h2198 | h2198
                                    · rcases p2194_3 (m.d 1 3) (by simp) with h2199 | h2199
                                      · rcases p2194_3 (m.d 2 3) (by simp) with h2200 | h2200
                                        · rcases p2194_3 (m.d 3 4) (by simp) with h2201 | h2201
                                          · linarith only [h2201, hlam, p2194_0]
                                          · rcases p2194_3 (m.d 3 5) (by simp) with h2203 | h2203
                                            · linarith only [h2064, h2203, hlam]
                                            · linarith only [h2192, h2203, hlam]
                                        · linarith only [h2189, h2200, hlam]
                                      · linarith only [h2186, h2199, hlam]
                                    · linarith only [h2198, hlam, p2194_0]
                                  · have p2194_0 := h2194c.1
                                    have p2194_1 := h2194c.2.1
                                    have p2194_2 := h2194c.2.2.1
                                    have p2194_3 := h2194c.2.2.2
                                    linarith only [h1198, hlam, hphi, ht01, ht0b, ht5b, p2194_1, u1elo2, u5ehi3]
                                  · have p2194_0 := h2194c.1
                                    have p2194_1 := h2194c.2.1
                                    have p2194_2 := h2194c.2.2.1
                                    have p2194_3 := h2194c.2.2.2
                                    linarith only [h2063, h2065, h2192, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2194_1, u1elo2]
                                  · have p2194_0 := h2194c.1
                                    have p2194_1 := h2194c.2.1
                                    have p2194_2 := h2194c.2.2.1
                                    have p2194_3 := h2194c.2.2.2
                                    linarith only [hlam, p2194_0]
                                  · have p2194_0 := h2194c.1
                                    have p2194_1 := h2194c.2.1
                                    have p2194_2 := h2194c.2.2.1
                                    have p2194_3 := h2194c.2.2.2
                                    linarith only [h2066, hlam, p2194_1]
                                  · have p2194_0 := h2194c.1
                                    have p2194_1 := h2194c.2.1
                                    have p2194_2 := h2194c.2.2.1
                                    have p2194_3 := h2194c.2.2.2
                                    rcases p2194_3 (m.d 0 3) (by simp) with h2213 | h2213
                                    · linarith only [h1198, h2213, hlam]
                                    · linarith only [h2063, h2213, hlam]
                                  · have p2194_0 := h2194c.1
                                    have p2194_1 := h2194c.2.1
                                    have p2194_2 := h2194c.2.2.1
                                    have p2194_3 := h2194c.2.2.2
                                    linarith only [hlam, hphi, ht01, ht0b, ht5b, p2194_1, u1elo2, u5ehi3]
                                  · have p2194_0 := h2194c.1
                                    have p2194_1 := h2194c.2.1
                                    have p2194_2 := h2194c.2.2.1
                                    have p2194_3 := h2194c.2.2.2
                                    linarith only [h2063, h2065, h2192, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2194_1]
                                  · have p2194_0 := h2194c.1
                                    have p2194_1 := h2194c.2.1
                                    have p2194_2 := h2194c.2.2.1
                                    have p2194_3 := h2194c.2.2.2
                                    linarith only [h1198, hc01, hc23, hlam, hphi, ht12, p2194_1]
                                  · have p2194_0 := h2194c.1
                                    have p2194_1 := h2194c.2.1
                                    have p2194_2 := h2194c.2.2.1
                                    have p2194_3 := h2194c.2.2.2
                                    linarith only [hlam, p2194_0]
                                  · have p2194_0 := h2194c.1
                                    have p2194_1 := h2194c.2.1
                                    have p2194_2 := h2194c.2.2.1
                                    have p2194_3 := h2194c.2.2.2
                                    rcases p2194_3 (m.d 0 3) (by simp) with h2220 | h2220
                                    · linarith only [h1626, h2220, hlam]
                                    · linarith only [h2063, h2220, hlam]
                                  · have p2194_0 := h2194c.1
                                    have p2194_1 := h2194c.2.1
                                    have p2194_2 := h2194c.2.2.1
                                    have p2194_3 := h2194c.2.2.2
                                    rcases p2194_3 (m.d 0 3) (by simp) with h2223 | h2223
                                    · linarith only [h1626, h2223, hlam]
                                    · linarith only [h2064, h2223, hlam]
                                  · have p2194_0 := h2194c.1
                                    have p2194_1 := h2194c.2.1
                                    have p2194_2 := h2194c.2.2.1
                                    have p2194_3 := h2194c.2.2.2
                                    linarith only [h2063, hlam, p2194_0]
                                  · have p2194_0 := h2194c.1
                                    have p2194_1 := h2194c.2.1
                                    have p2194_2 := h2194c.2.2.1
                                    have p2194_3 := h2194c.2.2.2
                                    linarith only [h2186, hlam, p2194_0]
                                  · have p2194_0 := h2194c.1
                                    have p2194_1 := h2194c.2.1
                                    have p2194_2 := h2194c.2.2.1
                                    have p2194_3 := h2194c.2.2.2
                                    linarith only [h2189, hlam, p2194_0]
                                  · have p2194_0 := h2194c.1
                                    have p2194_1 := h2194c.2.1
                                    have p2194_2 := h2194c.2.2.1
                                    have p2194_3 := h2194c.2.2.2
                                    linarith only [hlam, p2194_0]
                                  · have p2194_0 := h2194c.1
                                    have p2194_1 := h2194c.2.1
                                    have p2194_2 := h2194c.2.2.1
                                    have p2194_3 := h2194c.2.2.2
                                    linarith only [h2192, hlam, p2194_1]
                                  · have p2194_0 := h2194c.1
                                    have p2194_1 := h2194c.2.1
                                    have p2194_2 := h2194c.2.2.1
                                    have p2194_3 := h2194c.2.2.2
                                    linarith only [h2064, hlam, p2194_0]
                                  · have p2194_0 := h2194c.1
                                    have p2194_1 := h2194c.2.1
                                    have p2194_2 := h2194c.2.2.1
                                    have p2194_3 := h2194c.2.2.2
                                    linarith only [h2187, hlam, p2194_0]
                                  · have p2194_0 := h2194c.1
                                    have p2194_1 := h2194c.2.1
                                    have p2194_2 := h2194c.2.2.1
                                    have p2194_3 := h2194c.2.2.2
                                    linarith only [h2190, hlam, p2194_0]
                                  · have p2194_0 := h2194c.1
                                    have p2194_1 := h2194c.2.1
                                    have p2194_2 := h2194c.2.2.1
                                    have p2194_3 := h2194c.2.2.2
                                    linarith only [h1198, h2064, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2194_1, u1elo2]
                                  · have p2194_0 := h2194c.1
                                    have p2194_1 := h2194c.2.1
                                    have p2194_2 := h2194c.2.2.1
                                    have p2194_3 := h2194c.2.2.2
                                    linarith only [hlam, p2194_0]
                              · linarith only [h0, h1198, h2063, h2065, h2068, h2191, hc01, hlam, hphi, u1elo2]
                            · linarith only [h0, h1198, h2064, h2068, h2189, h2190, hc01, hlam, hphi, u1elo2]
                          · linarith only [h1626, h2063, h2189, hlam]
                        · linarith only [h1459, h2065, h2188, hlam]
                      · linarith only [h1198, h2064, h2187, hlam]
                    · linarith only [h1198, h2063, h2186, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2242 | h2242
              · linarith only [h0, h1626, h2242, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2244 | h2244
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2245 | h2245
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2246 | h2246
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2247 | h2247
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2248 | h2248
                        · linarith only [h1459, h2065, h2248, hc01, hlam, hphi, u1elo3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2250 | h2250
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2251 | h2251
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2252 | h2252
                              · linarith only [h2242, h2244, h2248, h2252, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2254 | h2254
                                · linarith only [h1459, h2248, h2254, hc01, hc34, hlam, hphi, ht12, ht23]
                                · rcases h3bigk with h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c | h2256c
                                  · have p2256_0 := h2256c.1
                                    have p2256_1 := h2256c.2.1
                                    have p2256_2 := h2256c.2.2.1
                                    have p2256_3 := h2256c.2.2.2
                                    linarith only [hlam, p2256_0]
                                  · have p2256_0 := h2256c.1
                                    have p2256_1 := h2256c.2.1
                                    have p2256_2 := h2256c.2.2.1
                                    have p2256_3 := h2256c.2.2.2
                                    linarith only [h1198, hlam, p2256_1]
                                  · have p2256_0 := h2256c.1
                                    have p2256_1 := h2256c.2.1
                                    have p2256_2 := h2256c.2.2.1
                                    have p2256_3 := h2256c.2.2.2
                                    linarith only [h1626, hlam, p2256_1]
                                  · have p2256_0 := h2256c.1
                                    have p2256_1 := h2256c.2.1
                                    have p2256_2 := h2256c.2.2.1
                                    have p2256_3 := h2256c.2.2.2
                                    rcases p2256_3 (m.d 0 3) (by simp) with h2260 | h2260
                                    · rcases p2256_3 (m.d 1 3) (by simp) with h2261 | h2261
                                      · rcases p2256_3 (m.d 2 3) (by simp) with h2262 | h2262
                                        · rcases p2256_3 (m.d 3 4) (by simp) with h2263 | h2263
                                          · linarith only [h2263, hlam, p2256_0]
                                          · rcases p2256_3 (m.d 3 5) (by simp) with h2265 | h2265
                                            · linarith only [h2064, h2265, hlam]
                                            · linarith only [h2254, h2265, hlam]
                                        · linarith only [h2250, h2262, hlam]
                                      · linarith only [h2246, h2261, hlam]
                                    · linarith only [h2260, hlam, p2256_0]
                                  · have p2256_0 := h2256c.1
                                    have p2256_1 := h2256c.2.1
                                    have p2256_2 := h2256c.2.2.1
                                    have p2256_3 := h2256c.2.2.2
                                    linarith only [h1198, hlam, hphi, ht01, ht0b, ht5b, p2256_1, u1elo2, u5ehi3]
                                  · have p2256_0 := h2256c.1
                                    have p2256_1 := h2256c.2.1
                                    have p2256_2 := h2256c.2.2.1
                                    have p2256_3 := h2256c.2.2.2
                                    linarith only [h1198, hc01, hlam, hphi, p2256_1, u1elo2]
                                  · have p2256_0 := h2256c.1
                                    have p2256_1 := h2256c.2.1
                                    have p2256_2 := h2256c.2.2.1
                                    have p2256_3 := h2256c.2.2.2
                                    linarith only [hlam, p2256_0]
                                  · have p2256_0 := h2256c.1
                                    have p2256_1 := h2256c.2.1
                                    have p2256_2 := h2256c.2.2.1
                                    have p2256_3 := h2256c.2.2.2
                                    linarith only [h2242, hlam, p2256_1]
                                  · have p2256_0 := h2256c.1
                                    have p2256_1 := h2256c.2.1
                                    have p2256_2 := h2256c.2.2.1
                                    have p2256_3 := h2256c.2.2.2
                                    rcases p2256_3 (m.d 0 3) (by simp) with h2275 | h2275
                                    · linarith only [h1198, h2275, hlam]
                                    · linarith only [h2063, h2275, hlam]
                                  · have p2256_0 := h2256c.1
                                    have p2256_1 := h2256c.2.1
                                    have p2256_2 := h2256c.2.2.1
                                    have p2256_3 := h2256c.2.2.2
                                    linarith only [hlam, hphi, ht01, ht0b, ht5b, p2256_1, u1elo2, u5ehi3]
                                  · have p2256_0 := h2256c.1
                                    have p2256_1 := h2256c.2.1
                                    have p2256_2 := h2256c.2.2.1
                                    have p2256_3 := h2256c.2.2.2
                                    linarith only [h2064, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2256_1, u5ehi3]
                                  · have p2256_0 := h2256c.1
                                    have p2256_1 := h2256c.2.1
                                    have p2256_2 := h2256c.2.2.1
                                    have p2256_3 := h2256c.2.2.2
                                    linarith only [h1198, hc01, hc23, hlam, hphi, ht12, p2256_1]
                                  · have p2256_0 := h2256c.1
                                    have p2256_1 := h2256c.2.1
                                    have p2256_2 := h2256c.2.2.1
                                    have p2256_3 := h2256c.2.2.2
                                    linarith only [hlam, p2256_0]
                                  · have p2256_0 := h2256c.1
                                    have p2256_1 := h2256c.2.1
                                    have p2256_2 := h2256c.2.2.1
                                    have p2256_3 := h2256c.2.2.2
                                    rcases p2256_3 (m.d 0 3) (by simp) with h2282 | h2282
                                    · linarith only [h1626, h2282, hlam]
                                    · linarith only [h2063, h2282, hlam]
                                  · have p2256_0 := h2256c.1
                                    have p2256_1 := h2256c.2.1
                                    have p2256_2 := h2256c.2.2.1
                                    have p2256_3 := h2256c.2.2.2
                                    rcases p2256_3 (m.d 0 3) (by simp) with h2285 | h2285
                                    · linarith only [h1626, h2285, hlam]
                                    · linarith only [h2064, h2285, hlam]
                                  · have p2256_0 := h2256c.1
                                    have p2256_1 := h2256c.2.1
                                    have p2256_2 := h2256c.2.2.1
                                    have p2256_3 := h2256c.2.2.2
                                    linarith only [h2063, hlam, p2256_0]
                                  · have p2256_0 := h2256c.1
                                    have p2256_1 := h2256c.2.1
                                    have p2256_2 := h2256c.2.2.1
                                    have p2256_3 := h2256c.2.2.2
                                    linarith only [h2246, hlam, p2256_0]
                                  · have p2256_0 := h2256c.1
                                    have p2256_1 := h2256c.2.1
                                    have p2256_2 := h2256c.2.2.1
                                    have p2256_3 := h2256c.2.2.2
                                    linarith only [h2250, hlam, p2256_0]
                                  · have p2256_0 := h2256c.1
                                    have p2256_1 := h2256c.2.1
                                    have p2256_2 := h2256c.2.2.1
                                    have p2256_3 := h2256c.2.2.2
                                    linarith only [hlam, p2256_0]
                                  · have p2256_0 := h2256c.1
                                    have p2256_1 := h2256c.2.1
                                    have p2256_2 := h2256c.2.2.1
                                    have p2256_3 := h2256c.2.2.2
                                    linarith only [h2254, hlam, p2256_1]
                                  · have p2256_0 := h2256c.1
                                    have p2256_1 := h2256c.2.1
                                    have p2256_2 := h2256c.2.2.1
                                    have p2256_3 := h2256c.2.2.2
                                    linarith only [h2064, hlam, p2256_0]
                                  · have p2256_0 := h2256c.1
                                    have p2256_1 := h2256c.2.1
                                    have p2256_2 := h2256c.2.2.1
                                    have p2256_3 := h2256c.2.2.2
                                    linarith only [h2247, hlam, p2256_0]
                                  · have p2256_0 := h2256c.1
                                    have p2256_1 := h2256c.2.1
                                    have p2256_2 := h2256c.2.2.1
                                    have p2256_3 := h2256c.2.2.2
                                    linarith only [h2251, hlam, p2256_0]
                                  · have p2256_0 := h2256c.1
                                    have p2256_1 := h2256c.2.1
                                    have p2256_2 := h2256c.2.2.1
                                    have p2256_3 := h2256c.2.2.2
                                    linarith only [h1198, h2064, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2256_1, u1elo2]
                                  · have p2256_0 := h2256c.1
                                    have p2256_1 := h2256c.2.1
                                    have p2256_2 := h2256c.2.2.1
                                    have p2256_3 := h2256c.2.2.2
                                    linarith only [hlam, p2256_0]
                            · linarith only [h1198, h1624, h2064, h2242, h2245, h2251, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi0]
                          · linarith only [h0, h2242, h2250, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h1198, h2064, h2247, hlam]
                    · linarith only [h1198, h2063, h2246, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2302 | h2302
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2303 | h2303
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2304 | h2304
                        · linarith only [h1459, h2065, h2304, hc01, hlam, hphi, u1elo3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2306 | h2306
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2307 | h2307
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2308 | h2308
                              · linarith only [h1459, h2304, h2308, hc01, hc24, hlam, hphi, ht12]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2310 | h2310
                                · linarith only [h2244, h2245, h2306, h2308, h2310, hlam]
                                · rcases h3bigk with h2312c | h2312c | h2312c | h2312c | h2312c | h2312c | h2312c | h2312c | h2312c | h2312c | h2312c | h2312c | h2312c | h2312c | h2312c | h2312c | h2312c | h2312c | h2312c | h2312c | h2312c | h2312c | h2312c | h2312c | h2312c
                                  · have p2312_0 := h2312c.1
                                    have p2312_1 := h2312c.2.1
                                    have p2312_2 := h2312c.2.2.1
                                    have p2312_3 := h2312c.2.2.2
                                    linarith only [hlam, p2312_0]
                                  · have p2312_0 := h2312c.1
                                    have p2312_1 := h2312c.2.1
                                    have p2312_2 := h2312c.2.2.1
                                    have p2312_3 := h2312c.2.2.2
                                    linarith only [h1198, hlam, p2312_1]
                                  · have p2312_0 := h2312c.1
                                    have p2312_1 := h2312c.2.1
                                    have p2312_2 := h2312c.2.2.1
                                    have p2312_3 := h2312c.2.2.2
                                    linarith only [h1626, hlam, p2312_1]
                                  · have p2312_0 := h2312c.1
                                    have p2312_1 := h2312c.2.1
                                    have p2312_2 := h2312c.2.2.1
                                    have p2312_3 := h2312c.2.2.2
                                    rcases p2312_3 (m.d 0 3) (by simp) with h2316 | h2316
                                    · rcases p2312_3 (m.d 1 3) (by simp) with h2317 | h2317
                                      · rcases p2312_3 (m.d 2 3) (by simp) with h2318 | h2318
                                        · rcases p2312_3 (m.d 3 4) (by simp) with h2319 | h2319
                                          · linarith only [h2319, hlam, p2312_0]
                                          · rcases p2312_3 (m.d 3 5) (by simp) with h2321 | h2321
                                            · linarith only [h2064, h2321, hlam]
                                            · linarith only [h2310, h2321, hlam]
                                        · linarith only [h2306, h2318, hlam]
                                      · linarith only [h2302, h2317, hlam]
                                    · linarith only [h2316, hlam, p2312_0]
                                  · have p2312_0 := h2312c.1
                                    have p2312_1 := h2312c.2.1
                                    have p2312_2 := h2312c.2.2.1
                                    have p2312_3 := h2312c.2.2.2
                                    linarith only [h1198, hlam, hphi, ht01, ht0b, ht5b, p2312_1, u1elo2, u5ehi3]
                                  · have p2312_0 := h2312c.1
                                    have p2312_1 := h2312c.2.1
                                    have p2312_2 := h2312c.2.2.1
                                    have p2312_3 := h2312c.2.2.2
                                    linarith only [h2064, hlam, hphi, ht01, ht0b, ht5b, p2312_1, u1elo2, u5ehi0]
                                  · have p2312_0 := h2312c.1
                                    have p2312_1 := h2312c.2.1
                                    have p2312_2 := h2312c.2.2.1
                                    have p2312_3 := h2312c.2.2.2
                                    linarith only [hlam, p2312_0]
                                  · have p2312_0 := h2312c.1
                                    have p2312_1 := h2312c.2.1
                                    have p2312_2 := h2312c.2.2.1
                                    have p2312_3 := h2312c.2.2.2
                                    linarith only [h2242, hlam, p2312_1]
                                  · have p2312_0 := h2312c.1
                                    have p2312_1 := h2312c.2.1
                                    have p2312_2 := h2312c.2.2.1
                                    have p2312_3 := h2312c.2.2.2
                                    rcases p2312_3 (m.d 0 3) (by simp) with h2331 | h2331
                                    · linarith only [h1198, h2331, hlam]
                                    · linarith only [h2063, h2331, hlam]
                                  · have p2312_0 := h2312c.1
                                    have p2312_1 := h2312c.2.1
                                    have p2312_2 := h2312c.2.2.1
                                    have p2312_3 := h2312c.2.2.2
                                    linarith only [hlam, hphi, ht01, ht0b, ht5b, p2312_1, u1elo2, u5ehi3]
                                  · have p2312_0 := h2312c.1
                                    have p2312_1 := h2312c.2.1
                                    have p2312_2 := h2312c.2.2.1
                                    have p2312_3 := h2312c.2.2.2
                                    linarith only [h2064, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2312_1, u5ehi3]
                                  · have p2312_0 := h2312c.1
                                    have p2312_1 := h2312c.2.1
                                    have p2312_2 := h2312c.2.2.1
                                    have p2312_3 := h2312c.2.2.2
                                    linarith only [h1198, hc01, hc23, hlam, hphi, ht12, p2312_1]
                                  · have p2312_0 := h2312c.1
                                    have p2312_1 := h2312c.2.1
                                    have p2312_2 := h2312c.2.2.1
                                    have p2312_3 := h2312c.2.2.2
                                    linarith only [hlam, p2312_0]
                                  · have p2312_0 := h2312c.1
                                    have p2312_1 := h2312c.2.1
                                    have p2312_2 := h2312c.2.2.1
                                    have p2312_3 := h2312c.2.2.2
                                    rcases p2312_3 (m.d 0 3) (by simp) with h2338 | h2338
                                    · linarith only [h1626, h2338, hlam]
                                    · linarith only [h2063, h2338, hlam]
                                  · have p2312_0 := h2312c.1
                                    have p2312_1 := h2312c.2.1
                                    have p2312_2 := h2312c.2.2.1
                                    have p2312_3 := h2312c.2.2.2
                                    rcases p2312_3 (m.d 0 3) (by simp) with h2341 | h2341
                                    · linarith only [h1626, h2341, hlam]
                                    · linarith only [h2064, h2341, hlam]
                                  · have p2312_0 := h2312c.1
                                    have p2312_1 := h2312c.2.1
                                    have p2312_2 := h2312c.2.2.1
                                    have p2312_3 := h2312c.2.2.2
                                    linarith only [h2063, hlam, p2312_0]
                                  · have p2312_0 := h2312c.1
                                    have p2312_1 := h2312c.2.1
                                    have p2312_2 := h2312c.2.2.1
                                    have p2312_3 := h2312c.2.2.2
                                    linarith only [h2302, hlam, p2312_0]
                                  · have p2312_0 := h2312c.1
                                    have p2312_1 := h2312c.2.1
                                    have p2312_2 := h2312c.2.2.1
                                    have p2312_3 := h2312c.2.2.2
                                    linarith only [h2306, hlam, p2312_0]
                                  · have p2312_0 := h2312c.1
                                    have p2312_1 := h2312c.2.1
                                    have p2312_2 := h2312c.2.2.1
                                    have p2312_3 := h2312c.2.2.2
                                    linarith only [hlam, p2312_0]
                                  · have p2312_0 := h2312c.1
                                    have p2312_1 := h2312c.2.1
                                    have p2312_2 := h2312c.2.2.1
                                    have p2312_3 := h2312c.2.2.2
                                    linarith only [h2310, hlam, p2312_1]
                                  · have p2312_0 := h2312c.1
                                    have p2312_1 := h2312c.2.1
                                    have p2312_2 := h2312c.2.2.1
                                    have p2312_3 := h2312c.2.2.2
                                    linarith only [h2064, hlam, p2312_0]
                                  · have p2312_0 := h2312c.1
                                    have p2312_1 := h2312c.2.1
                                    have p2312_2 := h2312c.2.2.1
                                    have p2312_3 := h2312c.2.2.2
                                    linarith only [h2303, hlam, p2312_0]
                                  · have p2312_0 := h2312c.1
                                    have p2312_1 := h2312c.2.1
                                    have p2312_2 := h2312c.2.2.1
                                    have p2312_3 := h2312c.2.2.2
                                    linarith only [h2307, hlam, p2312_0]
                                  · have p2312_0 := h2312c.1
                                    have p2312_1 := h2312c.2.1
                                    have p2312_2 := h2312c.2.2.1
                                    have p2312_3 := h2312c.2.2.2
                                    linarith only [h1198, h2064, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2312_1, u1elo2]
                                  · have p2312_0 := h2312c.1
                                    have p2312_1 := h2312c.2.1
                                    have p2312_2 := h2312c.2.2.1
                                    have p2312_3 := h2312c.2.2.2
                                    linarith only [hlam, p2312_0]
                            · linarith only [h0, h1198, h1626, h2064, h2307, hc01, hlam, hphi, u1elo2]
                          · linarith only [h1459, h2242, h2244, h2306, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h1198, h2064, h2303, hlam]
                    · linarith only [h1198, h1459, h2063, h2064, h2242, h2244, h2302, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2358 | h2358
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2359 | h2359
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2360 | h2360
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2361 | h2361
                        · linarith only [h1459, h2065, h2359, h2361, hc01, hlam, hphi, u1elo2]
                        · linarith only [h2244, h2358, h2361, hlam]
                      · linarith only [h1198, h2064, h2360, hlam]
                    · linarith only [h1198, h1459, h2063, h2064, h2359, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2366 | h2366
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2367 | h2367
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2368 | h2368
                        · linarith only [h1459, h2065, h2366, h2368, hc01, hlam, hphi, u1elo2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2370 | h2370
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2371 | h2371
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2372 | h2372
                              · linarith only [h0, h2244, h2368, h2372, hc01, hc24, hlam, hphi, ht12]
                              · linarith only [h0, h2244, h2372, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                            · linarith only [h0, h1198, h1626, h2064, h2371, hc01, hlam, hphi, u1elo2]
                          · linarith only [h0, h2242, h2370, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h1198, h2064, h2367, hlam]
                    · linarith only [h1198, h2063, h2366, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2379 | h2379
            · linarith only [h2063, h2064, h2379, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2381 | h2381
              · linarith only [h0, h1626, h2381, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2383 | h2383
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2384 | h2384
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2385 | h2385
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2386 | h2386
                      · linarith only [h2063, h2064, h2386, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · linarith only [h2381, h2384, h2386, hlam]
                    · linarith only [h2063, h2381, h2384, h2385, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2390 | h2390
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2391 | h2391
                      · linarith only [h2063, h2064, h2391, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2393 | h2393
                        · linarith only [h1459, h2379, h2383, h2393, hc01, hlam, hphi, u1elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2395 | h2395
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2396 | h2396
                            · linarith only [h0, h2381, h2391, h2396, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h1459, h2381, h2383, h2396, hc01, hc35, hlam, hphi, ht12, ht23]
                          · linarith only [h1459, h2063, h2381, h2383, h2395, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                    · linarith only [h1198, h1459, h2063, h2383, h2390, hc01, hlam, hphi, u1elo1]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2401 | h2401
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2402 | h2402
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2403 | h2403
                      · linarith only [h2063, h2064, h2403, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · linarith only [h2381, h2401, h2403, hlam]
                    · linarith only [h2063, h2381, h2401, h2402, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2407 | h2407
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2408 | h2408
                      · linarith only [h2063, h2064, h2408, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2410 | h2410
                        · linarith only [h1459, h2379, h2407, h2410, hc01, hlam, hphi, u1elo2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2412 | h2412
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2413 | h2413
                            · linarith only [h1198, h2408, h2413, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h0, h2381, h2413, hc01, hc35, hlam, hphi, ht12, ht23]
                          · linarith only [h0, h2063, h2381, h2412, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                    · linarith only [h1198, h1459, h2063, h2407, hc01, hlam, hphi, u1elo3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2418 | h2418
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2419 | h2419
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2420 | h2420
              · linarith only [h0, h1626, h2420, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2422 | h2422
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2423 | h2423
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2424 | h2424
                    · linarith only [h2063, h2418, h2424, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
                    · linarith only [h2420, h2422, h2424, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2427 | h2427
                    · linarith only [h2063, h2418, h2427, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
                    · linarith only [h2420, h2422, h2427, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2430 | h2430
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2431 | h2431
                    · linarith only [h2063, h2418, h2431, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2433 | h2433
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2434 | h2434
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2435 | h2435
                          · linarith only [h1198, h2431, h2435, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h2420, h2430, h2435, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · linarith only [h2419, h2420, h2430, h2431, h2434, hc04, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · linarith only [h2418, h2420, h2430, h2433, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2440 | h2440
                    · linarith only [h2063, h2418, h2440, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2442 | h2442
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2443 | h2443
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2444 | h2444
                          · linarith only [h1198, h2440, h2444, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h0, h2420, h2444, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h1459, h2419, h2443, hlam]
                      · linarith only [h1198, h2418, h2442, hlam]
            · linarith only [h2063, h2418, h2419, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2450 | h2450
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2451 | h2451
              · linarith only [h0, h1626, h2451, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2453 | h2453
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2454 | h2454
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2455 | h2455
                    · linarith only [h0, h1626, h2063, h2455, hc01, hlam, hphi, u1elo2]
                    · linarith only [h2451, h2453, h2455, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2458 | h2458
                    · linarith only [h0, h1626, h2063, h2458, hc01, hlam, hphi, u1elo2]
                    · linarith only [h2451, h2453, h2458, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2461 | h2461
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2462 | h2462
                    · linarith only [h0, h1626, h2063, h2462, hc01, hlam, hphi, u1elo2]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2464 | h2464
                      · linarith only [h0, h1626, h2418, h2462, h2464, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h2451, h2461, h2464, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2467 | h2467
                    · linarith only [h0, h1626, h2063, h2467, hc01, hlam, hphi, u1elo2]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2469 | h2469
                      · linarith only [h0, h1626, h2418, h2467, h2469, hc01, hc34, hlam, hphi, ht12, ht23]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2471 | h2471
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2472 | h2472
                          · linarith only [h0, h2451, h2467, h2472, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h0, h2451, h2472, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h1459, h2450, h2471, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2476 | h2476
              · linarith only [h0, h1626, h2476, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2478 | h2478
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2479 | h2479
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2480 | h2480
                    · linarith only [h0, h1626, h2063, h2480, hc01, hlam, hphi, u1elo2]
                    · linarith only [h2476, h2478, h2480, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2483 | h2483
                    · linarith only [h0, h1626, h2063, h2483, hc01, hlam, hphi, u1elo2]
                    · linarith only [h2476, h2478, h2483, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2486 | h2486
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2487 | h2487
                    · linarith only [h0, h1626, h2063, h2487, hc01, hlam, hphi, u1elo2]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2489 | h2489
                      · linarith only [h0, h1626, h2418, h2487, h2489, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h2476, h2486, h2489, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2492 | h2492
                    · linarith only [h0, h1626, h2063, h2492, hc01, hlam, hphi, u1elo2]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2494 | h2494
                      · linarith only [h0, h1626, h2418, h2492, h2494, hc01, hc34, hlam, hphi, ht12, ht23]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2496 | h2496
                        · linarith only [h0, h1626, h2063, h2450, h2496, hc01, hlam, hphi, u1elo3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2498 | h2498
                          · linarith only [h0, h2476, h2492, h2498, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h0, h2476, h2498, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 5002000 in
set_option maxHeartbeats 5002000 in
theorem r1l7_11_13_25_L_0_L_I_M_IR_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1198 | h1198
  · exact r1l7_11_13_25_L_0_L_I_M_IR_x1_x0 m hb1 hb3 hb5 h0 h1198
  · exact r1l7_11_13_25_L_0_L_I_M_IR_x1_x1 m hb1 hb3 hb5 h0 h1198

set_option maxHeartbeats 5002000 in
set_option maxHeartbeats 5002000 in
theorem r1l7_11_13_25_L_0_L_I_M_IR (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_13_25_L_0_L_I_M_IR_x0 m hb1 hb3 hb5 h0
  · exact r1l7_11_13_25_L_0_L_I_M_IR_x1 m hb1 hb3 hb5 h0

end R2N4
