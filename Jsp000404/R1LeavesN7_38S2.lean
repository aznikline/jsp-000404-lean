import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_38S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7280000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_LR_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1460 | h1460
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1461 | h1461
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1462 | h1462
      · linarith only [h0, h1, h1462, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1464 | h1464
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1465 | h1465
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1466 | h1466
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1467 | h1467
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1468 | h1468
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1469 | h1469
                  · linarith only [h1462, h1464, h1468, h1469, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1471 | h1471
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1472 | h1472
                      · linarith only [h0, h1, h1472, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                      · linarith only [h1471, h1472, hc24, hlam, hphi, ht45, u5elo2]
                    · linarith only [h0, h1, h1464, h1469, h1471, hc12, hc23, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1476 | h1476
                  · linarith only [h0, h1, h1462, h1476, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1478 | h1478
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1479 | h1479
                      · linarith only [h0, h1, h1476, h1479, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                      · linarith only [h0, h1, h1465, h1476, h1479, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h1464, h1476, h1478, hc12, hc23, hlam, hphi]
              · linarith only [h0, h1, h1465, h1467, hlam, hphi, u5ehi7, u5elo3]
            · linarith only [h0, h1, h1464, h1466, hlam]
          · linarith only [h1464, h1465, hc24, hlam, hphi, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1486 | h1486
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1487 | h1487
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1488 | h1488
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1489 | h1489
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1490 | h1490
                  · linarith only [h0, h1462, h1486, h1490, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1492 | h1492
                    · linarith only [h0, h1, h1464, h1486, h1490, h1492, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1494 | h1494
                      · linarith only [h1, h1460, h1490, h1492, h1494, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                      · linarith only [h1464, h1486, h1494, hc12, hc24, hlam, hphi]
                · linarith only [h1464, h1486, h1489, hlam, hphi, u5ehi7, u5elo4]
              · linarith only [h1, h1460, h1464, h1486, h1488, hlam, hphi, u5ehi7, u5elo3]
            · linarith only [h1, h1460, h1487, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1500 | h1500
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1501 | h1501
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1502 | h1502
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1503 | h1503
                  · linarith only [h0, h1462, h1486, h1503, hc03, hlam, hphi, ht34, ht45, u5elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1505 | h1505
                    · linarith only [h0, h1464, h1486, h1502, h1505, hlam, hphi, u5ehi9, u5elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1507 | h1507
                      · linarith only [h0, h1486, h1507, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1509 | h1509
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1510 | h1510
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1511 | h1511
                            · linarith only [h1, h1460, h1503, h1511, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                            · linarith only [h1, h1460, h1502, h1503, h1505, h1511, hc12, hc23, hlam, hphi]
                          · linarith only [h1, h1460, h1502, h1510, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
                        · linarith only [h1, h1460, h1502, h1509, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1516 | h1516
                  · linarith only [h0, h1464, h1502, h1516, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1518 | h1518
                    · linarith only [h0, h1464, h1518, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1520 | h1520
                      · linarith only [h0, h1464, h1502, h1520, hlam, hphi, u5ehi7, u5elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1522 | h1522
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1523 | h1523
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1524 | h1524
                            · linarith only [h1460, h1502, h1524, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1526 | h1526
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1527 | h1527
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1528 | h1528
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1529 | h1529
                                    · linarith only [h1460, h1502, h1522, h1529, hlam]
                                    · rcases h2bigk with h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c | h1531c
                                      · have p1531_0 := h1531c.1
                                        have p1531_1 := h1531c.2.1
                                        have p1531_2 := h1531c.2.2.1
                                        have p1531_3 := h1531c.2.2.2
                                        linarith only [hlam, p1531_0]
                                      · have p1531_0 := h1531c.1
                                        have p1531_1 := h1531c.2.1
                                        have p1531_2 := h1531c.2.2.1
                                        have p1531_3 := h1531c.2.2.2
                                        linarith only [h1464, h1502, h1528, hc12, hlam, hphi, ht23, ht34, ht45, p1531_1, u5elo2]
                                      · have p1531_0 := h1531c.1
                                        have p1531_1 := h1531c.2.1
                                        have p1531_2 := h1531c.2.2.1
                                        have p1531_3 := h1531c.2.2.2
                                        linarith only [h1462, hlam, p1531_0]
                                      · have p1531_0 := h1531c.1
                                        have p1531_1 := h1531c.2.1
                                        have p1531_2 := h1531c.2.2.1
                                        have p1531_3 := h1531c.2.2.2
                                        linarith only [h1464, hlam, p1531_0]
                                      · have p1531_0 := h1531c.1
                                        have p1531_1 := h1531c.2.1
                                        have p1531_2 := h1531c.2.2.1
                                        have p1531_3 := h1531c.2.2.2
                                        linarith only [h1486, hlam, p1531_0]
                                      · have p1531_0 := h1531c.1
                                        have p1531_1 := h1531c.2.1
                                        have p1531_2 := h1531c.2.2.1
                                        have p1531_3 := h1531c.2.2.2
                                        linarith only [h0, hlam, p1531_0]
                                      · have p1531_0 := h1531c.1
                                        have p1531_1 := h1531c.2.1
                                        have p1531_2 := h1531c.2.2.1
                                        have p1531_3 := h1531c.2.2.2
                                        linarith only [hlam, p1531_0]
                                      · have p1531_0 := h1531c.1
                                        have p1531_1 := h1531c.2.1
                                        have p1531_2 := h1531c.2.2.1
                                        have p1531_3 := h1531c.2.2.2
                                        linarith only [h1516, hlam, p1531_0]
                                      · have p1531_0 := h1531c.1
                                        have p1531_1 := h1531c.2.1
                                        have p1531_2 := h1531c.2.2.1
                                        have p1531_3 := h1531c.2.2.2
                                        linarith only [h1518, hlam, p1531_0]
                                      · have p1531_0 := h1531c.1
                                        have p1531_1 := h1531c.2.1
                                        have p1531_2 := h1531c.2.2.1
                                        have p1531_3 := h1531c.2.2.2
                                        linarith only [h1520, hlam, p1531_0]
                                      · have p1531_0 := h1531c.1
                                        have p1531_1 := h1531c.2.1
                                        have p1531_2 := h1531c.2.2.1
                                        have p1531_3 := h1531c.2.2.2
                                        rcases p1531_3 (m.d 0 2) (by simp) with h1542 | h1542
                                        · linarith only [h1542, hlam, p1531_0]
                                        · rcases p1531_3 (m.d 1 2) (by simp) with h1544 | h1544
                                          · linarith only [h1516, h1544, hlam]
                                          · rcases p1531_3 (m.d 2 3) (by simp) with h1546 | h1546
                                            · rcases p1531_3 (m.d 2 4) (by simp) with h1547 | h1547
                                              · linarith only [h1526, h1547, hlam]
                                              · linarith only [h1464, h1547, hlam]
                                            · linarith only [h1546, hlam, p1531_0]
                                      · have p1531_0 := h1531c.1
                                        have p1531_1 := h1531c.2.1
                                        have p1531_2 := h1531c.2.2.1
                                        have p1531_3 := h1531c.2.2.2
                                        rcases p1531_3 (m.d 0 2) (by simp) with h1551 | h1551
                                        · linarith only [h1462, h1551, hlam]
                                        · linarith only [h0, h1551, hlam]
                                      · have p1531_0 := h1531c.1
                                        have p1531_1 := h1531c.2.1
                                        have p1531_2 := h1531c.2.2.1
                                        have p1531_3 := h1531c.2.2.2
                                        linarith only [hlam, p1531_0]
                                      · have p1531_0 := h1531c.1
                                        have p1531_1 := h1531c.2.1
                                        have p1531_2 := h1531c.2.2.1
                                        have p1531_3 := h1531c.2.2.2
                                        linarith only [h1464, h1502, h1528, hc02, hc23, hlam, hphi, p1531_1]
                                      · have p1531_0 := h1531c.1
                                        have p1531_1 := h1531c.2.1
                                        have p1531_2 := h1531c.2.2.1
                                        have p1531_3 := h1531c.2.2.2
                                        linarith only [h0, h1464, h1502, h1528, hc12, hc23, hlam, hphi, p1531_1]
                                      · have p1531_0 := h1531c.1
                                        have p1531_1 := h1531c.2.1
                                        have p1531_2 := h1531c.2.2.1
                                        have p1531_3 := h1531c.2.2.2
                                        rcases p1531_3 (m.d 0 2) (by simp) with h1557 | h1557
                                        · linarith only [h1557, hlam, p1531_0]
                                        · rcases p1531_3 (m.d 1 2) (by simp) with h1559 | h1559
                                          · linarith only [h1518, h1559, hlam]
                                          · rcases p1531_3 (m.d 2 3) (by simp) with h1561 | h1561
                                            · rcases p1531_3 (m.d 2 4) (by simp) with h1562 | h1562
                                              · rcases p1531_3 (m.d 2 5) (by simp) with h1563 | h1563
                                                · linarith only [h1528, h1563, hlam]
                                                · linarith only [h1486, h1563, hlam]
                                              · linarith only [h1562, hlam, p1531_0]
                                            · linarith only [h1462, h1561, hlam]
                                      · have p1531_0 := h1531c.1
                                        have p1531_1 := h1531c.2.1
                                        have p1531_2 := h1531c.2.2.1
                                        have p1531_3 := h1531c.2.2.2
                                        rcases p1531_3 (m.d 0 2) (by simp) with h1568 | h1568
                                        · linarith only [h1464, h1568, hlam]
                                        · linarith only [h0, h1568, hlam]
                                      · have p1531_0 := h1531c.1
                                        have p1531_1 := h1531c.2.1
                                        have p1531_2 := h1531c.2.2.1
                                        have p1531_3 := h1531c.2.2.2
                                        linarith only [h1526, hlam, p1531_1]
                                      · have p1531_0 := h1531c.1
                                        have p1531_1 := h1531c.2.1
                                        have p1531_2 := h1531c.2.2.1
                                        have p1531_3 := h1531c.2.2.2
                                        linarith only [hlam, p1531_0]
                                      · have p1531_0 := h1531c.1
                                        have p1531_1 := h1531c.2.1
                                        have p1531_2 := h1531c.2.2.1
                                        have p1531_3 := h1531c.2.2.2
                                        linarith only [h0, h1464, h1502, h1528, hc12, hc24, hlam, hphi, p1531_1]
                                      · have p1531_0 := h1531c.1
                                        have p1531_1 := h1531c.2.1
                                        have p1531_2 := h1531c.2.2.1
                                        have p1531_3 := h1531c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p1531_1, u5elo2]
                                      · have p1531_0 := h1531c.1
                                        have p1531_1 := h1531c.2.1
                                        have p1531_2 := h1531c.2.2.1
                                        have p1531_3 := h1531c.2.2.2
                                        linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p1531_1, u5elo2]
                                      · have p1531_0 := h1531c.1
                                        have p1531_1 := h1531c.2.1
                                        have p1531_2 := h1531c.2.2.1
                                        have p1531_3 := h1531c.2.2.2
                                        linarith only [h1527, hlam, p1531_1]
                                      · have p1531_0 := h1531c.1
                                        have p1531_1 := h1531c.2.1
                                        have p1531_2 := h1531c.2.2.1
                                        have p1531_3 := h1531c.2.2.2
                                        linarith only [h1528, hlam, p1531_0]
                                      · have p1531_0 := h1531c.1
                                        have p1531_1 := h1531c.2.1
                                        have p1531_2 := h1531c.2.2.1
                                        have p1531_3 := h1531c.2.2.2
                                        linarith only [hlam, p1531_0]
                                  · linarith only [h0, h1464, h1528, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                                · linarith only [h0, h1, h1461, h1462, h1523, h1527, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                              · linarith only [h1, h1460, h1502, h1516, h1522, h1526, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                          · linarith only [h1, h1461, h1523, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi6]
                        · linarith only [h1, h1461, h1522, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi6]
              · linarith only [h1, h1461, h1501, hlam, hphi, u5ehi6, u5elo3]
            · linarith only [h1, h1460, h1500, hlam]
    · linarith only [h1460, h1461, hc14, hlam, hphi, ht45, u5elo1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1587 | h1587
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1588 | h1588
      · linarith only [h0, h1, h1588, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1590 | h1590
        · linarith only [h0, h1460, h1590, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1592 | h1592
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1593 | h1593
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1594 | h1594
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1595 | h1595
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1596 | h1596
                  · linarith only [h1588, h1592, h1596, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1598 | h1598
                    · linarith only [h0, h1590, h1592, h1598, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1600 | h1600
                      · linarith only [h0, h1, h1596, h1600, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                      · linarith only [h0, h1, h1592, h1596, h1600, hc12, hc23, hlam, hphi]
                · linarith only [h0, h1460, h1595, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
              · linarith only [h1593, h1594, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1605 | h1605
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1606 | h1606
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1607 | h1607
                  · linarith only [h0, h1, h1593, h1607, hc23, hc34, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1609 | h1609
                    · linarith only [h0, h1, h1590, h1592, h1593, h1609, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1611 | h1611
                      · linarith only [h0, h1, h1593, h1611, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                      · linarith only [h0, h1, h1592, h1593, h1611, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h0, h1, h1593, h1606, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
              · linarith only [h0, h1, h1592, h1605, hlam, hphi, u5ehi7, u5elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1616 | h1616
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1617 | h1617
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1618 | h1618
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1619 | h1619
                  · linarith only [h0, h1592, h1619, hc23, hlam, hphi, ht34, ht45, u5elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1621 | h1621
                    · linarith only [h0, h1460, h1587, h1590, h1592, h1621, hlam, hphi, u5ehi6, u5elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1623 | h1623
                      · linarith only [h0, h1592, h1623, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1625 | h1625
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1626 | h1626
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1627 | h1627
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1628 | h1628
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1629 | h1629
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1630 | h1630
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1631 | h1631
                                    · rcases h2bigk with h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c
                                      · have p1632_0 := h1632c.1
                                        have p1632_1 := h1632c.2.1
                                        have p1632_2 := h1632c.2.2.1
                                        have p1632_3 := h1632c.2.2.2
                                        linarith only [hlam, p1632_0]
                                      · have p1632_0 := h1632c.1
                                        have p1632_1 := h1632c.2.1
                                        have p1632_2 := h1632c.2.2.1
                                        have p1632_3 := h1632c.2.2.2
                                        linarith only [h1460, h1587, h1592, h1619, h1625, h1626, h1631, hc12, hc23, hlam, hphi, p1632_1, u5ehi9, u5elo2]
                                      · have p1632_0 := h1632c.1
                                        have p1632_1 := h1632c.2.1
                                        have p1632_2 := h1632c.2.2.1
                                        have p1632_3 := h1632c.2.2.2
                                        linarith only [h1588, hlam, p1632_0]
                                      · have p1632_0 := h1632c.1
                                        have p1632_1 := h1632c.2.1
                                        have p1632_2 := h1632c.2.2.1
                                        have p1632_3 := h1632c.2.2.2
                                        linarith only [h1590, hlam, p1632_0]
                                      · have p1632_0 := h1632c.1
                                        have p1632_1 := h1632c.2.1
                                        have p1632_2 := h1632c.2.2.1
                                        have p1632_3 := h1632c.2.2.2
                                        linarith only [h1592, hlam, p1632_0]
                                      · have p1632_0 := h1632c.1
                                        have p1632_1 := h1632c.2.1
                                        have p1632_2 := h1632c.2.2.1
                                        have p1632_3 := h1632c.2.2.2
                                        linarith only [h0, hlam, p1632_0]
                                      · have p1632_0 := h1632c.1
                                        have p1632_1 := h1632c.2.1
                                        have p1632_2 := h1632c.2.2.1
                                        have p1632_3 := h1632c.2.2.2
                                        linarith only [hlam, p1632_0]
                                      · have p1632_0 := h1632c.1
                                        have p1632_1 := h1632c.2.1
                                        have p1632_2 := h1632c.2.2.1
                                        have p1632_3 := h1632c.2.2.2
                                        linarith only [h1619, hlam, p1632_0]
                                      · have p1632_0 := h1632c.1
                                        have p1632_1 := h1632c.2.1
                                        have p1632_2 := h1632c.2.2.1
                                        have p1632_3 := h1632c.2.2.2
                                        linarith only [h1621, hlam, p1632_0]
                                      · have p1632_0 := h1632c.1
                                        have p1632_1 := h1632c.2.1
                                        have p1632_2 := h1632c.2.2.1
                                        have p1632_3 := h1632c.2.2.2
                                        linarith only [h1623, hlam, p1632_0]
                                      · have p1632_0 := h1632c.1
                                        have p1632_1 := h1632c.2.1
                                        have p1632_2 := h1632c.2.2.1
                                        have p1632_3 := h1632c.2.2.2
                                        rcases p1632_3 (m.d 0 2) (by simp) with h1643 | h1643
                                        · linarith only [h1643, hlam, p1632_0]
                                        · rcases p1632_3 (m.d 1 2) (by simp) with h1645 | h1645
                                          · linarith only [h1619, h1645, hlam]
                                          · rcases p1632_3 (m.d 2 3) (by simp) with h1647 | h1647
                                            · rcases p1632_3 (m.d 2 4) (by simp) with h1648 | h1648
                                              · linarith only [h1628, h1648, hlam]
                                              · linarith only [h1590, h1648, hlam]
                                            · linarith only [h1647, hlam, p1632_0]
                                      · have p1632_0 := h1632c.1
                                        have p1632_1 := h1632c.2.1
                                        have p1632_2 := h1632c.2.2.1
                                        have p1632_3 := h1632c.2.2.2
                                        rcases p1632_3 (m.d 0 2) (by simp) with h1652 | h1652
                                        · linarith only [h1588, h1652, hlam]
                                        · linarith only [h0, h1652, hlam]
                                      · have p1632_0 := h1632c.1
                                        have p1632_1 := h1632c.2.1
                                        have p1632_2 := h1632c.2.2.1
                                        have p1632_3 := h1632c.2.2.2
                                        linarith only [hlam, p1632_0]
                                      · have p1632_0 := h1632c.1
                                        have p1632_1 := h1632c.2.1
                                        have p1632_2 := h1632c.2.2.1
                                        have p1632_3 := h1632c.2.2.2
                                        linarith only [h1460, h1587, h1621, h1626, h1631, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1632_1, u5ehi9]
                                      · have p1632_0 := h1632c.1
                                        have p1632_1 := h1632c.2.1
                                        have p1632_2 := h1632c.2.2.1
                                        have p1632_3 := h1632c.2.2.2
                                        linarith only [h1592, hc02, hc23, hlam, hphi, p1632_1]
                                      · have p1632_0 := h1632c.1
                                        have p1632_1 := h1632c.2.1
                                        have p1632_2 := h1632c.2.2.1
                                        have p1632_3 := h1632c.2.2.2
                                        rcases p1632_3 (m.d 0 2) (by simp) with h1658 | h1658
                                        · linarith only [h1658, hlam, p1632_0]
                                        · rcases p1632_3 (m.d 1 2) (by simp) with h1660 | h1660
                                          · linarith only [h1621, h1660, hlam]
                                          · rcases p1632_3 (m.d 2 3) (by simp) with h1662 | h1662
                                            · rcases p1632_3 (m.d 2 4) (by simp) with h1663 | h1663
                                              · rcases p1632_3 (m.d 2 5) (by simp) with h1664 | h1664
                                                · linarith only [h1630, h1664, hlam]
                                                · linarith only [h1592, h1664, hlam]
                                              · linarith only [h1663, hlam, p1632_0]
                                            · linarith only [h1588, h1662, hlam]
                                      · have p1632_0 := h1632c.1
                                        have p1632_1 := h1632c.2.1
                                        have p1632_2 := h1632c.2.2.1
                                        have p1632_3 := h1632c.2.2.2
                                        rcases p1632_3 (m.d 0 2) (by simp) with h1669 | h1669
                                        · linarith only [h1590, h1669, hlam]
                                        · linarith only [h0, h1669, hlam]
                                      · have p1632_0 := h1632c.1
                                        have p1632_1 := h1632c.2.1
                                        have p1632_2 := h1632c.2.2.1
                                        have p1632_3 := h1632c.2.2.2
                                        linarith only [h1628, hlam, p1632_1]
                                      · have p1632_0 := h1632c.1
                                        have p1632_1 := h1632c.2.1
                                        have p1632_2 := h1632c.2.2.1
                                        have p1632_3 := h1632c.2.2.2
                                        linarith only [hlam, p1632_0]
                                      · have p1632_0 := h1632c.1
                                        have p1632_1 := h1632c.2.1
                                        have p1632_2 := h1632c.2.2.1
                                        have p1632_3 := h1632c.2.2.2
                                        linarith only [h0, h1592, hc12, hc24, hlam, hphi, p1632_1]
                                      · have p1632_0 := h1632c.1
                                        have p1632_1 := h1632c.2.1
                                        have p1632_2 := h1632c.2.2.1
                                        have p1632_3 := h1632c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p1632_1, u5elo2]
                                      · have p1632_0 := h1632c.1
                                        have p1632_1 := h1632c.2.1
                                        have p1632_2 := h1632c.2.2.1
                                        have p1632_3 := h1632c.2.2.2
                                        linarith only [h1460, h1587, h1619, h1625, h1626, h1631, hc12, hc23, hlam, hphi, p1632_1, u5ehi9, u5elo2]
                                      · have p1632_0 := h1632c.1
                                        have p1632_1 := h1632c.2.1
                                        have p1632_2 := h1632c.2.2.1
                                        have p1632_3 := h1632c.2.2.2
                                        linarith only [h1629, hlam, p1632_1]
                                      · have p1632_0 := h1632c.1
                                        have p1632_1 := h1632c.2.1
                                        have p1632_2 := h1632c.2.2.1
                                        have p1632_3 := h1632c.2.2.2
                                        linarith only [h1630, hlam, p1632_0]
                                      · have p1632_0 := h1632c.1
                                        have p1632_1 := h1632c.2.1
                                        have p1632_2 := h1632c.2.2.1
                                        have p1632_3 := h1632c.2.2.2
                                        linarith only [hlam, p1632_0]
                                    · rcases h2bigk with h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c | h1680c
                                      · have p1680_0 := h1680c.1
                                        have p1680_1 := h1680c.2.1
                                        have p1680_2 := h1680c.2.2.1
                                        have p1680_3 := h1680c.2.2.2
                                        linarith only [hlam, p1680_0]
                                      · have p1680_0 := h1680c.1
                                        have p1680_1 := h1680c.2.1
                                        have p1680_2 := h1680c.2.2.1
                                        have p1680_3 := h1680c.2.2.2
                                        linarith only [h0, h1460, h1619, h1625, hc12, hc23, hlam, hphi, p1680_1]
                                      · have p1680_0 := h1680c.1
                                        have p1680_1 := h1680c.2.1
                                        have p1680_2 := h1680c.2.2.1
                                        have p1680_3 := h1680c.2.2.2
                                        linarith only [h1588, hlam, p1680_0]
                                      · have p1680_0 := h1680c.1
                                        have p1680_1 := h1680c.2.1
                                        have p1680_2 := h1680c.2.2.1
                                        have p1680_3 := h1680c.2.2.2
                                        linarith only [h1590, hlam, p1680_0]
                                      · have p1680_0 := h1680c.1
                                        have p1680_1 := h1680c.2.1
                                        have p1680_2 := h1680c.2.2.1
                                        have p1680_3 := h1680c.2.2.2
                                        linarith only [h1592, hlam, p1680_0]
                                      · have p1680_0 := h1680c.1
                                        have p1680_1 := h1680c.2.1
                                        have p1680_2 := h1680c.2.2.1
                                        have p1680_3 := h1680c.2.2.2
                                        linarith only [h0, hlam, p1680_0]
                                      · have p1680_0 := h1680c.1
                                        have p1680_1 := h1680c.2.1
                                        have p1680_2 := h1680c.2.2.1
                                        have p1680_3 := h1680c.2.2.2
                                        linarith only [hlam, p1680_0]
                                      · have p1680_0 := h1680c.1
                                        have p1680_1 := h1680c.2.1
                                        have p1680_2 := h1680c.2.2.1
                                        have p1680_3 := h1680c.2.2.2
                                        linarith only [h1619, hlam, p1680_0]
                                      · have p1680_0 := h1680c.1
                                        have p1680_1 := h1680c.2.1
                                        have p1680_2 := h1680c.2.2.1
                                        have p1680_3 := h1680c.2.2.2
                                        linarith only [h1621, hlam, p1680_0]
                                      · have p1680_0 := h1680c.1
                                        have p1680_1 := h1680c.2.1
                                        have p1680_2 := h1680c.2.2.1
                                        have p1680_3 := h1680c.2.2.2
                                        linarith only [h1623, hlam, p1680_0]
                                      · have p1680_0 := h1680c.1
                                        have p1680_1 := h1680c.2.1
                                        have p1680_2 := h1680c.2.2.1
                                        have p1680_3 := h1680c.2.2.2
                                        rcases p1680_3 (m.d 0 2) (by simp) with h1691 | h1691
                                        · linarith only [h1691, hlam, p1680_0]
                                        · rcases p1680_3 (m.d 1 2) (by simp) with h1693 | h1693
                                          · linarith only [h1619, h1693, hlam]
                                          · rcases p1680_3 (m.d 2 3) (by simp) with h1695 | h1695
                                            · rcases p1680_3 (m.d 2 4) (by simp) with h1696 | h1696
                                              · linarith only [h1628, h1696, hlam]
                                              · linarith only [h1590, h1696, hlam]
                                            · linarith only [h1695, hlam, p1680_0]
                                      · have p1680_0 := h1680c.1
                                        have p1680_1 := h1680c.2.1
                                        have p1680_2 := h1680c.2.2.1
                                        have p1680_3 := h1680c.2.2.2
                                        rcases p1680_3 (m.d 0 2) (by simp) with h1700 | h1700
                                        · linarith only [h1588, h1700, hlam]
                                        · linarith only [h0, h1700, hlam]
                                      · have p1680_0 := h1680c.1
                                        have p1680_1 := h1680c.2.1
                                        have p1680_2 := h1680c.2.2.1
                                        have p1680_3 := h1680c.2.2.2
                                        linarith only [hlam, p1680_0]
                                      · have p1680_0 := h1680c.1
                                        have p1680_1 := h1680c.2.1
                                        have p1680_2 := h1680c.2.2.1
                                        have p1680_3 := h1680c.2.2.2
                                        linarith only [h1590, hc02, hc23, hlam, hphi, p1680_1]
                                      · have p1680_0 := h1680c.1
                                        have p1680_1 := h1680c.2.1
                                        have p1680_2 := h1680c.2.2.1
                                        have p1680_3 := h1680c.2.2.2
                                        linarith only [h0, h1592, hc12, hc23, hlam, hphi, p1680_1]
                                      · have p1680_0 := h1680c.1
                                        have p1680_1 := h1680c.2.1
                                        have p1680_2 := h1680c.2.2.1
                                        have p1680_3 := h1680c.2.2.2
                                        rcases p1680_3 (m.d 0 2) (by simp) with h1706 | h1706
                                        · linarith only [h1706, hlam, p1680_0]
                                        · rcases p1680_3 (m.d 1 2) (by simp) with h1708 | h1708
                                          · linarith only [h1621, h1708, hlam]
                                          · rcases p1680_3 (m.d 2 3) (by simp) with h1710 | h1710
                                            · rcases p1680_3 (m.d 2 4) (by simp) with h1711 | h1711
                                              · rcases p1680_3 (m.d 2 5) (by simp) with h1712 | h1712
                                                · linarith only [h1630, h1712, hlam]
                                                · linarith only [h1592, h1712, hlam]
                                              · linarith only [h1711, hlam, p1680_0]
                                            · linarith only [h1588, h1710, hlam]
                                      · have p1680_0 := h1680c.1
                                        have p1680_1 := h1680c.2.1
                                        have p1680_2 := h1680c.2.2.1
                                        have p1680_3 := h1680c.2.2.2
                                        rcases p1680_3 (m.d 0 2) (by simp) with h1717 | h1717
                                        · linarith only [h1590, h1717, hlam]
                                        · linarith only [h0, h1717, hlam]
                                      · have p1680_0 := h1680c.1
                                        have p1680_1 := h1680c.2.1
                                        have p1680_2 := h1680c.2.2.1
                                        have p1680_3 := h1680c.2.2.2
                                        linarith only [h1628, hlam, p1680_1]
                                      · have p1680_0 := h1680c.1
                                        have p1680_1 := h1680c.2.1
                                        have p1680_2 := h1680c.2.2.1
                                        have p1680_3 := h1680c.2.2.2
                                        linarith only [hlam, p1680_0]
                                      · have p1680_0 := h1680c.1
                                        have p1680_1 := h1680c.2.1
                                        have p1680_2 := h1680c.2.2.1
                                        have p1680_3 := h1680c.2.2.2
                                        linarith only [h0, h1592, hc12, hc24, hlam, hphi, p1680_1]
                                      · have p1680_0 := h1680c.1
                                        have p1680_1 := h1680c.2.1
                                        have p1680_2 := h1680c.2.2.1
                                        have p1680_3 := h1680c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p1680_1, u5elo2]
                                      · have p1680_0 := h1680c.1
                                        have p1680_1 := h1680c.2.1
                                        have p1680_2 := h1680c.2.2.1
                                        have p1680_3 := h1680c.2.2.2
                                        linarith only [h1460, h1587, h1619, h1625, h1627, h1631, hc12, hc23, hc34, hlam, hphi, ht45, p1680_1, u5elo2]
                                      · have p1680_0 := h1680c.1
                                        have p1680_1 := h1680c.2.1
                                        have p1680_2 := h1680c.2.2.1
                                        have p1680_3 := h1680c.2.2.2
                                        linarith only [h1629, hlam, p1680_1]
                                      · have p1680_0 := h1680c.1
                                        have p1680_1 := h1680c.2.1
                                        have p1680_2 := h1680c.2.2.1
                                        have p1680_3 := h1680c.2.2.2
                                        linarith only [h1630, hlam, p1680_0]
                                      · have p1680_0 := h1680c.1
                                        have p1680_1 := h1680c.2.1
                                        have p1680_2 := h1680c.2.2.1
                                        have p1680_3 := h1680c.2.2.2
                                        linarith only [hlam, p1680_0]
                                  · linarith only [h0, h1460, h1587, h1590, h1619, h1625, h1627, h1630, hc12, hc23, hlam, hphi]
                                · linarith only [h1460, h1587, h1619, h1625, h1629, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi6]
                              · linarith only [h1460, h1587, h1619, h1625, h1628, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi6]
                            · linarith only [h1460, h1587, h1626, h1627, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi8]
                          · linarith only [h1460, h1587, h1625, h1626, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi6]
                        · linarith only [h1, h1587, h1616, h1625, hc03, hlam, hphi, ht0b, ht5b, u5ehi6]
                · linarith only [h1460, h1587, h1618, hlam, hphi, u5ehi6, u5elo4]
              · linarith only [h1, h1587, h1617, hlam, hphi, u5ehi6, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1736 | h1736
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1737 | h1737
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1738 | h1738
                  · linarith only [h0, h1, h1616, h1738, hc23, hc34, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1740 | h1740
                    · linarith only [h0, h1, h1590, h1592, h1616, h1740, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1742 | h1742
                      · linarith only [h0, h1, h1592, h1742, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1744 | h1744
                        · linarith only [h1, h1587, h1616, h1744, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi6]
                        · linarith only [h1, h1587, h1744, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi6]
                · linarith only [h1, h1587, h1616, h1737, hlam, hphi, u5ehi6, u5elo4]
              · linarith only [h1, h1587, h1736, hlam, hphi, u5ehi6, u5elo3]
    · linarith only [h0, h1587, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]

set_option maxHeartbeats 7280000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_LR_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_LR_x0_x0 m hb0 hb2 hb3 hb5 h0 h1
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_LR_x0_x1 m hb0 hb2 hb3 hb5 h0 h1

set_option maxHeartbeats 7280000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_LR_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1750 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1751 | h1751
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1752 | h1752
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1753 | h1753
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1754 | h1754
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1755 | h1755
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1756 | h1756
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1757 | h1757
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1758 | h1758
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1759 | h1759
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1760 | h1760
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1761 | h1761
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1762 | h1762
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1763 | h1763
                          · linarith only [h0, h1750, h1763, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                          · linarith only [h0, h1750, h1757, h1762, h1763, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1766 | h1766
                          · linarith only [h0, h1750, h1766, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1768 | h1768
                            · linarith only [h0, h1750, h1756, h1762, h1768, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1770 | h1770
                              · linarith only [h1759, h1766, h1770, hc34, hlam, hphi, ht45, u5elo3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1772 | h1772
                                · linarith only [h1759, h1766, h1772, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1774 | h1774
                                  · linarith only [h1760, h1768, h1774, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1776 | h1776
                                    · linarith only [h0, h1750, h1756, h1768, h1776, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                    · linarith only [h1759, h1762, h1776, hc23, hlam, hphi, ht34, ht45, u5elo4]
                      · linarith only [h0, h1750, h1756, h1758, h1761, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                    · linarith only [h0, h1750, h1756, h1758, h1760, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                  · linarith only [h0, h1750, h1756, h1758, h1759, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1782 | h1782
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1783 | h1783
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1784 | h1784
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1785 | h1785
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1786 | h1786
                          · linarith only [h0, h1750, h1786, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                          · linarith only [h1785, h1786, hc34, hlam, hphi, ht45, u5elo3]
                        · linarith only [h1756, h1758, h1785, hc13, hlam, hphi, ht34, ht45, u5elo4]
                      · linarith only [h0, h1750, h1757, h1784, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                    · linarith only [h0, h1754, h1758, h1783, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h0, h1750, h1757, h1782, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
              · linarith only [h1756, h1757, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1794 | h1794
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1795 | h1795
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1796 | h1796
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1797 | h1797
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1798 | h1798
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1799 | h1799
                        · linarith only [h1750, h1756, h1794, h1799, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1801 | h1801
                          · linarith only [h0, h1751, h1799, h1801, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                          · linarith only [h1756, h1794, h1796, h1801, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h1798, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                    · linarith only [h0, h1751, h1756, h1794, h1797, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                  · linarith only [h0, h1751, h1756, h1794, h1796, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                · linarith only [h1756, h1794, h1795, hlam, hphi, u5ehi8, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1808 | h1808
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1809 | h1809
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1810 | h1810
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1811 | h1811
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1812 | h1812
                        · linarith only [h1750, h1794, h1812, hc34, hlam, hphi, ht45, u5elo3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1814 | h1814
                          · linarith only [h1750, h1794, h1814, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1816 | h1816
                            · linarith only [h0, h1751, h1816, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1818 | h1818
                              · linarith only [h1756, h1808, h1809, h1812, h1816, h1818, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1820 | h1820
                                · linarith only [h1794, h1808, h1809, h1812, h1816, h1820, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1822 | h1822
                                  · linarith only [h1810, h1816, h1822, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1824 | h1824
                                    · rcases h2bigk with h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c | h1825c
                                      · have p1825_0 := h1825c.1
                                        have p1825_1 := h1825c.2.1
                                        have p1825_2 := h1825c.2.2.1
                                        have p1825_3 := h1825c.2.2.2
                                        linarith only [hlam, p1825_0]
                                      · have p1825_0 := h1825c.1
                                        have p1825_1 := h1825c.2.1
                                        have p1825_2 := h1825c.2.2.1
                                        have p1825_3 := h1825c.2.2.2
                                        linarith only [h0, hlam, p1825_1]
                                      · have p1825_0 := h1825c.1
                                        have p1825_1 := h1825c.2.1
                                        have p1825_2 := h1825c.2.2.1
                                        have p1825_3 := h1825c.2.2.2
                                        rcases p1825_3 (m.d 0 2) (by simp) with h1828 | h1828
                                        · rcases p1825_3 (m.d 1 2) (by simp) with h1829 | h1829
                                          · rcases p1825_3 (m.d 2 3) (by simp) with h1830 | h1830
                                            · linarith only [h1830, hlam, p1825_0]
                                            · rcases p1825_3 (m.d 2 4) (by simp) with h1832 | h1832
                                              · linarith only [h1754, h1832, hlam]
                                              · linarith only [h1818, h1832, hlam]
                                          · linarith only [h1809, h1829, hlam]
                                        · linarith only [h1828, hlam, p1825_0]
                                      · have p1825_0 := h1825c.1
                                        have p1825_1 := h1825c.2.1
                                        have p1825_2 := h1825c.2.2.1
                                        have p1825_3 := h1825c.2.2.2
                                        rcases p1825_3 (m.d 0 2) (by simp) with h1837 | h1837
                                        · rcases p1825_3 (m.d 1 2) (by simp) with h1838 | h1838
                                          · rcases p1825_3 (m.d 2 3) (by simp) with h1839 | h1839
                                            · linarith only [h1753, h1839, hlam]
                                            · rcases p1825_3 (m.d 2 4) (by simp) with h1841 | h1841
                                              · linarith only [h1841, hlam, p1825_0]
                                              · rcases p1825_3 (m.d 2 5) (by simp) with h1843 | h1843
                                                · linarith only [h1755, h1843, hlam]
                                                · linarith only [h1822, h1843, hlam]
                                          · linarith only [h1810, h1838, hlam]
                                        · linarith only [h1837, hlam, p1825_0]
                                      · have p1825_0 := h1825c.1
                                        have p1825_1 := h1825c.2.1
                                        have p1825_2 := h1825c.2.2.1
                                        have p1825_3 := h1825c.2.2.2
                                        rcases p1825_3 (m.d 0 2) (by simp) with h1848 | h1848
                                        · rcases p1825_3 (m.d 1 2) (by simp) with h1849 | h1849
                                          · rcases p1825_3 (m.d 2 3) (by simp) with h1850 | h1850
                                            · linarith only [h1753, h1850, hlam]
                                            · rcases p1825_3 (m.d 2 4) (by simp) with h1852 | h1852
                                              · linarith only [h1754, h1852, hlam]
                                              · rcases p1825_3 (m.d 2 5) (by simp) with h1854 | h1854
                                                · linarith only [h1854, hlam, p1825_0]
                                                · rcases h3bigk with h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c
                                                  · have p1856_0 := h1856c.1
                                                    have p1856_1 := h1856c.2.1
                                                    have p1856_2 := h1856c.2.2.1
                                                    have p1856_3 := h1856c.2.2.2
                                                    linarith only [hlam, p1856_0]
                                                  · have p1856_0 := h1856c.1
                                                    have p1856_1 := h1856c.2.1
                                                    have p1856_2 := h1856c.2.2.1
                                                    have p1856_3 := h1856c.2.2.2
                                                    linarith only [h1756, h1809, hc23, hc34, hlam, hphi, p1856_1]
                                                  · have p1856_0 := h1856c.1
                                                    have p1856_1 := h1856c.2.1
                                                    have p1856_2 := h1856c.2.2.1
                                                    have p1856_3 := h1856c.2.2.2
                                                    linarith only [h1756, hc23, hc34, hlam, hphi, p1856_1]
                                                  · have p1856_0 := h1856c.1
                                                    have p1856_1 := h1856c.2.1
                                                    have p1856_2 := h1856c.2.2.1
                                                    have p1856_3 := h1856c.2.2.2
                                                    linarith only [h1756, hlam, p1856_0]
                                                  · have p1856_0 := h1856c.1
                                                    have p1856_1 := h1856c.2.1
                                                    have p1856_2 := h1856c.2.2.1
                                                    have p1856_3 := h1856c.2.2.2
                                                    linarith only [h1794, hlam, p1856_0]
                                                  · have p1856_0 := h1856c.1
                                                    have p1856_1 := h1856c.2.1
                                                    have p1856_2 := h1856c.2.2.1
                                                    have p1856_3 := h1856c.2.2.2
                                                    linarith only [h1750, hlam, p1856_0]
                                                  · have p1856_0 := h1856c.1
                                                    have p1856_1 := h1856c.2.1
                                                    have p1856_2 := h1856c.2.2.1
                                                    have p1856_3 := h1856c.2.2.2
                                                    linarith only [hlam, p1856_0]
                                                  · have p1856_0 := h1856c.1
                                                    have p1856_1 := h1856c.2.1
                                                    have p1856_2 := h1856c.2.2.1
                                                    have p1856_3 := h1856c.2.2.2
                                                    linarith only [h0, h1750, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1856_1]
                                                  · have p1856_0 := h1856c.1
                                                    have p1856_1 := h1856c.2.1
                                                    have p1856_2 := h1856c.2.2.1
                                                    have p1856_3 := h1856c.2.2.2
                                                    linarith only [h1812, hlam, p1856_0]
                                                  · have p1856_0 := h1856c.1
                                                    have p1856_1 := h1856c.2.1
                                                    have p1856_2 := h1856c.2.2.1
                                                    have p1856_3 := h1856c.2.2.2
                                                    linarith only [h1814, hlam, p1856_0]
                                                  · have p1856_0 := h1856c.1
                                                    have p1856_1 := h1856c.2.1
                                                    have p1856_2 := h1856c.2.2.1
                                                    have p1856_3 := h1856c.2.2.2
                                                    linarith only [h1753, hlam, p1856_0]
                                                  · have p1856_0 := h1856c.1
                                                    have p1856_1 := h1856c.2.1
                                                    have p1856_2 := h1856c.2.2.1
                                                    have p1856_3 := h1856c.2.2.2
                                                    linarith only [h1809, hlam, p1856_0]
                                                  · have p1856_0 := h1856c.1
                                                    have p1856_1 := h1856c.2.1
                                                    have p1856_2 := h1856c.2.2.1
                                                    have p1856_3 := h1856c.2.2.2
                                                    linarith only [hlam, p1856_0]
                                                  · have p1856_0 := h1856c.1
                                                    have p1856_1 := h1856c.2.1
                                                    have p1856_2 := h1856c.2.2.1
                                                    have p1856_3 := h1856c.2.2.2
                                                    linarith only [h1818, hlam, p1856_0]
                                                  · have p1856_0 := h1856c.1
                                                    have p1856_1 := h1856c.2.1
                                                    have p1856_2 := h1856c.2.2.1
                                                    have p1856_3 := h1856c.2.2.2
                                                    linarith only [h1820, hlam, p1856_0]
                                                  · have p1856_0 := h1856c.1
                                                    have p1856_1 := h1856c.2.1
                                                    have p1856_2 := h1856c.2.2.1
                                                    have p1856_3 := h1856c.2.2.2
                                                    rcases p1856_3 (m.d 0 3) (by simp) with h1872 | h1872
                                                    · linarith only [h1872, hlam, p1856_0]
                                                    · rcases p1856_3 (m.d 1 3) (by simp) with h1874 | h1874
                                                      · linarith only [h1812, h1874, hlam]
                                                      · rcases p1856_3 (m.d 2 3) (by simp) with h1876 | h1876
                                                        · linarith only [h1818, h1876, hlam]
                                                        · rcases p1856_3 (m.d 3 4) (by simp) with h1878 | h1878
                                                          · rcases p1856_3 (m.d 3 5) (by simp) with h1879 | h1879
                                                            · linarith only [h1824, h1879, hlam]
                                                            · linarith only [h1794, h1879, hlam]
                                                          · linarith only [h1878, hlam, p1856_0]
                                                  · have p1856_0 := h1856c.1
                                                    have p1856_1 := h1856c.2.1
                                                    have p1856_2 := h1856c.2.2.1
                                                    have p1856_3 := h1856c.2.2.2
                                                    rcases p1856_3 (m.d 0 3) (by simp) with h1883 | h1883
                                                    · linarith only [h1756, h1883, hlam]
                                                    · linarith only [h1750, h1883, hlam]
                                                  · have p1856_0 := h1856c.1
                                                    have p1856_1 := h1856c.2.1
                                                    have p1856_2 := h1856c.2.2.1
                                                    have p1856_3 := h1856c.2.2.2
                                                    rcases p1856_3 (m.d 0 3) (by simp) with h1886 | h1886
                                                    · linarith only [h1756, h1886, hlam]
                                                    · linarith only [h1753, h1886, hlam]
                                                  · have p1856_0 := h1856c.1
                                                    have p1856_1 := h1856c.2.1
                                                    have p1856_2 := h1856c.2.2.1
                                                    have p1856_3 := h1856c.2.2.2
                                                    linarith only [hlam, p1856_0]
                                                  · have p1856_0 := h1856c.1
                                                    have p1856_1 := h1856c.2.1
                                                    have p1856_2 := h1856c.2.2.1
                                                    have p1856_3 := h1856c.2.2.2
                                                    linarith only [h1794, hc03, hc34, hlam, hphi, p1856_1]
                                                  · have p1856_0 := h1856c.1
                                                    have p1856_1 := h1856c.2.1
                                                    have p1856_2 := h1856c.2.2.1
                                                    have p1856_3 := h1856c.2.2.2
                                                    linarith only [hc03, hlam, hphi, ht34, ht45, p1856_1, u5elo3]
                                                  · have p1856_0 := h1856c.1
                                                    have p1856_1 := h1856c.2.1
                                                    have p1856_2 := h1856c.2.2.1
                                                    have p1856_3 := h1856c.2.2.2
                                                    linarith only [h1809, hc23, hlam, hphi, ht34, ht45, p1856_1, u5elo3]
                                                  · have p1856_0 := h1856c.1
                                                    have p1856_1 := h1856c.2.1
                                                    have p1856_2 := h1856c.2.2.1
                                                    have p1856_3 := h1856c.2.2.2
                                                    linarith only [hc23, hlam, hphi, ht34, ht45, p1856_1, u5elo3]
                                                  · have p1856_0 := h1856c.1
                                                    have p1856_1 := h1856c.2.1
                                                    have p1856_2 := h1856c.2.2.1
                                                    have p1856_3 := h1856c.2.2.2
                                                    linarith only [h1824, hlam, p1856_0]
                                                  · have p1856_0 := h1856c.1
                                                    have p1856_1 := h1856c.2.1
                                                    have p1856_2 := h1856c.2.2.1
                                                    have p1856_3 := h1856c.2.2.2
                                                    linarith only [hlam, p1856_0]
                                          · linarith only [h1811, h1849, hlam]
                                        · linarith only [h1848, hlam, p1825_0]
                                      · have p1825_0 := h1825c.1
                                        have p1825_1 := h1825c.2.1
                                        have p1825_2 := h1825c.2.2.1
                                        have p1825_3 := h1825c.2.2.2
                                        linarith only [h0, h1751, h1808, h1816, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1825_1]
                                      · have p1825_0 := h1825c.1
                                        have p1825_1 := h1825c.2.1
                                        have p1825_2 := h1825c.2.2.1
                                        have p1825_3 := h1825c.2.2.2
                                        linarith only [hlam, p1825_0]
                                      · have p1825_0 := h1825c.1
                                        have p1825_1 := h1825c.2.1
                                        have p1825_2 := h1825c.2.2.1
                                        have p1825_3 := h1825c.2.2.2
                                        linarith only [h0, h1751, h1808, h1809, h1812, h1816, hlam, p1825_2]
                                      · have p1825_0 := h1825c.1
                                        have p1825_1 := h1825c.2.1
                                        have p1825_2 := h1825c.2.2.1
                                        have p1825_3 := h1825c.2.2.2
                                        linarith only [h0, h1751, h1808, h1810, h1816, hlam, p1825_2]
                                      · have p1825_0 := h1825c.1
                                        have p1825_1 := h1825c.2.1
                                        have p1825_2 := h1825c.2.2.1
                                        have p1825_3 := h1825c.2.2.2
                                        rcases p1825_3 (m.d 0 2) (by simp) with h1902 | h1902
                                        · linarith only [h0, h1902, hlam]
                                        · linarith only [h1755, h1902, hlam]
                                      · have p1825_0 := h1825c.1
                                        have p1825_1 := h1825c.2.1
                                        have p1825_2 := h1825c.2.2.1
                                        have p1825_3 := h1825c.2.2.2
                                        linarith only [h1753, hlam, p1825_0]
                                      · have p1825_0 := h1825c.1
                                        have p1825_1 := h1825c.2.1
                                        have p1825_2 := h1825c.2.2.1
                                        have p1825_3 := h1825c.2.2.2
                                        linarith only [h1809, hlam, p1825_0]
                                      · have p1825_0 := h1825c.1
                                        have p1825_1 := h1825c.2.1
                                        have p1825_2 := h1825c.2.2.1
                                        have p1825_3 := h1825c.2.2.2
                                        linarith only [hlam, p1825_0]
                                      · have p1825_0 := h1825c.1
                                        have p1825_1 := h1825c.2.1
                                        have p1825_2 := h1825c.2.2.1
                                        have p1825_3 := h1825c.2.2.2
                                        linarith only [h1818, hlam, p1825_0]
                                      · have p1825_0 := h1825c.1
                                        have p1825_1 := h1825c.2.1
                                        have p1825_2 := h1825c.2.2.1
                                        have p1825_3 := h1825c.2.2.2
                                        linarith only [h1820, hlam, p1825_0]
                                      · have p1825_0 := h1825c.1
                                        have p1825_1 := h1825c.2.1
                                        have p1825_2 := h1825c.2.2.1
                                        have p1825_3 := h1825c.2.2.2
                                        linarith only [h1754, hlam, p1825_0]
                                      · have p1825_0 := h1825c.1
                                        have p1825_1 := h1825c.2.1
                                        have p1825_2 := h1825c.2.2.1
                                        have p1825_3 := h1825c.2.2.2
                                        linarith only [h1810, hlam, p1825_0]
                                      · have p1825_0 := h1825c.1
                                        have p1825_1 := h1825c.2.1
                                        have p1825_2 := h1825c.2.2.1
                                        have p1825_3 := h1825c.2.2.2
                                        linarith only [h1751, h1808, h1810, h1816, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1825_1]
                                      · have p1825_0 := h1825c.1
                                        have p1825_1 := h1825c.2.1
                                        have p1825_2 := h1825c.2.2.1
                                        have p1825_3 := h1825c.2.2.2
                                        linarith only [hlam, p1825_0]
                                      · have p1825_0 := h1825c.1
                                        have p1825_1 := h1825c.2.1
                                        have p1825_2 := h1825c.2.2.1
                                        have p1825_3 := h1825c.2.2.2
                                        linarith only [h1822, hlam, p1825_1]
                                      · have p1825_0 := h1825c.1
                                        have p1825_1 := h1825c.2.1
                                        have p1825_2 := h1825c.2.2.1
                                        have p1825_3 := h1825c.2.2.2
                                        linarith only [h1755, hlam, p1825_0]
                                      · have p1825_0 := h1825c.1
                                        have p1825_1 := h1825c.2.1
                                        have p1825_2 := h1825c.2.2.1
                                        have p1825_3 := h1825c.2.2.2
                                        linarith only [h1811, hlam, p1825_0]
                                      · have p1825_0 := h1825c.1
                                        have p1825_1 := h1825c.2.1
                                        have p1825_2 := h1825c.2.2.1
                                        have p1825_3 := h1825c.2.2.2
                                        linarith only [h1811, hc23, hlam, hphi, ht34, ht45, p1825_1, u5elo1]
                                      · have p1825_0 := h1825c.1
                                        have p1825_1 := h1825c.2.1
                                        have p1825_2 := h1825c.2.2.1
                                        have p1825_3 := h1825c.2.2.2
                                        linarith only [h0, h1751, h1808, h1811, h1816, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1825_1]
                                      · have p1825_0 := h1825c.1
                                        have p1825_1 := h1825c.2.1
                                        have p1825_2 := h1825c.2.2.1
                                        have p1825_3 := h1825c.2.2.2
                                        linarith only [hlam, p1825_0]
                                    · linarith only [h0, h1750, h1751, h1756, h1808, h1809, h1824, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h1751, h1808, h1811, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                    · linarith only [h0, h1751, h1808, h1810, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                  · linarith only [h0, h1751, h1808, h1809, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1924 | h1924
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1925 | h1925
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1926 | h1926
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1927 | h1927
                        · linarith only [h1750, h1756, h1927, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1929 | h1929
                          · linarith only [h0, h1750, h1929, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1931 | h1931
                            · linarith only [h1751, h1808, h1931, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1933 | h1933
                              · linarith only [h1753, h1756, h1933, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1935 | h1935
                                · linarith only [h1750, h1794, h1924, h1935, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1937 | h1937
                                  · linarith only [h1754, h1808, h1937, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1939 | h1939
                                    · rcases h2bigk with h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c
                                      · have p1940_0 := h1940c.1
                                        have p1940_1 := h1940c.2.1
                                        have p1940_2 := h1940c.2.2.1
                                        have p1940_3 := h1940c.2.2.2
                                        linarith only [hlam, p1940_0]
                                      · have p1940_0 := h1940c.1
                                        have p1940_1 := h1940c.2.1
                                        have p1940_2 := h1940c.2.2.1
                                        have p1940_3 := h1940c.2.2.2
                                        linarith only [h0, hlam, p1940_1]
                                      · have p1940_0 := h1940c.1
                                        have p1940_1 := h1940c.2.1
                                        have p1940_2 := h1940c.2.2.1
                                        have p1940_3 := h1940c.2.2.2
                                        rcases p1940_3 (m.d 0 2) (by simp) with h1943 | h1943
                                        · rcases p1940_3 (m.d 1 2) (by simp) with h1944 | h1944
                                          · rcases p1940_3 (m.d 2 3) (by simp) with h1945 | h1945
                                            · linarith only [h1945, hlam, p1940_0]
                                            · rcases p1940_3 (m.d 2 4) (by simp) with h1947 | h1947
                                              · linarith only [h1754, h1947, hlam]
                                              · linarith only [h1933, h1947, hlam]
                                          · linarith only [h1924, h1944, hlam]
                                        · linarith only [h1943, hlam, p1940_0]
                                      · have p1940_0 := h1940c.1
                                        have p1940_1 := h1940c.2.1
                                        have p1940_2 := h1940c.2.2.1
                                        have p1940_3 := h1940c.2.2.2
                                        rcases p1940_3 (m.d 0 2) (by simp) with h1952 | h1952
                                        · rcases p1940_3 (m.d 1 2) (by simp) with h1953 | h1953
                                          · rcases p1940_3 (m.d 2 3) (by simp) with h1954 | h1954
                                            · linarith only [h1753, h1954, hlam]
                                            · rcases p1940_3 (m.d 2 4) (by simp) with h1956 | h1956
                                              · linarith only [h1956, hlam, p1940_0]
                                              · rcases p1940_3 (m.d 2 5) (by simp) with h1958 | h1958
                                                · linarith only [h1755, h1958, hlam]
                                                · linarith only [h1937, h1958, hlam]
                                          · linarith only [h1925, h1953, hlam]
                                        · linarith only [h1952, hlam, p1940_0]
                                      · have p1940_0 := h1940c.1
                                        have p1940_1 := h1940c.2.1
                                        have p1940_2 := h1940c.2.2.1
                                        have p1940_3 := h1940c.2.2.2
                                        rcases p1940_3 (m.d 0 2) (by simp) with h1963 | h1963
                                        · rcases p1940_3 (m.d 1 2) (by simp) with h1964 | h1964
                                          · rcases p1940_3 (m.d 2 3) (by simp) with h1965 | h1965
                                            · linarith only [h1753, h1965, hlam]
                                            · rcases p1940_3 (m.d 2 4) (by simp) with h1967 | h1967
                                              · linarith only [h1754, h1967, hlam]
                                              · rcases p1940_3 (m.d 2 5) (by simp) with h1969 | h1969
                                                · linarith only [h1969, hlam, p1940_0]
                                                · rcases h3bigk with h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c
                                                  · have p1971_0 := h1971c.1
                                                    have p1971_1 := h1971c.2.1
                                                    have p1971_2 := h1971c.2.2.1
                                                    have p1971_3 := h1971c.2.2.2
                                                    linarith only [hlam, p1971_0]
                                                  · have p1971_0 := h1971c.1
                                                    have p1971_1 := h1971c.2.1
                                                    have p1971_2 := h1971c.2.2.1
                                                    have p1971_3 := h1971c.2.2.2
                                                    linarith only [h1756, h1924, hc23, hc34, hlam, hphi, p1971_1]
                                                  · have p1971_0 := h1971c.1
                                                    have p1971_1 := h1971c.2.1
                                                    have p1971_2 := h1971c.2.2.1
                                                    have p1971_3 := h1971c.2.2.2
                                                    linarith only [h1756, hc23, hc34, hlam, hphi, p1971_1]
                                                  · have p1971_0 := h1971c.1
                                                    have p1971_1 := h1971c.2.1
                                                    have p1971_2 := h1971c.2.2.1
                                                    have p1971_3 := h1971c.2.2.2
                                                    linarith only [h1756, hlam, p1971_0]
                                                  · have p1971_0 := h1971c.1
                                                    have p1971_1 := h1971c.2.1
                                                    have p1971_2 := h1971c.2.2.1
                                                    have p1971_3 := h1971c.2.2.2
                                                    linarith only [h1794, hlam, p1971_0]
                                                  · have p1971_0 := h1971c.1
                                                    have p1971_1 := h1971c.2.1
                                                    have p1971_2 := h1971c.2.2.1
                                                    have p1971_3 := h1971c.2.2.2
                                                    linarith only [h1750, hlam, p1971_0]
                                                  · have p1971_0 := h1971c.1
                                                    have p1971_1 := h1971c.2.1
                                                    have p1971_2 := h1971c.2.2.1
                                                    have p1971_3 := h1971c.2.2.2
                                                    linarith only [hlam, p1971_0]
                                                  · have p1971_0 := h1971c.1
                                                    have p1971_1 := h1971c.2.1
                                                    have p1971_2 := h1971c.2.2.1
                                                    have p1971_3 := h1971c.2.2.2
                                                    linarith only [h0, h1750, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1971_1]
                                                  · have p1971_0 := h1971c.1
                                                    have p1971_1 := h1971c.2.1
                                                    have p1971_2 := h1971c.2.2.1
                                                    have p1971_3 := h1971c.2.2.2
                                                    linarith only [h1927, hlam, p1971_0]
                                                  · have p1971_0 := h1971c.1
                                                    have p1971_1 := h1971c.2.1
                                                    have p1971_2 := h1971c.2.2.1
                                                    have p1971_3 := h1971c.2.2.2
                                                    linarith only [h1929, hlam, p1971_0]
                                                  · have p1971_0 := h1971c.1
                                                    have p1971_1 := h1971c.2.1
                                                    have p1971_2 := h1971c.2.2.1
                                                    have p1971_3 := h1971c.2.2.2
                                                    linarith only [h1753, hlam, p1971_0]
                                                  · have p1971_0 := h1971c.1
                                                    have p1971_1 := h1971c.2.1
                                                    have p1971_2 := h1971c.2.2.1
                                                    have p1971_3 := h1971c.2.2.2
                                                    linarith only [h1924, hlam, p1971_0]
                                                  · have p1971_0 := h1971c.1
                                                    have p1971_1 := h1971c.2.1
                                                    have p1971_2 := h1971c.2.2.1
                                                    have p1971_3 := h1971c.2.2.2
                                                    linarith only [hlam, p1971_0]
                                                  · have p1971_0 := h1971c.1
                                                    have p1971_1 := h1971c.2.1
                                                    have p1971_2 := h1971c.2.2.1
                                                    have p1971_3 := h1971c.2.2.2
                                                    linarith only [h1933, hlam, p1971_0]
                                                  · have p1971_0 := h1971c.1
                                                    have p1971_1 := h1971c.2.1
                                                    have p1971_2 := h1971c.2.2.1
                                                    have p1971_3 := h1971c.2.2.2
                                                    linarith only [h1935, hlam, p1971_0]
                                                  · have p1971_0 := h1971c.1
                                                    have p1971_1 := h1971c.2.1
                                                    have p1971_2 := h1971c.2.2.1
                                                    have p1971_3 := h1971c.2.2.2
                                                    rcases p1971_3 (m.d 0 3) (by simp) with h1987 | h1987
                                                    · linarith only [h1987, hlam, p1971_0]
                                                    · rcases p1971_3 (m.d 1 3) (by simp) with h1989 | h1989
                                                      · linarith only [h1927, h1989, hlam]
                                                      · rcases p1971_3 (m.d 2 3) (by simp) with h1991 | h1991
                                                        · linarith only [h1933, h1991, hlam]
                                                        · rcases p1971_3 (m.d 3 4) (by simp) with h1993 | h1993
                                                          · rcases p1971_3 (m.d 3 5) (by simp) with h1994 | h1994
                                                            · linarith only [h1939, h1994, hlam]
                                                            · linarith only [h1794, h1994, hlam]
                                                          · linarith only [h1993, hlam, p1971_0]
                                                  · have p1971_0 := h1971c.1
                                                    have p1971_1 := h1971c.2.1
                                                    have p1971_2 := h1971c.2.2.1
                                                    have p1971_3 := h1971c.2.2.2
                                                    rcases p1971_3 (m.d 0 3) (by simp) with h1998 | h1998
                                                    · linarith only [h1756, h1998, hlam]
                                                    · linarith only [h1750, h1998, hlam]
                                                  · have p1971_0 := h1971c.1
                                                    have p1971_1 := h1971c.2.1
                                                    have p1971_2 := h1971c.2.2.1
                                                    have p1971_3 := h1971c.2.2.2
                                                    rcases p1971_3 (m.d 0 3) (by simp) with h2001 | h2001
                                                    · linarith only [h1756, h2001, hlam]
                                                    · linarith only [h1753, h2001, hlam]
                                                  · have p1971_0 := h1971c.1
                                                    have p1971_1 := h1971c.2.1
                                                    have p1971_2 := h1971c.2.2.1
                                                    have p1971_3 := h1971c.2.2.2
                                                    linarith only [hlam, p1971_0]
                                                  · have p1971_0 := h1971c.1
                                                    have p1971_1 := h1971c.2.1
                                                    have p1971_2 := h1971c.2.2.1
                                                    have p1971_3 := h1971c.2.2.2
                                                    linarith only [h1756, h1808, h1939, hc03, hc34, hlam, hphi, p1971_1]
                                                  · have p1971_0 := h1971c.1
                                                    have p1971_1 := h1971c.2.1
                                                    have p1971_2 := h1971c.2.2.1
                                                    have p1971_3 := h1971c.2.2.2
                                                    linarith only [h1750, hc13, hlam, hphi, ht34, ht45, p1971_1, u5elo3]
                                                  · have p1971_0 := h1971c.1
                                                    have p1971_1 := h1971c.2.1
                                                    have p1971_2 := h1971c.2.2.1
                                                    have p1971_3 := h1971c.2.2.2
                                                    linarith only [h1924, hc23, hlam, hphi, ht34, ht45, p1971_1, u5elo3]
                                                  · have p1971_0 := h1971c.1
                                                    have p1971_1 := h1971c.2.1
                                                    have p1971_2 := h1971c.2.2.1
                                                    have p1971_3 := h1971c.2.2.2
                                                    linarith only [hc23, hlam, hphi, ht34, ht45, p1971_1, u5elo3]
                                                  · have p1971_0 := h1971c.1
                                                    have p1971_1 := h1971c.2.1
                                                    have p1971_2 := h1971c.2.2.1
                                                    have p1971_3 := h1971c.2.2.2
                                                    linarith only [h1939, hlam, p1971_0]
                                                  · have p1971_0 := h1971c.1
                                                    have p1971_1 := h1971c.2.1
                                                    have p1971_2 := h1971c.2.2.1
                                                    have p1971_3 := h1971c.2.2.2
                                                    linarith only [hlam, p1971_0]
                                          · linarith only [h1926, h1964, hlam]
                                        · linarith only [h1963, hlam, p1940_0]
                                      · have p1940_0 := h1940c.1
                                        have p1940_1 := h1940c.2.1
                                        have p1940_2 := h1940c.2.2.1
                                        have p1940_3 := h1940c.2.2.2
                                        linarith only [h0, h1752, h1926, hc12, hlam, hphi, ht01, ht0b, ht5b, p1940_1, u5ehi7]
                                      · have p1940_0 := h1940c.1
                                        have p1940_1 := h1940c.2.1
                                        have p1940_2 := h1940c.2.2.1
                                        have p1940_3 := h1940c.2.2.2
                                        linarith only [hlam, p1940_0]
                                      · have p1940_0 := h1940c.1
                                        have p1940_1 := h1940c.2.1
                                        have p1940_2 := h1940c.2.2.1
                                        have p1940_3 := h1940c.2.2.2
                                        rcases p1940_3 (m.d 0 2) (by simp) with h2015 | h2015
                                        · linarith only [h0, h2015, hlam]
                                        · linarith only [h1753, h2015, hlam]
                                      · have p1940_0 := h1940c.1
                                        have p1940_1 := h1940c.2.1
                                        have p1940_2 := h1940c.2.2.1
                                        have p1940_3 := h1940c.2.2.2
                                        rcases p1940_3 (m.d 0 2) (by simp) with h2018 | h2018
                                        · linarith only [h0, h2018, hlam]
                                        · linarith only [h1754, h2018, hlam]
                                      · have p1940_0 := h1940c.1
                                        have p1940_1 := h1940c.2.1
                                        have p1940_2 := h1940c.2.2.1
                                        have p1940_3 := h1940c.2.2.2
                                        rcases p1940_3 (m.d 0 2) (by simp) with h2021 | h2021
                                        · linarith only [h0, h2021, hlam]
                                        · linarith only [h1755, h2021, hlam]
                                      · have p1940_0 := h1940c.1
                                        have p1940_1 := h1940c.2.1
                                        have p1940_2 := h1940c.2.2.1
                                        have p1940_3 := h1940c.2.2.2
                                        linarith only [h1753, hlam, p1940_0]
                                      · have p1940_0 := h1940c.1
                                        have p1940_1 := h1940c.2.1
                                        have p1940_2 := h1940c.2.2.1
                                        have p1940_3 := h1940c.2.2.2
                                        linarith only [h1924, hlam, p1940_0]
                                      · have p1940_0 := h1940c.1
                                        have p1940_1 := h1940c.2.1
                                        have p1940_2 := h1940c.2.2.1
                                        have p1940_3 := h1940c.2.2.2
                                        linarith only [hlam, p1940_0]
                                      · have p1940_0 := h1940c.1
                                        have p1940_1 := h1940c.2.1
                                        have p1940_2 := h1940c.2.2.1
                                        have p1940_3 := h1940c.2.2.2
                                        linarith only [h1933, hlam, p1940_0]
                                      · have p1940_0 := h1940c.1
                                        have p1940_1 := h1940c.2.1
                                        have p1940_2 := h1940c.2.2.1
                                        have p1940_3 := h1940c.2.2.2
                                        linarith only [h1935, hlam, p1940_0]
                                      · have p1940_0 := h1940c.1
                                        have p1940_1 := h1940c.2.1
                                        have p1940_2 := h1940c.2.2.1
                                        have p1940_3 := h1940c.2.2.2
                                        linarith only [h1754, hlam, p1940_0]
                                      · have p1940_0 := h1940c.1
                                        have p1940_1 := h1940c.2.1
                                        have p1940_2 := h1940c.2.2.1
                                        have p1940_3 := h1940c.2.2.2
                                        linarith only [h1925, hlam, p1940_0]
                                      · have p1940_0 := h1940c.1
                                        have p1940_1 := h1940c.2.1
                                        have p1940_2 := h1940c.2.2.1
                                        have p1940_3 := h1940c.2.2.2
                                        linarith only [h1751, h1808, h1925, h1939, hc23, hlam, hphi, ht34, ht45, p1940_1, u5elo3]
                                      · have p1940_0 := h1940c.1
                                        have p1940_1 := h1940c.2.1
                                        have p1940_2 := h1940c.2.2.1
                                        have p1940_3 := h1940c.2.2.2
                                        linarith only [hlam, p1940_0]
                                      · have p1940_0 := h1940c.1
                                        have p1940_1 := h1940c.2.1
                                        have p1940_2 := h1940c.2.2.1
                                        have p1940_3 := h1940c.2.2.2
                                        linarith only [h1937, hlam, p1940_1]
                                      · have p1940_0 := h1940c.1
                                        have p1940_1 := h1940c.2.1
                                        have p1940_2 := h1940c.2.2.1
                                        have p1940_3 := h1940c.2.2.2
                                        linarith only [h1755, hlam, p1940_0]
                                      · have p1940_0 := h1940c.1
                                        have p1940_1 := h1940c.2.1
                                        have p1940_2 := h1940c.2.2.1
                                        have p1940_3 := h1940c.2.2.2
                                        linarith only [h1926, hlam, p1940_0]
                                      · have p1940_0 := h1940c.1
                                        have p1940_1 := h1940c.2.1
                                        have p1940_2 := h1940c.2.2.1
                                        have p1940_3 := h1940c.2.2.2
                                        linarith only [h1752, h1926, hc23, hlam, hphi, ht34, ht45, p1940_1, u5elo0]
                                      · have p1940_0 := h1940c.1
                                        have p1940_1 := h1940c.2.1
                                        have p1940_2 := h1940c.2.2.1
                                        have p1940_3 := h1940c.2.2.2
                                        linarith only [h1752, h1808, h1926, h1939, hc24, hlam, hphi, ht45, p1940_1, u5elo3]
                                      · have p1940_0 := h1940c.1
                                        have p1940_1 := h1940c.2.1
                                        have p1940_2 := h1940c.2.2.1
                                        have p1940_3 := h1940c.2.2.2
                                        linarith only [hlam, p1940_0]
                                    · linarith only [h1750, h1756, h1939, hc13, hlam, hphi, ht34, ht45, u5elo4]
                      · linarith only [h0, h1752, h1926, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
                    · linarith only [h0, h1752, h1925, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
                  · linarith only [h0, h1752, h1924, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
          · linarith only [h0, h1752, h1755, hlam, hphi, u5ehi6, u5elo2]
        · linarith only [h0, h1751, h1754, hlam]
      · linarith only [h0, h1750, h1753, hlam]
    · linarith only [h1751, h1752, hc14, hlam, hphi, ht45, u5elo1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2047 | h2047
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2048 | h2048
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2049 | h2049
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2050 | h2050
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2051 | h2051
            · linarith only [h1750, h1751, h2051, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2053 | h2053
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2054 | h2054
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2055 | h2055
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2056 | h2056
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2057 | h2057
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2058 | h2058
                        · linarith only [h2051, h2053, h2058, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2060 | h2060
                          · linarith only [h1750, h1751, h2058, h2060, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi8]
                          · linarith only [h1750, h1751, h2053, h2058, h2060, hc13, hc34, hlam, hphi]
                      · linarith only [h1751, h2047, h2056, h2057, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
                    · linarith only [h0, h1750, h2049, h2053, h2056, hc02, hlam, hphi, ht0b, ht5b, u5ehi8]
                  · linarith only [h0, h1750, h2053, h2055, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                · linarith only [h1750, h1751, h2053, h2054, hlam, hphi, u5ehi8, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2067 | h2067
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2068 | h2068
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2069 | h2069
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2070 | h2070
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2071 | h2071
                        · linarith only [h1750, h2053, h2071, hc34, hlam, hphi, ht45, u5elo3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2073 | h2073
                          · linarith only [h1750, h2053, h2073, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2075 | h2075
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2076 | h2076
                              · linarith only [h1750, h1751, h2053, h2068, h2071, h2076, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2078 | h2078
                                · linarith only [h1750, h2053, h2068, h2078, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2080 | h2080
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2081 | h2081
                                    · rcases h2bigk with h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c | h2082c
                                      · have p2082_0 := h2082c.1
                                        have p2082_1 := h2082c.2.1
                                        have p2082_2 := h2082c.2.2.1
                                        have p2082_3 := h2082c.2.2.2
                                        linarith only [hlam, p2082_0]
                                      · have p2082_0 := h2082c.1
                                        have p2082_1 := h2082c.2.1
                                        have p2082_2 := h2082c.2.2.1
                                        have p2082_3 := h2082c.2.2.2
                                        linarith only [h0, hlam, p2082_1]
                                      · have p2082_0 := h2082c.1
                                        have p2082_1 := h2082c.2.1
                                        have p2082_2 := h2082c.2.2.1
                                        have p2082_3 := h2082c.2.2.2
                                        rcases p2082_3 (m.d 0 2) (by simp) with h2085 | h2085
                                        · rcases p2082_3 (m.d 1 2) (by simp) with h2086 | h2086
                                          · rcases p2082_3 (m.d 2 3) (by simp) with h2087 | h2087
                                            · linarith only [h2087, hlam, p2082_0]
                                            · rcases p2082_3 (m.d 2 4) (by simp) with h2089 | h2089
                                              · linarith only [h2049, h2089, hlam]
                                              · linarith only [h2076, h2089, hlam]
                                          · linarith only [h2068, h2086, hlam]
                                        · linarith only [h2085, hlam, p2082_0]
                                      · have p2082_0 := h2082c.1
                                        have p2082_1 := h2082c.2.1
                                        have p2082_2 := h2082c.2.2.1
                                        have p2082_3 := h2082c.2.2.2
                                        linarith only [h2080, hc02, hlam, hphi, ht0b, ht5b, p2082_1, u5ehi9]
                                      · have p2082_0 := h2082c.1
                                        have p2082_1 := h2082c.2.1
                                        have p2082_2 := h2082c.2.2.1
                                        have p2082_3 := h2082c.2.2.2
                                        rcases p2082_3 (m.d 0 2) (by simp) with h2095 | h2095
                                        · rcases p2082_3 (m.d 1 2) (by simp) with h2096 | h2096
                                          · rcases p2082_3 (m.d 2 3) (by simp) with h2097 | h2097
                                            · linarith only [h2048, h2097, hlam]
                                            · rcases p2082_3 (m.d 2 4) (by simp) with h2099 | h2099
                                              · linarith only [h2049, h2099, hlam]
                                              · linarith only [h2080, h2099, hlam]
                                          · linarith only [h2070, h2096, hlam]
                                        · linarith only [h2095, hlam, p2082_0]
                                      · have p2082_0 := h2082c.1
                                        have p2082_1 := h2082c.2.1
                                        have p2082_2 := h2082c.2.2.1
                                        have p2082_3 := h2082c.2.2.2
                                        linarith only [h0, h2047, h2070, h2080, hc12, hlam, hphi, ht01, ht0b, ht5b, p2082_1, u5ehi9]
                                      · have p2082_0 := h2082c.1
                                        have p2082_1 := h2082c.2.1
                                        have p2082_2 := h2082c.2.2.1
                                        have p2082_3 := h2082c.2.2.2
                                        linarith only [hlam, p2082_0]
                                      · have p2082_0 := h2082c.1
                                        have p2082_1 := h2082c.2.1
                                        have p2082_2 := h2082c.2.2.1
                                        have p2082_3 := h2082c.2.2.2
                                        rcases p2082_3 (m.d 0 2) (by simp) with h2106 | h2106
                                        · linarith only [h0, h2106, hlam]
                                        · linarith only [h2048, h2106, hlam]
                                      · have p2082_0 := h2082c.1
                                        have p2082_1 := h2082c.2.1
                                        have p2082_2 := h2082c.2.2.1
                                        have p2082_3 := h2082c.2.2.2
                                        linarith only [h2080, hc12, hlam, hphi, ht01, ht0b, ht5b, p2082_1, u5ehi9]
                                      · have p2082_0 := h2082c.1
                                        have p2082_1 := h2082c.2.1
                                        have p2082_2 := h2082c.2.2.1
                                        have p2082_3 := h2082c.2.2.2
                                        rcases p2082_3 (m.d 0 2) (by simp) with h2110 | h2110
                                        · linarith only [h0, h2110, hlam]
                                        · linarith only [h2050, h2110, hlam]
                                      · have p2082_0 := h2082c.1
                                        have p2082_1 := h2082c.2.1
                                        have p2082_2 := h2082c.2.2.1
                                        have p2082_3 := h2082c.2.2.2
                                        linarith only [h2048, hlam, p2082_0]
                                      · have p2082_0 := h2082c.1
                                        have p2082_1 := h2082c.2.1
                                        have p2082_2 := h2082c.2.2.1
                                        have p2082_3 := h2082c.2.2.2
                                        linarith only [h2068, hlam, p2082_0]
                                      · have p2082_0 := h2082c.1
                                        have p2082_1 := h2082c.2.1
                                        have p2082_2 := h2082c.2.2.1
                                        have p2082_3 := h2082c.2.2.2
                                        linarith only [hlam, p2082_0]
                                      · have p2082_0 := h2082c.1
                                        have p2082_1 := h2082c.2.1
                                        have p2082_2 := h2082c.2.2.1
                                        have p2082_3 := h2082c.2.2.2
                                        linarith only [h2076, hlam, p2082_0]
                                      · have p2082_0 := h2082c.1
                                        have p2082_1 := h2082c.2.1
                                        have p2082_2 := h2082c.2.2.1
                                        have p2082_3 := h2082c.2.2.2
                                        linarith only [h2078, hlam, p2082_0]
                                      · have p2082_0 := h2082c.1
                                        have p2082_1 := h2082c.2.1
                                        have p2082_2 := h2082c.2.2.1
                                        have p2082_3 := h2082c.2.2.2
                                        linarith only [h2049, hlam, p2082_0]
                                      · have p2082_0 := h2082c.1
                                        have p2082_1 := h2082c.2.1
                                        have p2082_2 := h2082c.2.2.1
                                        have p2082_3 := h2082c.2.2.2
                                        linarith only [h2069, hlam, p2082_0]
                                      · have p2082_0 := h2082c.1
                                        have p2082_1 := h2082c.2.1
                                        have p2082_2 := h2082c.2.2.1
                                        have p2082_3 := h2082c.2.2.2
                                        rcases p2082_3 (m.d 0 2) (by simp) with h2120 | h2120
                                        · rcases p2082_3 (m.d 1 2) (by simp) with h2121 | h2121
                                          · rcases p2082_3 (m.d 2 3) (by simp) with h2122 | h2122
                                            · linarith only [h2076, h2122, hlam]
                                            · rcases p2082_3 (m.d 2 4) (by simp) with h2124 | h2124
                                              · rcases p2082_3 (m.d 2 5) (by simp) with h2125 | h2125
                                                · linarith only [h2080, h2125, hlam]
                                                · linarith only [h2078, h2125, hlam]
                                              · linarith only [h2076, h2124, hlam]
                                          · linarith only [h2068, h2121, hlam]
                                        · linarith only [h2048, h2120, hlam]
                                      · have p2082_0 := h2082c.1
                                        have p2082_1 := h2082c.2.1
                                        have p2082_2 := h2082c.2.2.1
                                        have p2082_3 := h2082c.2.2.2
                                        linarith only [hlam, p2082_0]
                                      · have p2082_0 := h2082c.1
                                        have p2082_1 := h2082c.2.1
                                        have p2082_2 := h2082c.2.2.1
                                        have p2082_3 := h2082c.2.2.2
                                        linarith only [h2049, h2080, hc02, hlam, hphi, ht0b, ht5b, p2082_1, u5ehi9]
                                      · have p2082_0 := h2082c.1
                                        have p2082_1 := h2082c.2.1
                                        have p2082_2 := h2082c.2.2.1
                                        have p2082_3 := h2082c.2.2.2
                                        linarith only [h2050, hlam, p2082_0]
                                      · have p2082_0 := h2082c.1
                                        have p2082_1 := h2082c.2.1
                                        have p2082_2 := h2082c.2.2.1
                                        have p2082_3 := h2082c.2.2.2
                                        linarith only [h2070, hlam, p2082_0]
                                      · have p2082_0 := h2082c.1
                                        have p2082_1 := h2082c.2.1
                                        have p2082_2 := h2082c.2.2.1
                                        have p2082_3 := h2082c.2.2.2
                                        linarith only [h1751, h2047, h2070, h2071, hc23, hc34, hlam, hphi, p2082_1]
                                      · have p2082_0 := h2082c.1
                                        have p2082_1 := h2082c.2.1
                                        have p2082_2 := h2082c.2.2.1
                                        have p2082_3 := h2082c.2.2.2
                                        linarith only [h2080, hlam, p2082_0]
                                      · have p2082_0 := h2082c.1
                                        have p2082_1 := h2082c.2.1
                                        have p2082_2 := h2082c.2.2.1
                                        have p2082_3 := h2082c.2.2.2
                                        linarith only [hlam, p2082_0]
                                    · linarith only [h1751, h2047, h2070, h2071, h2080, h2081, hlam]
                                  · linarith only [h1751, h2047, h2071, h2075, h2076, h2080, hc23, hc34, hlam, hphi]
                            · linarith only [h1751, h2047, h2075, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi6]
                      · linarith only [h0, h2047, h2070, hlam, hphi, u5ehi6, u5elo2]
                    · linarith only [h0, h2047, h2069, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
                  · linarith only [h0, h2047, h2068, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
                · linarith only [h1751, h2047, h2067, hlam, hphi, u5ehi6, u5elo4]
          · linarith only [h2049, h2050, hc24, hlam, hphi, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2146 | h2146
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2147 | h2147
            · linarith only [h0, h1750, h2049, h2147, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2149 | h2149
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2150 | h2150
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2151 | h2151
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2152 | h2152
                    · linarith only [h0, h1750, h2049, h2149, h2152, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                    · linarith only [h0, h1750, h2149, h2152, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                  · linarith only [h0, h1750, h2149, h2151, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                · linarith only [h0, h1750, h2049, h2149, h2150, hlam, hphi, u5ehi8, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2157 | h2157
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2158 | h2158
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2159 | h2159
                    · linarith only [h0, h2047, h2049, h2159, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi6]
                    · linarith only [h0, h2047, h2159, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
                  · linarith only [h0, h2047, h2158, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
                · linarith only [h0, h2047, h2049, h2157, hlam, hphi, u5ehi6, u5elo4]
          · linarith only [h0, h2047, h2146, hlam, hphi, u5ehi6, u5elo2]
      · linarith only [h0, h1750, h2048, hlam]
    · linarith only [h1750, h2047, hc13, hlam, hphi, ht34, ht45, u5elo1]

set_option maxHeartbeats 7280000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_LR_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1750 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2167 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2168 | h2168
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2169 | h2169
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2170 | h2170
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2171 | h2171
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2172 | h2172
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2173 | h2173
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2174 | h2174
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2175 | h2175
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2176 | h2176
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2177 | h2177
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2178 | h2178
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2179 | h2179
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2180 | h2180
                          · linarith only [h1750, h2167, h2175, h2180, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2182 | h2182
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2183 | h2183
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2184 | h2184
                                · linarith only [h2176, h2180, h2184, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2186 | h2186
                                  · linarith only [h2176, h2180, h2182, h2186, hlam]
                                  · rcases h2bigk with h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c
                                    · have p2188_0 := h2188c.1
                                      have p2188_1 := h2188c.2.1
                                      have p2188_2 := h2188c.2.2.1
                                      have p2188_3 := h2188c.2.2.2
                                      linarith only [hlam, p2188_0]
                                    · have p2188_0 := h2188c.1
                                      have p2188_1 := h2188c.2.1
                                      have p2188_2 := h2188c.2.2.1
                                      have p2188_3 := h2188c.2.2.2
                                      linarith only [h0, hlam, p2188_1]
                                    · have p2188_0 := h2188c.1
                                      have p2188_1 := h2188c.2.1
                                      have p2188_2 := h2188c.2.2.1
                                      have p2188_3 := h2188c.2.2.2
                                      linarith only [h2183, hc02, hlam, hphi, ht0b, ht5b, p2188_1, u5ehi8]
                                    · have p2188_0 := h2188c.1
                                      have p2188_1 := h2188c.2.1
                                      have p2188_2 := h2188c.2.2.1
                                      have p2188_3 := h2188c.2.2.2
                                      rcases p2188_3 (m.d 0 2) (by simp) with h2192 | h2192
                                      · rcases p2188_3 (m.d 1 2) (by simp) with h2193 | h2193
                                        · rcases p2188_3 (m.d 2 3) (by simp) with h2194 | h2194
                                          · linarith only [h2169, h2194, hlam]
                                          · linarith only [h2182, h2194, hlam]
                                        · linarith only [h2176, h2193, hlam]
                                      · linarith only [h2192, hlam, p2188_0]
                                    · have p2188_0 := h2188c.1
                                      have p2188_1 := h2188c.2.1
                                      have p2188_2 := h2188c.2.2.1
                                      have p2188_3 := h2188c.2.2.2
                                      rcases p2188_3 (m.d 0 2) (by simp) with h2199 | h2199
                                      · rcases p2188_3 (m.d 1 2) (by simp) with h2200 | h2200
                                        · rcases p2188_3 (m.d 2 3) (by simp) with h2201 | h2201
                                          · linarith only [h2169, h2201, hlam]
                                          · linarith only [h2183, h2201, hlam]
                                        · linarith only [h2177, h2200, hlam]
                                      · linarith only [h2199, hlam, p2188_0]
                                    · have p2188_0 := h2188c.1
                                      have p2188_1 := h2188c.2.1
                                      have p2188_2 := h2188c.2.2.1
                                      have p2188_3 := h2188c.2.2.2
                                      linarith only [h0, h2167, h2174, h2176, h2180, h2182, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2188_1]
                                    · have p2188_0 := h2188c.1
                                      have p2188_1 := h2188c.2.1
                                      have p2188_2 := h2188c.2.2.1
                                      have p2188_3 := h2188c.2.2.2
                                      linarith only [hlam, p2188_0]
                                    · have p2188_0 := h2188c.1
                                      have p2188_1 := h2188c.2.1
                                      have p2188_2 := h2188c.2.2.1
                                      have p2188_3 := h2188c.2.2.2
                                      linarith only [h2183, hc12, hlam, hphi, ht01, ht0b, ht5b, p2188_1, u5ehi8]
                                    · have p2188_0 := h2188c.1
                                      have p2188_1 := h2188c.2.1
                                      have p2188_2 := h2188c.2.2.1
                                      have p2188_3 := h2188c.2.2.2
                                      linarith only [h0, h2167, h2174, h2176, h2180, hlam, p2188_2]
                                    · have p2188_0 := h2188c.1
                                      have p2188_1 := h2188c.2.1
                                      have p2188_2 := h2188c.2.2.1
                                      have p2188_3 := h2188c.2.2.2
                                      rcases p2188_3 (m.d 0 2) (by simp) with h2210 | h2210
                                      · linarith only [h0, h2210, hlam]
                                      · linarith only [h2171, h2210, hlam]
                                    · have p2188_0 := h2188c.1
                                      have p2188_1 := h2188c.2.1
                                      have p2188_2 := h2188c.2.2.1
                                      have p2188_3 := h2188c.2.2.2
                                      linarith only [h2169, hlam, p2188_0]
                                    · have p2188_0 := h2188c.1
                                      have p2188_1 := h2188c.2.1
                                      have p2188_2 := h2188c.2.2.1
                                      have p2188_3 := h2188c.2.2.2
                                      linarith only [h2175, hlam, p2188_0]
                                    · have p2188_0 := h2188c.1
                                      have p2188_1 := h2188c.2.1
                                      have p2188_2 := h2188c.2.2.1
                                      have p2188_3 := h2188c.2.2.2
                                      linarith only [hlam, p2188_0]
                                    · have p2188_0 := h2188c.1
                                      have p2188_1 := h2188c.2.1
                                      have p2188_2 := h2188c.2.2.1
                                      have p2188_3 := h2188c.2.2.2
                                      rcases p2188_3 (m.d 0 2) (by simp) with h2216 | h2216
                                      · rcases p2188_3 (m.d 1 2) (by simp) with h2217 | h2217
                                        · rcases p2188_3 (m.d 2 3) (by simp) with h2218 | h2218
                                          · rcases p2188_3 (m.d 2 4) (by simp) with h2219 | h2219
                                            · linarith only [h2182, h2219, hlam]
                                            · rcases p2188_3 (m.d 2 5) (by simp) with h2221 | h2221
                                              · linarith only [h2183, h2221, hlam]
                                              · linarith only [h2184, h2221, hlam]
                                          · linarith only [h2182, h2218, hlam]
                                        · linarith only [h2176, h2217, hlam]
                                      · linarith only [h2170, h2216, hlam]
                                    · have p2188_0 := h2188c.1
                                      have p2188_1 := h2188c.2.1
                                      have p2188_2 := h2188c.2.2.1
                                      have p2188_3 := h2188c.2.2.2
                                      linarith only [h2169, h2183, hc02, hlam, hphi, ht0b, ht5b, p2188_1, u5ehi8]
                                    · have p2188_0 := h2188c.1
                                      have p2188_1 := h2188c.2.1
                                      have p2188_2 := h2188c.2.2.1
                                      have p2188_3 := h2188c.2.2.2
                                      linarith only [h2170, hlam, p2188_0]
                                    · have p2188_0 := h2188c.1
                                      have p2188_1 := h2188c.2.1
                                      have p2188_2 := h2188c.2.2.1
                                      have p2188_3 := h2188c.2.2.2
                                      linarith only [h2176, hlam, p2188_0]
                                    · have p2188_0 := h2188c.1
                                      have p2188_1 := h2188c.2.1
                                      have p2188_2 := h2188c.2.2.1
                                      have p2188_3 := h2188c.2.2.2
                                      linarith only [h2182, hlam, p2188_1]
                                    · have p2188_0 := h2188c.1
                                      have p2188_1 := h2188c.2.1
                                      have p2188_2 := h2188c.2.2.1
                                      have p2188_3 := h2188c.2.2.2
                                      linarith only [hlam, p2188_0]
                                    · have p2188_0 := h2188c.1
                                      have p2188_1 := h2188c.2.1
                                      have p2188_2 := h2188c.2.2.1
                                      have p2188_3 := h2188c.2.2.2
                                      linarith only [h2184, hlam, p2188_1]
                                    · have p2188_0 := h2188c.1
                                      have p2188_1 := h2188c.2.1
                                      have p2188_2 := h2188c.2.2.1
                                      have p2188_3 := h2188c.2.2.2
                                      linarith only [h2171, hlam, p2188_0]
                                    · have p2188_0 := h2188c.1
                                      have p2188_1 := h2188c.2.1
                                      have p2188_2 := h2188c.2.2.1
                                      have p2188_3 := h2188c.2.2.2
                                      linarith only [h2177, hlam, p2188_0]
                                    · have p2188_0 := h2188c.1
                                      have p2188_1 := h2188c.2.1
                                      have p2188_2 := h2188c.2.2.1
                                      have p2188_3 := h2188c.2.2.2
                                      linarith only [h2183, hlam, p2188_1]
                                    · have p2188_0 := h2188c.1
                                      have p2188_1 := h2188c.2.1
                                      have p2188_2 := h2188c.2.2.1
                                      have p2188_3 := h2188c.2.2.2
                                      linarith only [h2177, h2182, hc34, hlam, hphi, ht45, p2188_1, u5elo1]
                                    · have p2188_0 := h2188c.1
                                      have p2188_1 := h2188c.2.1
                                      have p2188_2 := h2188c.2.2.1
                                      have p2188_3 := h2188c.2.2.2
                                      linarith only [hlam, p2188_0]
                              · linarith only [h1750, h2167, h2174, h2175, h2179, h2180, h2182, h2183, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h1750, h2167, h2174, h2175, h2178, h2180, h2182, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h1750, h2167, h2174, h2179, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
                      · linarith only [h1750, h2167, h2174, h2178, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
                    · linarith only [h1750, h2167, h2174, h2175, h2177, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                  · linarith only [h1750, h2167, h2174, h2175, h2176, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                · linarith only [h0, h2167, h2174, h2175, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2245 | h2245
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2246 | h2246
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2247 | h2247
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2248 | h2248
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2249 | h2249
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2250 | h2250
                          · linarith only [h1750, h2167, h2174, h2245, h2250, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2252 | h2252
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2253 | h2253
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2254 | h2254
                                · linarith only [h2167, h2174, h2246, h2254, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2256 | h2256
                                  · linarith only [h2167, h2174, h2246, h2252, h2256, hlam]
                                  · rcases h2bigk with h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c | h2258c
                                    · have p2258_0 := h2258c.1
                                      have p2258_1 := h2258c.2.1
                                      have p2258_2 := h2258c.2.2.1
                                      have p2258_3 := h2258c.2.2.2
                                      linarith only [hlam, p2258_0]
                                    · have p2258_0 := h2258c.1
                                      have p2258_1 := h2258c.2.1
                                      have p2258_2 := h2258c.2.2.1
                                      have p2258_3 := h2258c.2.2.2
                                      linarith only [h0, hlam, p2258_1]
                                    · have p2258_0 := h2258c.1
                                      have p2258_1 := h2258c.2.1
                                      have p2258_2 := h2258c.2.2.1
                                      have p2258_3 := h2258c.2.2.2
                                      linarith only [h2253, hc02, hlam, hphi, ht0b, ht5b, p2258_1, u5ehi8]
                                    · have p2258_0 := h2258c.1
                                      have p2258_1 := h2258c.2.1
                                      have p2258_2 := h2258c.2.2.1
                                      have p2258_3 := h2258c.2.2.2
                                      rcases p2258_3 (m.d 0 2) (by simp) with h2262 | h2262
                                      · rcases p2258_3 (m.d 1 2) (by simp) with h2263 | h2263
                                        · rcases p2258_3 (m.d 2 3) (by simp) with h2264 | h2264
                                          · linarith only [h2169, h2264, hlam]
                                          · linarith only [h2252, h2264, hlam]
                                        · linarith only [h2246, h2263, hlam]
                                      · linarith only [h2262, hlam, p2258_0]
                                    · have p2258_0 := h2258c.1
                                      have p2258_1 := h2258c.2.1
                                      have p2258_2 := h2258c.2.2.1
                                      have p2258_3 := h2258c.2.2.2
                                      rcases p2258_3 (m.d 0 2) (by simp) with h2269 | h2269
                                      · rcases p2258_3 (m.d 1 2) (by simp) with h2270 | h2270
                                        · rcases p2258_3 (m.d 2 3) (by simp) with h2271 | h2271
                                          · linarith only [h2169, h2271, hlam]
                                          · linarith only [h2253, h2271, hlam]
                                        · linarith only [h2247, h2270, hlam]
                                      · linarith only [h2269, hlam, p2258_0]
                                    · have p2258_0 := h2258c.1
                                      have p2258_1 := h2258c.2.1
                                      have p2258_2 := h2258c.2.2.1
                                      have p2258_3 := h2258c.2.2.2
                                      linarith only [h0, h2168, h2247, h2253, hc12, hlam, hphi, ht01, ht0b, ht5b, p2258_1, u5ehi8]
                                    · have p2258_0 := h2258c.1
                                      have p2258_1 := h2258c.2.1
                                      have p2258_2 := h2258c.2.2.1
                                      have p2258_3 := h2258c.2.2.2
                                      linarith only [hlam, p2258_0]
                                    · have p2258_0 := h2258c.1
                                      have p2258_1 := h2258c.2.1
                                      have p2258_2 := h2258c.2.2.1
                                      have p2258_3 := h2258c.2.2.2
                                      linarith only [h2253, hc12, hlam, hphi, ht01, ht0b, ht5b, p2258_1, u5ehi8]
                                    · have p2258_0 := h2258c.1
                                      have p2258_1 := h2258c.2.1
                                      have p2258_2 := h2258c.2.2.1
                                      have p2258_3 := h2258c.2.2.2
                                      rcases p2258_3 (m.d 0 2) (by simp) with h2279 | h2279
                                      · linarith only [h0, h2279, hlam]
                                      · linarith only [h2170, h2279, hlam]
                                    · have p2258_0 := h2258c.1
                                      have p2258_1 := h2258c.2.1
                                      have p2258_2 := h2258c.2.2.1
                                      have p2258_3 := h2258c.2.2.2
                                      rcases p2258_3 (m.d 0 2) (by simp) with h2282 | h2282
                                      · linarith only [h0, h2282, hlam]
                                      · linarith only [h2171, h2282, hlam]
                                    · have p2258_0 := h2258c.1
                                      have p2258_1 := h2258c.2.1
                                      have p2258_2 := h2258c.2.2.1
                                      have p2258_3 := h2258c.2.2.2
                                      linarith only [h2169, hlam, p2258_0]
                                    · have p2258_0 := h2258c.1
                                      have p2258_1 := h2258c.2.1
                                      have p2258_2 := h2258c.2.2.1
                                      have p2258_3 := h2258c.2.2.2
                                      linarith only [h2245, hlam, p2258_0]
                                    · have p2258_0 := h2258c.1
                                      have p2258_1 := h2258c.2.1
                                      have p2258_2 := h2258c.2.2.1
                                      have p2258_3 := h2258c.2.2.2
                                      linarith only [hlam, p2258_0]
                                    · have p2258_0 := h2258c.1
                                      have p2258_1 := h2258c.2.1
                                      have p2258_2 := h2258c.2.2.1
                                      have p2258_3 := h2258c.2.2.2
                                      rcases p2258_3 (m.d 0 2) (by simp) with h2288 | h2288
                                      · rcases p2258_3 (m.d 1 2) (by simp) with h2289 | h2289
                                        · rcases p2258_3 (m.d 2 3) (by simp) with h2290 | h2290
                                          · rcases p2258_3 (m.d 2 4) (by simp) with h2291 | h2291
                                            · linarith only [h2252, h2291, hlam]
                                            · rcases p2258_3 (m.d 2 5) (by simp) with h2293 | h2293
                                              · linarith only [h2253, h2293, hlam]
                                              · linarith only [h2254, h2293, hlam]
                                          · linarith only [h2252, h2290, hlam]
                                        · linarith only [h2246, h2289, hlam]
                                      · linarith only [h2170, h2288, hlam]
                                    · have p2258_0 := h2258c.1
                                      have p2258_1 := h2258c.2.1
                                      have p2258_2 := h2258c.2.2.1
                                      have p2258_3 := h2258c.2.2.2
                                      linarith only [h2169, h2253, hc02, hlam, hphi, ht0b, ht5b, p2258_1, u5ehi8]
                                    · have p2258_0 := h2258c.1
                                      have p2258_1 := h2258c.2.1
                                      have p2258_2 := h2258c.2.2.1
                                      have p2258_3 := h2258c.2.2.2
                                      linarith only [h2170, hlam, p2258_0]
                                    · have p2258_0 := h2258c.1
                                      have p2258_1 := h2258c.2.1
                                      have p2258_2 := h2258c.2.2.1
                                      have p2258_3 := h2258c.2.2.2
                                      linarith only [h2246, hlam, p2258_0]
                                    · have p2258_0 := h2258c.1
                                      have p2258_1 := h2258c.2.1
                                      have p2258_2 := h2258c.2.2.1
                                      have p2258_3 := h2258c.2.2.2
                                      linarith only [h2252, hlam, p2258_1]
                                    · have p2258_0 := h2258c.1
                                      have p2258_1 := h2258c.2.1
                                      have p2258_2 := h2258c.2.2.1
                                      have p2258_3 := h2258c.2.2.2
                                      linarith only [hlam, p2258_0]
                                    · have p2258_0 := h2258c.1
                                      have p2258_1 := h2258c.2.1
                                      have p2258_2 := h2258c.2.2.1
                                      have p2258_3 := h2258c.2.2.2
                                      linarith only [h2254, hlam, p2258_1]
                                    · have p2258_0 := h2258c.1
                                      have p2258_1 := h2258c.2.1
                                      have p2258_2 := h2258c.2.2.1
                                      have p2258_3 := h2258c.2.2.2
                                      linarith only [h2171, hlam, p2258_0]
                                    · have p2258_0 := h2258c.1
                                      have p2258_1 := h2258c.2.1
                                      have p2258_2 := h2258c.2.2.1
                                      have p2258_3 := h2258c.2.2.2
                                      linarith only [h2247, hlam, p2258_0]
                                    · have p2258_0 := h2258c.1
                                      have p2258_1 := h2258c.2.1
                                      have p2258_2 := h2258c.2.2.1
                                      have p2258_3 := h2258c.2.2.2
                                      linarith only [h2253, hlam, p2258_1]
                                    · have p2258_0 := h2258c.1
                                      have p2258_1 := h2258c.2.1
                                      have p2258_2 := h2258c.2.2.1
                                      have p2258_3 := h2258c.2.2.2
                                      linarith only [hc24, hlam, hphi, ht45, p2258_1, u5elo2]
                                    · have p2258_0 := h2258c.1
                                      have p2258_1 := h2258c.2.1
                                      have p2258_2 := h2258c.2.2.1
                                      have p2258_3 := h2258c.2.2.2
                                      linarith only [hlam, p2258_0]
                              · linarith only [h1750, h2168, h2245, h2249, h2252, h2253, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h2172, h2174, h2252, hc23, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h1750, h2168, h2249, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi6]
                      · linarith only [h1750, h2168, h2247, h2248, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                    · linarith only [h0, h2168, h2247, hlam, hphi, u5ehi6, u5elo2]
                  · linarith only [h0, h2168, h2246, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
                · linarith only [h0, h2168, h2245, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
            · linarith only [h1750, h2168, h2173, hlam, hphi, u5ehi6, u5elo3]
          · linarith only [h1750, h2167, h2172, hlam]
        · linarith only [h2169, h2171, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · linarith only [h1750, h2167, h2169, h2170, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2321 | h2321
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2322 | h2322
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2323 | h2323
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2324 | h2324
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2325 | h2325
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2326 | h2326
                · linarith only [h0, h2167, h2169, h2325, h2326, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                · linarith only [h0, h2167, h2325, h2326, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2329 | h2329
                · linarith only [h0, h2168, h2169, h2329, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi6]
                · linarith only [h0, h2168, h2329, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
            · linarith only [h0, h2168, h2169, h2324, hlam, hphi, u5ehi6, u5elo3]
          · linarith only [h0, h2167, h2169, h2323, hlam]
        · linarith only [h0, h2168, h2322, hlam, hphi, u5ehi6, u5elo2]
      · linarith only [h0, h2167, h2321, hlam]
  · linarith only [h2167, h2168, hc14, hlam, hphi, ht45, u5elo1]

end R2N4
