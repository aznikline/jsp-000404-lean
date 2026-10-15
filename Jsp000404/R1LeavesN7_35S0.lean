import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5224000 in
theorem r1l7_20_11_13_14_H_L_L_I_L_I_L_I_s1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg811 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1501 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h0elo := hb0.1
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h811 := hg811
  rcases m.htr 0 1 5 (by decide) (by decide) with h1502 | h1502
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1503 | h1503
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1504 | h1504
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1505 | h1505
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1506 | h1506
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1507 | h1507
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1508 | h1508
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1509 | h1509
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1510 | h1510
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1511 | h1511
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1512 | h1512
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1513 | h1513
                        · linarith only [h1501, h1513, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h1501, h1503, h1507, h1513, h811, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h1503, h1506, h1512, h811, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h1501, h1503, h1505, h1509, h1511, h811, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h1502, h1508, h1510, h811, hlam]
                · linarith only [h1504, h1508, h1509, h811, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h1503, h1508, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1521 | h1521
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1522 | h1522
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1523 | h1523
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1524 | h1524
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1525 | h1525
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1526 | h1526
                        · linarith only [h1501, h1507, h1526, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1528 | h1528
                          · linarith only [h1503, h1528, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · linarith only [h1501, h1503, h1524, h1528, h811, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h1503, h1506, h1525, h811, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h1501, h1503, h1505, h1522, h1524, h811, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h1502, h1521, h1523, h811, hlam]
                · linarith only [h1504, h1521, h1522, h811, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h1501, h1503, h1521, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
          · linarith only [h1502, h1506, h811, hlam]
        · linarith only [h1501, h1505, h811, hlam]
      · linarith only [h0, h1501, h1504, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1539 | h1539
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1540 | h1540
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1541 | h1541
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1542 | h1542
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1543 | h1543
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1544 | h1544
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1545 | h1545
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1546 | h1546
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1547 | h1547
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1548 | h1548
                        · linarith only [h0, h1501, h1503, h1548, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                        · linarith only [h0, h1501, h1503, h1542, h1548, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h0, h1503, h1541, h1543, h1547, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h0, h1501, h1503, h1540, h1543, h1544, h1546, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · linarith only [h0, h1501, h1503, h1543, h1544, h1545, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h1501, h1503, h1543, h1544, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1555 | h1555
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1556 | h1556
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1557 | h1557
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1558 | h1558
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1559 | h1559
                        · linarith only [h1501, h1559, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h0, h1501, h1542, h1543, h1559, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h1541, h1543, h1558, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h0, h1501, h1540, h1543, h1555, h1557, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · linarith only [h0, h1502, h1556, hlam]
                · linarith only [h0, h1503, h1539, h1555, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1566 | h1566
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1567 | h1567
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1568 | h1568
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1569 | h1569
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1570 | h1570
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1571 | h1571
                        · linarith only [h1501, h1542, h1571, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1573 | h1573
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1574 | h1574
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1575 | h1575
                              · linarith only [h0, h1501, h1503, h1542, h1567, h1575, hc05, hlam, hphi, ht0b, ht5b, u0elo2]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1577 | h1577
                                · linarith only [h1540, h1542, h1577, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
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
                                    linarith only [h0, hlam, p1579_0]
                                  · have p1579_0 := h1579c.1
                                    have p1579_1 := h1579c.2.1
                                    have p1579_2 := h1579c.2.2.1
                                    have p1579_3 := h1579c.2.2.2
                                    linarith only [h811, hlam, p1579_0]
                                  · have p1579_0 := h1579c.1
                                    have p1579_1 := h1579c.2.1
                                    have p1579_2 := h1579c.2.2.1
                                    have p1579_3 := h1579c.2.2.2
                                    linarith only [h0, h1503, h1567, h1573, hc34, hlam, hphi, ht0b, ht45, ht5b, p1579_1, u0elo2]
                                  · have p1579_0 := h1579c.1
                                    have p1579_1 := h1579c.2.1
                                    have p1579_2 := h1579c.2.2.1
                                    have p1579_3 := h1579c.2.2.2
                                    linarith only [h0, h1503, hc15, hlam, hphi, ht0b, ht5b, p1579_1, u0elo2]
                                  · have p1579_0 := h1579c.1
                                    have p1579_1 := h1579c.2.1
                                    have p1579_2 := h1579c.2.2.1
                                    have p1579_3 := h1579c.2.2.2
                                    rcases p1579_3 (m.d 0 1) (by simp) with h1585 | h1585
                                    · linarith only [h1585, hlam, p1579_0]
                                    · rcases p1579_3 (m.d 1 2) (by simp) with h1587 | h1587
                                      · rcases p1579_3 (m.d 1 3) (by simp) with h1588 | h1588
                                        · linarith only [h1566, h1588, hlam]
                                        · linarith only [h1588, h811, hlam]
                                      · linarith only [h1587, hlam, p1579_0]
                                  · have p1579_0 := h1579c.1
                                    have p1579_1 := h1579c.2.1
                                    have p1579_2 := h1579c.2.2.1
                                    have p1579_3 := h1579c.2.2.2
                                    linarith only [hlam, p1579_0]
                                  · have p1579_0 := h1579c.1
                                    have p1579_1 := h1579c.2.1
                                    have p1579_2 := h1579c.2.2.1
                                    have p1579_3 := h1579c.2.2.2
                                    linarith only [h0, h1503, h1566, hc01, hc12, hlam, hphi, p1579_1]
                                  · have p1579_0 := h1579c.1
                                    have p1579_1 := h1579c.2.1
                                    have p1579_2 := h1579c.2.2.1
                                    have p1579_3 := h1579c.2.2.2
                                    linarith only [h0, h1502, h1503, h1566, h1571, hlam, p1579_2]
                                  · have p1579_0 := h1579c.1
                                    have p1579_1 := h1579c.2.1
                                    have p1579_2 := h1579c.2.2.1
                                    have p1579_3 := h1579c.2.2.2
                                    linarith only [h0, h1502, h1503, h1566, hlam, p1579_2]
                                  · have p1579_0 := h1579c.1
                                    have p1579_1 := h1579c.2.1
                                    have p1579_2 := h1579c.2.2.1
                                    have p1579_3 := h1579c.2.2.2
                                    rcases p1579_3 (m.d 0 1) (by simp) with h1596 | h1596
                                    · linarith only [h1596, hlam, p1579_0]
                                    · rcases p1579_3 (m.d 1 2) (by simp) with h1598 | h1598
                                      · rcases p1579_3 (m.d 1 3) (by simp) with h1599 | h1599
                                        · rcases p1579_3 (m.d 1 4) (by simp) with h1600 | h1600
                                          · linarith only [h1569, h1600, hlam]
                                          · rcases p1579_3 (m.d 1 5) (by simp) with h1602 | h1602
                                            · linarith only [h1570, h1602, hlam]
                                            · rcases h3bigk with h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c
                                              · have p1604_0 := h1604c.1
                                                have p1604_1 := h1604c.2.1
                                                have p1604_2 := h1604c.2.2.1
                                                have p1604_3 := h1604c.2.2.2
                                                linarith only [hlam, p1604_0]
                                              · have p1604_0 := h1604c.1
                                                have p1604_1 := h1604c.2.1
                                                have p1604_2 := h1604c.2.2.1
                                                have p1604_3 := h1604c.2.2.2
                                                linarith only [h811, hlam, p1604_1]
                                              · have p1604_0 := h1604c.1
                                                have p1604_1 := h1604c.2.1
                                                have p1604_2 := h1604c.2.2.1
                                                have p1604_3 := h1604c.2.2.2
                                                linarith only [h1503, hlam, p1604_1]
                                              · have p1604_0 := h1604c.1
                                                have p1604_1 := h1604c.2.1
                                                have p1604_2 := h1604c.2.2.1
                                                have p1604_3 := h1604c.2.2.2
                                                linarith only [hc34, hlam, hphi, ht0b, ht45, ht5b, p1604_1, u0elo2]
                                              · have p1604_0 := h1604c.1
                                                have p1604_1 := h1604c.2.1
                                                have p1604_2 := h1604c.2.2.1
                                                have p1604_3 := h1604c.2.2.2
                                                linarith only [h1577, hc34, hlam, hphi, ht0b, ht45, ht5b, p1604_1, u0elo2]
                                              · have p1604_0 := h1604c.1
                                                have p1604_1 := h1604c.2.1
                                                have p1604_2 := h1604c.2.2.1
                                                have p1604_3 := h1604c.2.2.2
                                                rcases p1604_3 (m.d 0 3) (by simp) with h1610 | h1610
                                                · linarith only [h1610, h811, hlam]
                                                · rcases p1604_3 (m.d 1 3) (by simp) with h1612 | h1612
                                                  · rcases p1604_3 (m.d 2 3) (by simp) with h1613 | h1613
                                                    · linarith only [h1566, h1613, hlam]
                                                    · linarith only [h1503, h1613, hlam]
                                                  · linarith only [h1612, h811, hlam]
                                              · have p1604_0 := h1604c.1
                                                have p1604_1 := h1604c.2.1
                                                have p1604_2 := h1604c.2.2.1
                                                have p1604_3 := h1604c.2.2.2
                                                linarith only [hlam, p1604_0]
                                              · have p1604_0 := h1604c.1
                                                have p1604_1 := h1604c.2.1
                                                have p1604_2 := h1604c.2.2.1
                                                have p1604_3 := h1604c.2.2.2
                                                linarith only [h0, h1502, h1503, h1566, h1567, h1571, h1573, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1604_1]
                                              · have p1604_0 := h1604c.1
                                                have p1604_1 := h1604c.2.1
                                                have p1604_2 := h1604c.2.2.1
                                                have p1604_3 := h1604c.2.2.2
                                                linarith only [h1502, h1567, h1571, h1573, hlam, p1579_1, p1604_2]
                                              · have p1604_0 := h1604c.1
                                                have p1604_1 := h1604c.2.1
                                                have p1604_2 := h1604c.2.2.1
                                                have p1604_3 := h1604c.2.2.2
                                                linarith only [h1502, h1570, hlam, p1579_1, p1604_2]
                                              · have p1604_0 := h1604c.1
                                                have p1604_1 := h1604c.2.1
                                                have p1604_2 := h1604c.2.2.1
                                                have p1604_3 := h1604c.2.2.2
                                                linarith only [h0, h1502, h1503, h1566, h1567, h1571, h1573, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1604_1]
                                              · have p1604_0 := h1604c.1
                                                have p1604_1 := h1604c.2.1
                                                have p1604_2 := h1604c.2.2.1
                                                have p1604_3 := h1604c.2.2.2
                                                linarith only [h1566, hlam, p1604_0]
                                              · have p1604_0 := h1604c.1
                                                have p1604_1 := h1604c.2.1
                                                have p1604_2 := h1604c.2.2.1
                                                have p1604_3 := h1604c.2.2.2
                                                linarith only [hlam, p1604_0]
                                              · have p1604_0 := h1604c.1
                                                have p1604_1 := h1604c.2.1
                                                have p1604_2 := h1604c.2.2.1
                                                have p1604_3 := h1604c.2.2.2
                                                rcases p1604_3 (m.d 0 3) (by simp) with h1624 | h1624
                                                · linarith only [h1503, h1624, hlam]
                                                · linarith only [h1540, h1624, hlam]
                                              · have p1604_0 := h1604c.1
                                                have p1604_1 := h1604c.2.1
                                                have p1604_2 := h1604c.2.2.1
                                                have p1604_3 := h1604c.2.2.2
                                                rcases p1604_3 (m.d 0 3) (by simp) with h1627 | h1627
                                                · linarith only [h1503, h1627, hlam]
                                                · linarith only [h1541, h1627, hlam]
                                              · have p1604_0 := h1604c.1
                                                have p1604_1 := h1604c.2.1
                                                have p1604_2 := h1604c.2.2.1
                                                have p1604_3 := h1604c.2.2.2
                                                linarith only [h1540, hlam, p1604_0]
                                              · have p1604_0 := h1604c.1
                                                have p1604_1 := h1604c.2.1
                                                have p1604_2 := h1604c.2.2.1
                                                have p1604_3 := h1604c.2.2.2
                                                linarith only [h1569, hlam, p1604_0]
                                              · have p1604_0 := h1604c.1
                                                have p1604_1 := h1604c.2.1
                                                have p1604_2 := h1604c.2.2.1
                                                have p1604_3 := h1604c.2.2.2
                                                linarith only [h1573, hlam, p1604_0]
                                              · have p1604_0 := h1604c.1
                                                have p1604_1 := h1604c.2.1
                                                have p1604_2 := h1604c.2.2.1
                                                have p1604_3 := h1604c.2.2.2
                                                linarith only [hlam, p1604_0]
                                              · have p1604_0 := h1604c.1
                                                have p1604_1 := h1604c.2.1
                                                have p1604_2 := h1604c.2.2.1
                                                have p1604_3 := h1604c.2.2.2
                                                linarith only [h1577, hlam, p1604_1]
                                              · have p1604_0 := h1604c.1
                                                have p1604_1 := h1604c.2.1
                                                have p1604_2 := h1604c.2.2.1
                                                have p1604_3 := h1604c.2.2.2
                                                linarith only [h1541, hlam, p1604_0]
                                              · have p1604_0 := h1604c.1
                                                have p1604_1 := h1604c.2.1
                                                have p1604_2 := h1604c.2.2.1
                                                have p1604_3 := h1604c.2.2.2
                                                linarith only [h1570, hlam, p1604_0]
                                              · have p1604_0 := h1604c.1
                                                have p1604_1 := h1604c.2.1
                                                have p1604_2 := h1604c.2.2.1
                                                have p1604_3 := h1604c.2.2.2
                                                linarith only [h1574, hlam, p1604_0]
                                              · have p1604_0 := h1604c.1
                                                have p1604_1 := h1604c.2.1
                                                have p1604_2 := h1604c.2.2.1
                                                have p1604_3 := h1604c.2.2.2
                                                linarith only [h1502, h1568, h1574, hc34, hlam, hphi, ht0b, ht45, ht5b, p1604_1, u0elo0]
                                              · have p1604_0 := h1604c.1
                                                have p1604_1 := h1604c.2.1
                                                have p1604_2 := h1604c.2.2.1
                                                have p1604_3 := h1604c.2.2.2
                                                linarith only [hlam, p1604_0]
                                        · linarith only [h1599, hlam, p1579_0]
                                      · linarith only [h0, h1598, hlam]
                                  · have p1579_0 := h1579c.1
                                    have p1579_1 := h1579c.2.1
                                    have p1579_2 := h1579c.2.2.1
                                    have p1579_3 := h1579c.2.2.2
                                    linarith only [h1566, hlam, p1579_1]
                                  · have p1579_0 := h1579c.1
                                    have p1579_1 := h1579c.2.1
                                    have p1579_2 := h1579c.2.2.1
                                    have p1579_3 := h1579c.2.2.2
                                    linarith only [hlam, p1579_0]
                                  · have p1579_0 := h1579c.1
                                    have p1579_1 := h1579c.2.1
                                    have p1579_2 := h1579c.2.2.1
                                    have p1579_3 := h1579c.2.2.2
                                    rcases p1579_3 (m.d 0 1) (by simp) with h1644 | h1644
                                    · linarith only [h1644, h811, hlam]
                                    · linarith only [h1501, h1644, hlam]
                                  · have p1579_0 := h1579c.1
                                    have p1579_1 := h1579c.2.1
                                    have p1579_2 := h1579c.2.2.1
                                    have p1579_3 := h1579c.2.2.2
                                    rcases p1579_3 (m.d 0 1) (by simp) with h1647 | h1647
                                    · linarith only [h1647, h811, hlam]
                                    · linarith only [h1502, h1647, hlam]
                                  · have p1579_0 := h1579c.1
                                    have p1579_1 := h1579c.2.1
                                    have p1579_2 := h1579c.2.2.1
                                    have p1579_3 := h1579c.2.2.2
                                    linarith only [h1501, hlam, p1579_0]
                                  · have p1579_0 := h1579c.1
                                    have p1579_1 := h1579c.2.1
                                    have p1579_2 := h1579c.2.2.1
                                    have p1579_3 := h1579c.2.2.2
                                    linarith only [h1567, hlam, p1579_1]
                                  · have p1579_0 := h1579c.1
                                    have p1579_1 := h1579c.2.1
                                    have p1579_2 := h1579c.2.2.1
                                    have p1579_3 := h1579c.2.2.2
                                    linarith only [h1569, hlam, p1579_0]
                                  · have p1579_0 := h1579c.1
                                    have p1579_1 := h1579c.2.1
                                    have p1579_2 := h1579c.2.2.1
                                    have p1579_3 := h1579c.2.2.2
                                    linarith only [hlam, p1579_0]
                                  · have p1579_0 := h1579c.1
                                    have p1579_1 := h1579c.2.1
                                    have p1579_2 := h1579c.2.2.1
                                    have p1579_3 := h1579c.2.2.2
                                    linarith only [h1571, hlam, p1579_1]
                                  · have p1579_0 := h1579c.1
                                    have p1579_1 := h1579c.2.1
                                    have p1579_2 := h1579c.2.2.1
                                    have p1579_3 := h1579c.2.2.2
                                    linarith only [h1502, hlam, p1579_0]
                                  · have p1579_0 := h1579c.1
                                    have p1579_1 := h1579c.2.1
                                    have p1579_2 := h1579c.2.2.1
                                    have p1579_3 := h1579c.2.2.2
                                    linarith only [h1568, hlam, p1579_1]
                                  · have p1579_0 := h1579c.1
                                    have p1579_1 := h1579c.2.1
                                    have p1579_2 := h1579c.2.2.1
                                    have p1579_3 := h1579c.2.2.2
                                    linarith only [h1570, hlam, p1579_0]
                                  · have p1579_0 := h1579c.1
                                    have p1579_1 := h1579c.2.1
                                    have p1579_2 := h1579c.2.2.1
                                    have p1579_3 := h1579c.2.2.2
                                    linarith only [h0, h1502, h1503, h1567, h1573, hc34, hlam, hphi, ht0b, ht45, ht5b, p1579_1, u0elo2]
                                  · have p1579_0 := h1579c.1
                                    have p1579_1 := h1579c.2.1
                                    have p1579_2 := h1579c.2.2.1
                                    have p1579_3 := h1579c.2.2.2
                                    linarith only [hlam, p1579_0]
                            · linarith only [h0, h1503, h1541, h1574, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h0, h1503, h1540, h1573, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h1501, h1541, h1567, h1570, h811, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · linarith only [h0, h1503, h1540, h1566, h1569, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h0, h1501, h1503, h1566, h1567, h1568, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h1501, h1503, h1566, h1567, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1666 | h1666
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1667 | h1667
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1668 | h1668
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1669 | h1669
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1670 | h1670
                        · linarith only [h0, h1501, h1542, h1566, h1670, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1672 | h1672
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1673 | h1673
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1674 | h1674
                              · linarith only [h1501, h1542, h1666, h1674, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1676 | h1676
                                · linarith only [h1501, h1542, h1666, h1672, h1676, hlam]
                                · rcases h1bigk with h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c
                                  · have p1678_0 := h1678c.1
                                    have p1678_1 := h1678c.2.1
                                    have p1678_2 := h1678c.2.2.1
                                    have p1678_3 := h1678c.2.2.2
                                    linarith only [hlam, p1678_0]
                                  · have p1678_0 := h1678c.1
                                    have p1678_1 := h1678c.2.1
                                    have p1678_2 := h1678c.2.2.1
                                    have p1678_3 := h1678c.2.2.2
                                    linarith only [h0, hlam, p1678_0]
                                  · have p1678_0 := h1678c.1
                                    have p1678_1 := h1678c.2.1
                                    have p1678_2 := h1678c.2.2.1
                                    have p1678_3 := h1678c.2.2.2
                                    linarith only [h811, hlam, p1678_0]
                                  · have p1678_0 := h1678c.1
                                    have p1678_1 := h1678c.2.1
                                    have p1678_2 := h1678c.2.2.1
                                    have p1678_3 := h1678c.2.2.2
                                    linarith only [h0, h1566, h1666, h1672, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1678_1]
                                  · have p1678_0 := h1678c.1
                                    have p1678_1 := h1678c.2.1
                                    have p1678_2 := h1678c.2.2.1
                                    have p1678_3 := h1678c.2.2.2
                                    linarith only [h0, h1566, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1678_1]
                                  · have p1678_0 := h1678c.1
                                    have p1678_1 := h1678c.2.1
                                    have p1678_2 := h1678c.2.2.1
                                    have p1678_3 := h1678c.2.2.2
                                    linarith only [h1566, hc01, hc23, hlam, hphi, ht12, p1678_1]
                                  · have p1678_0 := h1678c.1
                                    have p1678_1 := h1678c.2.1
                                    have p1678_2 := h1678c.2.2.1
                                    have p1678_3 := h1678c.2.2.2
                                    linarith only [hlam, p1678_0]
                                  · have p1678_0 := h1678c.1
                                    have p1678_1 := h1678c.2.1
                                    have p1678_2 := h1678c.2.2.1
                                    have p1678_3 := h1678c.2.2.2
                                    linarith only [h1566, hlam, p1678_0]
                                  · have p1678_0 := h1678c.1
                                    have p1678_1 := h1678c.2.1
                                    have p1678_2 := h1678c.2.2.1
                                    have p1678_3 := h1678c.2.2.2
                                    rcases p1678_3 (m.d 0 1) (by simp) with h1687 | h1687
                                    · linarith only [h0, h1687, hlam]
                                    · linarith only [h1501, h1687, hlam]
                                  · have p1678_0 := h1678c.1
                                    have p1678_1 := h1678c.2.1
                                    have p1678_2 := h1678c.2.2.1
                                    have p1678_3 := h1678c.2.2.2
                                    rcases p1678_3 (m.d 0 1) (by simp) with h1690 | h1690
                                    · linarith only [h0, h1690, hlam]
                                    · linarith only [h1502, h1690, hlam]
                                  · have p1678_0 := h1678c.1
                                    have p1678_1 := h1678c.2.1
                                    have p1678_2 := h1678c.2.2.1
                                    have p1678_3 := h1678c.2.2.2
                                    rcases p1678_3 (m.d 0 1) (by simp) with h1693 | h1693
                                    · linarith only [h1693, hlam, p1678_0]
                                    · rcases p1678_3 (m.d 1 2) (by simp) with h1695 | h1695
                                      · linarith only [h1566, h1695, hlam]
                                      · linarith only [h0, h1695, hlam]
                                  · have p1678_0 := h1678c.1
                                    have p1678_1 := h1678c.2.1
                                    have p1678_2 := h1678c.2.2.1
                                    have p1678_3 := h1678c.2.2.2
                                    linarith only [h0, h1502, h1666, h1670, h1672, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1678_1]
                                  · have p1678_0 := h1678c.1
                                    have p1678_1 := h1678c.2.1
                                    have p1678_2 := h1678c.2.2.1
                                    have p1678_3 := h1678c.2.2.2
                                    linarith only [hlam, p1678_0]
                                  · have p1678_0 := h1678c.1
                                    have p1678_1 := h1678c.2.1
                                    have p1678_2 := h1678c.2.2.1
                                    have p1678_3 := h1678c.2.2.2
                                    rcases p1678_3 (m.d 0 1) (by simp) with h1700 | h1700
                                    · linarith only [h1700, h811, hlam]
                                    · linarith only [h1501, h1700, hlam]
                                  · have p1678_0 := h1678c.1
                                    have p1678_1 := h1678c.2.1
                                    have p1678_2 := h1678c.2.2.1
                                    have p1678_3 := h1678c.2.2.2
                                    rcases p1678_3 (m.d 0 1) (by simp) with h1703 | h1703
                                    · linarith only [h1703, h811, hlam]
                                    · linarith only [h1502, h1703, hlam]
                                  · have p1678_0 := h1678c.1
                                    have p1678_1 := h1678c.2.1
                                    have p1678_2 := h1678c.2.2.1
                                    have p1678_3 := h1678c.2.2.2
                                    linarith only [h1501, hlam, p1678_0]
                                  · have p1678_0 := h1678c.1
                                    have p1678_1 := h1678c.2.1
                                    have p1678_2 := h1678c.2.2.1
                                    have p1678_3 := h1678c.2.2.2
                                    linarith only [h1666, hlam, p1678_1]
                                  · have p1678_0 := h1678c.1
                                    have p1678_1 := h1678c.2.1
                                    have p1678_2 := h1678c.2.2.1
                                    have p1678_3 := h1678c.2.2.2
                                    linarith only [h1668, hlam, p1678_0]
                                  · have p1678_0 := h1678c.1
                                    have p1678_1 := h1678c.2.1
                                    have p1678_2 := h1678c.2.2.1
                                    have p1678_3 := h1678c.2.2.2
                                    linarith only [hlam, p1678_0]
                                  · have p1678_0 := h1678c.1
                                    have p1678_1 := h1678c.2.1
                                    have p1678_2 := h1678c.2.2.1
                                    have p1678_3 := h1678c.2.2.2
                                    linarith only [h1670, hlam, p1678_1]
                                  · have p1678_0 := h1678c.1
                                    have p1678_1 := h1678c.2.1
                                    have p1678_2 := h1678c.2.2.1
                                    have p1678_3 := h1678c.2.2.2
                                    linarith only [h1502, hlam, p1678_0]
                                  · have p1678_0 := h1678c.1
                                    have p1678_1 := h1678c.2.1
                                    have p1678_2 := h1678c.2.2.1
                                    have p1678_3 := h1678c.2.2.2
                                    linarith only [h1667, hlam, p1678_1]
                                  · have p1678_0 := h1678c.1
                                    have p1678_1 := h1678c.2.1
                                    have p1678_2 := h1678c.2.2.1
                                    have p1678_3 := h1678c.2.2.2
                                    linarith only [h1669, hlam, p1678_0]
                                  · have p1678_0 := h1678c.1
                                    have p1678_1 := h1678c.2.1
                                    have p1678_2 := h1678c.2.2.1
                                    have p1678_3 := h1678c.2.2.2
                                    linarith only [h1502, h1666, h1672, hc34, hlam, hphi, ht0b, ht45, ht5b, p1678_1, u0elo0]
                                  · have p1678_0 := h1678c.1
                                    have p1678_1 := h1678c.2.1
                                    have p1678_2 := h1678c.2.2.1
                                    have p1678_3 := h1678c.2.2.2
                                    linarith only [hlam, p1678_0]
                            · linarith only [h0, h1503, h1541, h1673, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h0, h1566, h1672, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h1541, h1669, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h0, h1501, h1540, h1566, h1666, h1668, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · linarith only [h0, h1502, h1667, hlam]
                · linarith only [h0, h1501, h1503, h1539, h1666, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
          · linarith only [h0, h1502, h1503, h1541, hlam]
        · linarith only [h0, h1501, h1503, h1540, hlam]
      · linarith only [h0, h1501, h1539, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1725 | h1725
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1726 | h1726
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1727 | h1727
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1728 | h1728
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1729 | h1729
            · linarith only [h1501, h1502, h1729, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1731 | h1731
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1732 | h1732
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1733 | h1733
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1734 | h1734
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1735 | h1735
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1736 | h1736
                        · linarith only [h1501, h1729, h1736, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1738 | h1738
                          · linarith only [h1725, h1738, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · linarith only [h1725, h1727, h1738, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h1725, h1728, h1735, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h1725, h1727, h1734, h811, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1743 | h1743
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1744 | h1744
                      · linarith only [h1731, h1733, h1744, hlam]
                      · linarith only [h1725, h1728, h1744, h811, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h1501, h1725, h1727, h1732, h1743, h811, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · linarith only [h1726, h1731, h1732, h811, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h1501, h1725, h1731, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1750 | h1750
            · linarith only [h1501, h1728, h1750, h811, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1752 | h1752
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1753 | h1753
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1754 | h1754
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1755 | h1755
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1756 | h1756
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1757 | h1757
                        · linarith only [h1501, h1728, h1750, h1752, h1756, h1757, h811, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1759 | h1759
                          · linarith only [h1725, h1759, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · linarith only [h1727, h1728, h1752, h1756, h1759, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1762 | h1762
                        · linarith only [h1501, h1762, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1764 | h1764
                          · linarith only [h1725, h1764, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · linarith only [h1727, h1764, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h1501, h1727, h1753, h1755, h811, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1768 | h1768
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1769 | h1769
                      · linarith only [h1501, h1728, h1752, h1753, h1754, h1769, h811, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1771 | h1771
                        · linarith only [h1501, h1750, h1771, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1773 | h1773
                          · linarith only [h1725, h1773, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · linarith only [h1725, h1727, h1773, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h1501, h1727, h1753, h1768, h811, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                · linarith only [h1726, h1753, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h1725, h1752, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
        · linarith only [h1501, h1727, h811, hlam]
      · linarith only [h0, h1501, h1726, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1781 | h1781
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1782 | h1782
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1783 | h1783
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1784 | h1784
            · linarith only [h1501, h1502, h1784, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1786 | h1786
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1787 | h1787
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1788 | h1788
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1789 | h1789
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1790 | h1790
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1791 | h1791
                        · linarith only [h0, h1501, h1725, h1784, h1786, h1791, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1793 | h1793
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1794 | h1794
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1795 | h1795
                              · linarith only [h0, h1501, h1725, h1786, h1787, h1791, h1795, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1797 | h1797
                                · linarith only [h1501, h1502, h1787, h1791, h1793, h1797, hlam]
                                · rcases h1bigk with h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c
                                  · have p1799_0 := h1799c.1
                                    have p1799_1 := h1799c.2.1
                                    have p1799_2 := h1799c.2.2.1
                                    have p1799_3 := h1799c.2.2.2
                                    linarith only [hlam, p1799_0]
                                  · have p1799_0 := h1799c.1
                                    have p1799_1 := h1799c.2.1
                                    have p1799_2 := h1799c.2.2.1
                                    have p1799_3 := h1799c.2.2.2
                                    linarith only [h0, hlam, p1799_0]
                                  · have p1799_0 := h1799c.1
                                    have p1799_1 := h1799c.2.1
                                    have p1799_2 := h1799c.2.2.1
                                    have p1799_3 := h1799c.2.2.2
                                    linarith only [h811, hlam, p1799_0]
                                  · have p1799_0 := h1799c.1
                                    have p1799_1 := h1799c.2.1
                                    have p1799_2 := h1799c.2.2.1
                                    have p1799_3 := h1799c.2.2.2
                                    linarith only [h0, h1725, h1786, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1799_1]
                                  · have p1799_0 := h1799c.1
                                    have p1799_1 := h1799c.2.1
                                    have p1799_2 := h1799c.2.2.1
                                    have p1799_3 := h1799c.2.2.2
                                    linarith only [h1502, hlam, p1799_0]
                                  · have p1799_0 := h1799c.1
                                    have p1799_1 := h1799c.2.1
                                    have p1799_2 := h1799c.2.2.1
                                    have p1799_3 := h1799c.2.2.2
                                    rcases p1799_3 (m.d 0 1) (by simp) with h1805 | h1805
                                    · linarith only [h1805, hlam, p1799_0]
                                    · rcases p1799_3 (m.d 1 2) (by simp) with h1807 | h1807
                                      · rcases p1799_3 (m.d 1 3) (by simp) with h1808 | h1808
                                        · linarith only [h1786, h1808, hlam]
                                        · linarith only [h1808, h811, hlam]
                                      · linarith only [h1807, hlam, p1799_0]
                                  · have p1799_0 := h1799c.1
                                    have p1799_1 := h1799c.2.1
                                    have p1799_2 := h1799c.2.2.1
                                    have p1799_3 := h1799c.2.2.2
                                    linarith only [hlam, p1799_0]
                                  · have p1799_0 := h1799c.1
                                    have p1799_1 := h1799c.2.1
                                    have p1799_2 := h1799c.2.2.1
                                    have p1799_3 := h1799c.2.2.2
                                    linarith only [h0, h1725, h1786, hc01, hc12, hlam, hphi, p1799_1]
                                  · have p1799_0 := h1799c.1
                                    have p1799_1 := h1799c.2.1
                                    have p1799_2 := h1799c.2.2.1
                                    have p1799_3 := h1799c.2.2.2
                                    linarith only [h0, h1501, h1725, h1786, hlam, p1799_2]
                                  · have p1799_0 := h1799c.1
                                    have p1799_1 := h1799c.2.1
                                    have p1799_2 := h1799c.2.2.1
                                    have p1799_3 := h1799c.2.2.2
                                    linarith only [h1501, h1502, h1787, h1793, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1799_1]
                                  · have p1799_0 := h1799c.1
                                    have p1799_1 := h1799c.2.1
                                    have p1799_2 := h1799c.2.2.1
                                    have p1799_3 := h1799c.2.2.2
                                    rcases p1799_3 (m.d 0 1) (by simp) with h1816 | h1816
                                    · linarith only [h1816, hlam, p1799_0]
                                    · rcases p1799_3 (m.d 1 2) (by simp) with h1818 | h1818
                                      · rcases p1799_3 (m.d 1 3) (by simp) with h1819 | h1819
                                        · rcases p1799_3 (m.d 1 4) (by simp) with h1820 | h1820
                                          · linarith only [h1789, h1820, hlam]
                                          · rcases p1799_3 (m.d 1 5) (by simp) with h1822 | h1822
                                            · linarith only [h1790, h1822, hlam]
                                            · linarith only [h1502, h1822, hlam]
                                        · linarith only [h1819, hlam, p1799_0]
                                      · linarith only [h0, h1818, hlam]
                                  · have p1799_0 := h1799c.1
                                    have p1799_1 := h1799c.2.1
                                    have p1799_2 := h1799c.2.2.1
                                    have p1799_3 := h1799c.2.2.2
                                    linarith only [h1786, hlam, p1799_1]
                                  · have p1799_0 := h1799c.1
                                    have p1799_1 := h1799c.2.1
                                    have p1799_2 := h1799c.2.2.1
                                    have p1799_3 := h1799c.2.2.2
                                    linarith only [hlam, p1799_0]
                                  · have p1799_0 := h1799c.1
                                    have p1799_1 := h1799c.2.1
                                    have p1799_2 := h1799c.2.2.1
                                    have p1799_3 := h1799c.2.2.2
                                    rcases p1799_3 (m.d 0 1) (by simp) with h1829 | h1829
                                    · linarith only [h1829, h811, hlam]
                                    · linarith only [h1501, h1829, hlam]
                                  · have p1799_0 := h1799c.1
                                    have p1799_1 := h1799c.2.1
                                    have p1799_2 := h1799c.2.2.1
                                    have p1799_3 := h1799c.2.2.2
                                    linarith only [h1501, h1502, h1787, h1793, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1799_1]
                                  · have p1799_0 := h1799c.1
                                    have p1799_1 := h1799c.2.1
                                    have p1799_2 := h1799c.2.2.1
                                    have p1799_3 := h1799c.2.2.2
                                    linarith only [h1501, hlam, p1799_0]
                                  · have p1799_0 := h1799c.1
                                    have p1799_1 := h1799c.2.1
                                    have p1799_2 := h1799c.2.2.1
                                    have p1799_3 := h1799c.2.2.2
                                    linarith only [h1787, hlam, p1799_1]
                                  · have p1799_0 := h1799c.1
                                    have p1799_1 := h1799c.2.1
                                    have p1799_2 := h1799c.2.2.1
                                    have p1799_3 := h1799c.2.2.2
                                    linarith only [h1789, hlam, p1799_0]
                                  · have p1799_0 := h1799c.1
                                    have p1799_1 := h1799c.2.1
                                    have p1799_2 := h1799c.2.2.1
                                    have p1799_3 := h1799c.2.2.2
                                    linarith only [hlam, p1799_0]
                                  · have p1799_0 := h1799c.1
                                    have p1799_1 := h1799c.2.1
                                    have p1799_2 := h1799c.2.2.1
                                    have p1799_3 := h1799c.2.2.2
                                    linarith only [h1791, hlam, p1799_1]
                                  · have p1799_0 := h1799c.1
                                    have p1799_1 := h1799c.2.1
                                    have p1799_2 := h1799c.2.2.1
                                    have p1799_3 := h1799c.2.2.2
                                    linarith only [h1501, h1787, h1791, h1793, hc34, hc45, hlam, hphi, p1799_1]
                                  · have p1799_0 := h1799c.1
                                    have p1799_1 := h1799c.2.1
                                    have p1799_2 := h1799c.2.2.1
                                    have p1799_3 := h1799c.2.2.2
                                    linarith only [h1788, hlam, p1799_1]
                                  · have p1799_0 := h1799c.1
                                    have p1799_1 := h1799c.2.1
                                    have p1799_2 := h1799c.2.2.1
                                    have p1799_3 := h1799c.2.2.2
                                    linarith only [h1790, hlam, p1799_0]
                                  · have p1799_0 := h1799c.1
                                    have p1799_1 := h1799c.2.1
                                    have p1799_2 := h1799c.2.2.1
                                    have p1799_3 := h1799c.2.2.2
                                    rcases p1799_3 (m.d 0 1) (by simp) with h1841 | h1841
                                    · linarith only [h1502, h1841, hlam]
                                    · linarith only [h1501, h1841, hlam]
                                  · have p1799_0 := h1799c.1
                                    have p1799_1 := h1799c.2.1
                                    have p1799_2 := h1799c.2.2.1
                                    have p1799_3 := h1799c.2.2.2
                                    linarith only [hlam, p1799_0]
                            · linarith only [h0, h1501, h1725, h1783, h1787, h1793, h1794, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                          · linarith only [h0, h1501, h1725, h1782, h1787, h1793, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h1783, h1790, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h0, h1501, h1725, h1782, h1786, h1787, h1789, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · linarith only [h0, h1501, h1725, h1786, h1787, h1788, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h1725, h1786, h1787, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1851 | h1851
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1852 | h1852
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1853 | h1853
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1854 | h1854
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1855 | h1855
                        · linarith only [h1501, h1855, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1857 | h1857
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1858 | h1858
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1859 | h1859
                              · linarith only [h1502, h1725, h1781, h1855, h1859, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1861 | h1861
                                · linarith only [h1501, h1502, h1851, h1855, h1857, h1861, hlam]
                                · rcases h1bigk with h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c | h1863c
                                  · have p1863_0 := h1863c.1
                                    have p1863_1 := h1863c.2.1
                                    have p1863_2 := h1863c.2.2.1
                                    have p1863_3 := h1863c.2.2.2
                                    linarith only [hlam, p1863_0]
                                  · have p1863_0 := h1863c.1
                                    have p1863_1 := h1863c.2.1
                                    have p1863_2 := h1863c.2.2.1
                                    have p1863_3 := h1863c.2.2.2
                                    linarith only [h0, hlam, p1863_0]
                                  · have p1863_0 := h1863c.1
                                    have p1863_1 := h1863c.2.1
                                    have p1863_2 := h1863c.2.2.1
                                    have p1863_3 := h1863c.2.2.2
                                    linarith only [h811, hlam, p1863_0]
                                  · have p1863_0 := h1863c.1
                                    have p1863_1 := h1863c.2.1
                                    have p1863_2 := h1863c.2.2.1
                                    have p1863_3 := h1863c.2.2.2
                                    linarith only [h1502, h1786, h1851, h1852, h1857, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1863_1]
                                  · have p1863_0 := h1863c.1
                                    have p1863_1 := h1863c.2.1
                                    have p1863_2 := h1863c.2.2.1
                                    have p1863_3 := h1863c.2.2.2
                                    linarith only [h1502, hlam, p1863_0]
                                  · have p1863_0 := h1863c.1
                                    have p1863_1 := h1863c.2.1
                                    have p1863_2 := h1863c.2.2.1
                                    have p1863_3 := h1863c.2.2.2
                                    linarith only [h1786, hc01, hc23, hlam, hphi, ht12, p1863_1]
                                  · have p1863_0 := h1863c.1
                                    have p1863_1 := h1863c.2.1
                                    have p1863_2 := h1863c.2.2.1
                                    have p1863_3 := h1863c.2.2.2
                                    linarith only [hlam, p1863_0]
                                  · have p1863_0 := h1863c.1
                                    have p1863_1 := h1863c.2.1
                                    have p1863_2 := h1863c.2.2.1
                                    have p1863_3 := h1863c.2.2.2
                                    linarith only [h1786, hlam, p1863_0]
                                  · have p1863_0 := h1863c.1
                                    have p1863_1 := h1863c.2.1
                                    have p1863_2 := h1863c.2.2.1
                                    have p1863_3 := h1863c.2.2.2
                                    rcases p1863_3 (m.d 0 1) (by simp) with h1872 | h1872
                                    · linarith only [h0, h1872, hlam]
                                    · linarith only [h1501, h1872, hlam]
                                  · have p1863_0 := h1863c.1
                                    have p1863_1 := h1863c.2.1
                                    have p1863_2 := h1863c.2.2.1
                                    have p1863_3 := h1863c.2.2.2
                                    linarith only [h1501, h1502, h1786, h1851, h1857, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1863_1]
                                  · have p1863_0 := h1863c.1
                                    have p1863_1 := h1863c.2.1
                                    have p1863_2 := h1863c.2.2.1
                                    have p1863_3 := h1863c.2.2.2
                                    rcases p1863_3 (m.d 0 1) (by simp) with h1876 | h1876
                                    · linarith only [h1876, hlam, p1863_0]
                                    · rcases p1863_3 (m.d 1 2) (by simp) with h1878 | h1878
                                      · linarith only [h1786, h1878, hlam]
                                      · linarith only [h0, h1878, hlam]
                                  · have p1863_0 := h1863c.1
                                    have p1863_1 := h1863c.2.1
                                    have p1863_2 := h1863c.2.2.1
                                    have p1863_3 := h1863c.2.2.2
                                    linarith only [h0, h1501, h1851, h1857, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1863_1]
                                  · have p1863_0 := h1863c.1
                                    have p1863_1 := h1863c.2.1
                                    have p1863_2 := h1863c.2.2.1
                                    have p1863_3 := h1863c.2.2.2
                                    linarith only [hlam, p1863_0]
                                  · have p1863_0 := h1863c.1
                                    have p1863_1 := h1863c.2.1
                                    have p1863_2 := h1863c.2.2.1
                                    have p1863_3 := h1863c.2.2.2
                                    rcases p1863_3 (m.d 0 1) (by simp) with h1883 | h1883
                                    · linarith only [h1883, h811, hlam]
                                    · linarith only [h1501, h1883, hlam]
                                  · have p1863_0 := h1863c.1
                                    have p1863_1 := h1863c.2.1
                                    have p1863_2 := h1863c.2.2.1
                                    have p1863_3 := h1863c.2.2.2
                                    linarith only [h1501, h1502, h1851, h1857, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1863_1]
                                  · have p1863_0 := h1863c.1
                                    have p1863_1 := h1863c.2.1
                                    have p1863_2 := h1863c.2.2.1
                                    have p1863_3 := h1863c.2.2.2
                                    linarith only [h1501, hlam, p1863_0]
                                  · have p1863_0 := h1863c.1
                                    have p1863_1 := h1863c.2.1
                                    have p1863_2 := h1863c.2.2.1
                                    have p1863_3 := h1863c.2.2.2
                                    linarith only [h1851, hlam, p1863_1]
                                  · have p1863_0 := h1863c.1
                                    have p1863_1 := h1863c.2.1
                                    have p1863_2 := h1863c.2.2.1
                                    have p1863_3 := h1863c.2.2.2
                                    linarith only [h1853, hlam, p1863_0]
                                  · have p1863_0 := h1863c.1
                                    have p1863_1 := h1863c.2.1
                                    have p1863_2 := h1863c.2.2.1
                                    have p1863_3 := h1863c.2.2.2
                                    linarith only [hlam, p1863_0]
                                  · have p1863_0 := h1863c.1
                                    have p1863_1 := h1863c.2.1
                                    have p1863_2 := h1863c.2.2.1
                                    have p1863_3 := h1863c.2.2.2
                                    linarith only [h1855, hlam, p1863_1]
                                  · have p1863_0 := h1863c.1
                                    have p1863_1 := h1863c.2.1
                                    have p1863_2 := h1863c.2.2.1
                                    have p1863_3 := h1863c.2.2.2
                                    linarith only [h1501, h1851, h1855, h1857, hc34, hc45, hlam, hphi, p1863_1]
                                  · have p1863_0 := h1863c.1
                                    have p1863_1 := h1863c.2.1
                                    have p1863_2 := h1863c.2.2.1
                                    have p1863_3 := h1863c.2.2.2
                                    linarith only [h1852, hlam, p1863_1]
                                  · have p1863_0 := h1863c.1
                                    have p1863_1 := h1863c.2.1
                                    have p1863_2 := h1863c.2.2.1
                                    have p1863_3 := h1863c.2.2.2
                                    linarith only [h1854, hlam, p1863_0]
                                  · have p1863_0 := h1863c.1
                                    have p1863_1 := h1863c.2.1
                                    have p1863_2 := h1863c.2.2.1
                                    have p1863_3 := h1863c.2.2.2
                                    rcases p1863_3 (m.d 0 1) (by simp) with h1895 | h1895
                                    · linarith only [h1502, h1895, hlam]
                                    · linarith only [h1501, h1895, hlam]
                                  · have p1863_0 := h1863c.1
                                    have p1863_1 := h1863c.2.1
                                    have p1863_2 := h1863c.2.2.1
                                    have p1863_3 := h1863c.2.2.2
                                    linarith only [hlam, p1863_0]
                            · linarith only [h1783, h1786, h1858, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h1501, h1502, h1786, h1851, h1852, h1857, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h1783, h1854, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h1501, h1502, h1782, h1786, h1851, h1852, h1853, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1903 | h1903
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1904 | h1904
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1905 | h1905
                        · linarith only [h1501, h1905, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1907 | h1907
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1908 | h1908
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1909 | h1909
                              · linarith only [h0, h1725, h1781, h1852, h1905, h1909, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                              · linarith only [h0, h1501, h1851, h1852, h1907, h1909, hc34, hc45, hlam, hphi]
                            · linarith only [h1783, h1908, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h0, h1501, h1786, h1851, h1907, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h1783, h1904, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h0, h1501, h1782, h1786, h1851, h1903, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                · linarith only [h0, h1501, h1725, h1781, h1851, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1917 | h1917
            · linarith only [h0, h1501, h1725, h1783, h1917, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1919 | h1919
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1920 | h1920
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1921 | h1921
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1922 | h1922
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1923 | h1923
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1924 | h1924
                        · linarith only [h0, h1501, h1725, h1783, h1917, h1919, h1923, h1924, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1926 | h1926
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1927 | h1927
                            · linarith only [h0, h1725, h1783, h1919, h1927, hc01, hc12, hlam, hphi]
                            · linarith only [h0, h1501, h1725, h1920, h1923, h1924, h1926, h1927, hc34, hc45, hlam, hphi]
                          · linarith only [h0, h1501, h1725, h1782, h1920, h1926, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1931 | h1931
                        · linarith only [h1501, h1931, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1933 | h1933
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1934 | h1934
                            · linarith only [h1919, h1923, h1934, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1936 | h1936
                              · linarith only [h0, h1501, h1725, h1919, h1920, h1923, h1931, h1936, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1938 | h1938
                                · linarith only [h0, h1501, h1725, h1919, h1920, h1923, h1931, h1933, h1938, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                · linarith only [h0, h1501, h1725, h1919, h1923, h1938, hc14, hc45, hlam, hphi]
                          · linarith only [h0, h1501, h1725, h1782, h1920, h1933, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · linarith only [h0, h1501, h1725, h1782, h1919, h1920, h1922, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · linarith only [h0, h1501, h1725, h1919, h1920, h1921, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h1501, h1725, h1919, h1920, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1945 | h1945
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1946 | h1946
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1947 | h1947
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1948 | h1948
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1949 | h1949
                        · linarith only [h1501, h1949, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1951 | h1951
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1952 | h1952
                            · linarith only [h0, h1725, h1783, h1919, h1946, h1952, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h0, h1501, h1919, h1945, h1951, h1952, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1501, h1725, h1783, h1919, h1945, h1946, h1948, h1951, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h1919, h1946, h1948, hlam]
                    · linarith only [h1782, h1783, h1919, h1947, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1958 | h1958
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1959 | h1959
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1960 | h1960
                        · linarith only [h0, h1501, h1725, h1783, h1919, h1959, h1960, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1962 | h1962
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1963 | h1963
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1964 | h1964
                              · linarith only [h0, h1501, h1725, h1783, h1945, h1959, h1960, h1964, hlam]
                              · linarith only [h0, h1501, h1945, h1946, h1962, h1964, hc34, hc45, hlam, hphi]
                            · linarith only [h1919, h1959, h1963, hlam]
                          · linarith only [h0, h1501, h1725, h1783, h1919, h1945, h1959, h1962, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1969 | h1969
                        · linarith only [h0, h1501, h1919, h1959, h1969, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1971 | h1971
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1972 | h1972
                            · linarith only [h0, h1919, h1959, h1972, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h0, h1501, h1919, h1945, h1971, h1972, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1501, h1919, h1945, h1971, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h1501, h1782, h1919, h1945, h1958, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                · linarith only [h0, h1501, h1725, h1781, h1783, h1945, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
        · linarith only [h0, h1501, h1725, h1782, hlam]
      · linarith only [h0, h1501, h1781, hlam]

set_option maxHeartbeats 5224000 in
theorem r1l7_20_11_13_14_H_L_L_I_L_I_L_I_s1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg811 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1501 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1980 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h0elo := hb0.1
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h811 := hg811
  rcases m.htr 0 2 3 (by decide) (by decide) with h1981 | h1981
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1982 | h1982
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1983 | h1983
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1984 | h1984
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1985 | h1985
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1986 | h1986
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1987 | h1987
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1988 | h1988
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1989 | h1989
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1990 | h1990
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1991 | h1991
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1992 | h1992
                        · linarith only [h1981, h1992, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h1983, h1992, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h1501, h1985, h1991, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h1501, h1980, h1981, h1984, h1988, h1989, h1990, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                  · linarith only [h1981, h1983, h1989, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h1980, h1988, hlam]
              · linarith only [h1982, h1986, h1987, h811, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h1981, h1986, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
          · linarith only [h1501, h1980, h1985, hlam]
        · linarith only [h1980, h1984, h811, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2003 | h2003
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2004 | h2004
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2005 | h2005
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2006 | h2006
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2007 | h2007
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2008 | h2008
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2009 | h2009
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2010 | h2010
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2011 | h2011
                        · linarith only [h1981, h1983, h2011, h811, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2013 | h2013
                          · linarith only [h1982, h2011, h2013, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                          · linarith only [h2003, h2013, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h1501, h1980, h2004, h2007, h2010, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                    · linarith only [h1983, h2008, h2009, hc03, hc35, hlam, hphi]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2018 | h2018
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2019 | h2019
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2020 | h2020
                        · linarith only [h1980, h2007, h2008, h2020, h811, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2022 | h2022
                          · linarith only [h1982, h2020, h2022, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                          · linarith only [h2003, h2022, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h1980, h1982, h2004, h2007, h2008, h2019, h811, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                    · linarith only [h1980, h1982, h1983, h2003, h2007, h2018, h811, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                · linarith only [h0, h1980, h2007, hlam]
              · linarith only [h1982, h2005, h2006, h811, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h1980, h1981, h2005, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
          · linarith only [h1980, h1983, h2004, h811, hlam]
        · linarith only [h1980, h2003, h811, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2032 | h2032
      · linarith only [h1981, h1982, h2032, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2034 | h2034
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2035 | h2035
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2036 | h2036
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2037 | h2037
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2038 | h2038
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2039 | h2039
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2040 | h2040
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2041 | h2041
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2042 | h2042
                        · linarith only [h1981, h1982, h2032, h2042, h811, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2044 | h2044
                          · linarith only [h1981, h1982, h2036, h2039, h2042, h2044, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h2034, h2044, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h1981, h1982, h2037, h2041, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h2032, h2039, h2040, hc03, hc35, hlam, hphi]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2049 | h2049
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2050 | h2050
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2051 | h2051
                        · linarith only [h1980, h2038, h2039, h2051, h811, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2053 | h2053
                          · linarith only [h1981, h1982, h2037, h2053, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h2034, h2053, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h1981, h1982, h2037, h2050, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h1980, h1981, h2034, h2038, h2049, h811, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                · linarith only [h1982, h2037, h2038, hc02, hc25, hlam, hphi]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2059 | h2059
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2060 | h2060
                  · linarith only [h1980, h2032, h2036, h2037, h2059, h2060, h811, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2062 | h2062
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2063 | h2063
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2064 | h2064
                        · linarith only [h1981, h2060, h2064, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2066 | h2066
                          · linarith only [h1981, h1982, h2066, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                          · linarith only [h2034, h2066, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h1980, h2035, h2036, h2037, h2059, h2063, h811, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                    · linarith only [h1980, h1981, h1982, h2034, h2059, h2062, h811, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                · linarith only [h1980, h2036, h2059, h811, hlam]
            · linarith only [h1981, h1982, h2036, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
          · linarith only [h0, h1980, h1982, h2035, hlam]
        · linarith only [h1980, h2034, h811, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2075 | h2075
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2076 | h2076
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2077 | h2077
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2078 | h2078
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2079 | h2079
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2080 | h2080
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2081 | h2081
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2082 | h2082
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2083 | h2083
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2084 | h2084
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2085 | h2085
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2086 | h2086
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2087 | h2087
                            · linarith only [h2075, h2087, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                            · linarith only [h1981, h2075, h2078, h2087, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                          · linarith only [h1501, h1981, h2075, h2077, h2086, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h1501, h1981, h2075, h2076, h2085, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h1501, h1980, h2075, h2078, h2081, h2084, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                    · linarith only [h1981, h2075, h2077, h2079, h2083, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · linarith only [h1501, h1980, h1981, h2075, h2076, h2079, h2081, h2082, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                · linarith only [h1501, h1981, h2075, h2079, h2081, hc01, hc25, hlam, hphi, ht12]
              · linarith only [h1501, h1980, h1981, h2075, h2079, h2080, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2097 | h2097
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2098 | h2098
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2099 | h2099
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2100 | h2100
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2101 | h2101
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2102 | h2102
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2103 | h2103
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2104 | h2104
                            · linarith only [h2075, h2104, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                            · linarith only [h2078, h2104, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                          · linarith only [h1501, h1980, h2079, h2097, h2098, h2103, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h1501, h1980, h2079, h2097, h2098, h2102, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h1501, h1980, h1981, h2075, h2078, h2098, h2101, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                    · linarith only [h2077, h2100, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h1501, h1980, h2076, h2079, h2097, h2098, h2099, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                · linarith only [h1501, h1980, h2097, h2098, hlam]
              · linarith only [h1981, h2075, h2097, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
          · linarith only [h1501, h1980, h2078, hlam]
        · linarith only [h0, h1980, h1981, h2077, hlam]
      · linarith only [h1981, h2075, h2076, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2117 | h2117
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2118 | h2118
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2119 | h2119
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2120 | h2120
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2121 | h2121
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2122 | h2122
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2123 | h2123
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2124 | h2124
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2125 | h2125
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2126 | h2126
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2127 | h2127
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2128 | h2128
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2129 | h2129
                              · linarith only [h2117, h2129, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                              · linarith only [h2117, h2119, h2129, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · linarith only [h0, h1980, h2075, h2125, h2128, hlam]
                          · linarith only [h0, h2075, h2118, h2126, h2127, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h1981, h2117, h2126, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h1980, h2075, h2119, h2121, h2122, h2125, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                    · linarith only [h0, h1980, h2075, h2118, h2121, h2122, h2123, h2124, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                  · linarith only [h2117, h2123, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                · linarith only [h0, h1980, h1981, h2120, h2122, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · linarith only [h0, h1980, h1981, h2120, h2121, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2140 | h2140
              · linarith only [h0, h1980, h2075, h2120, h2140, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2142 | h2142
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2143 | h2143
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2144 | h2144
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2145 | h2145
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2146 | h2146
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2147 | h2147
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2148 | h2148
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2149 | h2149
                              · linarith only [h2117, h2149, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                              · linarith only [h2117, h2119, h2149, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · linarith only [h1980, h2140, h2145, h2148, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h2118, h2147, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h1980, h2120, h2142, h2146, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h0, h1980, h2117, h2119, h2140, h2142, h2145, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                    · linarith only [h0, h1980, h2118, h2140, h2142, h2143, h2144, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                  · linarith only [h2117, h2143, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                · linarith only [h0, h1980, h2142, hlam]
          · linarith only [h1501, h1980, h2119, hlam]
        · linarith only [h1980, h2118, h811, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2161 | h2161
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2162 | h2162
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2163 | h2163
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2164 | h2164
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2165 | h2165
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2166 | h2166
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2167 | h2167
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2168 | h2168
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2169 | h2169
                        · linarith only [h0, h1981, h2117, h2163, h2169, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h1980, h1981, h2165, h2166, h2169, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h2162, h2168, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                    · linarith only [h2161, h2167, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2174 | h2174
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2175 | h2175
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2176 | h2176
                        · linarith only [h2163, h2166, h2176, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2178 | h2178
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2179 | h2179
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2180 | h2180
                              · rcases h1bigk with h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c
                                · have p2181_0 := h2181c.1
                                  have p2181_1 := h2181c.2.1
                                  have p2181_2 := h2181c.2.2.1
                                  have p2181_3 := h2181c.2.2.2
                                  linarith only [hlam, p2181_0]
                                · have p2181_0 := h2181c.1
                                  have p2181_1 := h2181c.2.1
                                  have p2181_2 := h2181c.2.2.1
                                  have p2181_3 := h2181c.2.2.2
                                  linarith only [h0, hlam, p2181_0]
                                · have p2181_0 := h2181c.1
                                  have p2181_1 := h2181c.2.1
                                  have p2181_2 := h2181c.2.2.1
                                  have p2181_3 := h2181c.2.2.2
                                  linarith only [h811, hlam, p2181_0]
                                · have p2181_0 := h2181c.1
                                  have p2181_1 := h2181c.2.1
                                  have p2181_2 := h2181c.2.2.1
                                  have p2181_3 := h2181c.2.2.2
                                  linarith only [h1501, hlam, p2181_0]
                                · have p2181_0 := h2181c.1
                                  have p2181_1 := h2181c.2.1
                                  have p2181_2 := h2181c.2.2.1
                                  have p2181_3 := h2181c.2.2.2
                                  linarith only [h0, h1981, h2163, h2165, h2166, h2178, h2180, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2181_1]
                                · have p2181_0 := h2181c.1
                                  have p2181_1 := h2181c.2.1
                                  have p2181_2 := h2181c.2.2.1
                                  have p2181_3 := h2181c.2.2.2
                                  rcases p2181_3 (m.d 0 1) (by simp) with h2187 | h2187
                                  · linarith only [h2187, hlam, p2181_0]
                                  · rcases p2181_3 (m.d 1 2) (by simp) with h2189 | h2189
                                    · rcases p2181_3 (m.d 1 3) (by simp) with h2190 | h2190
                                      · linarith only [h2163, h2190, hlam]
                                      · linarith only [h2190, h811, hlam]
                                    · linarith only [h2189, hlam, p2181_0]
                                · have p2181_0 := h2181c.1
                                  have p2181_1 := h2181c.2.1
                                  have p2181_2 := h2181c.2.2.1
                                  have p2181_3 := h2181c.2.2.2
                                  linarith only [hlam, p2181_0]
                                · have p2181_0 := h2181c.1
                                  have p2181_1 := h2181c.2.1
                                  have p2181_2 := h2181c.2.2.1
                                  have p2181_3 := h2181c.2.2.2
                                  linarith only [h0, h1981, h2163, hc01, hc12, hlam, hphi, p2181_1]
                                · have p2181_0 := h2181c.1
                                  have p2181_1 := h2181c.2.1
                                  have p2181_2 := h2181c.2.2.1
                                  have p2181_3 := h2181c.2.2.2
                                  linarith only [h1501, h1980, h2165, h2178, h2180, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2181_1]
                                · have p2181_0 := h2181c.1
                                  have p2181_1 := h2181c.2.1
                                  have p2181_2 := h2181c.2.2.1
                                  have p2181_3 := h2181c.2.2.2
                                  linarith only [h0, h1980, h1981, h2163, hlam, p2181_2]
                                · have p2181_0 := h2181c.1
                                  have p2181_1 := h2181c.2.1
                                  have p2181_2 := h2181c.2.2.1
                                  have p2181_3 := h2181c.2.2.2
                                  linarith only [h1980, h2165, h2166, h2178, h2180, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2181_1]
                                · have p2181_0 := h2181c.1
                                  have p2181_1 := h2181c.2.1
                                  have p2181_2 := h2181c.2.2.1
                                  have p2181_3 := h2181c.2.2.2
                                  linarith only [h2163, hlam, p2181_1]
                                · have p2181_0 := h2181c.1
                                  have p2181_1 := h2181c.2.1
                                  have p2181_2 := h2181c.2.2.1
                                  have p2181_3 := h2181c.2.2.2
                                  linarith only [hlam, p2181_0]
                                · have p2181_0 := h2181c.1
                                  have p2181_1 := h2181c.2.1
                                  have p2181_2 := h2181c.2.2.1
                                  have p2181_3 := h2181c.2.2.2
                                  linarith only [h2166, hlam, p2181_1]
                                · have p2181_0 := h2181c.1
                                  have p2181_1 := h2181c.2.1
                                  have p2181_2 := h2181c.2.2.1
                                  have p2181_3 := h2181c.2.2.2
                                  rcases p2181_3 (m.d 0 1) (by simp) with h2202 | h2202
                                  · linarith only [h2202, h811, hlam]
                                  · linarith only [h1980, h2202, hlam]
                                · have p2181_0 := h2181c.1
                                  have p2181_1 := h2181c.2.1
                                  have p2181_2 := h2181c.2.2.1
                                  have p2181_3 := h2181c.2.2.2
                                  rcases p2181_3 (m.d 0 1) (by simp) with h2205 | h2205
                                  · linarith only [h2205, hlam, p2181_0]
                                  · rcases p2181_3 (m.d 1 2) (by simp) with h2207 | h2207
                                    · rcases p2181_3 (m.d 1 3) (by simp) with h2208 | h2208
                                      · linarith only [h2166, h2208, hlam]
                                      · linarith only [h2208, h811, hlam]
                                    · linarith only [h0, h2207, hlam]
                                · have p2181_0 := h2181c.1
                                  have p2181_1 := h2181c.2.1
                                  have p2181_2 := h2181c.2.2.1
                                  have p2181_3 := h2181c.2.2.2
                                  linarith only [h2164, hlam, p2181_1]
                                · have p2181_0 := h2181c.1
                                  have p2181_1 := h2181c.2.1
                                  have p2181_2 := h2181c.2.2.1
                                  have p2181_3 := h2181c.2.2.2
                                  linarith only [h1980, h2165, h2178, h2180, h811, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p2181_1]
                                · have p2181_0 := h2181c.1
                                  have p2181_1 := h2181c.2.1
                                  have p2181_2 := h2181c.2.2.1
                                  have p2181_3 := h2181c.2.2.2
                                  linarith only [hlam, p2181_0]
                                · have p2181_0 := h2181c.1
                                  have p2181_1 := h2181c.2.1
                                  have p2181_2 := h2181c.2.2.1
                                  have p2181_3 := h2181c.2.2.2
                                  rcases p2181_3 (m.d 0 1) (by simp) with h2215 | h2215
                                  · linarith only [h1501, h2215, hlam]
                                  · linarith only [h1980, h2215, hlam]
                                · have p2181_0 := h2181c.1
                                  have p2181_1 := h2181c.2.1
                                  have p2181_2 := h2181c.2.2.1
                                  have p2181_3 := h2181c.2.2.2
                                  linarith only [h1980, hlam, p2181_0]
                                · have p2181_0 := h2181c.1
                                  have p2181_1 := h2181c.2.1
                                  have p2181_2 := h2181c.2.2.1
                                  have p2181_3 := h2181c.2.2.2
                                  linarith only [h2165, hlam, p2181_1]
                                · have p2181_0 := h2181c.1
                                  have p2181_1 := h2181c.2.1
                                  have p2181_2 := h2181c.2.2.1
                                  have p2181_3 := h2181c.2.2.2
                                  linarith only [h2174, hlam, p2181_0]
                                · have p2181_0 := h2181c.1
                                  have p2181_1 := h2181c.2.1
                                  have p2181_2 := h2181c.2.2.1
                                  have p2181_3 := h2181c.2.2.2
                                  linarith only [h2175, hlam, p2181_0]
                                · have p2181_0 := h2181c.1
                                  have p2181_1 := h2181c.2.1
                                  have p2181_2 := h2181c.2.2.1
                                  have p2181_3 := h2181c.2.2.2
                                  linarith only [hlam, p2181_0]
                              · linarith only [h0, h1981, h2117, h2162, h2180, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                            · linarith only [h0, h1980, h1981, h2175, h2176, h2179, hlam]
                          · linarith only [h0, h1980, h1981, h2161, h2165, h2178, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                      · linarith only [h2162, h2175, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                    · linarith only [h0, h1980, h1981, h2161, h2163, h2165, h2174, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                · linarith only [h0, h2075, h2164, h2165, hc01, hc25, hlam, hphi, ht12]
              · linarith only [h0, h1980, h1981, h2163, h2164, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2230 | h2230
              · linarith only [h0, h1980, h2075, h2163, h2230, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2232 | h2232
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2233 | h2233
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2234 | h2234
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2235 | h2235
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2236 | h2236
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2237 | h2237
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2238 | h2238
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2239 | h2239
                              · rcases h1bigk with h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c
                                · have p2240_0 := h2240c.1
                                  have p2240_1 := h2240c.2.1
                                  have p2240_2 := h2240c.2.2.1
                                  have p2240_3 := h2240c.2.2.2
                                  linarith only [hlam, p2240_0]
                                · have p2240_0 := h2240c.1
                                  have p2240_1 := h2240c.2.1
                                  have p2240_2 := h2240c.2.2.1
                                  have p2240_3 := h2240c.2.2.2
                                  linarith only [h0, hlam, p2240_0]
                                · have p2240_0 := h2240c.1
                                  have p2240_1 := h2240c.2.1
                                  have p2240_2 := h2240c.2.2.1
                                  have p2240_3 := h2240c.2.2.2
                                  linarith only [h811, hlam, p2240_0]
                                · have p2240_0 := h2240c.1
                                  have p2240_1 := h2240c.2.1
                                  have p2240_2 := h2240c.2.2.1
                                  have p2240_3 := h2240c.2.2.2
                                  linarith only [h1501, hlam, p2240_0]
                                · have p2240_0 := h2240c.1
                                  have p2240_1 := h2240c.2.1
                                  have p2240_2 := h2240c.2.2.1
                                  have p2240_3 := h2240c.2.2.2
                                  linarith only [h2232, h2237, h2239, hc45, hlam, hphi, ht0b, ht5b, p2240_1, u0elo0]
                                · have p2240_0 := h2240c.1
                                  have p2240_1 := h2240c.2.1
                                  have p2240_2 := h2240c.2.2.1
                                  have p2240_3 := h2240c.2.2.2
                                  linarith only [h2230, h2236, hc01, hc23, hlam, hphi, ht12, p2240_1]
                                · have p2240_0 := h2240c.1
                                  have p2240_1 := h2240c.2.1
                                  have p2240_2 := h2240c.2.2.1
                                  have p2240_3 := h2240c.2.2.2
                                  linarith only [hlam, p2240_0]
                                · have p2240_0 := h2240c.1
                                  have p2240_1 := h2240c.2.1
                                  have p2240_2 := h2240c.2.2.1
                                  have p2240_3 := h2240c.2.2.2
                                  linarith only [h2163, hlam, p2240_0]
                                · have p2240_0 := h2240c.1
                                  have p2240_1 := h2240c.2.1
                                  have p2240_2 := h2240c.2.2.1
                                  have p2240_3 := h2240c.2.2.2
                                  linarith only [h2230, hlam, p2240_0]
                                · have p2240_0 := h2240c.1
                                  have p2240_1 := h2240c.2.1
                                  have p2240_2 := h2240c.2.2.1
                                  have p2240_3 := h2240c.2.2.2
                                  rcases p2240_3 (m.d 0 1) (by simp) with h2250 | h2250
                                  · linarith only [h0, h2250, hlam]
                                  · linarith only [h1980, h2250, hlam]
                                · have p2240_0 := h2240c.1
                                  have p2240_1 := h2240c.2.1
                                  have p2240_2 := h2240c.2.2.1
                                  have p2240_3 := h2240c.2.2.2
                                  rcases p2240_3 (m.d 0 1) (by simp) with h2253 | h2253
                                  · linarith only [h2253, hlam, p2240_0]
                                  · rcases p2240_3 (m.d 1 2) (by simp) with h2255 | h2255
                                    · linarith only [h2163, h2255, hlam]
                                    · linarith only [h0, h2255, hlam]
                                · have p2240_0 := h2240c.1
                                  have p2240_1 := h2240c.2.1
                                  have p2240_2 := h2240c.2.2.1
                                  have p2240_3 := h2240c.2.2.2
                                  linarith only [h0, h1980, h2163, h2232, h2237, h2239, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2240_1]
                                · have p2240_0 := h2240c.1
                                  have p2240_1 := h2240c.2.1
                                  have p2240_2 := h2240c.2.2.1
                                  have p2240_3 := h2240c.2.2.2
                                  linarith only [hlam, p2240_0]
                                · have p2240_0 := h2240c.1
                                  have p2240_1 := h2240c.2.1
                                  have p2240_2 := h2240c.2.2.1
                                  have p2240_3 := h2240c.2.2.2
                                  linarith only [h0, h1980, h2163, h2230, h2232, h2237, h2239, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2240_1]
                                · have p2240_0 := h2240c.1
                                  have p2240_1 := h2240c.2.1
                                  have p2240_2 := h2240c.2.2.1
                                  have p2240_3 := h2240c.2.2.2
                                  linarith only [h0, h1980, h1981, h2117, h2233, hlam, p2240_2]
                                · have p2240_0 := h2240c.1
                                  have p2240_1 := h2240c.2.1
                                  have p2240_2 := h2240c.2.2.1
                                  have p2240_3 := h2240c.2.2.2
                                  rcases p2240_3 (m.d 0 1) (by simp) with h2262 | h2262
                                  · linarith only [h2262, hlam, p2240_0]
                                  · rcases p2240_3 (m.d 1 2) (by simp) with h2264 | h2264
                                    · linarith only [h2230, h2264, hlam]
                                    · linarith only [h0, h2264, hlam]
                                · have p2240_0 := h2240c.1
                                  have p2240_1 := h2240c.2.1
                                  have p2240_2 := h2240c.2.2.1
                                  have p2240_3 := h2240c.2.2.2
                                  linarith only [h0, hc01, hc14, hlam, hphi, p2240_1]
                                · have p2240_0 := h2240c.1
                                  have p2240_1 := h2240c.2.1
                                  have p2240_2 := h2240c.2.2.1
                                  have p2240_3 := h2240c.2.2.2
                                  linarith only [h2233, hlam, p2240_0]
                                · have p2240_0 := h2240c.1
                                  have p2240_1 := h2240c.2.1
                                  have p2240_2 := h2240c.2.2.1
                                  have p2240_3 := h2240c.2.2.2
                                  linarith only [hlam, p2240_0]
                                · have p2240_0 := h2240c.1
                                  have p2240_1 := h2240c.2.1
                                  have p2240_2 := h2240c.2.2.1
                                  have p2240_3 := h2240c.2.2.2
                                  rcases p2240_3 (m.d 0 1) (by simp) with h2270 | h2270
                                  · linarith only [h1501, h2270, hlam]
                                  · linarith only [h1980, h2270, hlam]
                                · have p2240_0 := h2240c.1
                                  have p2240_1 := h2240c.2.1
                                  have p2240_2 := h2240c.2.2.1
                                  have p2240_3 := h2240c.2.2.2
                                  linarith only [h1980, hlam, p2240_0]
                                · have p2240_0 := h2240c.1
                                  have p2240_1 := h2240c.2.1
                                  have p2240_2 := h2240c.2.2.1
                                  have p2240_3 := h2240c.2.2.2
                                  linarith only [h2232, hlam, p2240_1]
                                · have p2240_0 := h2240c.1
                                  have p2240_1 := h2240c.2.1
                                  have p2240_2 := h2240c.2.2.1
                                  have p2240_3 := h2240c.2.2.2
                                  linarith only [h2234, hlam, p2240_0]
                                · have p2240_0 := h2240c.1
                                  have p2240_1 := h2240c.2.1
                                  have p2240_2 := h2240c.2.2.1
                                  have p2240_3 := h2240c.2.2.2
                                  linarith only [h2235, hlam, p2240_0]
                                · have p2240_0 := h2240c.1
                                  have p2240_1 := h2240c.2.1
                                  have p2240_2 := h2240c.2.2.1
                                  have p2240_3 := h2240c.2.2.2
                                  linarith only [hlam, p2240_0]
                              · linarith only [h0, h1981, h2117, h2162, h2239, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                            · linarith only [h1980, h2235, h2238, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h0, h1981, h2117, h2163, h2233, h2237, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h2163, h2233, h2236, hlam]
                      · linarith only [h2162, h2235, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                    · linarith only [h0, h1980, h1981, h2117, h2232, h2233, h2234, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2284 | h2284
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2285 | h2285
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2286 | h2286
                        · linarith only [h0, h1980, h2163, h2232, h2233, h2286, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h0, h1980, h2163, h2232, h2286, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h0, h1980, h2162, h2163, h2232, h2233, h2285, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                    · linarith only [h0, h1980, h2161, h2163, h2232, h2284, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                · linarith only [h0, h1980, h2232, hlam]
          · linarith only [h1980, h2117, h2162, h811, hlam]
        · linarith only [h0, h1980, h1981, h2161, hlam]

end R2N4
