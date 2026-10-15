import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_41S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6700000 in
set_option maxHeartbeats 6700000 in
theorem r1l7_11_13_25_L_I_L_I_M_LR_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have h1bigk := hb1.1
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
  rcases m.htr 0 1 4 (by decide) (by decide) with h1500 | h1500
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1501 | h1501
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1502 | h1502
      · linarith only [h0, h1, h1502, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1504 | h1504
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1505 | h1505
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1506 | h1506
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1507 | h1507
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1508 | h1508
                · linarith only [h1502, h1504, h1508, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1510 | h1510
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1511 | h1511
                    · linarith only [h0, h1, h1511, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                    · linarith only [h1510, h1511, hc24, hlam, hphi, ht45, u5elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1514 | h1514
                    · linarith only [h1, h1500, h1510, h1514, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                    · linarith only [h0, h1, h1504, h1508, h1514, hc12, hc23, hlam, hphi]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1517 | h1517
                · linarith only [h0, h1, h1502, h1517, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1519 | h1519
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1520 | h1520
                    · linarith only [h0, h1, h1517, h1520, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                    · linarith only [h0, h1, h1504, h1517, h1520, hc12, hc23, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1523 | h1523
                    · linarith only [h0, h1, h1517, h1523, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                    · linarith only [h0, h1, h1504, h1517, h1523, hc12, hc23, hlam, hphi]
            · linarith only [h0, h1, h1506, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
          · linarith only [h1, h1500, h1505, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1528 | h1528
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1529 | h1529
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1530 | h1530
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1531 | h1531
                · linarith only [h0, h1, h1502, h1531, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1533 | h1533
                  · linarith only [h0, h1504, h1533, hc24, hlam, hphi, ht45, u5elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1535 | h1535
                    · linarith only [h0, h1504, h1535, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1537 | h1537
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1538 | h1538
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1539 | h1539
                          · linarith only [h1, h1500, h1539, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                          · linarith only [h1, h1500, h1530, h1531, h1533, h1539, hc12, hc23, hlam, hphi]
                        · linarith only [h1, h1500, h1530, h1538, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
                      · linarith only [h1, h1500, h1528, h1530, h1537, hc03, hlam, hphi, ht0b, ht5b, u5ehi9]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1544 | h1544
                · linarith only [h0, h1502, h1504, h1544, hc03, hlam, hphi, ht34, ht45, u5elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1546 | h1546
                  · linarith only [h0, h1504, h1546, hc24, hlam, hphi, ht45, u5elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1548 | h1548
                    · linarith only [h1500, h1504, h1530, h1546, h1548, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1550 | h1550
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1551 | h1551
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1552 | h1552
                          · linarith only [h1500, h1530, h1552, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1554 | h1554
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1555 | h1555
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1556 | h1556
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1557 | h1557
                                  · linarith only [h1500, h1530, h1550, h1557, hlam]
                                  · rcases h1bigk with h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c
                                    · have p1559_0 := h1559c.1
                                      have p1559_1 := h1559c.2.1
                                      have p1559_2 := h1559c.2.2.1
                                      have p1559_3 := h1559c.2.2.2
                                      linarith only [hlam, p1559_0]
                                    · have p1559_0 := h1559c.1
                                      have p1559_1 := h1559c.2.1
                                      have p1559_2 := h1559c.2.2.1
                                      have p1559_3 := h1559c.2.2.2
                                      linarith only [h1, h1544, hc12, hc23, hlam, hphi, p1559_1]
                                    · have p1559_0 := h1559c.1
                                      have p1559_1 := h1559c.2.1
                                      have p1559_2 := h1559c.2.2.1
                                      have p1559_3 := h1559c.2.2.2
                                      linarith only [h1, hlam, p1559_0]
                                    · have p1559_0 := h1559c.1
                                      have p1559_1 := h1559c.2.1
                                      have p1559_2 := h1559c.2.2.1
                                      have p1559_3 := h1559c.2.2.2
                                      linarith only [h1, h1544, h1546, hc12, hc23, hlam, hphi, p1559_1]
                                    · have p1559_0 := h1559c.1
                                      have p1559_1 := h1559c.2.1
                                      have p1559_2 := h1559c.2.2.1
                                      have p1559_3 := h1559c.2.2.2
                                      linarith only [h1, h1544, h1551, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1559_1, u5ehi8]
                                    · have p1559_0 := h1559c.1
                                      have p1559_1 := h1559c.2.1
                                      have p1559_2 := h1559c.2.2.1
                                      have p1559_3 := h1559c.2.2.2
                                      linarith only [h0, hlam, p1559_0]
                                    · have p1559_0 := h1559c.1
                                      have p1559_1 := h1559c.2.1
                                      have p1559_2 := h1559c.2.2.1
                                      have p1559_3 := h1559c.2.2.2
                                      linarith only [hlam, p1559_0]
                                    · have p1559_0 := h1559c.1
                                      have p1559_1 := h1559c.2.1
                                      have p1559_2 := h1559c.2.2.1
                                      have p1559_3 := h1559c.2.2.2
                                      linarith only [h1544, hlam, p1559_0]
                                    · have p1559_0 := h1559c.1
                                      have p1559_1 := h1559c.2.1
                                      have p1559_2 := h1559c.2.2.1
                                      have p1559_3 := h1559c.2.2.2
                                      linarith only [h1546, hlam, p1559_0]
                                    · have p1559_0 := h1559c.1
                                      have p1559_1 := h1559c.2.1
                                      have p1559_2 := h1559c.2.2.1
                                      have p1559_3 := h1559c.2.2.2
                                      linarith only [h1548, hlam, p1559_0]
                                    · have p1559_0 := h1559c.1
                                      have p1559_1 := h1559c.2.1
                                      have p1559_2 := h1559c.2.2.1
                                      have p1559_3 := h1559c.2.2.2
                                      linarith only [h0, h1544, hc12, hc23, hlam, hphi, p1559_1]
                                    · have p1559_0 := h1559c.1
                                      have p1559_1 := h1559c.2.1
                                      have p1559_2 := h1559c.2.2.1
                                      have p1559_3 := h1559c.2.2.2
                                      rcases p1559_3 (m.d 0 1) (by simp) with h1571 | h1571
                                      · linarith only [h1, h1571, hlam]
                                      · linarith only [h0, h1571, hlam]
                                    · have p1559_0 := h1559c.1
                                      have p1559_1 := h1559c.2.1
                                      have p1559_2 := h1559c.2.2.1
                                      have p1559_3 := h1559c.2.2.2
                                      linarith only [hlam, p1559_0]
                                    · have p1559_0 := h1559c.1
                                      have p1559_1 := h1559c.2.1
                                      have p1559_2 := h1559c.2.2.1
                                      have p1559_3 := h1559c.2.2.2
                                      rcases p1559_3 (m.d 0 1) (by simp) with h1575 | h1575
                                      · linarith only [h1, h1575, hlam]
                                      · linarith only [h1500, h1575, hlam]
                                    · have p1559_0 := h1559c.1
                                      have p1559_1 := h1559c.2.1
                                      have p1559_2 := h1559c.2.2.1
                                      have p1559_3 := h1559c.2.2.2
                                      rcases p1559_3 (m.d 0 1) (by simp) with h1578 | h1578
                                      · linarith only [h1, h1578, hlam]
                                      · linarith only [h1501, h1578, hlam]
                                    · have p1559_0 := h1559c.1
                                      have p1559_1 := h1559c.2.1
                                      have p1559_2 := h1559c.2.2.1
                                      have p1559_3 := h1559c.2.2.2
                                      linarith only [h1500, hlam, p1559_0]
                                    · have p1559_0 := h1559c.1
                                      have p1559_1 := h1559c.2.1
                                      have p1559_2 := h1559c.2.2.1
                                      have p1559_3 := h1559c.2.2.2
                                      linarith only [h1500, h1530, h1556, hc12, hlam, hphi, ht23, ht34, ht45, p1559_1, u5elo2]
                                    · have p1559_0 := h1559c.1
                                      have p1559_1 := h1559c.2.1
                                      have p1559_2 := h1559c.2.2.1
                                      have p1559_3 := h1559c.2.2.2
                                      linarith only [h1550, hlam, p1559_0]
                                    · have p1559_0 := h1559c.1
                                      have p1559_1 := h1559c.2.1
                                      have p1559_2 := h1559c.2.2.1
                                      have p1559_3 := h1559c.2.2.2
                                      linarith only [hlam, p1559_0]
                                    · have p1559_0 := h1559c.1
                                      have p1559_1 := h1559c.2.1
                                      have p1559_2 := h1559c.2.2.1
                                      have p1559_3 := h1559c.2.2.2
                                      linarith only [h1552, hlam, p1559_1]
                                    · have p1559_0 := h1559c.1
                                      have p1559_1 := h1559c.2.1
                                      have p1559_2 := h1559c.2.2.1
                                      have p1559_3 := h1559c.2.2.2
                                      linarith only [h1501, hlam, p1559_0]
                                    · have p1559_0 := h1559c.1
                                      have p1559_1 := h1559c.2.1
                                      have p1559_2 := h1559c.2.2.1
                                      have p1559_3 := h1559c.2.2.2
                                      linarith only [h1501, hc12, hlam, hphi, ht23, ht34, ht45, p1559_1, u5elo0]
                                    · have p1559_0 := h1559c.1
                                      have p1559_1 := h1559c.2.1
                                      have p1559_2 := h1559c.2.2.1
                                      have p1559_3 := h1559c.2.2.2
                                      linarith only [h1551, hlam, p1559_0]
                                    · have p1559_0 := h1559c.1
                                      have p1559_1 := h1559c.2.1
                                      have p1559_2 := h1559c.2.2.1
                                      have p1559_3 := h1559c.2.2.2
                                      linarith only [h1, h1501, h1544, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1559_1]
                                    · have p1559_0 := h1559c.1
                                      have p1559_1 := h1559c.2.1
                                      have p1559_2 := h1559c.2.2.1
                                      have p1559_3 := h1559c.2.2.2
                                      linarith only [hlam, p1559_0]
                                · linarith only [h1546, h1556, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                              · linarith only [h1, h1501, h1544, h1555, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi6]
                            · linarith only [h1, h1501, h1544, h1551, h1554, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi8]
                        · linarith only [h1, h1501, h1551, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi6]
                      · linarith only [h1, h1501, h1550, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi6]
            · linarith only [h1, h1501, h1529, hlam, hphi, u5ehi6, u5elo3]
          · linarith only [h1, h1500, h1528, hlam]
    · linarith only [h0, h1501, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1599 | h1599
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1600 | h1600
      · linarith only [h0, h1, h1600, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1602 | h1602
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1603 | h1603
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1604 | h1604
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1605 | h1605
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1606 | h1606
                · linarith only [h1600, h1602, h1606, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1608 | h1608
                  · linarith only [h0, h1500, h1608, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1610 | h1610
                    · linarith only [h0, h1, h1610, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                    · linarith only [h0, h1, h1602, h1606, h1610, hc12, hc23, hlam, hphi]
              · linarith only [h0, h1500, h1602, h1605, hlam, hphi, u5ehi7, u5elo4]
            · linarith only [h1603, h1604, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1615 | h1615
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1616 | h1616
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1617 | h1617
                · linarith only [h0, h1, h1603, h1617, hc23, hc34, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1619 | h1619
                  · linarith only [h0, h1500, h1619, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1621 | h1621
                    · linarith only [h0, h1, h1603, h1621, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                    · linarith only [h0, h1, h1602, h1603, h1621, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h0, h1, h1602, h1603, h1616, hlam, hphi, u5ehi7, u5elo4]
            · linarith only [h0, h1, h1602, h1615, hlam, hphi, u5ehi7, u5elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1626 | h1626
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1627 | h1627
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1628 | h1628
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1629 | h1629
                · linarith only [h0, h1602, h1629, hc23, hlam, hphi, ht34, ht45, u5elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1631 | h1631
                  · linarith only [h0, h1602, h1631, hc24, hlam, hphi, ht45, u5elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1633 | h1633
                    · linarith only [h0, h1602, h1633, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1635 | h1635
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1636 | h1636
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1637 | h1637
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1638 | h1638
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1639 | h1639
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1640 | h1640
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1641 | h1641
                                  · rcases h1bigk with h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c | h1642c
                                    · have p1642_0 := h1642c.1
                                      have p1642_1 := h1642c.2.1
                                      have p1642_2 := h1642c.2.2.1
                                      have p1642_3 := h1642c.2.2.2
                                      linarith only [hlam, p1642_0]
                                    · have p1642_0 := h1642c.1
                                      have p1642_1 := h1642c.2.1
                                      have p1642_2 := h1642c.2.2.1
                                      have p1642_3 := h1642c.2.2.2
                                      linarith only [h1500, h1629, h1635, hc12, hc23, hlam, hphi, p1642_1]
                                    · have p1642_0 := h1642c.1
                                      have p1642_1 := h1642c.2.1
                                      have p1642_2 := h1642c.2.2.1
                                      have p1642_3 := h1642c.2.2.2
                                      linarith only [h1, hlam, p1642_0]
                                    · have p1642_0 := h1642c.1
                                      have p1642_1 := h1642c.2.1
                                      have p1642_2 := h1642c.2.2.1
                                      have p1642_3 := h1642c.2.2.2
                                      linarith only [h1500, hlam, p1642_0]
                                    · have p1642_0 := h1642c.1
                                      have p1642_1 := h1642c.2.1
                                      have p1642_2 := h1642c.2.2.1
                                      have p1642_3 := h1642c.2.2.2
                                      linarith only [h1500, h1629, h1635, h1636, h1641, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1642_1, u5ehi9]
                                    · have p1642_0 := h1642c.1
                                      have p1642_1 := h1642c.2.1
                                      have p1642_2 := h1642c.2.2.1
                                      have p1642_3 := h1642c.2.2.2
                                      linarith only [h0, hlam, p1642_0]
                                    · have p1642_0 := h1642c.1
                                      have p1642_1 := h1642c.2.1
                                      have p1642_2 := h1642c.2.2.1
                                      have p1642_3 := h1642c.2.2.2
                                      linarith only [hlam, p1642_0]
                                    · have p1642_0 := h1642c.1
                                      have p1642_1 := h1642c.2.1
                                      have p1642_2 := h1642c.2.2.1
                                      have p1642_3 := h1642c.2.2.2
                                      linarith only [h1629, hlam, p1642_0]
                                    · have p1642_0 := h1642c.1
                                      have p1642_1 := h1642c.2.1
                                      have p1642_2 := h1642c.2.2.1
                                      have p1642_3 := h1642c.2.2.2
                                      linarith only [h1631, hlam, p1642_0]
                                    · have p1642_0 := h1642c.1
                                      have p1642_1 := h1642c.2.1
                                      have p1642_2 := h1642c.2.2.1
                                      have p1642_3 := h1642c.2.2.2
                                      linarith only [h1633, hlam, p1642_0]
                                    · have p1642_0 := h1642c.1
                                      have p1642_1 := h1642c.2.1
                                      have p1642_2 := h1642c.2.2.1
                                      have p1642_3 := h1642c.2.2.2
                                      linarith only [h0, h1629, hc12, hc23, hlam, hphi, p1642_1]
                                    · have p1642_0 := h1642c.1
                                      have p1642_1 := h1642c.2.1
                                      have p1642_2 := h1642c.2.2.1
                                      have p1642_3 := h1642c.2.2.2
                                      rcases p1642_3 (m.d 0 1) (by simp) with h1654 | h1654
                                      · linarith only [h1, h1654, hlam]
                                      · linarith only [h0, h1654, hlam]
                                    · have p1642_0 := h1642c.1
                                      have p1642_1 := h1642c.2.1
                                      have p1642_2 := h1642c.2.2.1
                                      have p1642_3 := h1642c.2.2.2
                                      linarith only [hlam, p1642_0]
                                    · have p1642_0 := h1642c.1
                                      have p1642_1 := h1642c.2.1
                                      have p1642_2 := h1642c.2.2.1
                                      have p1642_3 := h1642c.2.2.2
                                      linarith only [h1500, h1599, h1629, h1636, h1641, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1642_1, u5ehi9]
                                    · have p1642_0 := h1642c.1
                                      have p1642_1 := h1642c.2.1
                                      have p1642_2 := h1642c.2.2.1
                                      have p1642_3 := h1642c.2.2.2
                                      rcases p1642_3 (m.d 0 1) (by simp) with h1659 | h1659
                                      · linarith only [h1, h1659, hlam]
                                      · linarith only [h1599, h1659, hlam]
                                    · have p1642_0 := h1642c.1
                                      have p1642_1 := h1642c.2.1
                                      have p1642_2 := h1642c.2.2.1
                                      have p1642_3 := h1642c.2.2.2
                                      linarith only [h1599, h1636, h1641, hc14, hlam, hphi, ht01, ht0b, ht5b, p1642_1, u5ehi9]
                                    · have p1642_0 := h1642c.1
                                      have p1642_1 := h1642c.2.1
                                      have p1642_2 := h1642c.2.2.1
                                      have p1642_3 := h1642c.2.2.2
                                      rcases p1642_3 (m.d 0 1) (by simp) with h1663 | h1663
                                      · linarith only [h1500, h1663, hlam]
                                      · linarith only [h0, h1663, hlam]
                                    · have p1642_0 := h1642c.1
                                      have p1642_1 := h1642c.2.1
                                      have p1642_2 := h1642c.2.2.1
                                      have p1642_3 := h1642c.2.2.2
                                      linarith only [h1635, hlam, p1642_0]
                                    · have p1642_0 := h1642c.1
                                      have p1642_1 := h1642c.2.1
                                      have p1642_2 := h1642c.2.2.1
                                      have p1642_3 := h1642c.2.2.2
                                      linarith only [hlam, p1642_0]
                                    · have p1642_0 := h1642c.1
                                      have p1642_1 := h1642c.2.1
                                      have p1642_2 := h1642c.2.2.1
                                      have p1642_3 := h1642c.2.2.2
                                      rcases p1642_3 (m.d 0 1) (by simp) with h1668 | h1668
                                      · linarith only [h1500, h1668, hlam]
                                      · linarith only [h1599, h1668, hlam]
                                    · have p1642_0 := h1642c.1
                                      have p1642_1 := h1642c.2.1
                                      have p1642_2 := h1642c.2.2.1
                                      have p1642_3 := h1642c.2.2.2
                                      linarith only [h1599, hlam, p1642_0]
                                    · have p1642_0 := h1642c.1
                                      have p1642_1 := h1642c.2.1
                                      have p1642_2 := h1642c.2.2.1
                                      have p1642_3 := h1642c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p1642_1, u5elo1]
                                    · have p1642_0 := h1642c.1
                                      have p1642_1 := h1642c.2.1
                                      have p1642_2 := h1642c.2.2.1
                                      have p1642_3 := h1642c.2.2.2
                                      linarith only [h1636, hlam, p1642_0]
                                    · have p1642_0 := h1642c.1
                                      have p1642_1 := h1642c.2.1
                                      have p1642_2 := h1642c.2.2.1
                                      have p1642_3 := h1642c.2.2.2
                                      linarith only [h1637, hlam, p1642_0]
                                    · have p1642_0 := h1642c.1
                                      have p1642_1 := h1642c.2.1
                                      have p1642_2 := h1642c.2.2.1
                                      have p1642_3 := h1642c.2.2.2
                                      linarith only [hlam, p1642_0]
                                  · rcases h1bigk with h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c | h1676c
                                    · have p1676_0 := h1676c.1
                                      have p1676_1 := h1676c.2.1
                                      have p1676_2 := h1676c.2.2.1
                                      have p1676_3 := h1676c.2.2.2
                                      linarith only [hlam, p1676_0]
                                    · have p1676_0 := h1676c.1
                                      have p1676_1 := h1676c.2.1
                                      have p1676_2 := h1676c.2.2.1
                                      have p1676_3 := h1676c.2.2.2
                                      linarith only [h1500, h1629, h1635, hc12, hc23, hlam, hphi, p1676_1]
                                    · have p1676_0 := h1676c.1
                                      have p1676_1 := h1676c.2.1
                                      have p1676_2 := h1676c.2.2.1
                                      have p1676_3 := h1676c.2.2.2
                                      linarith only [h1, hlam, p1676_0]
                                    · have p1676_0 := h1676c.1
                                      have p1676_1 := h1676c.2.1
                                      have p1676_2 := h1676c.2.2.1
                                      have p1676_3 := h1676c.2.2.2
                                      linarith only [h1500, hlam, p1676_0]
                                    · have p1676_0 := h1676c.1
                                      have p1676_1 := h1676c.2.1
                                      have p1676_2 := h1676c.2.2.1
                                      have p1676_3 := h1676c.2.2.2
                                      linarith only [h1500, h1629, h1635, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1676_1, u5ehi6]
                                    · have p1676_0 := h1676c.1
                                      have p1676_1 := h1676c.2.1
                                      have p1676_2 := h1676c.2.2.1
                                      have p1676_3 := h1676c.2.2.2
                                      linarith only [h0, hlam, p1676_0]
                                    · have p1676_0 := h1676c.1
                                      have p1676_1 := h1676c.2.1
                                      have p1676_2 := h1676c.2.2.1
                                      have p1676_3 := h1676c.2.2.2
                                      linarith only [hlam, p1676_0]
                                    · have p1676_0 := h1676c.1
                                      have p1676_1 := h1676c.2.1
                                      have p1676_2 := h1676c.2.2.1
                                      have p1676_3 := h1676c.2.2.2
                                      linarith only [h1629, hlam, p1676_0]
                                    · have p1676_0 := h1676c.1
                                      have p1676_1 := h1676c.2.1
                                      have p1676_2 := h1676c.2.2.1
                                      have p1676_3 := h1676c.2.2.2
                                      linarith only [h1631, hlam, p1676_0]
                                    · have p1676_0 := h1676c.1
                                      have p1676_1 := h1676c.2.1
                                      have p1676_2 := h1676c.2.2.1
                                      have p1676_3 := h1676c.2.2.2
                                      linarith only [h1633, hlam, p1676_0]
                                    · have p1676_0 := h1676c.1
                                      have p1676_1 := h1676c.2.1
                                      have p1676_2 := h1676c.2.2.1
                                      have p1676_3 := h1676c.2.2.2
                                      linarith only [h0, h1629, hc12, hc23, hlam, hphi, p1676_1]
                                    · have p1676_0 := h1676c.1
                                      have p1676_1 := h1676c.2.1
                                      have p1676_2 := h1676c.2.2.1
                                      have p1676_3 := h1676c.2.2.2
                                      rcases p1676_3 (m.d 0 1) (by simp) with h1688 | h1688
                                      · linarith only [h1, h1688, hlam]
                                      · linarith only [h0, h1688, hlam]
                                    · have p1676_0 := h1676c.1
                                      have p1676_1 := h1676c.2.1
                                      have p1676_2 := h1676c.2.2.1
                                      have p1676_3 := h1676c.2.2.2
                                      linarith only [hlam, p1676_0]
                                    · have p1676_0 := h1676c.1
                                      have p1676_1 := h1676c.2.1
                                      have p1676_2 := h1676c.2.2.1
                                      have p1676_3 := h1676c.2.2.2
                                      linarith only [h1500, h1599, h1629, h1637, h1641, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1676_1]
                                    · have p1676_0 := h1676c.1
                                      have p1676_1 := h1676c.2.1
                                      have p1676_2 := h1676c.2.2.1
                                      have p1676_3 := h1676c.2.2.2
                                      rcases p1676_3 (m.d 0 1) (by simp) with h1693 | h1693
                                      · linarith only [h1, h1693, hlam]
                                      · linarith only [h1599, h1693, hlam]
                                    · have p1676_0 := h1676c.1
                                      have p1676_1 := h1676c.2.1
                                      have p1676_2 := h1676c.2.2.1
                                      have p1676_3 := h1676c.2.2.2
                                      linarith only [h1599, h1637, h1641, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1676_1]
                                    · have p1676_0 := h1676c.1
                                      have p1676_1 := h1676c.2.1
                                      have p1676_2 := h1676c.2.2.1
                                      have p1676_3 := h1676c.2.2.2
                                      rcases p1676_3 (m.d 0 1) (by simp) with h1697 | h1697
                                      · linarith only [h1500, h1697, hlam]
                                      · linarith only [h0, h1697, hlam]
                                    · have p1676_0 := h1676c.1
                                      have p1676_1 := h1676c.2.1
                                      have p1676_2 := h1676c.2.2.1
                                      have p1676_3 := h1676c.2.2.2
                                      linarith only [h1635, hlam, p1676_0]
                                    · have p1676_0 := h1676c.1
                                      have p1676_1 := h1676c.2.1
                                      have p1676_2 := h1676c.2.2.1
                                      have p1676_3 := h1676c.2.2.2
                                      linarith only [hlam, p1676_0]
                                    · have p1676_0 := h1676c.1
                                      have p1676_1 := h1676c.2.1
                                      have p1676_2 := h1676c.2.2.1
                                      have p1676_3 := h1676c.2.2.2
                                      rcases p1676_3 (m.d 0 1) (by simp) with h1702 | h1702
                                      · linarith only [h1500, h1702, hlam]
                                      · linarith only [h1599, h1702, hlam]
                                    · have p1676_0 := h1676c.1
                                      have p1676_1 := h1676c.2.1
                                      have p1676_2 := h1676c.2.2.1
                                      have p1676_3 := h1676c.2.2.2
                                      linarith only [h1599, hlam, p1676_0]
                                    · have p1676_0 := h1676c.1
                                      have p1676_1 := h1676c.2.1
                                      have p1676_2 := h1676c.2.2.1
                                      have p1676_3 := h1676c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p1676_1, u5elo1]
                                    · have p1676_0 := h1676c.1
                                      have p1676_1 := h1676c.2.1
                                      have p1676_2 := h1676c.2.2.1
                                      have p1676_3 := h1676c.2.2.2
                                      linarith only [h1636, hlam, p1676_0]
                                    · have p1676_0 := h1676c.1
                                      have p1676_1 := h1676c.2.1
                                      have p1676_2 := h1676c.2.2.1
                                      have p1676_3 := h1676c.2.2.2
                                      linarith only [h1637, hlam, p1676_0]
                                    · have p1676_0 := h1676c.1
                                      have p1676_1 := h1676c.2.1
                                      have p1676_2 := h1676c.2.2.1
                                      have p1676_3 := h1676c.2.2.2
                                      linarith only [hlam, p1676_0]
                                · linarith only [h1500, h1599, h1631, h1637, h1640, hlam]
                              · linarith only [h1500, h1599, h1631, h1636, h1638, h1639, hlam]
                            · linarith only [h1, h1599, h1629, h1636, h1638, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi8]
                          · linarith only [h1500, h1599, h1636, h1637, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi8]
                        · linarith only [h1500, h1599, h1635, h1636, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi6]
                      · linarith only [h1, h1626, h1635, hlam]
              · linarith only [h1500, h1599, h1628, hlam, hphi, u5ehi6, u5elo4]
            · linarith only [h1626, h1627, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1718 | h1718
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1719 | h1719
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1720 | h1720
                · linarith only [h0, h1, h1626, h1720, hc23, hc34, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1722 | h1722
                  · linarith only [h0, h1602, h1722, hc24, hlam, hphi, ht45, u5elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1724 | h1724
                    · linarith only [h0, h1602, h1724, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1726 | h1726
                      · linarith only [h1, h1599, h1626, h1726, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi6]
                      · linarith only [h1, h1599, h1726, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi6]
              · linarith only [h1, h1599, h1626, h1719, hlam, hphi, u5ehi6, u5elo4]
            · linarith only [h1, h1599, h1718, hlam, hphi, u5ehi6, u5elo3]
    · linarith only [h0, h1599, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]

set_option maxHeartbeats 6700000 in
set_option maxHeartbeats 6700000 in
theorem r1l7_11_13_25_L_I_L_I_M_LR_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have h1bigk := hb1.1
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
  · exact r1l7_11_13_25_L_I_L_I_M_LR_x0_x0 m hb1 hb3 hb5 h0 h1
  · exact r1l7_11_13_25_L_I_L_I_M_LR_x0_x1 m hb1 hb3 hb5 h0 h1

set_option maxHeartbeats 6700000 in
set_option maxHeartbeats 6700000 in
theorem r1l7_11_13_25_L_I_L_I_M_LR_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1732 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h1bigk := hb1.1
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
  rcases m.htr 0 1 4 (by decide) (by decide) with h1733 | h1733
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1734 | h1734
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1735 | h1735
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1736 | h1736
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1737 | h1737
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1738 | h1738
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1739 | h1739
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1740 | h1740
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1741 | h1741
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1742 | h1742
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1743 | h1743
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1744 | h1744
                        · linarith only [h0, h1732, h1744, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                        · linarith only [h1743, h1744, hc34, hlam, hphi, ht45, u5elo3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1747 | h1747
                        · linarith only [h0, h1732, h1737, h1743, h1747, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1749 | h1749
                          · linarith only [h0, h1733, h1749, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1751 | h1751
                            · linarith only [h1740, h1743, h1751, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1753 | h1753
                              · linarith only [h1740, h1747, h1753, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1755 | h1755
                                · linarith only [h1741, h1749, h1755, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1757 | h1757
                                  · linarith only [h0, h1732, h1737, h1740, h1743, h1749, h1757, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                  · linarith only [h1740, h1743, h1757, hc23, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h0, h1732, h1737, h1739, h1742, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                  · linarith only [h0, h1732, h1737, h1739, h1741, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                · linarith only [h0, h1732, h1737, h1739, h1740, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1763 | h1763
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1764 | h1764
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1765 | h1765
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1766 | h1766
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1767 | h1767
                        · linarith only [h0, h1732, h1767, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                        · linarith only [h0, h1732, h1738, h1766, h1767, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h1737, h1739, h1763, h1766, hc23, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h0, h1732, h1738, h1765, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                  · linarith only [h0, h1732, h1738, h1764, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                · linarith only [h0, h1732, h1738, h1763, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
            · linarith only [h1737, h1738, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1775 | h1775
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1776 | h1776
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1777 | h1777
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1778 | h1778
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1779 | h1779
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1780 | h1780
                      · linarith only [h1732, h1737, h1775, h1780, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1782 | h1782
                        · linarith only [h0, h1733, h1780, h1782, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                        · linarith only [h1737, h1775, h1777, h1782, hc23, hc34, hlam, hphi]
                    · linarith only [h0, h1734, h1779, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
                  · linarith only [h0, h1733, h1737, h1775, h1778, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                · linarith only [h0, h1733, h1737, h1775, h1777, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
              · linarith only [h1737, h1775, h1776, hlam, hphi, u5ehi8, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1789 | h1789
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1790 | h1790
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1791 | h1791
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1792 | h1792
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1793 | h1793
                      · linarith only [h1732, h1737, h1789, h1793, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1795 | h1795
                        · linarith only [h1732, h1775, h1795, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1797 | h1797
                          · linarith only [h0, h1733, h1797, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1799 | h1799
                            · linarith only [h1737, h1789, h1790, h1793, h1797, h1799, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1801 | h1801
                              · linarith only [h1775, h1789, h1790, h1793, h1797, h1801, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1803 | h1803
                                · linarith only [h1791, h1797, h1803, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1805 | h1805
                                  · rcases h1bigk with h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [hlam, p1806_0]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [h0, hlam, p1806_0]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      rcases p1806_3 (m.d 0 1) (by simp) with h1809 | h1809
                                      · rcases p1806_3 (m.d 1 2) (by simp) with h1810 | h1810
                                        · rcases p1806_3 (m.d 1 3) (by simp) with h1811 | h1811
                                          · linarith only [h1811, hlam, p1806_0]
                                          · rcases p1806_3 (m.d 1 4) (by simp) with h1813 | h1813
                                            · linarith only [h1733, h1813, hlam]
                                            · linarith only [h1793, h1813, hlam]
                                        · linarith only [h1790, h1810, hlam]
                                      · linarith only [h1809, hlam, p1806_0]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      rcases p1806_3 (m.d 0 1) (by simp) with h1818 | h1818
                                      · rcases p1806_3 (m.d 1 2) (by simp) with h1819 | h1819
                                        · rcases p1806_3 (m.d 1 3) (by simp) with h1820 | h1820
                                          · linarith only [h1732, h1820, hlam]
                                          · rcases p1806_3 (m.d 1 4) (by simp) with h1822 | h1822
                                            · linarith only [h1822, hlam, p1806_0]
                                            · rcases p1806_3 (m.d 1 5) (by simp) with h1824 | h1824
                                              · linarith only [h1734, h1824, hlam]
                                              · linarith only [h1797, h1824, hlam]
                                        · linarith only [h1791, h1819, hlam]
                                      · linarith only [h1818, hlam, p1806_0]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [h0, h1792, hc12, hlam, hphi, ht01, ht0b, ht5b, p1806_1, u5ehi7]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [h1733, h1789, h1793, h1797, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1806_1]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [hlam, p1806_0]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [h0, h1733, h1789, h1793, h1797, hlam, p1806_2]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [h0, h1733, h1789, h1797, hlam, p1806_2]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      rcases p1806_3 (m.d 0 1) (by simp) with h1834 | h1834
                                      · linarith only [h0, h1834, hlam]
                                      · linarith only [h1734, h1834, hlam]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [h1732, hlam, p1806_0]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [h1790, hlam, p1806_1]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [hlam, p1806_0]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [h1793, hlam, p1806_1]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [h1795, hlam, p1806_1]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [h1733, hlam, p1806_0]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [h1791, hlam, p1806_1]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [h1733, h1789, h1790, h1797, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1806_1]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [hlam, p1806_0]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [h1797, hlam, p1806_1]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [h1734, hlam, p1806_0]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [h1792, hlam, p1806_1]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [h1790, hc23, hlam, hphi, ht34, ht45, p1806_1, u5elo1]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [h0, h1733, h1789, h1797, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1806_1]
                                    · have p1806_0 := h1806c.1
                                      have p1806_1 := h1806c.2.1
                                      have p1806_2 := h1806c.2.2.1
                                      have p1806_3 := h1806c.2.2.2
                                      linarith only [hlam, p1806_0]
                                  · linarith only [h1737, h1789, h1805, hlam]
                    · linarith only [h0, h1733, h1789, h1792, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                  · linarith only [h0, h1733, h1789, h1791, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                · linarith only [h0, h1733, h1789, h1790, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1856 | h1856
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1857 | h1857
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1858 | h1858
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1859 | h1859
                      · linarith only [h0, h1732, h1737, h1859, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1861 | h1861
                        · linarith only [h0, h1732, h1861, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1863 | h1863
                          · linarith only [h1733, h1789, h1863, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1865 | h1865
                            · linarith only [h1732, h1737, h1856, h1865, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1867 | h1867
                              · linarith only [h1732, h1737, h1775, h1789, h1856, h1867, hlam, hphi, u5ehi5, u5elo4]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1869 | h1869
                                · linarith only [h1733, h1789, h1857, h1869, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1871 | h1871
                                  · rcases h1bigk with h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c | h1872c
                                    · have p1872_0 := h1872c.1
                                      have p1872_1 := h1872c.2.1
                                      have p1872_2 := h1872c.2.2.1
                                      have p1872_3 := h1872c.2.2.2
                                      linarith only [hlam, p1872_0]
                                    · have p1872_0 := h1872c.1
                                      have p1872_1 := h1872c.2.1
                                      have p1872_2 := h1872c.2.2.1
                                      have p1872_3 := h1872c.2.2.2
                                      linarith only [h0, hlam, p1872_0]
                                    · have p1872_0 := h1872c.1
                                      have p1872_1 := h1872c.2.1
                                      have p1872_2 := h1872c.2.2.1
                                      have p1872_3 := h1872c.2.2.2
                                      rcases p1872_3 (m.d 0 1) (by simp) with h1875 | h1875
                                      · rcases p1872_3 (m.d 1 2) (by simp) with h1876 | h1876
                                        · rcases p1872_3 (m.d 1 3) (by simp) with h1877 | h1877
                                          · linarith only [h1877, hlam, p1872_0]
                                          · rcases p1872_3 (m.d 1 4) (by simp) with h1879 | h1879
                                            · linarith only [h1733, h1879, hlam]
                                            · linarith only [h1859, h1879, hlam]
                                        · linarith only [h1856, h1876, hlam]
                                      · linarith only [h1875, hlam, p1872_0]
                                    · have p1872_0 := h1872c.1
                                      have p1872_1 := h1872c.2.1
                                      have p1872_2 := h1872c.2.2.1
                                      have p1872_3 := h1872c.2.2.2
                                      rcases p1872_3 (m.d 0 1) (by simp) with h1884 | h1884
                                      · rcases p1872_3 (m.d 1 2) (by simp) with h1885 | h1885
                                        · rcases p1872_3 (m.d 1 3) (by simp) with h1886 | h1886
                                          · linarith only [h1732, h1886, hlam]
                                          · rcases p1872_3 (m.d 1 4) (by simp) with h1888 | h1888
                                            · linarith only [h1888, hlam, p1872_0]
                                            · rcases p1872_3 (m.d 1 5) (by simp) with h1890 | h1890
                                              · linarith only [h1734, h1890, hlam]
                                              · linarith only [h1863, h1890, hlam]
                                        · linarith only [h1857, h1885, hlam]
                                      · linarith only [h1884, hlam, p1872_0]
                                    · have p1872_0 := h1872c.1
                                      have p1872_1 := h1872c.2.1
                                      have p1872_2 := h1872c.2.2.1
                                      have p1872_3 := h1872c.2.2.2
                                      linarith only [h0, h1858, hc12, hlam, hphi, ht01, ht0b, ht5b, p1872_1, u5ehi7]
                                    · have p1872_0 := h1872c.1
                                      have p1872_1 := h1872c.2.1
                                      have p1872_2 := h1872c.2.2.1
                                      have p1872_3 := h1872c.2.2.2
                                      linarith only [h1734, h1858, hc12, hlam, hphi, ht01, ht0b, ht5b, p1872_1, u5ehi7]
                                    · have p1872_0 := h1872c.1
                                      have p1872_1 := h1872c.2.1
                                      have p1872_2 := h1872c.2.2.1
                                      have p1872_3 := h1872c.2.2.2
                                      linarith only [hlam, p1872_0]
                                    · have p1872_0 := h1872c.1
                                      have p1872_1 := h1872c.2.1
                                      have p1872_2 := h1872c.2.2.1
                                      have p1872_3 := h1872c.2.2.2
                                      rcases p1872_3 (m.d 0 1) (by simp) with h1898 | h1898
                                      · linarith only [h0, h1898, hlam]
                                      · linarith only [h1732, h1898, hlam]
                                    · have p1872_0 := h1872c.1
                                      have p1872_1 := h1872c.2.1
                                      have p1872_2 := h1872c.2.2.1
                                      have p1872_3 := h1872c.2.2.2
                                      rcases p1872_3 (m.d 0 1) (by simp) with h1901 | h1901
                                      · linarith only [h0, h1901, hlam]
                                      · linarith only [h1733, h1901, hlam]
                                    · have p1872_0 := h1872c.1
                                      have p1872_1 := h1872c.2.1
                                      have p1872_2 := h1872c.2.2.1
                                      have p1872_3 := h1872c.2.2.2
                                      rcases p1872_3 (m.d 0 1) (by simp) with h1904 | h1904
                                      · linarith only [h0, h1904, hlam]
                                      · linarith only [h1734, h1904, hlam]
                                    · have p1872_0 := h1872c.1
                                      have p1872_1 := h1872c.2.1
                                      have p1872_2 := h1872c.2.2.1
                                      have p1872_3 := h1872c.2.2.2
                                      linarith only [h1732, hlam, p1872_0]
                                    · have p1872_0 := h1872c.1
                                      have p1872_1 := h1872c.2.1
                                      have p1872_2 := h1872c.2.2.1
                                      have p1872_3 := h1872c.2.2.2
                                      linarith only [h1856, hlam, p1872_1]
                                    · have p1872_0 := h1872c.1
                                      have p1872_1 := h1872c.2.1
                                      have p1872_2 := h1872c.2.2.1
                                      have p1872_3 := h1872c.2.2.2
                                      linarith only [hlam, p1872_0]
                                    · have p1872_0 := h1872c.1
                                      have p1872_1 := h1872c.2.1
                                      have p1872_2 := h1872c.2.2.1
                                      have p1872_3 := h1872c.2.2.2
                                      linarith only [h1859, hlam, p1872_1]
                                    · have p1872_0 := h1872c.1
                                      have p1872_1 := h1872c.2.1
                                      have p1872_2 := h1872c.2.2.1
                                      have p1872_3 := h1872c.2.2.2
                                      linarith only [h1861, hlam, p1872_1]
                                    · have p1872_0 := h1872c.1
                                      have p1872_1 := h1872c.2.1
                                      have p1872_2 := h1872c.2.2.1
                                      have p1872_3 := h1872c.2.2.2
                                      linarith only [h1733, hlam, p1872_0]
                                    · have p1872_0 := h1872c.1
                                      have p1872_1 := h1872c.2.1
                                      have p1872_2 := h1872c.2.2.1
                                      have p1872_3 := h1872c.2.2.2
                                      linarith only [h1857, hlam, p1872_1]
                                    · have p1872_0 := h1872c.1
                                      have p1872_1 := h1872c.2.1
                                      have p1872_2 := h1872c.2.2.1
                                      have p1872_3 := h1872c.2.2.2
                                      linarith only [h1733, h1789, h1871, hc13, hlam, hphi, ht34, ht45, p1872_1, u5elo3]
                                    · have p1872_0 := h1872c.1
                                      have p1872_1 := h1872c.2.1
                                      have p1872_2 := h1872c.2.2.1
                                      have p1872_3 := h1872c.2.2.2
                                      linarith only [hlam, p1872_0]
                                    · have p1872_0 := h1872c.1
                                      have p1872_1 := h1872c.2.1
                                      have p1872_2 := h1872c.2.2.1
                                      have p1872_3 := h1872c.2.2.2
                                      linarith only [h1863, hlam, p1872_1]
                                    · have p1872_0 := h1872c.1
                                      have p1872_1 := h1872c.2.1
                                      have p1872_2 := h1872c.2.2.1
                                      have p1872_3 := h1872c.2.2.2
                                      linarith only [h1734, hlam, p1872_0]
                                    · have p1872_0 := h1872c.1
                                      have p1872_1 := h1872c.2.1
                                      have p1872_2 := h1872c.2.2.1
                                      have p1872_3 := h1872c.2.2.2
                                      linarith only [h1858, hlam, p1872_1]
                                    · have p1872_0 := h1872c.1
                                      have p1872_1 := h1872c.2.1
                                      have p1872_2 := h1872c.2.2.1
                                      have p1872_3 := h1872c.2.2.2
                                      linarith only [h1734, h1856, hc23, hlam, hphi, ht34, ht45, p1872_1, u5elo0]
                                    · have p1872_0 := h1872c.1
                                      have p1872_1 := h1872c.2.1
                                      have p1872_2 := h1872c.2.2.1
                                      have p1872_3 := h1872c.2.2.2
                                      linarith only [h1734, h1789, h1871, hc14, hlam, hphi, ht45, p1872_1, u5elo3]
                                    · have p1872_0 := h1872c.1
                                      have p1872_1 := h1872c.2.1
                                      have p1872_2 := h1872c.2.2.1
                                      have p1872_3 := h1872c.2.2.2
                                      linarith only [hlam, p1872_0]
                                  · linarith only [h1737, h1871, hc03, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h0, h1734, h1858, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
                  · linarith only [h0, h1734, h1857, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
                · linarith only [h0, h1734, h1856, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
        · linarith only [h0, h1734, h1736, hlam, hphi, u5ehi6, u5elo2]
      · linarith only [h0, h1732, h1735, hlam]
    · linarith only [h1732, h1734, hc13, hlam, hphi, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1929 | h1929
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1930 | h1930
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1931 | h1931
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1932 | h1932
          · linarith only [h1732, h1733, h1932, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1934 | h1934
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1935 | h1935
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1936 | h1936
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1937 | h1937
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1938 | h1938
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1939 | h1939
                      · linarith only [h1732, h1932, h1934, h1939, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1941 | h1941
                        · linarith only [h1732, h1733, h1939, h1941, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi8]
                        · linarith only [h1732, h1733, h1934, h1936, h1939, h1941, hc23, hc34, hlam, hphi]
                    · linarith only [h1733, h1929, h1937, h1938, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
                  · linarith only [h0, h1732, h1934, h1937, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                · linarith only [h0, h1732, h1934, h1936, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
              · linarith only [h1732, h1733, h1934, h1935, hlam, hphi, u5ehi8, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1948 | h1948
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1949 | h1949
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1950 | h1950
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1951 | h1951
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1952 | h1952
                      · linarith only [h1732, h1934, h1952, hc34, hlam, hphi, ht45, u5elo3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1954 | h1954
                        · linarith only [h1732, h1934, h1954, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1956 | h1956
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1957 | h1957
                            · linarith only [h1732, h1733, h1929, h1934, h1949, h1951, h1952, h1957, hlam, hphi, u5ehi7, u5elo3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1959 | h1959
                              · linarith only [h1732, h1934, h1949, h1959, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1961 | h1961
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1962 | h1962
                                  · rcases h1bigk with h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [hlam, p1963_0]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [h0, hlam, p1963_0]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [h1733, h1952, hc13, hc34, hlam, hphi, p1963_1]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [h1733, hlam, p1963_0]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [h1733, h1951, h1952, h1961, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1963_1, u5ehi9]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [h1929, h1951, h1961, hc12, hlam, hphi, ht01, ht0b, ht5b, p1963_1, u5ehi9]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [hlam, p1963_0]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      rcases p1963_3 (m.d 0 1) (by simp) with h1971 | h1971
                                      · linarith only [h0, h1971, hlam]
                                      · linarith only [h1732, h1971, hlam]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [h1733, h1929, h1951, h1961, hc12, hlam, hphi, ht01, ht0b, ht5b, p1963_1, u5ehi9]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      rcases p1963_3 (m.d 0 1) (by simp) with h1975 | h1975
                                      · linarith only [h0, h1975, hlam]
                                      · linarith only [h1929, h1975, hlam]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [h1732, hlam, p1963_0]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [h1949, hlam, p1963_1]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [hlam, p1963_0]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [h1952, hlam, p1963_1]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [h1954, hlam, p1963_1]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [h1929, h1951, h1961, hc14, hlam, hphi, ht01, ht0b, ht5b, p1963_1, u5ehi9]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [h1950, hlam, p1963_1]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      rcases p1963_3 (m.d 0 1) (by simp) with h1985 | h1985
                                      · linarith only [h1733, h1985, hlam]
                                      · linarith only [h1732, h1985, hlam]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [hlam, p1963_0]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      rcases p1963_3 (m.d 0 1) (by simp) with h1989 | h1989
                                      · linarith only [h1733, h1989, hlam]
                                      · linarith only [h1929, h1989, hlam]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [h1929, hlam, p1963_0]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [h1951, hlam, p1963_1]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [hc13, hlam, hphi, ht34, ht45, p1963_1, u5elo1]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [h1956, hlam, p1963_0]
                                    · have p1963_0 := h1963c.1
                                      have p1963_1 := h1963c.2.1
                                      have p1963_2 := h1963c.2.2.1
                                      have p1963_3 := h1963c.2.2.2
                                      linarith only [hlam, p1963_0]
                                  · linarith only [h1733, h1929, h1951, h1952, h1961, h1962, hlam]
                                · linarith only [h1733, h1929, h1952, h1956, h1957, h1961, hc23, hc34, hlam, hphi]
                          · linarith only [h1733, h1929, h1948, h1951, h1956, hc04, hlam, hphi, ht0b, ht5b, u5ehi7]
                    · linarith only [h0, h1951, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h1929, h1950, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
                · linarith only [h0, h1929, h1949, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
              · linarith only [h1733, h1929, h1948, hlam, hphi, u5ehi6, u5elo4]
        · linarith only [h0, h1929, h1931, hlam, hphi, u5ehi6, u5elo2]
      · linarith only [h0, h1732, h1930, hlam]
    · linarith only [h1732, h1929, hc13, hlam, hphi, ht34, ht45, u5elo1]

set_option maxHeartbeats 6700000 in
set_option maxHeartbeats 6700000 in
theorem r1l7_11_13_25_L_I_L_I_M_LR_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1732 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2007 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h1bigk := hb1.1
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
  rcases m.htr 0 1 5 (by decide) (by decide) with h2008 | h2008
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2009 | h2009
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2010 | h2010
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2011 | h2011
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2012 | h2012
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2013 | h2013
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2014 | h2014
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2015 | h2015
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2016 | h2016
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2017 | h2017
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2018 | h2018
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2019 | h2019
                        · linarith only [h1732, h2007, h2014, h2019, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2021 | h2021
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2022 | h2022
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2023 | h2023
                              · linarith only [h2015, h2019, h2023, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2025 | h2025
                                · linarith only [h2015, h2019, h2021, h2025, hlam]
                                · rcases h1bigk with h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c
                                  · have p2027_0 := h2027c.1
                                    have p2027_1 := h2027c.2.1
                                    have p2027_2 := h2027c.2.2.1
                                    have p2027_3 := h2027c.2.2.2
                                    linarith only [hlam, p2027_0]
                                  · have p2027_0 := h2027c.1
                                    have p2027_1 := h2027c.2.1
                                    have p2027_2 := h2027c.2.2.1
                                    have p2027_3 := h2027c.2.2.2
                                    linarith only [h0, hlam, p2027_0]
                                  · have p2027_0 := h2027c.1
                                    have p2027_1 := h2027c.2.1
                                    have p2027_2 := h2027c.2.2.1
                                    have p2027_3 := h2027c.2.2.2
                                    linarith only [h1732, hlam, p2027_0]
                                  · have p2027_0 := h2027c.1
                                    have p2027_1 := h2027c.2.1
                                    have p2027_2 := h2027c.2.2.1
                                    have p2027_3 := h2027c.2.2.2
                                    rcases p2027_3 (m.d 0 1) (by simp) with h2031 | h2031
                                    · rcases p2027_3 (m.d 1 2) (by simp) with h2032 | h2032
                                      · rcases p2027_3 (m.d 1 3) (by simp) with h2033 | h2033
                                        · rcases p2027_3 (m.d 1 4) (by simp) with h2034 | h2034
                                          · linarith only [h2034, hlam, p2027_0]
                                          · rcases p2027_3 (m.d 1 5) (by simp) with h2036 | h2036
                                            · linarith only [h2008, h2036, hlam]
                                            · linarith only [h2019, h2036, hlam]
                                        · linarith only [h2017, h2033, hlam]
                                      · linarith only [h2015, h2032, hlam]
                                    · linarith only [h2031, hlam, p2027_0]
                                  · have p2027_0 := h2027c.1
                                    have p2027_1 := h2027c.2.1
                                    have p2027_2 := h2027c.2.2.1
                                    have p2027_3 := h2027c.2.2.2
                                    linarith only [h1732, h2014, h2016, h2022, hc12, hlam, hphi, ht01, ht0b, ht5b, p2027_1, u5ehi8]
                                  · have p2027_0 := h2027c.1
                                    have p2027_1 := h2027c.2.1
                                    have p2027_2 := h2027c.2.2.1
                                    have p2027_3 := h2027c.2.2.2
                                    linarith only [h2007, h2013, h2019, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2027_1]
                                  · have p2027_0 := h2027c.1
                                    have p2027_1 := h2027c.2.1
                                    have p2027_2 := h2027c.2.2.1
                                    have p2027_3 := h2027c.2.2.2
                                    linarith only [hlam, p2027_0]
                                  · have p2027_0 := h2027c.1
                                    have p2027_1 := h2027c.2.1
                                    have p2027_2 := h2027c.2.2.1
                                    have p2027_3 := h2027c.2.2.2
                                    linarith only [h1732, h2007, h2013, h2015, h2019, h2021, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2027_1]
                                  · have p2027_0 := h2027c.1
                                    have p2027_1 := h2027c.2.1
                                    have p2027_2 := h2027c.2.2.1
                                    have p2027_3 := h2027c.2.2.2
                                    linarith only [h0, h2007, h2013, h2019, hlam, p2027_2]
                                  · have p2027_0 := h2027c.1
                                    have p2027_1 := h2027c.2.1
                                    have p2027_2 := h2027c.2.2.1
                                    have p2027_3 := h2027c.2.2.2
                                    rcases p2027_3 (m.d 0 1) (by simp) with h2047 | h2047
                                    · linarith only [h0, h2047, hlam]
                                    · linarith only [h2008, h2047, hlam]
                                  · have p2027_0 := h2027c.1
                                    have p2027_1 := h2027c.2.1
                                    have p2027_2 := h2027c.2.2.1
                                    have p2027_3 := h2027c.2.2.2
                                    linarith only [h2007, h2013, h2014, h2015, h2019, h2021, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2027_1]
                                  · have p2027_0 := h2027c.1
                                    have p2027_1 := h2027c.2.1
                                    have p2027_2 := h2027c.2.2.1
                                    have p2027_3 := h2027c.2.2.2
                                    linarith only [h2014, hlam, p2027_1]
                                  · have p2027_0 := h2027c.1
                                    have p2027_1 := h2027c.2.1
                                    have p2027_2 := h2027c.2.2.1
                                    have p2027_3 := h2027c.2.2.2
                                    linarith only [hlam, p2027_0]
                                  · have p2027_0 := h2027c.1
                                    have p2027_1 := h2027c.2.1
                                    have p2027_2 := h2027c.2.2.1
                                    have p2027_3 := h2027c.2.2.2
                                    linarith only [h1732, h2007, h2013, h2019, hlam, p2027_2]
                                  · have p2027_0 := h2027c.1
                                    have p2027_1 := h2027c.2.1
                                    have p2027_2 := h2027c.2.2.1
                                    have p2027_3 := h2027c.2.2.2
                                    rcases p2027_3 (m.d 0 1) (by simp) with h2054 | h2054
                                    · linarith only [h1732, h2054, hlam]
                                    · linarith only [h2008, h2054, hlam]
                                  · have p2027_0 := h2027c.1
                                    have p2027_1 := h2027c.2.1
                                    have p2027_2 := h2027c.2.2.1
                                    have p2027_3 := h2027c.2.2.2
                                    linarith only [h2007, hlam, p2027_0]
                                  · have p2027_0 := h2027c.1
                                    have p2027_1 := h2027c.2.1
                                    have p2027_2 := h2027c.2.2.1
                                    have p2027_3 := h2027c.2.2.2
                                    linarith only [h2015, hlam, p2027_1]
                                  · have p2027_0 := h2027c.1
                                    have p2027_1 := h2027c.2.1
                                    have p2027_2 := h2027c.2.2.1
                                    have p2027_3 := h2027c.2.2.2
                                    linarith only [h2017, hlam, p2027_0]
                                  · have p2027_0 := h2027c.1
                                    have p2027_1 := h2027c.2.1
                                    have p2027_2 := h2027c.2.2.1
                                    have p2027_3 := h2027c.2.2.2
                                    linarith only [hlam, p2027_0]
                                  · have p2027_0 := h2027c.1
                                    have p2027_1 := h2027c.2.1
                                    have p2027_2 := h2027c.2.2.1
                                    have p2027_3 := h2027c.2.2.2
                                    linarith only [h2019, hlam, p2027_1]
                                  · have p2027_0 := h2027c.1
                                    have p2027_1 := h2027c.2.1
                                    have p2027_2 := h2027c.2.2.1
                                    have p2027_3 := h2027c.2.2.2
                                    linarith only [h2008, hlam, p2027_0]
                                  · have p2027_0 := h2027c.1
                                    have p2027_1 := h2027c.2.1
                                    have p2027_2 := h2027c.2.2.1
                                    have p2027_3 := h2027c.2.2.2
                                    linarith only [h2016, hlam, p2027_1]
                                  · have p2027_0 := h2027c.1
                                    have p2027_1 := h2027c.2.1
                                    have p2027_2 := h2027c.2.2.1
                                    have p2027_3 := h2027c.2.2.2
                                    linarith only [h2018, hlam, p2027_0]
                                  · have p2027_0 := h2027c.1
                                    have p2027_1 := h2027c.2.1
                                    have p2027_2 := h2027c.2.2.1
                                    have p2027_3 := h2027c.2.2.2
                                    linarith only [h2015, h2021, hc34, hlam, hphi, ht45, p2027_1, u5elo1]
                                  · have p2027_0 := h2027c.1
                                    have p2027_1 := h2027c.2.1
                                    have p2027_2 := h2027c.2.2.1
                                    have p2027_3 := h2027c.2.2.2
                                    linarith only [hlam, p2027_0]
                            · linarith only [h1732, h2007, h2013, h2018, h2019, h2021, h2022, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h1732, h2007, h2013, h2014, h2017, h2019, h2021, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h1732, h2007, h2013, h2018, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
                    · linarith only [h1732, h2007, h2013, h2017, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
                  · linarith only [h0, h2007, h2013, h2016, hlam, hphi, u5ehi9, u5elo2]
                · linarith only [h0, h2007, h2013, h2015, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
              · linarith only [h0, h2007, h2013, h2014, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2074 | h2074
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2075 | h2075
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2076 | h2076
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2077 | h2077
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2078 | h2078
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2079 | h2079
                        · linarith only [h1732, h2007, h2013, h2074, h2079, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2081 | h2081
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2082 | h2082
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2083 | h2083
                              · linarith only [h2007, h2013, h2075, h2083, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2085 | h2085
                                · linarith only [h2007, h2013, h2075, h2081, h2085, hlam]
                                · rcases h1bigk with h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c | h2087c
                                  · have p2087_0 := h2087c.1
                                    have p2087_1 := h2087c.2.1
                                    have p2087_2 := h2087c.2.2.1
                                    have p2087_3 := h2087c.2.2.2
                                    linarith only [hlam, p2087_0]
                                  · have p2087_0 := h2087c.1
                                    have p2087_1 := h2087c.2.1
                                    have p2087_2 := h2087c.2.2.1
                                    have p2087_3 := h2087c.2.2.2
                                    linarith only [h0, hlam, p2087_0]
                                  · have p2087_0 := h2087c.1
                                    have p2087_1 := h2087c.2.1
                                    have p2087_2 := h2087c.2.2.1
                                    have p2087_3 := h2087c.2.2.2
                                    linarith only [h1732, hlam, p2087_0]
                                  · have p2087_0 := h2087c.1
                                    have p2087_1 := h2087c.2.1
                                    have p2087_2 := h2087c.2.2.1
                                    have p2087_3 := h2087c.2.2.2
                                    rcases p2087_3 (m.d 0 1) (by simp) with h2091 | h2091
                                    · rcases p2087_3 (m.d 1 2) (by simp) with h2092 | h2092
                                      · rcases p2087_3 (m.d 1 3) (by simp) with h2093 | h2093
                                        · rcases p2087_3 (m.d 1 4) (by simp) with h2094 | h2094
                                          · linarith only [h2094, hlam, p2087_0]
                                          · rcases p2087_3 (m.d 1 5) (by simp) with h2096 | h2096
                                            · linarith only [h2008, h2096, hlam]
                                            · linarith only [h2079, h2096, hlam]
                                        · linarith only [h2077, h2093, hlam]
                                      · linarith only [h2075, h2092, hlam]
                                    · linarith only [h2091, hlam, p2087_0]
                                  · have p2087_0 := h2087c.1
                                    have p2087_1 := h2087c.2.1
                                    have p2087_2 := h2087c.2.2.1
                                    have p2087_3 := h2087c.2.2.2
                                    linarith only [h1732, h2074, hc12, hlam, hphi, ht01, ht0b, ht5b, p2087_1, u5ehi6]
                                  · have p2087_0 := h2087c.1
                                    have p2087_1 := h2087c.2.1
                                    have p2087_2 := h2087c.2.2.1
                                    have p2087_3 := h2087c.2.2.2
                                    linarith only [h2008, h2076, hc12, hlam, hphi, ht01, ht0b, ht5b, p2087_1, u5ehi7]
                                  · have p2087_0 := h2087c.1
                                    have p2087_1 := h2087c.2.1
                                    have p2087_2 := h2087c.2.2.1
                                    have p2087_3 := h2087c.2.2.2
                                    linarith only [hlam, p2087_0]
                                  · have p2087_0 := h2087c.1
                                    have p2087_1 := h2087c.2.1
                                    have p2087_2 := h2087c.2.2.1
                                    have p2087_3 := h2087c.2.2.2
                                    linarith only [h1732, hc01, hc12, hlam, hphi, p2087_1]
                                  · have p2087_0 := h2087c.1
                                    have p2087_1 := h2087c.2.1
                                    have p2087_2 := h2087c.2.2.1
                                    have p2087_3 := h2087c.2.2.2
                                    rcases p2087_3 (m.d 0 1) (by simp) with h2106 | h2106
                                    · linarith only [h0, h2106, hlam]
                                    · linarith only [h2007, h2106, hlam]
                                  · have p2087_0 := h2087c.1
                                    have p2087_1 := h2087c.2.1
                                    have p2087_2 := h2087c.2.2.1
                                    have p2087_3 := h2087c.2.2.2
                                    rcases p2087_3 (m.d 0 1) (by simp) with h2109 | h2109
                                    · linarith only [h0, h2109, hlam]
                                    · linarith only [h2008, h2109, hlam]
                                  · have p2087_0 := h2087c.1
                                    have p2087_1 := h2087c.2.1
                                    have p2087_2 := h2087c.2.2.1
                                    have p2087_3 := h2087c.2.2.2
                                    linarith only [h2008, h2074, h2076, h2082, hc12, hlam, hphi, ht01, ht0b, ht5b, p2087_1, u5ehi8]
                                  · have p2087_0 := h2087c.1
                                    have p2087_1 := h2087c.2.1
                                    have p2087_2 := h2087c.2.2.1
                                    have p2087_3 := h2087c.2.2.2
                                    linarith only [h2074, hlam, p2087_1]
                                  · have p2087_0 := h2087c.1
                                    have p2087_1 := h2087c.2.1
                                    have p2087_2 := h2087c.2.2.1
                                    have p2087_3 := h2087c.2.2.2
                                    linarith only [hlam, p2087_0]
                                  · have p2087_0 := h2087c.1
                                    have p2087_1 := h2087c.2.1
                                    have p2087_2 := h2087c.2.2.1
                                    have p2087_3 := h2087c.2.2.2
                                    rcases p2087_3 (m.d 0 1) (by simp) with h2115 | h2115
                                    · linarith only [h1732, h2115, hlam]
                                    · linarith only [h2007, h2115, hlam]
                                  · have p2087_0 := h2087c.1
                                    have p2087_1 := h2087c.2.1
                                    have p2087_2 := h2087c.2.2.1
                                    have p2087_3 := h2087c.2.2.2
                                    rcases p2087_3 (m.d 0 1) (by simp) with h2118 | h2118
                                    · linarith only [h1732, h2118, hlam]
                                    · linarith only [h2008, h2118, hlam]
                                  · have p2087_0 := h2087c.1
                                    have p2087_1 := h2087c.2.1
                                    have p2087_2 := h2087c.2.2.1
                                    have p2087_3 := h2087c.2.2.2
                                    linarith only [h2007, hlam, p2087_0]
                                  · have p2087_0 := h2087c.1
                                    have p2087_1 := h2087c.2.1
                                    have p2087_2 := h2087c.2.2.1
                                    have p2087_3 := h2087c.2.2.2
                                    linarith only [h2075, hlam, p2087_1]
                                  · have p2087_0 := h2087c.1
                                    have p2087_1 := h2087c.2.1
                                    have p2087_2 := h2087c.2.2.1
                                    have p2087_3 := h2087c.2.2.2
                                    linarith only [h2077, hlam, p2087_0]
                                  · have p2087_0 := h2087c.1
                                    have p2087_1 := h2087c.2.1
                                    have p2087_2 := h2087c.2.2.1
                                    have p2087_3 := h2087c.2.2.2
                                    linarith only [hlam, p2087_0]
                                  · have p2087_0 := h2087c.1
                                    have p2087_1 := h2087c.2.1
                                    have p2087_2 := h2087c.2.2.1
                                    have p2087_3 := h2087c.2.2.2
                                    linarith only [h2079, hlam, p2087_1]
                                  · have p2087_0 := h2087c.1
                                    have p2087_1 := h2087c.2.1
                                    have p2087_2 := h2087c.2.2.1
                                    have p2087_3 := h2087c.2.2.2
                                    linarith only [h2008, hlam, p2087_0]
                                  · have p2087_0 := h2087c.1
                                    have p2087_1 := h2087c.2.1
                                    have p2087_2 := h2087c.2.2.1
                                    have p2087_3 := h2087c.2.2.2
                                    linarith only [h2076, hlam, p2087_1]
                                  · have p2087_0 := h2087c.1
                                    have p2087_1 := h2087c.2.1
                                    have p2087_2 := h2087c.2.2.1
                                    have p2087_3 := h2087c.2.2.2
                                    linarith only [h2078, hlam, p2087_0]
                                  · have p2087_0 := h2087c.1
                                    have p2087_1 := h2087c.2.1
                                    have p2087_2 := h2087c.2.2.1
                                    have p2087_3 := h2087c.2.2.2
                                    linarith only [hc14, hlam, hphi, ht45, p2087_1, u5elo1]
                                  · have p2087_0 := h2087c.1
                                    have p2087_1 := h2087c.2.1
                                    have p2087_2 := h2087c.2.2.1
                                    have p2087_3 := h2087c.2.2.2
                                    linarith only [hlam, p2087_0]
                            · linarith only [h2008, h2078, h2081, h2082, hc34, hlam, hphi, ht45, u5elo0]
                          · linarith only [h2011, h2013, h2081, hc23, hlam, hphi, ht34, ht45, u5elo4]
                      · linarith only [h1732, h2008, h2078, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi6]
                    · linarith only [h1732, h2008, h2076, h2077, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                  · linarith only [h1732, h2008, h2074, h2076, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
                · linarith only [h1732, h2008, h2074, h2075, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
              · linarith only [h0, h2008, h2074, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
          · linarith only [h1732, h2008, h2012, hlam, hphi, u5ehi6, u5elo3]
        · linarith only [h1732, h2007, h2011, hlam]
      · linarith only [h2009, h2010, hc23, hlam, hphi, ht34, ht45, u5elo2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2141 | h2141
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2142 | h2142
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2143 | h2143
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2144 | h2144
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2145 | h2145
              · linarith only [h0, h2007, h2009, h2144, h2145, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
              · linarith only [h0, h2007, h2144, h2145, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2148 | h2148
              · linarith only [h0, h2008, h2009, h2148, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi6]
              · linarith only [h0, h2008, h2148, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
          · linarith only [h0, h2008, h2009, h2143, hlam, hphi, u5ehi6, u5elo3]
        · linarith only [h0, h2007, h2009, h2142, hlam]
      · linarith only [h0, h2008, h2141, hlam, hphi, u5ehi6, u5elo2]
  · linarith only [h2007, h2008, hc14, hlam, hphi, ht45, u5elo1]

set_option maxHeartbeats 6700000 in
set_option maxHeartbeats 6700000 in
theorem r1l7_11_13_25_L_I_L_I_M_LR_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1732 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2007 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2155 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h1bigk := hb1.1
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
  rcases m.htr 0 2 3 (by decide) (by decide) with h2156 | h2156
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2157 | h2157
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2158 | h2158
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2159 | h2159
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2160 | h2160
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2161 | h2161
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2162 | h2162
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2163 | h2163
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2164 | h2164
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2165 | h2165
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2166 | h2166
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2167 | h2167
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2168 | h2168
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2169 | h2169
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2170 | h2170
                              · linarith only [h2156, h2167, h2170, hc02, hlam, hphi, ht0b, ht5b, u5ehi9]
                              · rcases h1bigk with h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c | h2172c
                                · have p2172_0 := h2172c.1
                                  have p2172_1 := h2172c.2.1
                                  have p2172_2 := h2172c.2.2.1
                                  have p2172_3 := h2172c.2.2.2
                                  linarith only [hlam, p2172_0]
                                · have p2172_0 := h2172c.1
                                  have p2172_1 := h2172c.2.1
                                  have p2172_2 := h2172c.2.2.1
                                  have p2172_3 := h2172c.2.2.2
                                  linarith only [h0, hlam, p2172_0]
                                · have p2172_0 := h2172c.1
                                  have p2172_1 := h2172c.2.1
                                  have p2172_2 := h2172c.2.2.1
                                  have p2172_3 := h2172c.2.2.2
                                  linarith only [h1732, hlam, p2172_0]
                                · have p2172_0 := h2172c.1
                                  have p2172_1 := h2172c.2.1
                                  have p2172_2 := h2172c.2.2.1
                                  have p2172_3 := h2172c.2.2.2
                                  linarith only [h2007, hlam, p2172_0]
                                · have p2172_0 := h2172c.1
                                  have p2172_1 := h2172c.2.1
                                  have p2172_2 := h2172c.2.2.1
                                  have p2172_3 := h2172c.2.2.2
                                  linarith only [h2007, h2163, h2164, h2169, h2170, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2172_1]
                                · have p2172_0 := h2172c.1
                                  have p2172_1 := h2172c.2.1
                                  have p2172_2 := h2172c.2.2.1
                                  have p2172_3 := h2172c.2.2.2
                                  linarith only [h2155, h2163, h2169, h2170, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2172_1]
                                · have p2172_0 := h2172c.1
                                  have p2172_1 := h2172c.2.1
                                  have p2172_2 := h2172c.2.2.1
                                  have p2172_3 := h2172c.2.2.2
                                  linarith only [hlam, p2172_0]
                                · have p2172_0 := h2172c.1
                                  have p2172_1 := h2172c.2.1
                                  have p2172_2 := h2172c.2.2.1
                                  have p2172_3 := h2172c.2.2.2
                                  linarith only [h1732, h2155, h2163, h2169, h2170, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2172_1]
                                · have p2172_0 := h2172c.1
                                  have p2172_1 := h2172c.2.1
                                  have p2172_2 := h2172c.2.2.1
                                  have p2172_3 := h2172c.2.2.2
                                  linarith only [h2007, h2155, h2163, h2169, h2170, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2172_1]
                                · have p2172_0 := h2172c.1
                                  have p2172_1 := h2172c.2.1
                                  have p2172_2 := h2172c.2.2.1
                                  have p2172_3 := h2172c.2.2.2
                                  rcases p2172_3 (m.d 0 1) (by simp) with h2182 | h2182
                                  · linarith only [h0, h2182, hlam]
                                  · linarith only [h2155, h2182, hlam]
                                · have p2172_0 := h2172c.1
                                  have p2172_1 := h2172c.2.1
                                  have p2172_2 := h2172c.2.2.1
                                  have p2172_3 := h2172c.2.2.2
                                  linarith only [h2155, h2163, h2169, h2170, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2172_1]
                                · have p2172_0 := h2172c.1
                                  have p2172_1 := h2172c.2.1
                                  have p2172_2 := h2172c.2.2.1
                                  have p2172_3 := h2172c.2.2.2
                                  linarith only [h2161, hlam, p2172_1]
                                · have p2172_0 := h2172c.1
                                  have p2172_1 := h2172c.2.1
                                  have p2172_2 := h2172c.2.2.1
                                  have p2172_3 := h2172c.2.2.2
                                  linarith only [hlam, p2172_0]
                                · have p2172_0 := h2172c.1
                                  have p2172_1 := h2172c.2.1
                                  have p2172_2 := h2172c.2.2.1
                                  have p2172_3 := h2172c.2.2.2
                                  linarith only [h2007, h2155, h2161, h2163, h2169, h2170, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2172_1]
                                · have p2172_0 := h2172c.1
                                  have p2172_1 := h2172c.2.1
                                  have p2172_2 := h2172c.2.2.1
                                  have p2172_3 := h2172c.2.2.2
                                  rcases p2172_3 (m.d 0 1) (by simp) with h2189 | h2189
                                  · linarith only [h1732, h2189, hlam]
                                  · linarith only [h2155, h2189, hlam]
                                · have p2172_0 := h2172c.1
                                  have p2172_1 := h2172c.2.1
                                  have p2172_2 := h2172c.2.2.1
                                  have p2172_3 := h2172c.2.2.2
                                  linarith only [h2155, h2163, h2169, h2170, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2172_1]
                                · have p2172_0 := h2172c.1
                                  have p2172_1 := h2172c.2.1
                                  have p2172_2 := h2172c.2.2.1
                                  have p2172_3 := h2172c.2.2.2
                                  linarith only [h2162, hlam, p2172_1]
                                · have p2172_0 := h2172c.1
                                  have p2172_1 := h2172c.2.1
                                  have p2172_2 := h2172c.2.2.1
                                  have p2172_3 := h2172c.2.2.2
                                  linarith only [h2164, hlam, p2172_0]
                                · have p2172_0 := h2172c.1
                                  have p2172_1 := h2172c.2.1
                                  have p2172_2 := h2172c.2.2.1
                                  have p2172_3 := h2172c.2.2.2
                                  linarith only [hlam, p2172_0]
                                · have p2172_0 := h2172c.1
                                  have p2172_1 := h2172c.2.1
                                  have p2172_2 := h2172c.2.2.1
                                  have p2172_3 := h2172c.2.2.2
                                  rcases p2172_3 (m.d 0 1) (by simp) with h2196 | h2196
                                  · linarith only [h2007, h2196, hlam]
                                  · linarith only [h2155, h2196, hlam]
                                · have p2172_0 := h2172c.1
                                  have p2172_1 := h2172c.2.1
                                  have p2172_2 := h2172c.2.2.1
                                  have p2172_3 := h2172c.2.2.2
                                  linarith only [h2155, hlam, p2172_0]
                                · have p2172_0 := h2172c.1
                                  have p2172_1 := h2172c.2.1
                                  have p2172_2 := h2172c.2.2.1
                                  have p2172_3 := h2172c.2.2.2
                                  linarith only [h2163, hlam, p2172_1]
                                · have p2172_0 := h2172c.1
                                  have p2172_1 := h2172c.2.1
                                  have p2172_2 := h2172c.2.2.1
                                  have p2172_3 := h2172c.2.2.2
                                  linarith only [h2165, hlam, p2172_0]
                                · have p2172_0 := h2172c.1
                                  have p2172_1 := h2172c.2.1
                                  have p2172_2 := h2172c.2.2.1
                                  have p2172_3 := h2172c.2.2.2
                                  linarith only [h2166, hlam, p2172_0]
                                · have p2172_0 := h2172c.1
                                  have p2172_1 := h2172c.2.1
                                  have p2172_2 := h2172c.2.2.1
                                  have p2172_3 := h2172c.2.2.2
                                  linarith only [hlam, p2172_0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2204 | h2204
                              · linarith only [h0, h2156, h2167, h2169, h2204, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                              · rcases h1bigk with h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c | h2206c
                                · have p2206_0 := h2206c.1
                                  have p2206_1 := h2206c.2.1
                                  have p2206_2 := h2206c.2.2.1
                                  have p2206_3 := h2206c.2.2.2
                                  linarith only [hlam, p2206_0]
                                · have p2206_0 := h2206c.1
                                  have p2206_1 := h2206c.2.1
                                  have p2206_2 := h2206c.2.2.1
                                  have p2206_3 := h2206c.2.2.2
                                  linarith only [h0, hlam, p2206_0]
                                · have p2206_0 := h2206c.1
                                  have p2206_1 := h2206c.2.1
                                  have p2206_2 := h2206c.2.2.1
                                  have p2206_3 := h2206c.2.2.2
                                  linarith only [h1732, hlam, p2206_0]
                                · have p2206_0 := h2206c.1
                                  have p2206_1 := h2206c.2.1
                                  have p2206_2 := h2206c.2.2.1
                                  have p2206_3 := h2206c.2.2.2
                                  linarith only [h2007, hlam, p2206_0]
                                · have p2206_0 := h2206c.1
                                  have p2206_1 := h2206c.2.1
                                  have p2206_2 := h2206c.2.2.1
                                  have p2206_3 := h2206c.2.2.2
                                  linarith only [h0, h2166, h2168, h2169, hc12, hlam, hphi, ht01, ht0b, ht5b, p2206_1, u5ehi8]
                                · have p2206_0 := h2206c.1
                                  have p2206_1 := h2206c.2.1
                                  have p2206_2 := h2206c.2.2.1
                                  have p2206_3 := h2206c.2.2.2
                                  linarith only [h2155, h2166, h2168, h2169, hc12, hlam, hphi, ht01, ht0b, ht5b, p2206_1, u5ehi8]
                                · have p2206_0 := h2206c.1
                                  have p2206_1 := h2206c.2.1
                                  have p2206_2 := h2206c.2.2.1
                                  have p2206_3 := h2206c.2.2.2
                                  linarith only [hlam, p2206_0]
                                · have p2206_0 := h2206c.1
                                  have p2206_1 := h2206c.2.1
                                  have p2206_2 := h2206c.2.2.1
                                  have p2206_3 := h2206c.2.2.2
                                  linarith only [h1732, hc01, hc12, hlam, hphi, p2206_1]
                                · have p2206_0 := h2206c.1
                                  have p2206_1 := h2206c.2.1
                                  have p2206_2 := h2206c.2.2.1
                                  have p2206_3 := h2206c.2.2.2
                                  linarith only [h2007, h2155, h2166, h2168, h2169, hc12, hlam, hphi, ht01, ht0b, ht5b, p2206_1, u5ehi8]
                                · have p2206_0 := h2206c.1
                                  have p2206_1 := h2206c.2.1
                                  have p2206_2 := h2206c.2.2.1
                                  have p2206_3 := h2206c.2.2.2
                                  rcases p2206_3 (m.d 0 1) (by simp) with h2216 | h2216
                                  · linarith only [h0, h2216, hlam]
                                  · linarith only [h2155, h2216, hlam]
                                · have p2206_0 := h2206c.1
                                  have p2206_1 := h2206c.2.1
                                  have p2206_2 := h2206c.2.2.1
                                  have p2206_3 := h2206c.2.2.2
                                  linarith only [h2155, h2166, h2168, h2169, hc13, hlam, hphi, ht01, ht0b, ht5b, p2206_1, u5ehi8]
                                · have p2206_0 := h2206c.1
                                  have p2206_1 := h2206c.2.1
                                  have p2206_2 := h2206c.2.2.1
                                  have p2206_3 := h2206c.2.2.2
                                  linarith only [h2161, hlam, p2206_1]
                                · have p2206_0 := h2206c.1
                                  have p2206_1 := h2206c.2.1
                                  have p2206_2 := h2206c.2.2.1
                                  have p2206_3 := h2206c.2.2.2
                                  linarith only [hlam, p2206_0]
                                · have p2206_0 := h2206c.1
                                  have p2206_1 := h2206c.2.1
                                  have p2206_2 := h2206c.2.2.1
                                  have p2206_3 := h2206c.2.2.2
                                  linarith only [h2007, h2155, h2161, h2166, h2168, h2169, hc12, hlam, hphi, ht01, ht0b, ht5b, p2206_1, u5ehi8]
                                · have p2206_0 := h2206c.1
                                  have p2206_1 := h2206c.2.1
                                  have p2206_2 := h2206c.2.2.1
                                  have p2206_3 := h2206c.2.2.2
                                  rcases p2206_3 (m.d 0 1) (by simp) with h2223 | h2223
                                  · linarith only [h1732, h2223, hlam]
                                  · linarith only [h2155, h2223, hlam]
                                · have p2206_0 := h2206c.1
                                  have p2206_1 := h2206c.2.1
                                  have p2206_2 := h2206c.2.2.1
                                  have p2206_3 := h2206c.2.2.2
                                  linarith only [h2155, h2166, h2168, h2169, hc14, hlam, hphi, ht01, ht0b, ht5b, p2206_1, u5ehi8]
                                · have p2206_0 := h2206c.1
                                  have p2206_1 := h2206c.2.1
                                  have p2206_2 := h2206c.2.2.1
                                  have p2206_3 := h2206c.2.2.2
                                  linarith only [h2162, hlam, p2206_1]
                                · have p2206_0 := h2206c.1
                                  have p2206_1 := h2206c.2.1
                                  have p2206_2 := h2206c.2.2.1
                                  have p2206_3 := h2206c.2.2.2
                                  linarith only [h2164, hlam, p2206_0]
                                · have p2206_0 := h2206c.1
                                  have p2206_1 := h2206c.2.1
                                  have p2206_2 := h2206c.2.2.1
                                  have p2206_3 := h2206c.2.2.2
                                  linarith only [hlam, p2206_0]
                                · have p2206_0 := h2206c.1
                                  have p2206_1 := h2206c.2.1
                                  have p2206_2 := h2206c.2.2.1
                                  have p2206_3 := h2206c.2.2.2
                                  rcases p2206_3 (m.d 0 1) (by simp) with h2230 | h2230
                                  · linarith only [h2007, h2230, hlam]
                                  · linarith only [h2155, h2230, hlam]
                                · have p2206_0 := h2206c.1
                                  have p2206_1 := h2206c.2.1
                                  have p2206_2 := h2206c.2.2.1
                                  have p2206_3 := h2206c.2.2.2
                                  linarith only [h2155, hlam, p2206_0]
                                · have p2206_0 := h2206c.1
                                  have p2206_1 := h2206c.2.1
                                  have p2206_2 := h2206c.2.2.1
                                  have p2206_3 := h2206c.2.2.2
                                  linarith only [h2163, hlam, p2206_1]
                                · have p2206_0 := h2206c.1
                                  have p2206_1 := h2206c.2.1
                                  have p2206_2 := h2206c.2.2.1
                                  have p2206_3 := h2206c.2.2.2
                                  linarith only [h2165, hlam, p2206_0]
                                · have p2206_0 := h2206c.1
                                  have p2206_1 := h2206c.2.1
                                  have p2206_2 := h2206c.2.2.1
                                  have p2206_3 := h2206c.2.2.2
                                  linarith only [h2166, hlam, p2206_0]
                                · have p2206_0 := h2206c.1
                                  have p2206_1 := h2206c.2.1
                                  have p2206_2 := h2206c.2.2.1
                                  have p2206_3 := h2206c.2.2.2
                                  linarith only [hlam, p2206_0]
                          · linarith only [h2165, h2167, h2168, hc34, hlam, hphi, ht45, u5elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2239 | h2239
                          · linarith only [h2158, h2167, h2239, hc03, hlam, hphi, ht0b, ht5b, u5ehi8]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2241 | h2241
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2242 | h2242
                              · rcases h1bigk with h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c | h2243c
                                · have p2243_0 := h2243c.1
                                  have p2243_1 := h2243c.2.1
                                  have p2243_2 := h2243c.2.2.1
                                  have p2243_3 := h2243c.2.2.2
                                  linarith only [hlam, p2243_0]
                                · have p2243_0 := h2243c.1
                                  have p2243_1 := h2243c.2.1
                                  have p2243_2 := h2243c.2.2.1
                                  have p2243_3 := h2243c.2.2.2
                                  linarith only [h0, hlam, p2243_0]
                                · have p2243_0 := h2243c.1
                                  have p2243_1 := h2243c.2.1
                                  have p2243_2 := h2243c.2.2.1
                                  have p2243_3 := h2243c.2.2.2
                                  linarith only [h1732, hlam, p2243_0]
                                · have p2243_0 := h2243c.1
                                  have p2243_1 := h2243c.2.1
                                  have p2243_2 := h2243c.2.2.1
                                  have p2243_3 := h2243c.2.2.2
                                  linarith only [h2007, hlam, p2243_0]
                                · have p2243_0 := h2243c.1
                                  have p2243_1 := h2243c.2.1
                                  have p2243_2 := h2243c.2.2.1
                                  have p2243_3 := h2243c.2.2.2
                                  linarith only [h2007, h2161, h2164, h2165, h2239, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2243_1]
                                · have p2243_0 := h2243c.1
                                  have p2243_1 := h2243c.2.1
                                  have p2243_2 := h2243c.2.2.1
                                  have p2243_3 := h2243c.2.2.2
                                  linarith only [h2155, h2165, h2239, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2243_1]
                                · have p2243_0 := h2243c.1
                                  have p2243_1 := h2243c.2.1
                                  have p2243_2 := h2243c.2.2.1
                                  have p2243_3 := h2243c.2.2.2
                                  linarith only [hlam, p2243_0]
                                · have p2243_0 := h2243c.1
                                  have p2243_1 := h2243c.2.1
                                  have p2243_2 := h2243c.2.2.1
                                  have p2243_3 := h2243c.2.2.2
                                  linarith only [h1732, hc01, hc12, hlam, hphi, p2243_1]
                                · have p2243_0 := h2243c.1
                                  have p2243_1 := h2243c.2.1
                                  have p2243_2 := h2243c.2.2.1
                                  have p2243_3 := h2243c.2.2.2
                                  linarith only [h2007, h2155, h2165, h2239, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2243_1]
                                · have p2243_0 := h2243c.1
                                  have p2243_1 := h2243c.2.1
                                  have p2243_2 := h2243c.2.2.1
                                  have p2243_3 := h2243c.2.2.2
                                  rcases p2243_3 (m.d 0 1) (by simp) with h2253 | h2253
                                  · linarith only [h0, h2253, hlam]
                                  · linarith only [h2155, h2253, hlam]
                                · have p2243_0 := h2243c.1
                                  have p2243_1 := h2243c.2.1
                                  have p2243_2 := h2243c.2.2.1
                                  have p2243_3 := h2243c.2.2.2
                                  linarith only [h2155, h2165, h2239, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2243_1]
                                · have p2243_0 := h2243c.1
                                  have p2243_1 := h2243c.2.1
                                  have p2243_2 := h2243c.2.2.1
                                  have p2243_3 := h2243c.2.2.2
                                  linarith only [h2161, hlam, p2243_1]
                                · have p2243_0 := h2243c.1
                                  have p2243_1 := h2243c.2.1
                                  have p2243_2 := h2243c.2.2.1
                                  have p2243_3 := h2243c.2.2.2
                                  linarith only [hlam, p2243_0]
                                · have p2243_0 := h2243c.1
                                  have p2243_1 := h2243c.2.1
                                  have p2243_2 := h2243c.2.2.1
                                  have p2243_3 := h2243c.2.2.2
                                  linarith only [h2007, h2155, h2161, h2165, h2239, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2243_1]
                                · have p2243_0 := h2243c.1
                                  have p2243_1 := h2243c.2.1
                                  have p2243_2 := h2243c.2.2.1
                                  have p2243_3 := h2243c.2.2.2
                                  rcases p2243_3 (m.d 0 1) (by simp) with h2260 | h2260
                                  · linarith only [h1732, h2260, hlam]
                                  · linarith only [h2155, h2260, hlam]
                                · have p2243_0 := h2243c.1
                                  have p2243_1 := h2243c.2.1
                                  have p2243_2 := h2243c.2.2.1
                                  have p2243_3 := h2243c.2.2.2
                                  linarith only [h2155, h2165, h2239, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2243_1]
                                · have p2243_0 := h2243c.1
                                  have p2243_1 := h2243c.2.1
                                  have p2243_2 := h2243c.2.2.1
                                  have p2243_3 := h2243c.2.2.2
                                  linarith only [h2162, hlam, p2243_1]
                                · have p2243_0 := h2243c.1
                                  have p2243_1 := h2243c.2.1
                                  have p2243_2 := h2243c.2.2.1
                                  have p2243_3 := h2243c.2.2.2
                                  linarith only [h2164, hlam, p2243_0]
                                · have p2243_0 := h2243c.1
                                  have p2243_1 := h2243c.2.1
                                  have p2243_2 := h2243c.2.2.1
                                  have p2243_3 := h2243c.2.2.2
                                  linarith only [hlam, p2243_0]
                                · have p2243_0 := h2243c.1
                                  have p2243_1 := h2243c.2.1
                                  have p2243_2 := h2243c.2.2.1
                                  have p2243_3 := h2243c.2.2.2
                                  rcases p2243_3 (m.d 0 1) (by simp) with h2267 | h2267
                                  · linarith only [h2007, h2267, hlam]
                                  · linarith only [h2155, h2267, hlam]
                                · have p2243_0 := h2243c.1
                                  have p2243_1 := h2243c.2.1
                                  have p2243_2 := h2243c.2.2.1
                                  have p2243_3 := h2243c.2.2.2
                                  linarith only [h2155, hlam, p2243_0]
                                · have p2243_0 := h2243c.1
                                  have p2243_1 := h2243c.2.1
                                  have p2243_2 := h2243c.2.2.1
                                  have p2243_3 := h2243c.2.2.2
                                  linarith only [h2163, hlam, p2243_1]
                                · have p2243_0 := h2243c.1
                                  have p2243_1 := h2243c.2.1
                                  have p2243_2 := h2243c.2.2.1
                                  have p2243_3 := h2243c.2.2.2
                                  linarith only [h2165, hlam, p2243_0]
                                · have p2243_0 := h2243c.1
                                  have p2243_1 := h2243c.2.1
                                  have p2243_2 := h2243c.2.2.1
                                  have p2243_3 := h2243c.2.2.2
                                  linarith only [h2166, hlam, p2243_0]
                                · have p2243_0 := h2243c.1
                                  have p2243_1 := h2243c.2.1
                                  have p2243_2 := h2243c.2.2.1
                                  have p2243_3 := h2243c.2.2.2
                                  linarith only [hlam, p2243_0]
                              · linarith only [h2165, h2167, h2239, h2241, h2242, hc23, hlam, hphi, ht34, ht45, u5elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2276 | h2276
                              · rcases h1bigk with h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c | h2277c
                                · have p2277_0 := h2277c.1
                                  have p2277_1 := h2277c.2.1
                                  have p2277_2 := h2277c.2.2.1
                                  have p2277_3 := h2277c.2.2.2
                                  linarith only [hlam, p2277_0]
                                · have p2277_0 := h2277c.1
                                  have p2277_1 := h2277c.2.1
                                  have p2277_2 := h2277c.2.2.1
                                  have p2277_3 := h2277c.2.2.2
                                  linarith only [h0, hlam, p2277_0]
                                · have p2277_0 := h2277c.1
                                  have p2277_1 := h2277c.2.1
                                  have p2277_2 := h2277c.2.2.1
                                  have p2277_3 := h2277c.2.2.2
                                  linarith only [h1732, hlam, p2277_0]
                                · have p2277_0 := h2277c.1
                                  have p2277_1 := h2277c.2.1
                                  have p2277_2 := h2277c.2.2.1
                                  have p2277_3 := h2277c.2.2.2
                                  linarith only [h2007, hlam, p2277_0]
                                · have p2277_0 := h2277c.1
                                  have p2277_1 := h2277c.2.1
                                  have p2277_2 := h2277c.2.2.1
                                  have p2277_3 := h2277c.2.2.2
                                  linarith only [h2007, h2161, h2164, hc12, hlam, hphi, ht01, ht0b, ht5b, p2277_1, u5ehi6]
                                · have p2277_0 := h2277c.1
                                  have p2277_1 := h2277c.2.1
                                  have p2277_2 := h2277c.2.2.1
                                  have p2277_3 := h2277c.2.2.2
                                  linarith only [h2155, h2165, hc12, hlam, hphi, ht01, ht0b, ht5b, p2277_1, u5ehi8]
                                · have p2277_0 := h2277c.1
                                  have p2277_1 := h2277c.2.1
                                  have p2277_2 := h2277c.2.2.1
                                  have p2277_3 := h2277c.2.2.2
                                  linarith only [hlam, p2277_0]
                                · have p2277_0 := h2277c.1
                                  have p2277_1 := h2277c.2.1
                                  have p2277_2 := h2277c.2.2.1
                                  have p2277_3 := h2277c.2.2.2
                                  linarith only [h1732, hc01, hc12, hlam, hphi, p2277_1]
                                · have p2277_0 := h2277c.1
                                  have p2277_1 := h2277c.2.1
                                  have p2277_2 := h2277c.2.2.1
                                  have p2277_3 := h2277c.2.2.2
                                  linarith only [h2007, h2155, h2165, hc12, hlam, hphi, ht01, ht0b, ht5b, p2277_1, u5ehi8]
                                · have p2277_0 := h2277c.1
                                  have p2277_1 := h2277c.2.1
                                  have p2277_2 := h2277c.2.2.1
                                  have p2277_3 := h2277c.2.2.2
                                  rcases p2277_3 (m.d 0 1) (by simp) with h2287 | h2287
                                  · linarith only [h0, h2287, hlam]
                                  · linarith only [h2155, h2287, hlam]
                                · have p2277_0 := h2277c.1
                                  have p2277_1 := h2277c.2.1
                                  have p2277_2 := h2277c.2.2.1
                                  have p2277_3 := h2277c.2.2.2
                                  linarith only [h2155, h2165, h2167, h2241, h2276, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2277_1]
                                · have p2277_0 := h2277c.1
                                  have p2277_1 := h2277c.2.1
                                  have p2277_2 := h2277c.2.2.1
                                  have p2277_3 := h2277c.2.2.2
                                  linarith only [h2161, hlam, p2277_1]
                                · have p2277_0 := h2277c.1
                                  have p2277_1 := h2277c.2.1
                                  have p2277_2 := h2277c.2.2.1
                                  have p2277_3 := h2277c.2.2.2
                                  linarith only [hlam, p2277_0]
                                · have p2277_0 := h2277c.1
                                  have p2277_1 := h2277c.2.1
                                  have p2277_2 := h2277c.2.2.1
                                  have p2277_3 := h2277c.2.2.2
                                  linarith only [h2007, h2155, h2161, h2165, h2167, h2241, h2276, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2277_1]
                                · have p2277_0 := h2277c.1
                                  have p2277_1 := h2277c.2.1
                                  have p2277_2 := h2277c.2.2.1
                                  have p2277_3 := h2277c.2.2.2
                                  rcases p2277_3 (m.d 0 1) (by simp) with h2294 | h2294
                                  · linarith only [h1732, h2294, hlam]
                                  · linarith only [h2155, h2294, hlam]
                                · have p2277_0 := h2277c.1
                                  have p2277_1 := h2277c.2.1
                                  have p2277_2 := h2277c.2.2.1
                                  have p2277_3 := h2277c.2.2.2
                                  linarith only [h2155, h2165, h2167, h2241, h2276, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2277_1]
                                · have p2277_0 := h2277c.1
                                  have p2277_1 := h2277c.2.1
                                  have p2277_2 := h2277c.2.2.1
                                  have p2277_3 := h2277c.2.2.2
                                  linarith only [h2162, hlam, p2277_1]
                                · have p2277_0 := h2277c.1
                                  have p2277_1 := h2277c.2.1
                                  have p2277_2 := h2277c.2.2.1
                                  have p2277_3 := h2277c.2.2.2
                                  linarith only [h2164, hlam, p2277_0]
                                · have p2277_0 := h2277c.1
                                  have p2277_1 := h2277c.2.1
                                  have p2277_2 := h2277c.2.2.1
                                  have p2277_3 := h2277c.2.2.2
                                  linarith only [hlam, p2277_0]
                                · have p2277_0 := h2277c.1
                                  have p2277_1 := h2277c.2.1
                                  have p2277_2 := h2277c.2.2.1
                                  have p2277_3 := h2277c.2.2.2
                                  rcases p2277_3 (m.d 0 1) (by simp) with h2301 | h2301
                                  · linarith only [h2007, h2301, hlam]
                                  · linarith only [h2155, h2301, hlam]
                                · have p2277_0 := h2277c.1
                                  have p2277_1 := h2277c.2.1
                                  have p2277_2 := h2277c.2.2.1
                                  have p2277_3 := h2277c.2.2.2
                                  linarith only [h2155, hlam, p2277_0]
                                · have p2277_0 := h2277c.1
                                  have p2277_1 := h2277c.2.1
                                  have p2277_2 := h2277c.2.2.1
                                  have p2277_3 := h2277c.2.2.2
                                  linarith only [h2163, hlam, p2277_1]
                                · have p2277_0 := h2277c.1
                                  have p2277_1 := h2277c.2.1
                                  have p2277_2 := h2277c.2.2.1
                                  have p2277_3 := h2277c.2.2.2
                                  linarith only [h2165, hlam, p2277_0]
                                · have p2277_0 := h2277c.1
                                  have p2277_1 := h2277c.2.1
                                  have p2277_2 := h2277c.2.2.1
                                  have p2277_3 := h2277c.2.2.2
                                  linarith only [h2166, hlam, p2277_0]
                                · have p2277_0 := h2277c.1
                                  have p2277_1 := h2277c.2.1
                                  have p2277_2 := h2277c.2.2.1
                                  have p2277_3 := h2277c.2.2.2
                                  linarith only [hlam, p2277_0]
                              · linarith only [h2167, h2276, hc23, hlam, hphi, ht34, ht45, u5elo4]
                      · linarith only [h2007, h2155, h2160, h2166, hc04, hlam, hphi, ht0b, ht5b, u5ehi6]
                    · linarith only [h2007, h2155, h2163, h2164, h2165, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                  · linarith only [h1732, h2155, h2163, h2164, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                · linarith only [h0, h2156, h2158, h2163, hc34, hlam, hphi, ht45, u5elo2]
              · linarith only [h1732, h2155, h2161, h2162, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
            · linarith only [h0, h2155, h2161, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
          · linarith only [h2007, h2155, h2160, hlam, hphi, u5ehi6, u5elo4]
        · linarith only [h2158, h2159, hc34, hlam, hphi, ht45, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2318 | h2318
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2319 | h2319
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2320 | h2320
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2321 | h2321
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2322 | h2322
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2323 | h2323
                  · linarith only [h1732, h2155, h2158, h2320, h2322, h2323, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                  · linarith only [h1732, h2155, h2322, h2323, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                · linarith only [h2321, h2322, hc24, hlam, hphi, ht45, u5elo2]
              · linarith only [h1732, h2155, h2320, h2321, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
            · linarith only [h0, h2155, h2156, h2320, hc02, hlam, hphi, ht0b, ht5b, u5ehi6]
          · linarith only [h1732, h2155, h2158, h2319, hlam, hphi, u5ehi6, u5elo4]
        · linarith only [h1732, h2155, h2318, hlam, hphi, u5ehi6, u5elo3]
    · linarith only [h2156, h2157, hc23, hlam, hphi, ht34, ht45, u5elo2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2332 | h2332
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2333 | h2333
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2334 | h2334
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2335 | h2335
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2336 | h2336
            · linarith only [h0, h2155, h2156, h2336, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi6]
            · linarith only [h0, h2155, h2336, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
          · linarith only [h2007, h2155, h2335, hlam, hphi, u5ehi6, u5elo4]
        · linarith only [h0, h2155, h2156, h2334, hlam, hphi, u5ehi6, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2341 | h2341
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2342 | h2342
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2343 | h2343
            · linarith only [h0, h2155, h2156, h2343, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi6]
            · linarith only [h0, h2155, h2343, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
          · linarith only [h0, h2155, h2156, h2333, h2342, hlam, hphi, u5ehi6, u5elo4]
        · linarith only [h0, h2155, h2156, h2341, hlam, hphi, u5ehi6, u5elo3]
    · linarith only [h0, h2155, h2332, hlam, hphi, u5ehi6, u5elo2]

end R2N4
