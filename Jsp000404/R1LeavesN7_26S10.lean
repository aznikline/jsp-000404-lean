import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_26S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5518000 in
set_option maxHeartbeats 5518000 in
theorem r1l7_13_24_L_I_M_IR_s0_x0_x0_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h3bigk := hb3.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 4 (by decide) (by decide) with h1489 | h1489
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1490 | h1490
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1491 | h1491
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1492 | h1492
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1493 | h1493
          · linarith only [h1489, h1493, h3, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1495 | h1495
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1496 | h1496
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1497 | h1497
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1498 | h1498
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1499 | h1499
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1500 | h1500
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1501 | h1501
                        · linarith only [h1, h1493, h1495, h1501, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h1489, h1492, h1501, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                      · linarith only [h1, h1497, h1500, h3, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h1489, h1498, h1499, h2, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                  · linarith only [h1489, h1492, h1498, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · linarith only [h1489, h1491, h1492, h1493, h1495, h1497, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
              · linarith only [h1490, h1493, h1495, h1496, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
            · linarith only [h1489, h1495, h3, hc12, hc23, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1510 | h1510
          · linarith only [h1489, h1510, h3, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1512 | h1512
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1513 | h1513
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1514 | h1514
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1515 | h1515
                  · linarith only [h1492, h1515, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1517 | h1517
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1518 | h1518
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1519 | h1519
                        · linarith only [h1492, h1512, h1519, h2, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1521 | h1521
                          · linarith only [h1492, h1512, h1517, h1521, h2, hlam]
                          · rcases h3bigk with h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c
                            · have p1523_0 := h1523c.1
                              have p1523_1 := h1523c.2.1
                              have p1523_2 := h1523c.2.2.1
                              have p1523_3 := h1523c.2.2.2
                              linarith only [hlam, p1523_0]
                            · have p1523_0 := h1523c.1
                              have p1523_1 := h1523c.2.1
                              have p1523_2 := h1523c.2.2.1
                              have p1523_3 := h1523c.2.2.2
                              linarith only [h1510, h1512, h1517, hc03, hlam, hphi, ht0b, ht45, ht5b, p1523_1, u4ehi3]
                            · have p1523_0 := h1523c.1
                              have p1523_1 := h1523c.2.1
                              have p1523_2 := h1523c.2.2.1
                              have p1523_3 := h1523c.2.2.2
                              linarith only [h3, hlam, p1523_1]
                            · have p1523_0 := h1523c.1
                              have p1523_1 := h1523c.2.1
                              have p1523_2 := h1523c.2.2.1
                              have p1523_3 := h1523c.2.2.2
                              rcases p1523_3 (m.d 0 3) (by simp) with h1527 | h1527
                              · rcases p1523_3 (m.d 1 3) (by simp) with h1528 | h1528
                                · linarith only [h1, h1528, hlam]
                                · linarith only [h1513, h1528, hlam]
                              · linarith only [h1527, hlam, p1523_0]
                            · have p1523_0 := h1523c.1
                              have p1523_1 := h1523c.2.1
                              have p1523_2 := h1523c.2.2.1
                              have p1523_3 := h1523c.2.2.2
                              rcases p1523_3 (m.d 0 3) (by simp) with h1532 | h1532
                              · rcases p1523_3 (m.d 1 3) (by simp) with h1533 | h1533
                                · linarith only [h1, h1533, hlam]
                                · linarith only [h1514, h1533, hlam]
                              · linarith only [h1532, hlam, p1523_0]
                            · have p1523_0 := h1523c.1
                              have p1523_1 := h1523c.2.1
                              have p1523_2 := h1523c.2.2.1
                              have p1523_3 := h1523c.2.2.2
                              linarith only [h1, hlam, p1523_0]
                            · have p1523_0 := h1523c.1
                              have p1523_1 := h1523c.2.1
                              have p1523_2 := h1523c.2.2.1
                              have p1523_3 := h1523c.2.2.2
                              linarith only [hlam, p1523_0]
                            · have p1523_0 := h1523c.1
                              have p1523_1 := h1523c.2.1
                              have p1523_2 := h1523c.2.2.1
                              have p1523_3 := h1523c.2.2.2
                              linarith only [h1510, hlam, p1523_1]
                            · have p1523_0 := h1523c.1
                              have p1523_1 := h1523c.2.1
                              have p1523_2 := h1523c.2.2.1
                              have p1523_3 := h1523c.2.2.2
                              linarith only [h1, hc01, hlam, hphi, ht0b, ht45, ht5b, p1523_1, u4ehi3]
                            · have p1523_0 := h1523c.1
                              have p1523_1 := h1523c.2.1
                              have p1523_2 := h1523c.2.2.1
                              have p1523_3 := h1523c.2.2.2
                              linarith only [h1, h1521, hc01, hlam, hphi, ht0b, ht45, ht5b, p1523_1, u4ehi3]
                            · have p1523_0 := h1523c.1
                              have p1523_1 := h1523c.2.1
                              have p1523_2 := h1523c.2.2.1
                              have p1523_3 := h1523c.2.2.2
                              linarith only [h0, h1512, h1517, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1523_1, u4ehi3]
                            · have p1523_0 := h1523c.1
                              have p1523_1 := h1523c.2.1
                              have p1523_2 := h1523c.2.2.1
                              have p1523_3 := h1523c.2.2.2
                              linarith only [h1510, h1512, h1517, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1523_1, u4ehi3]
                            · have p1523_0 := h1523c.1
                              have p1523_1 := h1523c.2.1
                              have p1523_2 := h1523c.2.2.1
                              have p1523_3 := h1523c.2.2.2
                              linarith only [hlam, p1523_0]
                            · have p1523_0 := h1523c.1
                              have p1523_1 := h1523c.2.1
                              have p1523_2 := h1523c.2.2.1
                              have p1523_3 := h1523c.2.2.2
                              rcases p1523_3 (m.d 0 3) (by simp) with h1545 | h1545
                              · linarith only [h1545, h3, hlam]
                              · linarith only [h1490, h1545, hlam]
                            · have p1523_0 := h1523c.1
                              have p1523_1 := h1523c.2.1
                              have p1523_2 := h1523c.2.2.1
                              have p1523_3 := h1523c.2.2.2
                              rcases p1523_3 (m.d 0 3) (by simp) with h1548 | h1548
                              · linarith only [h1548, h3, hlam]
                              · linarith only [h1491, h1548, hlam]
                            · have p1523_0 := h1523c.1
                              have p1523_1 := h1523c.2.1
                              have p1523_2 := h1523c.2.2.1
                              have p1523_3 := h1523c.2.2.2
                              linarith only [h1490, hlam, p1523_0]
                            · have p1523_0 := h1523c.1
                              have p1523_1 := h1523c.2.1
                              have p1523_2 := h1523c.2.2.1
                              have p1523_3 := h1523c.2.2.2
                              linarith only [h1513, hlam, p1523_0]
                            · have p1523_0 := h1523c.1
                              have p1523_1 := h1523c.2.1
                              have p1523_2 := h1523c.2.2.1
                              have p1523_3 := h1523c.2.2.2
                              linarith only [h1517, hlam, p1523_0]
                            · have p1523_0 := h1523c.1
                              have p1523_1 := h1523c.2.1
                              have p1523_2 := h1523c.2.2.1
                              have p1523_3 := h1523c.2.2.2
                              linarith only [hlam, p1523_0]
                            · have p1523_0 := h1523c.1
                              have p1523_1 := h1523c.2.1
                              have p1523_2 := h1523c.2.2.1
                              have p1523_3 := h1523c.2.2.2
                              linarith only [h1521, hlam, p1523_1]
                            · have p1523_0 := h1523c.1
                              have p1523_1 := h1523c.2.1
                              have p1523_2 := h1523c.2.2.1
                              have p1523_3 := h1523c.2.2.2
                              linarith only [h1491, hlam, p1523_0]
                            · have p1523_0 := h1523c.1
                              have p1523_1 := h1523c.2.1
                              have p1523_2 := h1523c.2.2.1
                              have p1523_3 := h1523c.2.2.2
                              linarith only [h1514, hlam, p1523_0]
                            · have p1523_0 := h1523c.1
                              have p1523_1 := h1523c.2.1
                              have p1523_2 := h1523c.2.2.1
                              have p1523_3 := h1523c.2.2.2
                              linarith only [h1518, hlam, p1523_0]
                            · have p1523_0 := h1523c.1
                              have p1523_1 := h1523c.2.1
                              have p1523_2 := h1523c.2.2.1
                              have p1523_3 := h1523c.2.2.2
                              linarith only [h1491, hc03, hlam, hphi, ht0b, ht45, ht5b, p1523_1, u4ehi3]
                            · have p1523_0 := h1523c.1
                              have p1523_1 := h1523c.2.1
                              have p1523_2 := h1523c.2.2.1
                              have p1523_3 := h1523c.2.2.2
                              linarith only [hlam, p1523_0]
                      · linarith only [h1, h1514, h1518, h3, hlam]
                    · linarith only [h0, h1512, h1517, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                · linarith only [h1491, h1513, h1514, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
              · linarith only [h1490, h1510, h1512, h1513, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
            · linarith only [h1489, h1512, h3, hc12, hc23, hlam, hphi]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1566 | h1566
        · linarith only [h1489, h1491, h1566, h3, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1568 | h1568
          · linarith only [h1489, h1568, h3, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1570 | h1570
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1571 | h1571
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1572 | h1572
                · linarith only [h0, h1491, h1570, h1572, h3, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1574 | h1574
                  · linarith only [h1566, h1574, h2, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1576 | h1576
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1577 | h1577
                      · linarith only [h0, h1491, h1570, h1576, h1577, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                      · linarith only [h0, h1570, h1576, h1577, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                    · linarith only [h0, h1570, h1576, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
              · linarith only [h1490, h1491, h1571, hc13, hc35, hlam, hphi]
            · linarith only [h1489, h1570, h3, hc12, hc23, hlam, hphi]
    · linarith only [h1489, h1490, h3, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1584 | h1584
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1585 | h1585
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1586 | h1586
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1587 | h1587
          · linarith only [h0, h1587, h3, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1589 | h1589
            · linarith only [h0, h1489, h1589, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1591 | h1591
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1592 | h1592
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1593 | h1593
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1594 | h1594
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1595 | h1595
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1596 | h1596
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1597 | h1597
                          · linarith only [h1, h1591, h1597, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h1593, h1597, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                        · linarith only [h1, h1489, h1591, h1593, h1596, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                      · linarith only [h1, h1592, h1595, h3, hlam]
                    · linarith only [h1584, h1594, h3, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1603 | h1603
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1604 | h1604
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1605 | h1605
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1606 | h1606
                          · linarith only [h1591, h1593, h1606, hlam]
                          · rcases h3bigk with h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c | h1608c
                            · have p1608_0 := h1608c.1
                              have p1608_1 := h1608c.2.1
                              have p1608_2 := h1608c.2.2.1
                              have p1608_3 := h1608c.2.2.2
                              linarith only [hlam, p1608_0]
                            · have p1608_0 := h1608c.1
                              have p1608_1 := h1608c.2.1
                              have p1608_2 := h1608c.2.2.1
                              have p1608_3 := h1608c.2.2.2
                              linarith only [h1592, h1606, hc03, hlam, hphi, ht0b, ht45, ht5b, p1608_1, u4ehi3]
                            · have p1608_0 := h1608c.1
                              have p1608_1 := h1608c.2.1
                              have p1608_2 := h1608c.2.2.1
                              have p1608_3 := h1608c.2.2.2
                              linarith only [h3, hlam, p1608_1]
                            · have p1608_0 := h1608c.1
                              have p1608_1 := h1608c.2.1
                              have p1608_2 := h1608c.2.2.1
                              have p1608_3 := h1608c.2.2.2
                              rcases p1608_3 (m.d 0 3) (by simp) with h1612 | h1612
                              · rcases p1608_3 (m.d 1 3) (by simp) with h1613 | h1613
                                · linarith only [h1, h1613, hlam]
                                · linarith only [h1591, h1613, hlam]
                              · linarith only [h1612, hlam, p1608_0]
                            · have p1608_0 := h1608c.1
                              have p1608_1 := h1608c.2.1
                              have p1608_2 := h1608c.2.2.1
                              have p1608_3 := h1608c.2.2.2
                              rcases p1608_3 (m.d 0 3) (by simp) with h1617 | h1617
                              · rcases p1608_3 (m.d 1 3) (by simp) with h1618 | h1618
                                · linarith only [h1, h1618, hlam]
                                · linarith only [h1592, h1618, hlam]
                              · linarith only [h1617, hlam, p1608_0]
                            · have p1608_0 := h1608c.1
                              have p1608_1 := h1608c.2.1
                              have p1608_2 := h1608c.2.2.1
                              have p1608_3 := h1608c.2.2.2
                              linarith only [h1, hlam, p1608_0]
                            · have p1608_0 := h1608c.1
                              have p1608_1 := h1608c.2.1
                              have p1608_2 := h1608c.2.2.1
                              have p1608_3 := h1608c.2.2.2
                              linarith only [hlam, p1608_0]
                            · have p1608_0 := h1608c.1
                              have p1608_1 := h1608c.2.1
                              have p1608_2 := h1608c.2.2.1
                              have p1608_3 := h1608c.2.2.2
                              linarith only [h1587, hlam, p1608_1]
                            · have p1608_0 := h1608c.1
                              have p1608_1 := h1608c.2.1
                              have p1608_2 := h1608c.2.2.1
                              have p1608_3 := h1608c.2.2.2
                              linarith only [h1, hc01, hlam, hphi, ht0b, ht45, ht5b, p1608_1, u4ehi3]
                            · have p1608_0 := h1608c.1
                              have p1608_1 := h1608c.2.1
                              have p1608_2 := h1608c.2.2.1
                              have p1608_3 := h1608c.2.2.2
                              linarith only [h1, h1606, hc01, hlam, hphi, ht0b, ht45, ht5b, p1608_1, u4ehi3]
                            · have p1608_0 := h1608c.1
                              have p1608_1 := h1608c.2.1
                              have p1608_2 := h1608c.2.2.1
                              have p1608_3 := h1608c.2.2.2
                              linarith only [h1584, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1608_1, u4ehi3]
                            · have p1608_0 := h1608c.1
                              have p1608_1 := h1608c.2.1
                              have p1608_2 := h1608c.2.2.1
                              have p1608_3 := h1608c.2.2.2
                              linarith only [h1591, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1608_1, u4ehi3]
                            · have p1608_0 := h1608c.1
                              have p1608_1 := h1608c.2.1
                              have p1608_2 := h1608c.2.2.1
                              have p1608_3 := h1608c.2.2.2
                              linarith only [hlam, p1608_0]
                            · have p1608_0 := h1608c.1
                              have p1608_1 := h1608c.2.1
                              have p1608_2 := h1608c.2.2.1
                              have p1608_3 := h1608c.2.2.2
                              rcases p1608_3 (m.d 0 3) (by simp) with h1630 | h1630
                              · linarith only [h1630, h3, hlam]
                              · linarith only [h1584, h1630, hlam]
                            · have p1608_0 := h1608c.1
                              have p1608_1 := h1608c.2.1
                              have p1608_2 := h1608c.2.2.1
                              have p1608_3 := h1608c.2.2.2
                              rcases p1608_3 (m.d 0 3) (by simp) with h1633 | h1633
                              · linarith only [h1633, h3, hlam]
                              · linarith only [h1585, h1633, hlam]
                            · have p1608_0 := h1608c.1
                              have p1608_1 := h1608c.2.1
                              have p1608_2 := h1608c.2.2.1
                              have p1608_3 := h1608c.2.2.2
                              linarith only [h1584, hlam, p1608_0]
                            · have p1608_0 := h1608c.1
                              have p1608_1 := h1608c.2.1
                              have p1608_2 := h1608c.2.2.1
                              have p1608_3 := h1608c.2.2.2
                              linarith only [h1591, hlam, p1608_0]
                            · have p1608_0 := h1608c.1
                              have p1608_1 := h1608c.2.1
                              have p1608_2 := h1608c.2.2.1
                              have p1608_3 := h1608c.2.2.2
                              linarith only [h1603, hlam, p1608_0]
                            · have p1608_0 := h1608c.1
                              have p1608_1 := h1608c.2.1
                              have p1608_2 := h1608c.2.2.1
                              have p1608_3 := h1608c.2.2.2
                              linarith only [hlam, p1608_0]
                            · have p1608_0 := h1608c.1
                              have p1608_1 := h1608c.2.1
                              have p1608_2 := h1608c.2.2.1
                              have p1608_3 := h1608c.2.2.2
                              linarith only [h1606, hlam, p1608_1]
                            · have p1608_0 := h1608c.1
                              have p1608_1 := h1608c.2.1
                              have p1608_2 := h1608c.2.2.1
                              have p1608_3 := h1608c.2.2.2
                              linarith only [h1585, hlam, p1608_0]
                            · have p1608_0 := h1608c.1
                              have p1608_1 := h1608c.2.1
                              have p1608_2 := h1608c.2.2.1
                              have p1608_3 := h1608c.2.2.2
                              linarith only [h1592, hlam, p1608_0]
                            · have p1608_0 := h1608c.1
                              have p1608_1 := h1608c.2.1
                              have p1608_2 := h1608c.2.2.1
                              have p1608_3 := h1608c.2.2.2
                              linarith only [h1604, hlam, p1608_0]
                            · have p1608_0 := h1608c.1
                              have p1608_1 := h1608c.2.1
                              have p1608_2 := h1608c.2.2.1
                              have p1608_3 := h1608c.2.2.2
                              linarith only [h1592, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p1608_1, u4ehi3]
                            · have p1608_0 := h1608c.1
                              have p1608_1 := h1608c.2.1
                              have p1608_2 := h1608c.2.2.1
                              have p1608_3 := h1608c.2.2.2
                              linarith only [hlam, p1608_0]
                        · linarith only [h1489, h1586, h1605, hlam]
                      · linarith only [h0, h1, h1592, h1604, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h1584, h1586, h1591, h1593, h1603, h3, hlam]
                · linarith only [h1585, h1591, h1592, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1650 | h1650
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1651 | h1651
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1652 | h1652
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1653 | h1653
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1654 | h1654
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1655 | h1655
                          · linarith only [h1584, h1591, h1650, h1655, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                          · linarith only [h1591, h1650, h1651, h1655, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h1584, h1591, h1650, h1651, h1654, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                      · linarith only [h1584, h1591, h1653, h3, hc13, hc35, hlam, hphi]
                    · linarith only [h1584, h1652, h3, hlam]
                  · linarith only [h1591, h1650, h1651, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1662 | h1662
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1663 | h1663
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1664 | h1664
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1665 | h1665
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1666 | h1666
                          · rcases h3bigk with h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c
                            · have p1667_0 := h1667c.1
                              have p1667_1 := h1667c.2.1
                              have p1667_2 := h1667c.2.2.1
                              have p1667_3 := h1667c.2.2.2
                              linarith only [hlam, p1667_0]
                            · have p1667_0 := h1667c.1
                              have p1667_1 := h1667c.2.1
                              have p1667_2 := h1667c.2.2.1
                              have p1667_3 := h1667c.2.2.2
                              rcases p1667_3 (m.d 0 3) (by simp) with h1669 | h1669
                              · rcases p1667_3 (m.d 1 3) (by simp) with h1670 | h1670
                                · linarith only [h1, h1670, hlam]
                                · rcases p1667_3 (m.d 2 3) (by simp) with h1672 | h1672
                                  · rcases p1667_3 (m.d 3 4) (by simp) with h1673 | h1673
                                    · linarith only [h1584, h1673, hlam]
                                    · linarith only [h1591, h1673, hlam]
                                  · linarith only [h1587, h1672, hlam]
                              · linarith only [h1, h1669, hlam]
                            · have p1667_0 := h1667c.1
                              have p1667_1 := h1667c.2.1
                              have p1667_2 := h1667c.2.2.1
                              have p1667_3 := h1667c.2.2.2
                              linarith only [h3, hlam, p1667_1]
                            · have p1667_0 := h1667c.1
                              have p1667_1 := h1667c.2.1
                              have p1667_2 := h1667c.2.2.1
                              have p1667_3 := h1667c.2.2.2
                              linarith only [h1587, h1650, h1666, h3, hc12, hc23, hlam, hphi, p1667_1]
                            · have p1667_0 := h1667c.1
                              have p1667_1 := h1667c.2.1
                              have p1667_2 := h1667c.2.2.1
                              have p1667_3 := h1667c.2.2.2
                              linarith only [h1587, h1650, h3, hc12, hc23, hlam, hphi, p1667_1]
                            · have p1667_0 := h1667c.1
                              have p1667_1 := h1667c.2.1
                              have p1667_2 := h1667c.2.2.1
                              have p1667_3 := h1667c.2.2.2
                              linarith only [h1, hlam, p1667_0]
                            · have p1667_0 := h1667c.1
                              have p1667_1 := h1667c.2.1
                              have p1667_2 := h1667c.2.2.1
                              have p1667_3 := h1667c.2.2.2
                              linarith only [hlam, p1667_0]
                            · have p1667_0 := h1667c.1
                              have p1667_1 := h1667c.2.1
                              have p1667_2 := h1667c.2.2.1
                              have p1667_3 := h1667c.2.2.2
                              linarith only [h1587, hlam, p1667_1]
                            · have p1667_0 := h1667c.1
                              have p1667_1 := h1667c.2.1
                              have p1667_2 := h1667c.2.2.1
                              have p1667_3 := h1667c.2.2.2
                              linarith only [h1591, hlam, p1667_0]
                            · have p1667_0 := h1667c.1
                              have p1667_1 := h1667c.2.1
                              have p1667_2 := h1667c.2.2.1
                              have p1667_3 := h1667c.2.2.2
                              linarith only [h1650, hlam, p1667_0]
                            · have p1667_0 := h1667c.1
                              have p1667_1 := h1667c.2.1
                              have p1667_2 := h1667c.2.2.1
                              have p1667_3 := h1667c.2.2.2
                              linarith only [h1584, h1587, h1650, h1666, hc12, hc23, hlam, hphi, p1667_1]
                            · have p1667_0 := h1667c.1
                              have p1667_1 := h1667c.2.1
                              have p1667_2 := h1667c.2.2.1
                              have p1667_3 := h1667c.2.2.2
                              rcases p1667_3 (m.d 0 3) (by simp) with h1687 | h1687
                              · linarith only [h1687, h3, hlam]
                              · linarith only [h1, h1687, hlam]
                            · have p1667_0 := h1667c.1
                              have p1667_1 := h1667c.2.1
                              have p1667_2 := h1667c.2.2.1
                              have p1667_3 := h1667c.2.2.2
                              linarith only [hlam, p1667_0]
                            · have p1667_0 := h1667c.1
                              have p1667_1 := h1667c.2.1
                              have p1667_2 := h1667c.2.2.1
                              have p1667_3 := h1667c.2.2.2
                              linarith only [h1591, h1662, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1667_1, u4ehi4]
                            · have p1667_0 := h1667c.1
                              have p1667_1 := h1667c.2.1
                              have p1667_2 := h1667c.2.2.1
                              have p1667_3 := h1667c.2.2.2
                              linarith only [h1587, h1650, hc12, hc23, hlam, hphi, p1667_1]
                            · have p1667_0 := h1667c.1
                              have p1667_1 := h1667c.2.1
                              have p1667_2 := h1667c.2.2.1
                              have p1667_3 := h1667c.2.2.2
                              linarith only [h1584, hlam, p1667_0]
                            · have p1667_0 := h1667c.1
                              have p1667_1 := h1667c.2.1
                              have p1667_2 := h1667c.2.2.1
                              have p1667_3 := h1667c.2.2.2
                              linarith only [h1584, h1587, h3, hc12, hc23, hlam, hphi, p1667_1]
                            · have p1667_0 := h1667c.1
                              have p1667_1 := h1667c.2.1
                              have p1667_2 := h1667c.2.2.1
                              have p1667_3 := h1667c.2.2.2
                              linarith only [h1663, hlam, p1667_0]
                            · have p1667_0 := h1667c.1
                              have p1667_1 := h1667c.2.1
                              have p1667_2 := h1667c.2.2.1
                              have p1667_3 := h1667c.2.2.2
                              linarith only [hlam, p1667_0]
                            · have p1667_0 := h1667c.1
                              have p1667_1 := h1667c.2.1
                              have p1667_2 := h1667c.2.2.1
                              have p1667_3 := h1667c.2.2.2
                              linarith only [h1584, h1587, h1650, h3, hc12, hc23, hlam, hphi, p1667_1]
                            · have p1667_0 := h1667c.1
                              have p1667_1 := h1667c.2.1
                              have p1667_2 := h1667c.2.2.1
                              have p1667_3 := h1667c.2.2.2
                              linarith only [h1585, hlam, p1667_0]
                            · have p1667_0 := h1667c.1
                              have p1667_1 := h1667c.2.1
                              have p1667_2 := h1667c.2.2.1
                              have p1667_3 := h1667c.2.2.2
                              linarith only [h1585, h1587, h3, hc12, hc23, hlam, hphi, p1667_1]
                            · have p1667_0 := h1667c.1
                              have p1667_1 := h1667c.2.1
                              have p1667_2 := h1667c.2.2.1
                              have p1667_3 := h1667c.2.2.2
                              linarith only [h1664, hlam, p1667_0]
                            · have p1667_0 := h1667c.1
                              have p1667_1 := h1667c.2.1
                              have p1667_2 := h1667c.2.2.1
                              have p1667_3 := h1667c.2.2.2
                              linarith only [h1666, hlam, p1667_0]
                            · have p1667_0 := h1667c.1
                              have p1667_1 := h1667c.2.1
                              have p1667_2 := h1667c.2.2.1
                              have p1667_3 := h1667c.2.2.2
                              linarith only [hlam, p1667_0]
                          · linarith only [h1662, h1666, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                        · linarith only [h1489, h1584, h1591, h1662, h1665, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                      · linarith only [h1584, h1585, h1586, h1591, h1662, h1664, h3, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h1584, h1663, h3, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1707 | h1707
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1708 | h1708
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1709 | h1709
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1710 | h1710
                          · linarith only [h1584, h1662, h1710, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                          · linarith only [h1584, h1586, h1587, h1591, h1710, h3, hc12, hc23, hlam, hphi]
                        · linarith only [h1489, h1584, h1586, h1709, h3, hc02, hc23, hlam, hphi]
                      · linarith only [h1585, h1708, h3, hlam]
                    · linarith only [h1584, h1707, h3, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1716 | h1716
          · linarith only [h0, h1716, h3, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1718 | h1718
            · linarith only [h0, h1489, h1718, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1720 | h1720
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1721 | h1721
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1722 | h1722
                  · linarith only [h1586, h1722, h2, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1724 | h1724
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1725 | h1725
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1726 | h1726
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1727 | h1727
                          · linarith only [h1, h1586, h1720, h1727, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                          · rcases h3bigk with h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c
                            · have p1729_0 := h1729c.1
                              have p1729_1 := h1729c.2.1
                              have p1729_2 := h1729c.2.2.1
                              have p1729_3 := h1729c.2.2.2
                              linarith only [hlam, p1729_0]
                            · have p1729_0 := h1729c.1
                              have p1729_1 := h1729c.2.1
                              have p1729_2 := h1729c.2.2.1
                              have p1729_3 := h1729c.2.2.2
                              linarith only [h1720, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1729_1, u4ehi3]
                            · have p1729_0 := h1729c.1
                              have p1729_1 := h1729c.2.1
                              have p1729_2 := h1729c.2.2.1
                              have p1729_3 := h1729c.2.2.2
                              linarith only [h3, hlam, p1729_1]
                            · have p1729_0 := h1729c.1
                              have p1729_1 := h1729c.2.1
                              have p1729_2 := h1729c.2.2.1
                              have p1729_3 := h1729c.2.2.2
                              rcases p1729_3 (m.d 0 3) (by simp) with h1733 | h1733
                              · rcases p1729_3 (m.d 1 3) (by simp) with h1734 | h1734
                                · linarith only [h1, h1734, hlam]
                                · linarith only [h1720, h1734, hlam]
                              · linarith only [h1733, hlam, p1729_0]
                            · have p1729_0 := h1729c.1
                              have p1729_1 := h1729c.2.1
                              have p1729_2 := h1729c.2.2.1
                              have p1729_3 := h1729c.2.2.2
                              rcases p1729_3 (m.d 0 3) (by simp) with h1738 | h1738
                              · rcases p1729_3 (m.d 1 3) (by simp) with h1739 | h1739
                                · linarith only [h1, h1739, hlam]
                                · linarith only [h1721, h1739, hlam]
                              · linarith only [h1738, hlam, p1729_0]
                            · have p1729_0 := h1729c.1
                              have p1729_1 := h1729c.2.1
                              have p1729_2 := h1729c.2.2.1
                              have p1729_3 := h1729c.2.2.2
                              linarith only [h1, hlam, p1729_0]
                            · have p1729_0 := h1729c.1
                              have p1729_1 := h1729c.2.1
                              have p1729_2 := h1729c.2.2.1
                              have p1729_3 := h1729c.2.2.2
                              linarith only [hlam, p1729_0]
                            · have p1729_0 := h1729c.1
                              have p1729_1 := h1729c.2.1
                              have p1729_2 := h1729c.2.2.1
                              have p1729_3 := h1729c.2.2.2
                              linarith only [h1716, hlam, p1729_1]
                            · have p1729_0 := h1729c.1
                              have p1729_1 := h1729c.2.1
                              have p1729_2 := h1729c.2.2.1
                              have p1729_3 := h1729c.2.2.2
                              linarith only [h1, hc01, hlam, hphi, ht0b, ht45, ht5b, p1729_1, u4ehi3]
                            · have p1729_0 := h1729c.1
                              have p1729_1 := h1729c.2.1
                              have p1729_2 := h1729c.2.2.1
                              have p1729_3 := h1729c.2.2.2
                              linarith only [h1, h1727, hc01, hlam, hphi, ht0b, ht45, ht5b, p1729_1, u4ehi3]
                            · have p1729_0 := h1729c.1
                              have p1729_1 := h1729c.2.1
                              have p1729_2 := h1729c.2.2.1
                              have p1729_3 := h1729c.2.2.2
                              linarith only [h1584, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1729_1, u4ehi3]
                            · have p1729_0 := h1729c.1
                              have p1729_1 := h1729c.2.1
                              have p1729_2 := h1729c.2.2.1
                              have p1729_3 := h1729c.2.2.2
                              linarith only [h1720, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1729_1, u4ehi3]
                            · have p1729_0 := h1729c.1
                              have p1729_1 := h1729c.2.1
                              have p1729_2 := h1729c.2.2.1
                              have p1729_3 := h1729c.2.2.2
                              linarith only [hlam, p1729_0]
                            · have p1729_0 := h1729c.1
                              have p1729_1 := h1729c.2.1
                              have p1729_2 := h1729c.2.2.1
                              have p1729_3 := h1729c.2.2.2
                              rcases p1729_3 (m.d 0 3) (by simp) with h1751 | h1751
                              · linarith only [h1751, h3, hlam]
                              · linarith only [h1584, h1751, hlam]
                            · have p1729_0 := h1729c.1
                              have p1729_1 := h1729c.2.1
                              have p1729_2 := h1729c.2.2.1
                              have p1729_3 := h1729c.2.2.2
                              rcases p1729_3 (m.d 0 3) (by simp) with h1754 | h1754
                              · linarith only [h1754, h3, hlam]
                              · linarith only [h1585, h1754, hlam]
                            · have p1729_0 := h1729c.1
                              have p1729_1 := h1729c.2.1
                              have p1729_2 := h1729c.2.2.1
                              have p1729_3 := h1729c.2.2.2
                              linarith only [h1584, hlam, p1729_0]
                            · have p1729_0 := h1729c.1
                              have p1729_1 := h1729c.2.1
                              have p1729_2 := h1729c.2.2.1
                              have p1729_3 := h1729c.2.2.2
                              linarith only [h1720, hlam, p1729_0]
                            · have p1729_0 := h1729c.1
                              have p1729_1 := h1729c.2.1
                              have p1729_2 := h1729c.2.2.1
                              have p1729_3 := h1729c.2.2.2
                              linarith only [h1724, hlam, p1729_0]
                            · have p1729_0 := h1729c.1
                              have p1729_1 := h1729c.2.1
                              have p1729_2 := h1729c.2.2.1
                              have p1729_3 := h1729c.2.2.2
                              linarith only [hlam, p1729_0]
                            · have p1729_0 := h1729c.1
                              have p1729_1 := h1729c.2.1
                              have p1729_2 := h1729c.2.2.1
                              have p1729_3 := h1729c.2.2.2
                              linarith only [h1727, hlam, p1729_1]
                            · have p1729_0 := h1729c.1
                              have p1729_1 := h1729c.2.1
                              have p1729_2 := h1729c.2.2.1
                              have p1729_3 := h1729c.2.2.2
                              linarith only [h1585, hlam, p1729_0]
                            · have p1729_0 := h1729c.1
                              have p1729_1 := h1729c.2.1
                              have p1729_2 := h1729c.2.2.1
                              have p1729_3 := h1729c.2.2.2
                              linarith only [h1721, hlam, p1729_0]
                            · have p1729_0 := h1729c.1
                              have p1729_1 := h1729c.2.1
                              have p1729_2 := h1729c.2.2.1
                              have p1729_3 := h1729c.2.2.2
                              linarith only [h1725, hlam, p1729_0]
                            · have p1729_0 := h1729c.1
                              have p1729_1 := h1729c.2.1
                              have p1729_2 := h1729c.2.2.1
                              have p1729_3 := h1729c.2.2.2
                              linarith only [h1, h1721, hc03, hlam, hphi, ht0b, ht45, ht5b, p1729_1, u4ehi3]
                            · have p1729_0 := h1729c.1
                              have p1729_1 := h1729c.2.1
                              have p1729_2 := h1729c.2.2.1
                              have p1729_3 := h1729c.2.2.2
                              linarith only [hlam, p1729_0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1767 | h1767
                          · linarith only [h1720, h1726, h1767, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                          · rcases h3bigk with h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c
                            · have p1769_0 := h1769c.1
                              have p1769_1 := h1769c.2.1
                              have p1769_2 := h1769c.2.2.1
                              have p1769_3 := h1769c.2.2.2
                              linarith only [hlam, p1769_0]
                            · have p1769_0 := h1769c.1
                              have p1769_1 := h1769c.2.1
                              have p1769_2 := h1769c.2.2.1
                              have p1769_3 := h1769c.2.2.2
                              linarith only [h1721, h1767, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1769_1, u4ehi3]
                            · have p1769_0 := h1769c.1
                              have p1769_1 := h1769c.2.1
                              have p1769_2 := h1769c.2.2.1
                              have p1769_3 := h1769c.2.2.2
                              linarith only [h3, hlam, p1769_1]
                            · have p1769_0 := h1769c.1
                              have p1769_1 := h1769c.2.1
                              have p1769_2 := h1769c.2.2.1
                              have p1769_3 := h1769c.2.2.2
                              rcases p1769_3 (m.d 0 3) (by simp) with h1773 | h1773
                              · rcases p1769_3 (m.d 1 3) (by simp) with h1774 | h1774
                                · linarith only [h1, h1774, hlam]
                                · linarith only [h1720, h1774, hlam]
                              · linarith only [h1773, hlam, p1769_0]
                            · have p1769_0 := h1769c.1
                              have p1769_1 := h1769c.2.1
                              have p1769_2 := h1769c.2.2.1
                              have p1769_3 := h1769c.2.2.2
                              rcases p1769_3 (m.d 0 3) (by simp) with h1778 | h1778
                              · rcases p1769_3 (m.d 1 3) (by simp) with h1779 | h1779
                                · linarith only [h1, h1779, hlam]
                                · linarith only [h1721, h1779, hlam]
                              · linarith only [h1778, hlam, p1769_0]
                            · have p1769_0 := h1769c.1
                              have p1769_1 := h1769c.2.1
                              have p1769_2 := h1769c.2.2.1
                              have p1769_3 := h1769c.2.2.2
                              linarith only [h1, hlam, p1769_0]
                            · have p1769_0 := h1769c.1
                              have p1769_1 := h1769c.2.1
                              have p1769_2 := h1769c.2.2.1
                              have p1769_3 := h1769c.2.2.2
                              linarith only [hlam, p1769_0]
                            · have p1769_0 := h1769c.1
                              have p1769_1 := h1769c.2.1
                              have p1769_2 := h1769c.2.2.1
                              have p1769_3 := h1769c.2.2.2
                              linarith only [h1716, hlam, p1769_1]
                            · have p1769_0 := h1769c.1
                              have p1769_1 := h1769c.2.1
                              have p1769_2 := h1769c.2.2.1
                              have p1769_3 := h1769c.2.2.2
                              linarith only [h1, hc01, hlam, hphi, ht0b, ht45, ht5b, p1769_1, u4ehi3]
                            · have p1769_0 := h1769c.1
                              have p1769_1 := h1769c.2.1
                              have p1769_2 := h1769c.2.2.1
                              have p1769_3 := h1769c.2.2.2
                              linarith only [h1, h1767, hc01, hlam, hphi, ht0b, ht45, ht5b, p1769_1, u4ehi3]
                            · have p1769_0 := h1769c.1
                              have p1769_1 := h1769c.2.1
                              have p1769_2 := h1769c.2.2.1
                              have p1769_3 := h1769c.2.2.2
                              linarith only [h1584, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1769_1, u4ehi3]
                            · have p1769_0 := h1769c.1
                              have p1769_1 := h1769c.2.1
                              have p1769_2 := h1769c.2.2.1
                              have p1769_3 := h1769c.2.2.2
                              linarith only [h1720, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1769_1, u4ehi3]
                            · have p1769_0 := h1769c.1
                              have p1769_1 := h1769c.2.1
                              have p1769_2 := h1769c.2.2.1
                              have p1769_3 := h1769c.2.2.2
                              linarith only [hlam, p1769_0]
                            · have p1769_0 := h1769c.1
                              have p1769_1 := h1769c.2.1
                              have p1769_2 := h1769c.2.2.1
                              have p1769_3 := h1769c.2.2.2
                              rcases p1769_3 (m.d 0 3) (by simp) with h1791 | h1791
                              · linarith only [h1791, h3, hlam]
                              · linarith only [h1584, h1791, hlam]
                            · have p1769_0 := h1769c.1
                              have p1769_1 := h1769c.2.1
                              have p1769_2 := h1769c.2.2.1
                              have p1769_3 := h1769c.2.2.2
                              rcases p1769_3 (m.d 0 3) (by simp) with h1794 | h1794
                              · linarith only [h1794, h3, hlam]
                              · linarith only [h1585, h1794, hlam]
                            · have p1769_0 := h1769c.1
                              have p1769_1 := h1769c.2.1
                              have p1769_2 := h1769c.2.2.1
                              have p1769_3 := h1769c.2.2.2
                              linarith only [h1584, hlam, p1769_0]
                            · have p1769_0 := h1769c.1
                              have p1769_1 := h1769c.2.1
                              have p1769_2 := h1769c.2.2.1
                              have p1769_3 := h1769c.2.2.2
                              linarith only [h1720, hlam, p1769_0]
                            · have p1769_0 := h1769c.1
                              have p1769_1 := h1769c.2.1
                              have p1769_2 := h1769c.2.2.1
                              have p1769_3 := h1769c.2.2.2
                              linarith only [h1724, hlam, p1769_0]
                            · have p1769_0 := h1769c.1
                              have p1769_1 := h1769c.2.1
                              have p1769_2 := h1769c.2.2.1
                              have p1769_3 := h1769c.2.2.2
                              linarith only [hlam, p1769_0]
                            · have p1769_0 := h1769c.1
                              have p1769_1 := h1769c.2.1
                              have p1769_2 := h1769c.2.2.1
                              have p1769_3 := h1769c.2.2.2
                              linarith only [h1767, hlam, p1769_1]
                            · have p1769_0 := h1769c.1
                              have p1769_1 := h1769c.2.1
                              have p1769_2 := h1769c.2.2.1
                              have p1769_3 := h1769c.2.2.2
                              linarith only [h1585, hlam, p1769_0]
                            · have p1769_0 := h1769c.1
                              have p1769_1 := h1769c.2.1
                              have p1769_2 := h1769c.2.2.1
                              have p1769_3 := h1769c.2.2.2
                              linarith only [h1721, hlam, p1769_0]
                            · have p1769_0 := h1769c.1
                              have p1769_1 := h1769c.2.1
                              have p1769_2 := h1769c.2.2.1
                              have p1769_3 := h1769c.2.2.2
                              linarith only [h1725, hlam, p1769_0]
                            · have p1769_0 := h1769c.1
                              have p1769_1 := h1769c.2.1
                              have p1769_2 := h1769c.2.2.1
                              have p1769_3 := h1769c.2.2.2
                              linarith only [h1, h1721, hc03, hlam, hphi, ht0b, ht45, ht5b, p1769_1, u4ehi3]
                            · have p1769_0 := h1769c.1
                              have p1769_1 := h1769c.2.1
                              have p1769_2 := h1769c.2.2.1
                              have p1769_3 := h1769c.2.2.2
                              linarith only [hlam, p1769_0]
                      · linarith only [h1, h1721, h1725, h3, hlam]
                    · linarith only [h1, h1720, h1724, h3, hlam]
                · linarith only [h1585, h1720, h1721, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1810 | h1810
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1811 | h1811
                  · linarith only [h1584, h1586, h1720, h1811, hlam]
                  · linarith only [h1584, h1586, h1720, h1810, h1811, hc45, hlam, hphi, u4ehi1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1814 | h1814
                  · linarith only [h1586, h1814, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1816 | h1816
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1817 | h1817
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1818 | h1818
                        · linarith only [h1584, h1586, h1716, h1720, h1818, hc12, hc24, hlam, hphi]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1820 | h1820
                          · linarith only [h1489, h1584, h1818, h1820, hlam]
                          · rcases h3bigk with h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c | h1822c
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [hlam, p1822_0]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              rcases p1822_3 (m.d 0 3) (by simp) with h1824 | h1824
                              · rcases p1822_3 (m.d 1 3) (by simp) with h1825 | h1825
                                · linarith only [h1, h1825, hlam]
                                · rcases p1822_3 (m.d 2 3) (by simp) with h1827 | h1827
                                  · rcases p1822_3 (m.d 3 4) (by simp) with h1828 | h1828
                                    · linarith only [h1584, h1828, hlam]
                                    · linarith only [h1720, h1828, hlam]
                                  · linarith only [h1716, h1827, hlam]
                              · linarith only [h1, h1824, hlam]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [h3, hlam, p1822_1]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [h1716, h1720, h3, hc12, hc23, hlam, hphi, p1822_1]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [h1716, h1810, h3, hc12, hc23, hlam, hphi, p1822_1]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [h1, hlam, p1822_0]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [hlam, p1822_0]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [h1716, hlam, p1822_1]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [h1720, hlam, p1822_0]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [h1810, hlam, p1822_0]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [h1584, h1716, h1720, hc12, hc23, hlam, hphi, p1822_1]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              rcases p1822_3 (m.d 0 3) (by simp) with h1842 | h1842
                              · linarith only [h1842, h3, hlam]
                              · linarith only [h1, h1842, hlam]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [hlam, p1822_0]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [h1716, h1720, hc12, hc23, hlam, hphi, p1822_1]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [h1716, h1720, h1820, hc12, hc23, hlam, hphi, p1822_1]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [h1584, hlam, p1822_0]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [h1489, h1584, h1716, h1818, hc12, hc45, hlam, hphi, ht23, ht34, p1822_1]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [h1816, hlam, p1822_0]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [hlam, p1822_0]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [h1820, hlam, p1822_1]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [h1585, hlam, p1822_0]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [h1585, h1716, h3, hc12, hc23, hlam, hphi, p1822_1]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [h1817, hlam, p1822_0]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [h1585, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1822_1, u4ehi3]
                            · have p1822_0 := h1822c.1
                              have p1822_1 := h1822c.2.1
                              have p1822_2 := h1822c.2.2.1
                              have p1822_3 := h1822c.2.2.2
                              linarith only [hlam, p1822_0]
                      · linarith only [h1585, h1817, h3, hlam]
                    · linarith only [h1584, h1816, h3, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1860 | h1860
        · linarith only [h1584, h1585, h1860, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1862 | h1862
          · linarith only [h0, h1862, h3, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1864 | h1864
            · linarith only [h0, h1489, h1864, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1866 | h1866
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1867 | h1867
                · linarith only [h1, h1585, h1867, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1869 | h1869
                  · linarith only [h1860, h1869, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1871 | h1871
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1872 | h1872
                      · linarith only [h1, h1585, h1866, h1872, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1874 | h1874
                        · linarith only [h1860, h1871, h1872, h1874, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1876 | h1876
                          · linarith only [h1, h1866, h1874, h1876, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                          · linarith only [h1, h1866, h1872, h1876, h3, hc45, hlam, hphi, u4ehi3]
                    · linarith only [h1, h1866, h1871, h3, hlam]
              · linarith only [h1584, h1585, h1866, hc13, hc35, hlam, hphi]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1881 | h1881
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1882 | h1882
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1883 | h1883
          · linarith only [h0, h1883, h3, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1885 | h1885
            · linarith only [h0, h1489, h1885, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1887 | h1887
              · linarith only [h1, h1584, h1887, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1889 | h1889
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1890 | h1890
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1891 | h1891
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1892 | h1892
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1893 | h1893
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1894 | h1894
                          · linarith only [h1, h1584, h1889, h1891, h1894, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                          · linarith only [h1, h1584, h1889, h1890, h1894, h2, hc04, hc35, hlam, hphi, ht0b, ht5b]
                        · linarith only [h1, h1584, h1889, h1890, h1891, h1893, hlam]
                      · linarith only [h1, h1584, h1889, h1890, h1891, h1892, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1899 | h1899
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1900 | h1900
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1901 | h1901
                          · rcases h3bigk with h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c | h1902c
                            · have p1902_0 := h1902c.1
                              have p1902_1 := h1902c.2.1
                              have p1902_2 := h1902c.2.2.1
                              have p1902_3 := h1902c.2.2.2
                              linarith only [hlam, p1902_0]
                            · have p1902_0 := h1902c.1
                              have p1902_1 := h1902c.2.1
                              have p1902_2 := h1902c.2.2.1
                              have p1902_3 := h1902c.2.2.2
                              linarith only [h1889, h1901, hc03, hlam, hphi, ht0b, ht45, ht5b, p1902_1, u4ehi4]
                            · have p1902_0 := h1902c.1
                              have p1902_1 := h1902c.2.1
                              have p1902_2 := h1902c.2.2.1
                              have p1902_3 := h1902c.2.2.2
                              linarith only [h3, hlam, p1902_1]
                            · have p1902_0 := h1902c.1
                              have p1902_1 := h1902c.2.1
                              have p1902_2 := h1902c.2.2.1
                              have p1902_3 := h1902c.2.2.2
                              linarith only [h1584, hlam, p1902_0]
                            · have p1902_0 := h1902c.1
                              have p1902_1 := h1902c.2.1
                              have p1902_2 := h1902c.2.2.1
                              have p1902_3 := h1902c.2.2.2
                              linarith only [h1891, h1901, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1902_1, u4ehi4]
                            · have p1902_0 := h1902c.1
                              have p1902_1 := h1902c.2.1
                              have p1902_2 := h1902c.2.2.1
                              have p1902_3 := h1902c.2.2.2
                              linarith only [h1, hlam, p1902_0]
                            · have p1902_0 := h1902c.1
                              have p1902_1 := h1902c.2.1
                              have p1902_2 := h1902c.2.2.1
                              have p1902_3 := h1902c.2.2.2
                              linarith only [hlam, p1902_0]
                            · have p1902_0 := h1902c.1
                              have p1902_1 := h1902c.2.1
                              have p1902_2 := h1902c.2.2.1
                              have p1902_3 := h1902c.2.2.2
                              linarith only [h1883, hlam, p1902_1]
                            · have p1902_0 := h1902c.1
                              have p1902_1 := h1902c.2.1
                              have p1902_2 := h1902c.2.2.1
                              have p1902_3 := h1902c.2.2.2
                              linarith only [h1887, hlam, p1902_0]
                            · have p1902_0 := h1902c.1
                              have p1902_1 := h1902c.2.1
                              have p1902_2 := h1902c.2.2.1
                              have p1902_3 := h1902c.2.2.2
                              linarith only [h1, h1901, hc01, hlam, hphi, ht0b, ht45, ht5b, p1902_1, u4ehi4]
                            · have p1902_0 := h1902c.1
                              have p1902_1 := h1902c.2.1
                              have p1902_2 := h1902c.2.2.1
                              have p1902_3 := h1902c.2.2.2
                              linarith only [h1891, hc03, hc34, hlam, hphi, p1902_1]
                            · have p1902_0 := h1902c.1
                              have p1902_1 := h1902c.2.1
                              have p1902_2 := h1902c.2.2.1
                              have p1902_3 := h1902c.2.2.2
                              linarith only [h1891, hc13, hc34, hlam, hphi, p1902_1]
                            · have p1902_0 := h1902c.1
                              have p1902_1 := h1902c.2.1
                              have p1902_2 := h1902c.2.2.1
                              have p1902_3 := h1902c.2.2.2
                              linarith only [hlam, p1902_0]
                            · have p1902_0 := h1902c.1
                              have p1902_1 := h1902c.2.1
                              have p1902_2 := h1902c.2.2.1
                              have p1902_3 := h1902c.2.2.2
                              linarith only [h1891, hlam, p1902_0]
                            · have p1902_0 := h1902c.1
                              have p1902_1 := h1902c.2.1
                              have p1902_2 := h1902c.2.2.1
                              have p1902_3 := h1902c.2.2.2
                              linarith only [h1891, h1901, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1902_1, u4ehi4]
                            · have p1902_0 := h1902c.1
                              have p1902_1 := h1902c.2.1
                              have p1902_2 := h1902c.2.2.1
                              have p1902_3 := h1902c.2.2.2
                              linarith only [h1, h1889, h1901, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1902_1, u4ehi4]
                            · have p1902_0 := h1902c.1
                              have p1902_1 := h1902c.2.1
                              have p1902_2 := h1902c.2.2.1
                              have p1902_3 := h1902c.2.2.2
                              linarith only [h1889, h1901, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1902_1, u4ehi4]
                            · have p1902_0 := h1902c.1
                              have p1902_1 := h1902c.2.1
                              have p1902_2 := h1902c.2.2.1
                              have p1902_3 := h1902c.2.2.2
                              linarith only [h0, h3, hc12, hc34, hlam, hphi, ht23, p1902_1]
                            · have p1902_0 := h1902c.1
                              have p1902_1 := h1902c.2.1
                              have p1902_2 := h1902c.2.2.1
                              have p1902_3 := h1902c.2.2.2
                              linarith only [hlam, p1902_0]
                            · have p1902_0 := h1902c.1
                              have p1902_1 := h1902c.2.1
                              have p1902_2 := h1902c.2.2.1
                              have p1902_3 := h1902c.2.2.2
                              rcases p1902_3 (m.d 0 3) (by simp) with h1922 | h1922
                              · linarith only [h1584, h1922, hlam]
                              · linarith only [h1881, h1922, hlam]
                            · have p1902_0 := h1902c.1
                              have p1902_1 := h1902c.2.1
                              have p1902_2 := h1902c.2.2.1
                              have p1902_3 := h1902c.2.2.2
                              linarith only [h1881, hlam, p1902_0]
                            · have p1902_0 := h1902c.1
                              have p1902_1 := h1902c.2.1
                              have p1902_2 := h1902c.2.2.1
                              have p1902_3 := h1902c.2.2.2
                              linarith only [h1889, hlam, p1902_0]
                            · have p1902_0 := h1902c.1
                              have p1902_1 := h1902c.2.1
                              have p1902_2 := h1902c.2.2.1
                              have p1902_3 := h1902c.2.2.2
                              linarith only [h1899, hlam, p1902_0]
                            · have p1902_0 := h1902c.1
                              have p1902_1 := h1902c.2.1
                              have p1902_2 := h1902c.2.2.1
                              have p1902_3 := h1902c.2.2.2
                              linarith only [h1901, hlam, p1902_0]
                            · have p1902_0 := h1902c.1
                              have p1902_1 := h1902c.2.1
                              have p1902_2 := h1902c.2.2.1
                              have p1902_3 := h1902c.2.2.2
                              linarith only [hlam, p1902_0]
                          · linarith only [h1489, h1882, h1891, h1901, hlam]
                        · linarith only [h0, h1, h1489, h1889, h1890, h1891, h1900, h3, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h1, h1889, h1899, h3, hlam]
                  · linarith only [h1887, h1889, h1890, hlam]
                · linarith only [h1584, h1881, h1889, hc13, hc34, hlam, hphi]
        · linarith only [h1584, h1881, h1882, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1936 | h1936
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1937 | h1937
          · linarith only [h0, h1937, h3, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1939 | h1939
            · linarith only [h0, h1489, h1939, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1941 | h1941
              · linarith only [h1, h1584, h1941, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1943 | h1943
                · linarith only [h1, h1881, h1943, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1945 | h1945
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1946 | h1946
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1947 | h1947
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1948 | h1948
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1949 | h1949
                          · rcases h3bigk with h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c
                            · have p1950_0 := h1950c.1
                              have p1950_1 := h1950c.2.1
                              have p1950_2 := h1950c.2.2.1
                              have p1950_3 := h1950c.2.2.2
                              linarith only [hlam, p1950_0]
                            · have p1950_0 := h1950c.1
                              have p1950_1 := h1950c.2.1
                              have p1950_2 := h1950c.2.2.1
                              have p1950_3 := h1950c.2.2.2
                              linarith only [h1881, h1937, h1946, h1949, hc12, hc23, hlam, hphi, p1950_1]
                            · have p1950_0 := h1950c.1
                              have p1950_1 := h1950c.2.1
                              have p1950_2 := h1950c.2.2.1
                              have p1950_3 := h1950c.2.2.2
                              linarith only [h3, hlam, p1950_1]
                            · have p1950_0 := h1950c.1
                              have p1950_1 := h1950c.2.1
                              have p1950_2 := h1950c.2.2.1
                              have p1950_3 := h1950c.2.2.2
                              linarith only [h1584, hlam, p1950_0]
                            · have p1950_0 := h1950c.1
                              have p1950_1 := h1950c.2.1
                              have p1950_2 := h1950c.2.2.1
                              have p1950_3 := h1950c.2.2.2
                              linarith only [h1881, hlam, p1950_0]
                            · have p1950_0 := h1950c.1
                              have p1950_1 := h1950c.2.1
                              have p1950_2 := h1950c.2.2.1
                              have p1950_3 := h1950c.2.2.2
                              linarith only [h1, hlam, p1950_0]
                            · have p1950_0 := h1950c.1
                              have p1950_1 := h1950c.2.1
                              have p1950_2 := h1950c.2.2.1
                              have p1950_3 := h1950c.2.2.2
                              linarith only [hlam, p1950_0]
                            · have p1950_0 := h1950c.1
                              have p1950_1 := h1950c.2.1
                              have p1950_2 := h1950c.2.2.1
                              have p1950_3 := h1950c.2.2.2
                              linarith only [h1937, hlam, p1950_1]
                            · have p1950_0 := h1950c.1
                              have p1950_1 := h1950c.2.1
                              have p1950_2 := h1950c.2.2.1
                              have p1950_3 := h1950c.2.2.2
                              linarith only [h1941, hlam, p1950_0]
                            · have p1950_0 := h1950c.1
                              have p1950_1 := h1950c.2.1
                              have p1950_2 := h1950c.2.2.1
                              have p1950_3 := h1950c.2.2.2
                              linarith only [h1943, hlam, p1950_0]
                            · have p1950_0 := h1950c.1
                              have p1950_1 := h1950c.2.1
                              have p1950_2 := h1950c.2.2.1
                              have p1950_3 := h1950c.2.2.2
                              rcases p1950_3 (m.d 0 3) (by simp) with h1961 | h1961
                              · linarith only [h1961, h3, hlam]
                              · rcases p1950_3 (m.d 1 3) (by simp) with h1963 | h1963
                                · linarith only [h1937, h1963, hlam]
                                · rcases p1950_3 (m.d 2 3) (by simp) with h1965 | h1965
                                  · rcases p1950_3 (m.d 3 4) (by simp) with h1966 | h1966
                                    · linarith only [h1946, h1966, hlam]
                                    · linarith only [h1584, h1966, hlam]
                                  · linarith only [h1965, h3, hlam]
                            · have p1950_0 := h1950c.1
                              have p1950_1 := h1950c.2.1
                              have p1950_2 := h1950c.2.2.1
                              have p1950_3 := h1950c.2.2.2
                              rcases p1950_3 (m.d 0 3) (by simp) with h1970 | h1970
                              · linarith only [h1970, h3, hlam]
                              · linarith only [h1, h1970, hlam]
                            · have p1950_0 := h1950c.1
                              have p1950_1 := h1950c.2.1
                              have p1950_2 := h1950c.2.2.1
                              have p1950_3 := h1950c.2.2.2
                              linarith only [hlam, p1950_0]
                            · have p1950_0 := h1950c.1
                              have p1950_1 := h1950c.2.1
                              have p1950_2 := h1950c.2.2.1
                              have p1950_3 := h1950c.2.2.2
                              linarith only [h1881, h1949, h3, hc02, hc23, hlam, hphi, p1950_1]
                            · have p1950_0 := h1950c.1
                              have p1950_1 := h1950c.2.1
                              have p1950_2 := h1950c.2.2.1
                              have p1950_3 := h1950c.2.2.2
                              linarith only [h0, h1881, h3, hc12, hc23, hlam, hphi, p1950_1]
                            · have p1950_0 := h1950c.1
                              have p1950_1 := h1950c.2.1
                              have p1950_2 := h1950c.2.2.1
                              have p1950_3 := h1950c.2.2.2
                              linarith only [h0, h1946, h3, hc12, hc23, hlam, hphi, p1950_1]
                            · have p1950_0 := h1950c.1
                              have p1950_1 := h1950c.2.1
                              have p1950_2 := h1950c.2.2.1
                              have p1950_3 := h1950c.2.2.2
                              linarith only [h1937, h1946, hc12, hc23, hlam, hphi, p1950_1]
                            · have p1950_0 := h1950c.1
                              have p1950_1 := h1950c.2.1
                              have p1950_2 := h1950c.2.2.1
                              have p1950_3 := h1950c.2.2.2
                              linarith only [h1946, hlam, p1950_0]
                            · have p1950_0 := h1950c.1
                              have p1950_1 := h1950c.2.1
                              have p1950_2 := h1950c.2.2.1
                              have p1950_3 := h1950c.2.2.2
                              linarith only [hlam, p1950_0]
                            · have p1950_0 := h1950c.1
                              have p1950_1 := h1950c.2.1
                              have p1950_2 := h1950c.2.2.1
                              have p1950_3 := h1950c.2.2.2
                              linarith only [h0, h1881, h1946, h3, hc12, hc23, hlam, hphi, p1950_1]
                            · have p1950_0 := h1950c.1
                              have p1950_1 := h1950c.2.1
                              have p1950_2 := h1950c.2.2.1
                              have p1950_3 := h1950c.2.2.2
                              linarith only [h0, h1947, h3, hc12, hc23, hlam, hphi, p1950_1]
                            · have p1950_0 := h1950c.1
                              have p1950_1 := h1950c.2.1
                              have p1950_2 := h1950c.2.2.1
                              have p1950_3 := h1950c.2.2.2
                              linarith only [h1937, h1947, hc12, hc23, hlam, hphi, p1950_1]
                            · have p1950_0 := h1950c.1
                              have p1950_1 := h1950c.2.1
                              have p1950_2 := h1950c.2.2.1
                              have p1950_3 := h1950c.2.2.2
                              linarith only [h1947, hlam, p1950_0]
                            · have p1950_0 := h1950c.1
                              have p1950_1 := h1950c.2.1
                              have p1950_2 := h1950c.2.2.1
                              have p1950_3 := h1950c.2.2.2
                              linarith only [h1949, hlam, p1950_0]
                            · have p1950_0 := h1950c.1
                              have p1950_1 := h1950c.2.1
                              have p1950_2 := h1950c.2.2.1
                              have p1950_3 := h1950c.2.2.2
                              linarith only [hlam, p1950_0]
                          · linarith only [h1945, h1949, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                        · linarith only [h1584, h1945, h1946, h1948, h2, hlam]
                      · linarith only [h1584, h1945, h1946, h1947, h2, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1989 | h1989
                      · linarith only [h0, h1881, h1946, h1989, h3, hc12, hc34, hlam, hphi, ht23]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1991 | h1991
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1992 | h1992
                          · rcases h3bigk with h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [hlam, p1993_0]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [h1937, h1989, h1992, h3, hc12, hc34, hlam, hphi, ht23, p1993_1]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [h3, hlam, p1993_1]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [h1584, hlam, p1993_0]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [h1881, hlam, p1993_0]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [h1, hlam, p1993_0]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [hlam, p1993_0]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [h1937, hlam, p1993_1]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [h1941, hlam, p1993_0]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [h1943, hlam, p1993_0]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [h1989, h1992, hc03, hc34, hlam, hphi, p1993_1]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [h1937, h1989, h1992, hc12, hc34, hlam, hphi, ht23, p1993_1]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [hlam, p1993_0]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [h1946, hlam, p1993_0]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [h1989, hlam, p1993_0]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              rcases p1993_3 (m.d 0 3) (by simp) with h2009 | h2009
                              · linarith only [h2009, hlam, p1993_0]
                              · rcases p1993_3 (m.d 1 3) (by simp) with h2011 | h2011
                                · linarith only [h1941, h2011, hlam]
                                · rcases p1993_3 (m.d 2 3) (by simp) with h2013 | h2013
                                  · linarith only [h1946, h2013, hlam]
                                  · linarith only [h2013, h3, hlam]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              rcases p1993_3 (m.d 0 3) (by simp) with h2016 | h2016
                              · linarith only [h1584, h2016, hlam]
                              · linarith only [h1, h2016, hlam]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [h0, h3, hc12, hc34, hlam, hphi, ht23, p1993_1]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [hlam, p1993_0]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [h1, h1881, h1937, hc12, hc34, hlam, hphi, ht23, p1993_1]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              rcases p1993_3 (m.d 0 3) (by simp) with h2022 | h2022
                              · linarith only [h2022, hlam, p1993_0]
                              · rcases p1993_3 (m.d 1 3) (by simp) with h2024 | h2024
                                · linarith only [h1943, h2024, hlam]
                                · rcases p1993_3 (m.d 2 3) (by simp) with h2026 | h2026
                                  · linarith only [h1989, h2026, hlam]
                                  · linarith only [h2026, h3, hlam]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              rcases p1993_3 (m.d 0 3) (by simp) with h2029 | h2029
                              · linarith only [h1881, h2029, hlam]
                              · linarith only [h1, h2029, hlam]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [h0, h3, hc12, hc35, hlam, hphi, ht23, p1993_1]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [h1992, hlam, p1993_0]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [hlam, p1993_0]
                          · linarith only [h1945, h1992, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                        · linarith only [h1489, h1945, h1991, h2, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2037 | h2037
                    · linarith only [h1584, h1936, h1945, h2037, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2039 | h2039
                      · linarith only [h1881, h2037, h2039, hc03, hc34, hlam, hphi]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2041 | h2041
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2042 | h2042
                          · rcases h3bigk with h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c
                            · have p2043_0 := h2043c.1
                              have p2043_1 := h2043c.2.1
                              have p2043_2 := h2043c.2.2.1
                              have p2043_3 := h2043c.2.2.2
                              linarith only [hlam, p2043_0]
                            · have p2043_0 := h2043c.1
                              have p2043_1 := h2043c.2.1
                              have p2043_2 := h2043c.2.2.1
                              have p2043_3 := h2043c.2.2.2
                              linarith only [h1937, h2039, h2042, h3, hc12, hc34, hlam, hphi, ht23, p2043_1]
                            · have p2043_0 := h2043c.1
                              have p2043_1 := h2043c.2.1
                              have p2043_2 := h2043c.2.2.1
                              have p2043_3 := h2043c.2.2.2
                              linarith only [h3, hlam, p2043_1]
                            · have p2043_0 := h2043c.1
                              have p2043_1 := h2043c.2.1
                              have p2043_2 := h2043c.2.2.1
                              have p2043_3 := h2043c.2.2.2
                              linarith only [h1584, hlam, p2043_0]
                            · have p2043_0 := h2043c.1
                              have p2043_1 := h2043c.2.1
                              have p2043_2 := h2043c.2.2.1
                              have p2043_3 := h2043c.2.2.2
                              linarith only [h1881, hlam, p2043_0]
                            · have p2043_0 := h2043c.1
                              have p2043_1 := h2043c.2.1
                              have p2043_2 := h2043c.2.2.1
                              have p2043_3 := h2043c.2.2.2
                              linarith only [h1, hlam, p2043_0]
                            · have p2043_0 := h2043c.1
                              have p2043_1 := h2043c.2.1
                              have p2043_2 := h2043c.2.2.1
                              have p2043_3 := h2043c.2.2.2
                              linarith only [hlam, p2043_0]
                            · have p2043_0 := h2043c.1
                              have p2043_1 := h2043c.2.1
                              have p2043_2 := h2043c.2.2.1
                              have p2043_3 := h2043c.2.2.2
                              linarith only [h1937, hlam, p2043_1]
                            · have p2043_0 := h2043c.1
                              have p2043_1 := h2043c.2.1
                              have p2043_2 := h2043c.2.2.1
                              have p2043_3 := h2043c.2.2.2
                              linarith only [h1941, hlam, p2043_0]
                            · have p2043_0 := h2043c.1
                              have p2043_1 := h2043c.2.1
                              have p2043_2 := h2043c.2.2.1
                              have p2043_3 := h2043c.2.2.2
                              linarith only [h1943, hlam, p2043_0]
                            · have p2043_0 := h2043c.1
                              have p2043_1 := h2043c.2.1
                              have p2043_2 := h2043c.2.2.1
                              have p2043_3 := h2043c.2.2.2
                              linarith only [h2039, h2042, hc03, hc34, hlam, hphi, p2043_1]
                            · have p2043_0 := h2043c.1
                              have p2043_1 := h2043c.2.1
                              have p2043_2 := h2043c.2.2.1
                              have p2043_3 := h2043c.2.2.2
                              linarith only [h1937, h2039, h2042, hc12, hc34, hlam, hphi, ht23, p2043_1]
                            · have p2043_0 := h2043c.1
                              have p2043_1 := h2043c.2.1
                              have p2043_2 := h2043c.2.2.1
                              have p2043_3 := h2043c.2.2.2
                              linarith only [hlam, p2043_0]
                            · have p2043_0 := h2043c.1
                              have p2043_1 := h2043c.2.1
                              have p2043_2 := h2043c.2.2.1
                              have p2043_3 := h2043c.2.2.2
                              linarith only [h2037, hlam, p2043_0]
                            · have p2043_0 := h2043c.1
                              have p2043_1 := h2043c.2.1
                              have p2043_2 := h2043c.2.2.1
                              have p2043_3 := h2043c.2.2.2
                              linarith only [h2039, hlam, p2043_0]
                            · have p2043_0 := h2043c.1
                              have p2043_1 := h2043c.2.1
                              have p2043_2 := h2043c.2.2.1
                              have p2043_3 := h2043c.2.2.2
                              rcases p2043_3 (m.d 0 3) (by simp) with h2059 | h2059
                              · linarith only [h2059, hlam, p2043_0]
                              · rcases p2043_3 (m.d 1 3) (by simp) with h2061 | h2061
                                · linarith only [h1941, h2061, hlam]
                                · rcases p2043_3 (m.d 2 3) (by simp) with h2063 | h2063
                                  · linarith only [h2037, h2063, hlam]
                                  · linarith only [h2063, h3, hlam]
                            · have p2043_0 := h2043c.1
                              have p2043_1 := h2043c.2.1
                              have p2043_2 := h2043c.2.2.1
                              have p2043_3 := h2043c.2.2.2
                              rcases p2043_3 (m.d 0 3) (by simp) with h2066 | h2066
                              · linarith only [h1584, h2066, hlam]
                              · linarith only [h1, h2066, hlam]
                            · have p2043_0 := h2043c.1
                              have p2043_1 := h2043c.2.1
                              have p2043_2 := h2043c.2.2.1
                              have p2043_3 := h2043c.2.2.2
                              linarith only [h0, h3, hc12, hc34, hlam, hphi, ht23, p2043_1]
                            · have p2043_0 := h2043c.1
                              have p2043_1 := h2043c.2.1
                              have p2043_2 := h2043c.2.2.1
                              have p2043_3 := h2043c.2.2.2
                              linarith only [hlam, p2043_0]
                            · have p2043_0 := h2043c.1
                              have p2043_1 := h2043c.2.1
                              have p2043_2 := h2043c.2.2.1
                              have p2043_3 := h2043c.2.2.2
                              linarith only [h1, h1881, h1937, hc12, hc34, hlam, hphi, ht23, p2043_1]
                            · have p2043_0 := h2043c.1
                              have p2043_1 := h2043c.2.1
                              have p2043_2 := h2043c.2.2.1
                              have p2043_3 := h2043c.2.2.2
                              rcases p2043_3 (m.d 0 3) (by simp) with h2072 | h2072
                              · linarith only [h2072, hlam, p2043_0]
                              · rcases p2043_3 (m.d 1 3) (by simp) with h2074 | h2074
                                · linarith only [h1943, h2074, hlam]
                                · rcases p2043_3 (m.d 2 3) (by simp) with h2076 | h2076
                                  · linarith only [h2039, h2076, hlam]
                                  · linarith only [h2076, h3, hlam]
                            · have p2043_0 := h2043c.1
                              have p2043_1 := h2043c.2.1
                              have p2043_2 := h2043c.2.2.1
                              have p2043_3 := h2043c.2.2.2
                              rcases p2043_3 (m.d 0 3) (by simp) with h2079 | h2079
                              · linarith only [h1881, h2079, hlam]
                              · linarith only [h1, h2079, hlam]
                            · have p2043_0 := h2043c.1
                              have p2043_1 := h2043c.2.1
                              have p2043_2 := h2043c.2.2.1
                              have p2043_3 := h2043c.2.2.2
                              linarith only [h0, h3, hc12, hc35, hlam, hphi, ht23, p2043_1]
                            · have p2043_0 := h2043c.1
                              have p2043_1 := h2043c.2.1
                              have p2043_2 := h2043c.2.2.1
                              have p2043_3 := h2043c.2.2.2
                              linarith only [h2042, hlam, p2043_0]
                            · have p2043_0 := h2043c.1
                              have p2043_1 := h2043c.2.1
                              have p2043_2 := h2043c.2.2.1
                              have p2043_3 := h2043c.2.2.2
                              linarith only [hlam, p2043_0]
                          · linarith only [h1, h1489, h1584, h1936, h1937, h2042, hc12, hc24, hlam, hphi]
                        · linarith only [h1489, h1936, h2041, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2087 | h2087
          · linarith only [h0, h2087, h3, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2089 | h2089
            · linarith only [h0, h1489, h2089, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2091 | h2091
              · linarith only [h1, h1584, h2091, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2093 | h2093
                · linarith only [h1, h1881, h2093, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2095 | h2095
                  · linarith only [h1936, h2, h2095, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2097 | h2097
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2098 | h2098
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2099 | h2099
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2100 | h2100
                          · linarith only [h1936, h2097, h2100, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                          · linarith only [h0, h1584, h2097, h2099, h2100, h3, hc12, hc23, hlam, hphi]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2103 | h2103
                          · linarith only [h0, h1489, h2099, h2103, hc12, hc34, hlam, hphi, ht23]
                          · rcases h3bigk with h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c | h2105c
                            · have p2105_0 := h2105c.1
                              have p2105_1 := h2105c.2.1
                              have p2105_2 := h2105c.2.2.1
                              have p2105_3 := h2105c.2.2.2
                              linarith only [hlam, p2105_0]
                            · have p2105_0 := h2105c.1
                              have p2105_1 := h2105c.2.1
                              have p2105_2 := h2105c.2.2.1
                              have p2105_3 := h2105c.2.2.2
                              linarith only [h1584, h2087, h2097, hc12, hc24, hlam, hphi, p2105_1]
                            · have p2105_0 := h2105c.1
                              have p2105_1 := h2105c.2.1
                              have p2105_2 := h2105c.2.2.1
                              have p2105_3 := h2105c.2.2.2
                              linarith only [h3, hlam, p2105_1]
                            · have p2105_0 := h2105c.1
                              have p2105_1 := h2105c.2.1
                              have p2105_2 := h2105c.2.2.1
                              have p2105_3 := h2105c.2.2.2
                              linarith only [h1584, hlam, p2105_0]
                            · have p2105_0 := h2105c.1
                              have p2105_1 := h2105c.2.1
                              have p2105_2 := h2105c.2.2.1
                              have p2105_3 := h2105c.2.2.2
                              linarith only [h1881, hlam, p2105_0]
                            · have p2105_0 := h2105c.1
                              have p2105_1 := h2105c.2.1
                              have p2105_2 := h2105c.2.2.1
                              have p2105_3 := h2105c.2.2.2
                              linarith only [h1, hlam, p2105_0]
                            · have p2105_0 := h2105c.1
                              have p2105_1 := h2105c.2.1
                              have p2105_2 := h2105c.2.2.1
                              have p2105_3 := h2105c.2.2.2
                              linarith only [hlam, p2105_0]
                            · have p2105_0 := h2105c.1
                              have p2105_1 := h2105c.2.1
                              have p2105_2 := h2105c.2.2.1
                              have p2105_3 := h2105c.2.2.2
                              linarith only [h2087, hlam, p2105_1]
                            · have p2105_0 := h2105c.1
                              have p2105_1 := h2105c.2.1
                              have p2105_2 := h2105c.2.2.1
                              have p2105_3 := h2105c.2.2.2
                              linarith only [h2091, hlam, p2105_0]
                            · have p2105_0 := h2105c.1
                              have p2105_1 := h2105c.2.1
                              have p2105_2 := h2105c.2.2.1
                              have p2105_3 := h2105c.2.2.2
                              linarith only [h2093, hlam, p2105_0]
                            · have p2105_0 := h2105c.1
                              have p2105_1 := h2105c.2.1
                              have p2105_2 := h2105c.2.2.1
                              have p2105_3 := h2105c.2.2.2
                              rcases p2105_3 (m.d 0 3) (by simp) with h2116 | h2116
                              · linarith only [h2116, h3, hlam]
                              · rcases p2105_3 (m.d 1 3) (by simp) with h2118 | h2118
                                · linarith only [h2087, h2118, hlam]
                                · rcases p2105_3 (m.d 2 3) (by simp) with h2120 | h2120
                                  · rcases p2105_3 (m.d 3 4) (by simp) with h2121 | h2121
                                    · linarith only [h2097, h2121, hlam]
                                    · linarith only [h1584, h2121, hlam]
                                  · linarith only [h2120, h3, hlam]
                            · have p2105_0 := h2105c.1
                              have p2105_1 := h2105c.2.1
                              have p2105_2 := h2105c.2.2.1
                              have p2105_3 := h2105c.2.2.2
                              rcases p2105_3 (m.d 0 3) (by simp) with h2125 | h2125
                              · linarith only [h2125, h3, hlam]
                              · linarith only [h1, h2125, hlam]
                            · have p2105_0 := h2105c.1
                              have p2105_1 := h2105c.2.1
                              have p2105_2 := h2105c.2.2.1
                              have p2105_3 := h2105c.2.2.2
                              linarith only [hlam, p2105_0]
                            · have p2105_0 := h2105c.1
                              have p2105_1 := h2105c.2.1
                              have p2105_2 := h2105c.2.2.1
                              have p2105_3 := h2105c.2.2.2
                              linarith only [h1, h1584, h2087, hc12, hc23, hlam, hphi, p2105_1]
                            · have p2105_0 := h2105c.1
                              have p2105_1 := h2105c.2.1
                              have p2105_2 := h2105c.2.2.1
                              have p2105_3 := h2105c.2.2.2
                              linarith only [h1, h1881, h2087, hc12, hc23, hlam, hphi, p2105_1]
                            · have p2105_0 := h2105c.1
                              have p2105_1 := h2105c.2.1
                              have p2105_2 := h2105c.2.2.1
                              have p2105_3 := h2105c.2.2.2
                              linarith only [h1, h2087, h2097, hc12, hc23, hlam, hphi, p2105_1]
                            · have p2105_0 := h2105c.1
                              have p2105_1 := h2105c.2.1
                              have p2105_2 := h2105c.2.2.1
                              have p2105_3 := h2105c.2.2.2
                              linarith only [h2087, h2097, hc12, hc23, hlam, hphi, p2105_1]
                            · have p2105_0 := h2105c.1
                              have p2105_1 := h2105c.2.1
                              have p2105_2 := h2105c.2.2.1
                              have p2105_3 := h2105c.2.2.2
                              linarith only [h2097, hlam, p2105_0]
                            · have p2105_0 := h2105c.1
                              have p2105_1 := h2105c.2.1
                              have p2105_2 := h2105c.2.2.1
                              have p2105_3 := h2105c.2.2.2
                              linarith only [hlam, p2105_0]
                            · have p2105_0 := h2105c.1
                              have p2105_1 := h2105c.2.1
                              have p2105_2 := h2105c.2.2.1
                              have p2105_3 := h2105c.2.2.2
                              linarith only [h2103, hlam, p2105_1]
                            · have p2105_0 := h2105c.1
                              have p2105_1 := h2105c.2.1
                              have p2105_2 := h2105c.2.2.1
                              have p2105_3 := h2105c.2.2.2
                              linarith only [h1, h2087, h2098, hc12, hc23, hlam, hphi, p2105_1]
                            · have p2105_0 := h2105c.1
                              have p2105_1 := h2105c.2.1
                              have p2105_2 := h2105c.2.2.1
                              have p2105_3 := h2105c.2.2.2
                              linarith only [h2087, h2098, hc12, hc23, hlam, hphi, p2105_1]
                            · have p2105_0 := h2105c.1
                              have p2105_1 := h2105c.2.1
                              have p2105_2 := h2105c.2.2.1
                              have p2105_3 := h2105c.2.2.2
                              linarith only [h2098, hlam, p2105_0]
                            · have p2105_0 := h2105c.1
                              have p2105_1 := h2105c.2.1
                              have p2105_2 := h2105c.2.2.1
                              have p2105_3 := h2105c.2.2.2
                              linarith only [h2098, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2105_1, u4ehi3]
                            · have p2105_0 := h2105c.1
                              have p2105_1 := h2105c.2.1
                              have p2105_2 := h2105c.2.2.1
                              have p2105_3 := h2105c.2.2.2
                              linarith only [hlam, p2105_0]
                      · linarith only [h1, h1584, h2087, h2097, h2098, hc12, hc35, hlam, hphi, ht23]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2142 | h2142
                      · linarith only [h1, h1881, h2087, h2097, h2142, hc12, hc34, hlam, hphi, ht23]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2144 | h2144
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2145 | h2145
                          · rcases h3bigk with h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c
                            · have p2146_0 := h2146c.1
                              have p2146_1 := h2146c.2.1
                              have p2146_2 := h2146c.2.2.1
                              have p2146_3 := h2146c.2.2.2
                              linarith only [hlam, p2146_0]
                            · have p2146_0 := h2146c.1
                              have p2146_1 := h2146c.2.1
                              have p2146_2 := h2146c.2.2.1
                              have p2146_3 := h2146c.2.2.2
                              linarith only [h2087, h2142, h2145, h3, hc12, hc34, hlam, hphi, ht23, p2146_1]
                            · have p2146_0 := h2146c.1
                              have p2146_1 := h2146c.2.1
                              have p2146_2 := h2146c.2.2.1
                              have p2146_3 := h2146c.2.2.2
                              linarith only [h3, hlam, p2146_1]
                            · have p2146_0 := h2146c.1
                              have p2146_1 := h2146c.2.1
                              have p2146_2 := h2146c.2.2.1
                              have p2146_3 := h2146c.2.2.2
                              linarith only [h1584, hlam, p2146_0]
                            · have p2146_0 := h2146c.1
                              have p2146_1 := h2146c.2.1
                              have p2146_2 := h2146c.2.2.1
                              have p2146_3 := h2146c.2.2.2
                              linarith only [h1881, hlam, p2146_0]
                            · have p2146_0 := h2146c.1
                              have p2146_1 := h2146c.2.1
                              have p2146_2 := h2146c.2.2.1
                              have p2146_3 := h2146c.2.2.2
                              linarith only [h1, hlam, p2146_0]
                            · have p2146_0 := h2146c.1
                              have p2146_1 := h2146c.2.1
                              have p2146_2 := h2146c.2.2.1
                              have p2146_3 := h2146c.2.2.2
                              linarith only [hlam, p2146_0]
                            · have p2146_0 := h2146c.1
                              have p2146_1 := h2146c.2.1
                              have p2146_2 := h2146c.2.2.1
                              have p2146_3 := h2146c.2.2.2
                              linarith only [h2087, hlam, p2146_1]
                            · have p2146_0 := h2146c.1
                              have p2146_1 := h2146c.2.1
                              have p2146_2 := h2146c.2.2.1
                              have p2146_3 := h2146c.2.2.2
                              linarith only [h2091, hlam, p2146_0]
                            · have p2146_0 := h2146c.1
                              have p2146_1 := h2146c.2.1
                              have p2146_2 := h2146c.2.2.1
                              have p2146_3 := h2146c.2.2.2
                              linarith only [h2093, hlam, p2146_0]
                            · have p2146_0 := h2146c.1
                              have p2146_1 := h2146c.2.1
                              have p2146_2 := h2146c.2.2.1
                              have p2146_3 := h2146c.2.2.2
                              linarith only [h2142, h2145, hc03, hc34, hlam, hphi, p2146_1]
                            · have p2146_0 := h2146c.1
                              have p2146_1 := h2146c.2.1
                              have p2146_2 := h2146c.2.2.1
                              have p2146_3 := h2146c.2.2.2
                              linarith only [h2087, h2142, h2145, hc12, hc34, hlam, hphi, ht23, p2146_1]
                            · have p2146_0 := h2146c.1
                              have p2146_1 := h2146c.2.1
                              have p2146_2 := h2146c.2.2.1
                              have p2146_3 := h2146c.2.2.2
                              linarith only [hlam, p2146_0]
                            · have p2146_0 := h2146c.1
                              have p2146_1 := h2146c.2.1
                              have p2146_2 := h2146c.2.2.1
                              have p2146_3 := h2146c.2.2.2
                              linarith only [h2097, hlam, p2146_0]
                            · have p2146_0 := h2146c.1
                              have p2146_1 := h2146c.2.1
                              have p2146_2 := h2146c.2.2.1
                              have p2146_3 := h2146c.2.2.2
                              linarith only [h2142, hlam, p2146_0]
                            · have p2146_0 := h2146c.1
                              have p2146_1 := h2146c.2.1
                              have p2146_2 := h2146c.2.2.1
                              have p2146_3 := h2146c.2.2.2
                              rcases p2146_3 (m.d 0 3) (by simp) with h2162 | h2162
                              · linarith only [h2162, hlam, p2146_0]
                              · rcases p2146_3 (m.d 1 3) (by simp) with h2164 | h2164
                                · linarith only [h2091, h2164, hlam]
                                · rcases p2146_3 (m.d 2 3) (by simp) with h2166 | h2166
                                  · linarith only [h2097, h2166, hlam]
                                  · linarith only [h2166, h3, hlam]
                            · have p2146_0 := h2146c.1
                              have p2146_1 := h2146c.2.1
                              have p2146_2 := h2146c.2.2.1
                              have p2146_3 := h2146c.2.2.2
                              rcases p2146_3 (m.d 0 3) (by simp) with h2169 | h2169
                              · linarith only [h1584, h2169, hlam]
                              · linarith only [h1, h2169, hlam]
                            · have p2146_0 := h2146c.1
                              have p2146_1 := h2146c.2.1
                              have p2146_2 := h2146c.2.2.1
                              have p2146_3 := h2146c.2.2.2
                              linarith only [h0, h3, hc12, hc34, hlam, hphi, ht23, p2146_1]
                            · have p2146_0 := h2146c.1
                              have p2146_1 := h2146c.2.1
                              have p2146_2 := h2146c.2.2.1
                              have p2146_3 := h2146c.2.2.2
                              linarith only [hlam, p2146_0]
                            · have p2146_0 := h2146c.1
                              have p2146_1 := h2146c.2.1
                              have p2146_2 := h2146c.2.2.1
                              have p2146_3 := h2146c.2.2.2
                              linarith only [h1, h1881, h2087, hc12, hc34, hlam, hphi, ht23, p2146_1]
                            · have p2146_0 := h2146c.1
                              have p2146_1 := h2146c.2.1
                              have p2146_2 := h2146c.2.2.1
                              have p2146_3 := h2146c.2.2.2
                              rcases p2146_3 (m.d 0 3) (by simp) with h2175 | h2175
                              · linarith only [h2175, hlam, p2146_0]
                              · rcases p2146_3 (m.d 1 3) (by simp) with h2177 | h2177
                                · linarith only [h2093, h2177, hlam]
                                · rcases p2146_3 (m.d 2 3) (by simp) with h2179 | h2179
                                  · linarith only [h2142, h2179, hlam]
                                  · linarith only [h2179, h3, hlam]
                            · have p2146_0 := h2146c.1
                              have p2146_1 := h2146c.2.1
                              have p2146_2 := h2146c.2.2.1
                              have p2146_3 := h2146c.2.2.2
                              rcases p2146_3 (m.d 0 3) (by simp) with h2182 | h2182
                              · linarith only [h1881, h2182, hlam]
                              · linarith only [h1, h2182, hlam]
                            · have p2146_0 := h2146c.1
                              have p2146_1 := h2146c.2.1
                              have p2146_2 := h2146c.2.2.1
                              have p2146_3 := h2146c.2.2.2
                              linarith only [h0, h3, hc12, hc35, hlam, hphi, ht23, p2146_1]
                            · have p2146_0 := h2146c.1
                              have p2146_1 := h2146c.2.1
                              have p2146_2 := h2146c.2.2.1
                              have p2146_3 := h2146c.2.2.2
                              linarith only [h2145, hlam, p2146_0]
                            · have p2146_0 := h2146c.1
                              have p2146_1 := h2146c.2.1
                              have p2146_2 := h2146c.2.2.1
                              have p2146_3 := h2146c.2.2.2
                              linarith only [hlam, p2146_0]
                          · linarith only [h1, h1584, h2087, h2144, h2145, hc12, hc24, hlam, hphi]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2189 | h2189
                          · linarith only [h0, h1489, h2144, h2189, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h0, h2097, h2189, h3, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5518000 in
set_option maxHeartbeats 5518000 in
theorem r1l7_13_24_L_I_M_IR_s0_x0_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h3bigk := hb3.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
  · exact r1l7_13_24_L_I_M_IR_s0_x0_x0_x0 m hb3 hb4 hg0 h1 h2 h3
  · exact r1l7_13_24_L_I_M_IR_s0_x0_x0_x1 m hb3 hb4 hg0 h1 h2 h3

set_option maxHeartbeats 5518000 in
set_option maxHeartbeats 5518000 in
theorem r1l7_13_24_L_I_M_IR_s0_x0_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h3bigk := hb3.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h2192 | h2192
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2193 | h2193
    · linarith only [h0, h2, h2193, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2195 | h2195
      · linarith only [h1, h2, h2195, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2197 | h2197
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2198 | h2198
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2199 | h2199
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2200 | h2200
              · linarith only [h0, h2, h2193, h2200, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2202 | h2202
                · linarith only [h1, h2, h2195, h2200, h2202, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · linarith only [h0, h2, h2199, h2202, hc23, hc34, hlam, hphi]
            · linarith only [h2192, h2193, h2199, hc12, hc24, hlam, hphi]
          · linarith only [h1, h2, h2197, h2198, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2207 | h2207
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2208 | h2208
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2209 | h2209
              · linarith only [h0, h2, h2193, h2209, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2211 | h2211
                · linarith only [h0, h2, h2208, h2209, h2211, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                · linarith only [h0, h2, h2208, h2211, hc23, hc34, hlam, hphi]
            · linarith only [h2192, h2193, h2208, hc12, hc24, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2215 | h2215
            · linarith only [h0, h2, h2207, h2215, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h0, h2, h2192, h2207, h2215, hc12, hc45, hlam, hphi, ht23, ht34]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2218 | h2218
    · linarith only [h1, h2, h2192, h2218, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2220 | h2220
      · linarith only [h1, h2, h2220, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2222 | h2222
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2223 | h2223
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2224 | h2224
            · linarith only [h0, h2, h2192, h2224, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2226 | h2226
              · linarith only [h0, h2, h2218, h2226, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2228 | h2228
                · linarith only [h1, h2, h2192, h2220, h2226, h2228, hc02, hc24, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2230 | h2230
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2231 | h2231
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2232 | h2232
                      · linarith only [h1, h2, h2228, h2230, h2231, h2232, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2234 | h2234
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2235 | h2235
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2236 | h2236
                            · linarith only [h1, h2, h2230, h2236, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h1, h2, h2226, h2230, h2231, h2232, h2236, hc15, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h1, h2, h2226, h2230, h2231, h2235, hlam]
                        · linarith only [h1, h2, h2192, h2226, h2230, h2232, h2234, hc02, hc34, hlam, hphi, ht23]
                    · linarith only [h1, h2, h2230, h2231, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                  · linarith only [h1, h2, h2222, h2228, h2230, hc13, hc34, hlam, hphi]
          · linarith only [h1, h2, h2222, h2223, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2244 | h2244
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2245 | h2245
            · linarith only [h0, h2192, h2245, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2247 | h2247
              · linarith only [h1, h2, h2245, h2247, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2249 | h2249
                · linarith only [h1, h2, h2247, h2249, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2251 | h2251
                  · linarith only [h1, h2, h2192, h2222, h2249, h2251, hc02, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2253 | h2253
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2254 | h2254
                      · linarith only [h0, h2, h2249, h2254, hc12, hc23, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2256 | h2256
                        · linarith only [h0, h2192, h2222, h2254, h2256, hc12, hc34, hlam, hphi, ht23]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2258 | h2258
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2259 | h2259
                            · rcases h3bigk with h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [hlam, p2260_0]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [h1, h2, h2245, h2247, hc12, hc24, hlam, hphi, p2260_1]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [h2192, hlam, p2260_1]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [h2220, hlam, p2260_0]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [h2222, hlam, p2260_0]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [h1, hlam, p2260_0]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [hlam, p2260_0]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [h2245, hlam, p2260_1]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [h2249, hlam, p2260_0]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [h2251, hlam, p2260_0]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [h2256, hc03, hc35, hlam, hphi, p2260_1]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [h2245, h2256, hc12, hc35, hlam, hphi, ht23, p2260_1]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [hlam, p2260_0]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [h2254, hlam, p2260_0]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [h2256, hlam, p2260_0]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                rcases p2260_3 (m.d 0 3) (by simp) with h2276 | h2276
                                · linarith only [h2276, hlam, p2260_0]
                                · rcases p2260_3 (m.d 1 3) (by simp) with h2278 | h2278
                                  · linarith only [h2249, h2278, hlam]
                                  · rcases p2260_3 (m.d 2 3) (by simp) with h2280 | h2280
                                    · linarith only [h2254, h2280, hlam]
                                    · linarith only [h2192, h2280, hlam]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                rcases p2260_3 (m.d 0 3) (by simp) with h2283 | h2283
                                · linarith only [h2220, h2283, hlam]
                                · linarith only [h1, h2283, hlam]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [h0, h2192, hc12, hc34, hlam, hphi, ht23, p2260_1]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [hlam, p2260_0]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [h1, h2222, h2245, hc12, hc34, hlam, hphi, ht23, p2260_1]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                rcases p2260_3 (m.d 0 3) (by simp) with h2289 | h2289
                                · linarith only [h2289, hlam, p2260_0]
                                · rcases p2260_3 (m.d 1 3) (by simp) with h2291 | h2291
                                  · linarith only [h2251, h2291, hlam]
                                  · rcases p2260_3 (m.d 2 3) (by simp) with h2293 | h2293
                                    · linarith only [h2256, h2293, hlam]
                                    · linarith only [h2192, h2293, hlam]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                rcases p2260_3 (m.d 0 3) (by simp) with h2296 | h2296
                                · linarith only [h2222, h2296, hlam]
                                · linarith only [h1, h2296, hlam]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [h0, h2192, hc12, hc35, hlam, hphi, ht23, p2260_1]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [h2259, hlam, p2260_0]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [hlam, p2260_0]
                            · linarith only [h0, h2, h2247, h2254, h2259, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h1, h2, h2244, h2245, h2247, h2258, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h2, h2244, h2253, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2305 | h2305
            · linarith only [h0, h2192, h2305, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2307 | h2307
              · linarith only [h0, h2, h2307, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2309 | h2309
                · linarith only [h1, h2, h2244, h2309, hc45, hlam, hphi, u4ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2311 | h2311
                  · linarith only [h1, h2, h2192, h2222, h2244, h2311, hc02, hc45, hlam, hphi, ht23, ht34]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2313 | h2313
                    · linarith only [h0, h2, h2244, h2309, h2313, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h1, h2, h2305, h2313, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5518000 in
set_option maxHeartbeats 5518000 in
theorem r1l7_13_24_L_I_M_IR_s0_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h3bigk := hb3.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_13_24_L_I_M_IR_s0_x0_x0 m hb3 hb4 hg0 h1 h2
  · exact r1l7_13_24_L_I_M_IR_s0_x0_x1 m hb3 hb4 hg0 h1 h2

end R2N4
