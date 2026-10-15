import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_52S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5050000 in
set_option maxHeartbeats 5050000 in
theorem r1l7_11_12_14_25_L_0_L_I_L_I_M_IR_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1281 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
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
  rcases m.htr 0 1 4 (by decide) (by decide) with h1561 | h1561
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1562 | h1562
    · linarith only [h0, h1562, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1564 | h1564
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1565 | h1565
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1566 | h1566
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1567 | h1567
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1568 | h1568
              · linarith only [h0, h1561, h1568, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1570 | h1570
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1571 | h1571
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1572 | h1572
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1573 | h1573
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1574 | h1574
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1575 | h1575
                          · linarith only [h1561, h1562, h1568, h1570, h1574, h1575, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1577 | h1577
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1578 | h1578
                              · linarith only [h0, h1564, h1578, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                              · linarith only [h1570, h1574, h1577, h1578, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                            · linarith only [h1561, h1562, h1570, h1573, h1574, h1577, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1582 | h1582
                          · linarith only [h1561, h1582, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1584 | h1584
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1585 | h1585
                              · linarith only [h1281, h1574, h1585, hc01, hc23, hlam, hphi, ht12]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1587 | h1587
                                · linarith only [h1281, h1561, h1571, h1574, h1582, h1587, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1589 | h1589
                                  · linarith only [h1281, h1561, h1571, h1574, h1582, h1584, h1589, hlam]
                                  · linarith only [h1281, h1561, h1571, h1574, h1584, h1589, hc34, hc45, hlam, hphi]
                            · linarith only [h1281, h1567, h1574, h1584, hc23, hc35, hlam, hphi]
                      · linarith only [h1281, h1561, h1567, h1573, hlam]
                    · linarith only [h0, h1566, h1572, hlam]
                  · linarith only [h0, h1565, h1571, hlam]
                · linarith only [h0, h1564, h1570, hlam]
            · linarith only [h1281, h1561, h1567, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1598 | h1598
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1599 | h1599
              · linarith only [h1281, h1561, h1599, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1601 | h1601
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1602 | h1602
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1603 | h1603
                    · linarith only [h1564, h1566, h1603, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1605 | h1605
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1606 | h1606
                        · linarith only [h1601, h1603, h1606, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1608 | h1608
                          · linarith only [h1281, h1561, h1599, h1606, h1608, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1610 | h1610
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1611 | h1611
                              · linarith only [h1281, h1564, h1606, h1611, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1613 | h1613
                                · linarith only [h1281, h1561, h1562, h1602, h1608, h1613, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi0]
                                · linarith only [h1281, h1561, h1601, h1602, h1603, h1610, h1613, hc34, hc45, hlam, hphi]
                            · linarith only [h1281, h1561, h1601, h1603, h1605, h1610, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · linarith only [h1281, h1598, h1605, hlam]
                  · linarith only [h1281, h1562, h1565, h1566, h1601, h1602, hc01, hlam, hphi, u1elo4]
                · linarith only [h0, h1561, h1564, h1601, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h1281, h1561, h1598, hlam]
        · linarith only [h0, h1561, h1565, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1622 | h1622
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1623 | h1623
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1624 | h1624
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1625 | h1625
              · linarith only [h1281, h1561, h1625, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1627 | h1627
                · linarith only [h1564, h1623, h1627, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1629 | h1629
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1630 | h1630
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1631 | h1631
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1632 | h1632
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1633 | h1633
                          · linarith only [h1561, h1562, h1625, h1627, h1630, h1633, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1635 | h1635
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1636 | h1636
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1637 | h1637
                                · linarith only [h1561, h1562, h1629, h1633, h1637, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1639 | h1639
                                  · linarith only [h1561, h1562, h1629, h1633, h1635, h1639, hlam]
                                  · rcases h2bigk with h1641c | h1641c | h1641c | h1641c | h1641c | h1641c | h1641c | h1641c | h1641c | h1641c | h1641c | h1641c | h1641c | h1641c | h1641c | h1641c | h1641c | h1641c | h1641c | h1641c | h1641c | h1641c | h1641c | h1641c | h1641c
                                    · have p1641_0 := h1641c.1
                                      have p1641_1 := h1641c.2.1
                                      have p1641_2 := h1641c.2.2.1
                                      have p1641_3 := h1641c.2.2.2
                                      linarith only [hlam, p1641_0]
                                    · have p1641_0 := h1641c.1
                                      have p1641_1 := h1641c.2.1
                                      have p1641_2 := h1641c.2.2.1
                                      have p1641_3 := h1641c.2.2.2
                                      linarith only [h0, hlam, p1641_0]
                                    · have p1641_0 := h1641c.1
                                      have p1641_1 := h1641c.2.1
                                      have p1641_2 := h1641c.2.2.1
                                      have p1641_3 := h1641c.2.2.2
                                      linarith only [h1564, hlam, p1641_0]
                                    · have p1641_0 := h1641c.1
                                      have p1641_1 := h1641c.2.1
                                      have p1641_2 := h1641c.2.2.1
                                      have p1641_3 := h1641c.2.2.2
                                      rcases p1641_3 (m.d 0 2) (by simp) with h1645 | h1645
                                      · rcases p1641_3 (m.d 1 2) (by simp) with h1646 | h1646
                                        · rcases p1641_3 (m.d 2 3) (by simp) with h1647 | h1647
                                          · rcases p1641_3 (m.d 2 4) (by simp) with h1648 | h1648
                                            · linarith only [h1648, hlam, p1641_0]
                                            · rcases p1641_3 (m.d 2 5) (by simp) with h1650 | h1650
                                              · linarith only [h1623, h1650, hlam]
                                              · linarith only [h1637, h1650, hlam]
                                          · linarith only [h1635, h1647, hlam]
                                        · linarith only [h1629, h1646, hlam]
                                      · linarith only [h1645, hlam, p1641_0]
                                    · have p1641_0 := h1641c.1
                                      have p1641_1 := h1641c.2.1
                                      have p1641_2 := h1641c.2.2.1
                                      have p1641_3 := h1641c.2.2.2
                                      linarith only [h0, h1627, h1636, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1641_1, u5ehi3]
                                    · have p1641_0 := h1641c.1
                                      have p1641_1 := h1641c.2.1
                                      have p1641_2 := h1641c.2.2.1
                                      have p1641_3 := h1641c.2.2.2
                                      linarith only [h1627, hc02, hc23, hlam, hphi, p1641_1]
                                    · have p1641_0 := h1641c.1
                                      have p1641_1 := h1641c.2.1
                                      have p1641_2 := h1641c.2.2.1
                                      have p1641_3 := h1641c.2.2.2
                                      linarith only [hlam, p1641_0]
                                    · have p1641_0 := h1641c.1
                                      have p1641_1 := h1641c.2.1
                                      have p1641_2 := h1641c.2.2.1
                                      have p1641_3 := h1641c.2.2.2
                                      linarith only [h1627, hlam, p1641_0]
                                    · have p1641_0 := h1641c.1
                                      have p1641_1 := h1641c.2.1
                                      have p1641_2 := h1641c.2.2.1
                                      have p1641_3 := h1641c.2.2.2
                                      rcases p1641_3 (m.d 0 2) (by simp) with h1660 | h1660
                                      · linarith only [h0, h1660, hlam]
                                      · linarith only [h1622, h1660, hlam]
                                    · have p1641_0 := h1641c.1
                                      have p1641_1 := h1641c.2.1
                                      have p1641_2 := h1641c.2.2.1
                                      have p1641_3 := h1641c.2.2.2
                                      linarith only [h1627, h1636, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1641_1, u5ehi3]
                                    · have p1641_0 := h1641c.1
                                      have p1641_1 := h1641c.2.1
                                      have p1641_2 := h1641c.2.2.1
                                      have p1641_3 := h1641c.2.2.2
                                      linarith only [h1623, h1636, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1641_1, u5ehi3]
                                    · have p1641_0 := h1641c.1
                                      have p1641_1 := h1641c.2.1
                                      have p1641_2 := h1641c.2.2.1
                                      have p1641_3 := h1641c.2.2.2
                                      linarith only [h1562, h1630, hc01, hc23, hlam, hphi, ht12, p1641_1]
                                    · have p1641_0 := h1641c.1
                                      have p1641_1 := h1641c.2.1
                                      have p1641_2 := h1641c.2.2.1
                                      have p1641_3 := h1641c.2.2.2
                                      linarith only [hlam, p1641_0]
                                    · have p1641_0 := h1641c.1
                                      have p1641_1 := h1641c.2.1
                                      have p1641_2 := h1641c.2.2.1
                                      have p1641_3 := h1641c.2.2.2
                                      linarith only [h1561, h1562, h1627, h1629, h1630, hlam, p1641_2]
                                    · have p1641_0 := h1641c.1
                                      have p1641_1 := h1641c.2.1
                                      have p1641_2 := h1641c.2.2.1
                                      have p1641_3 := h1641c.2.2.2
                                      rcases p1641_3 (m.d 0 2) (by simp) with h1668 | h1668
                                      · linarith only [h1564, h1668, hlam]
                                      · linarith only [h1623, h1668, hlam]
                                    · have p1641_0 := h1641c.1
                                      have p1641_1 := h1641c.2.1
                                      have p1641_2 := h1641c.2.2.1
                                      have p1641_3 := h1641c.2.2.2
                                      linarith only [h1622, hlam, p1641_0]
                                    · have p1641_0 := h1641c.1
                                      have p1641_1 := h1641c.2.1
                                      have p1641_2 := h1641c.2.2.1
                                      have p1641_3 := h1641c.2.2.2
                                      linarith only [h1629, hlam, p1641_0]
                                    · have p1641_0 := h1641c.1
                                      have p1641_1 := h1641c.2.1
                                      have p1641_2 := h1641c.2.2.1
                                      have p1641_3 := h1641c.2.2.2
                                      linarith only [h1635, hlam, p1641_0]
                                    · have p1641_0 := h1641c.1
                                      have p1641_1 := h1641c.2.1
                                      have p1641_2 := h1641c.2.2.1
                                      have p1641_3 := h1641c.2.2.2
                                      linarith only [hlam, p1641_0]
                                    · have p1641_0 := h1641c.1
                                      have p1641_1 := h1641c.2.1
                                      have p1641_2 := h1641c.2.2.1
                                      have p1641_3 := h1641c.2.2.2
                                      linarith only [h1637, hlam, p1641_0]
                                    · have p1641_0 := h1641c.1
                                      have p1641_1 := h1641c.2.1
                                      have p1641_2 := h1641c.2.2.1
                                      have p1641_3 := h1641c.2.2.2
                                      linarith only [h1623, hlam, p1641_0]
                                    · have p1641_0 := h1641c.1
                                      have p1641_1 := h1641c.2.1
                                      have p1641_2 := h1641c.2.2.1
                                      have p1641_3 := h1641c.2.2.2
                                      linarith only [h1630, hlam, p1641_0]
                                    · have p1641_0 := h1641c.1
                                      have p1641_1 := h1641c.2.1
                                      have p1641_2 := h1641c.2.2.1
                                      have p1641_3 := h1641c.2.2.2
                                      linarith only [h1636, hlam, p1641_0]
                                    · have p1641_0 := h1641c.1
                                      have p1641_1 := h1641c.2.1
                                      have p1641_2 := h1641c.2.2.1
                                      have p1641_3 := h1641c.2.2.2
                                      linarith only [h0, h1623, h1635, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1641_1, u1elo1]
                                    · have p1641_0 := h1641c.1
                                      have p1641_1 := h1641c.2.1
                                      have p1641_2 := h1641c.2.2.1
                                      have p1641_3 := h1641c.2.2.2
                                      linarith only [hlam, p1641_0]
                              · linarith only [h0, h1561, h1627, h1629, h1635, h1636, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h1562, h1627, h1630, h1635, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h1627, h1630, h1632, hlam]
                      · linarith only [h1281, h1624, h1631, hlam]
                    · linarith only [h0, h1281, h1561, h1564, h1623, h1629, h1630, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                  · linarith only [h0, h1622, h1629, hlam]
            · linarith only [h0, h1561, h1564, h1623, h1624, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1688 | h1688
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1689 | h1689
              · linarith only [h0, h1561, h1689, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1691 | h1691
                · linarith only [h1564, h1622, h1691, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1693 | h1693
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1694 | h1694
                    · linarith only [h0, h1623, h1691, h1694, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1696 | h1696
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1697 | h1697
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1698 | h1698
                          · linarith only [h0, h1561, h1689, h1698, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1700 | h1700
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1701 | h1701
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1702 | h1702
                                · linarith only [h0, h1561, h1693, h1694, h1698, h1702, hlam]
                                · linarith only [h0, h1561, h1693, h1694, h1700, h1702, hc34, hc45, hlam, hphi]
                              · linarith only [h0, h1561, h1564, h1693, h1697, h1700, h1701, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                            · linarith only [h0, h1561, h1691, h1693, h1700, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1707 | h1707
                          · linarith only [h0, h1561, h1707, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1709 | h1709
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1710 | h1710
                              · linarith only [h0, h1691, h1697, h1710, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h0, h1561, h1691, h1693, h1709, h1710, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h0, h1561, h1691, h1693, h1709, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h1561, h1688, h1691, h1693, h1696, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h1561, h1622, h1623, h1693, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h1561, h1564, h1688, hlam]
        · linarith only [h0, h1561, h1622, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1718 | h1718
    · linarith only [h1561, h1718, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1720 | h1720
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1721 | h1721
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1722 | h1722
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1723 | h1723
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1724 | h1724
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1725 | h1725
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1726 | h1726
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1727 | h1727
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1728 | h1728
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1729 | h1729
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1730 | h1730
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1731 | h1731
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1732 | h1732
                              · linarith only [h0, h1720, h1732, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                              · linarith only [h1725, h1729, h1731, h1732, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1735 | h1735
                              · linarith only [h1723, h1731, h1735, hc03, hlam, hphi, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1737 | h1737
                                · linarith only [h0, h1721, h1737, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1739 | h1739
                                  · linarith only [h1281, h1723, h1725, h1731, h1737, h1739, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                                  · linarith only [h1561, h1724, h1725, h1728, h1731, h1739, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                          · linarith only [h1561, h1724, h1730, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1743 | h1743
                          · linarith only [h1728, h1729, h1743, hlam]
                          · linarith only [h1561, h1724, h1743, hlam]
                      · linarith only [h1281, h1723, h1728, hlam]
                    · linarith only [h0, h1722, h1727, hlam]
                  · linarith only [h0, h1721, h1726, hlam]
                · linarith only [h0, h1720, h1725, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1750 | h1750
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1751 | h1751
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1752 | h1752
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1753 | h1753
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1754 | h1754
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1755 | h1755
                          · linarith only [h1561, h1724, h1755, hc01, hlam, hphi, u1elo3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1757 | h1757
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1758 | h1758
                              · linarith only [h0, h1720, h1758, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                              · linarith only [h1754, h1757, h1758, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1761 | h1761
                              · linarith only [h1561, h1723, h1757, h1761, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1763 | h1763
                                · linarith only [h0, h1561, h1720, h1723, h1755, h1757, h1763, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1765 | h1765
                                  · linarith only [h0, h1561, h1720, h1723, h1755, h1765, hc01, hlam, hphi, u1elo1]
                                  · rcases h2bigk with h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c
                                    · have p1767_0 := h1767c.1
                                      have p1767_1 := h1767c.2.1
                                      have p1767_2 := h1767c.2.2.1
                                      have p1767_3 := h1767c.2.2.2
                                      linarith only [hlam, p1767_0]
                                    · have p1767_0 := h1767c.1
                                      have p1767_1 := h1767c.2.1
                                      have p1767_2 := h1767c.2.2.1
                                      have p1767_3 := h1767c.2.2.2
                                      linarith only [h0, hlam, p1767_0]
                                    · have p1767_0 := h1767c.1
                                      have p1767_1 := h1767c.2.1
                                      have p1767_2 := h1767c.2.2.1
                                      have p1767_3 := h1767c.2.2.2
                                      rcases p1767_3 (m.d 0 2) (by simp) with h1770 | h1770
                                      · rcases p1767_3 (m.d 1 2) (by simp) with h1771 | h1771
                                        · rcases p1767_3 (m.d 2 3) (by simp) with h1772 | h1772
                                          · linarith only [h1772, hlam, p1767_0]
                                          · rcases p1767_3 (m.d 2 4) (by simp) with h1774 | h1774
                                            · linarith only [h1721, h1774, hlam]
                                            · linarith only [h1757, h1774, hlam]
                                        · linarith only [h1750, h1771, hlam]
                                      · linarith only [h1770, hlam, p1767_0]
                                    · have p1767_0 := h1767c.1
                                      have p1767_1 := h1767c.2.1
                                      have p1767_2 := h1767c.2.2.1
                                      have p1767_3 := h1767c.2.2.2
                                      rcases p1767_3 (m.d 0 2) (by simp) with h1779 | h1779
                                      · rcases p1767_3 (m.d 1 2) (by simp) with h1780 | h1780
                                        · rcases p1767_3 (m.d 2 3) (by simp) with h1781 | h1781
                                          · linarith only [h1720, h1781, hlam]
                                          · rcases p1767_3 (m.d 2 4) (by simp) with h1783 | h1783
                                            · linarith only [h1783, hlam, p1767_0]
                                            · rcases p1767_3 (m.d 2 5) (by simp) with h1785 | h1785
                                              · linarith only [h1722, h1785, hlam]
                                              · linarith only [h1763, h1785, hlam]
                                        · linarith only [h1751, h1780, hlam]
                                      · linarith only [h1779, hlam, p1767_0]
                                    · have p1767_0 := h1767c.1
                                      have p1767_1 := h1767c.2.1
                                      have p1767_2 := h1767c.2.2.1
                                      have p1767_3 := h1767c.2.2.2
                                      linarith only [h0, hlam, hphi, ht01, ht0b, ht5b, p1767_1, u1elo1, u5ehi2]
                                    · have p1767_0 := h1767c.1
                                      have p1767_1 := h1767c.2.1
                                      have p1767_2 := h1767c.2.2.1
                                      have p1767_3 := h1767c.2.2.2
                                      linarith only [h1720, h1723, h1757, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1767_1, u1elo1]
                                    · have p1767_0 := h1767c.1
                                      have p1767_1 := h1767c.2.1
                                      have p1767_2 := h1767c.2.2.1
                                      have p1767_3 := h1767c.2.2.2
                                      linarith only [hlam, p1767_0]
                                    · have p1767_0 := h1767c.1
                                      have p1767_1 := h1767c.2.1
                                      have p1767_2 := h1767c.2.2.1
                                      have p1767_3 := h1767c.2.2.2
                                      rcases p1767_3 (m.d 0 2) (by simp) with h1793 | h1793
                                      · linarith only [h0, h1793, hlam]
                                      · linarith only [h1720, h1793, hlam]
                                    · have p1767_0 := h1767c.1
                                      have p1767_1 := h1767c.2.1
                                      have p1767_2 := h1767c.2.2.1
                                      have p1767_3 := h1767c.2.2.2
                                      rcases p1767_3 (m.d 0 2) (by simp) with h1796 | h1796
                                      · linarith only [h0, h1796, hlam]
                                      · linarith only [h1721, h1796, hlam]
                                    · have p1767_0 := h1767c.1
                                      have p1767_1 := h1767c.2.1
                                      have p1767_2 := h1767c.2.2.1
                                      have p1767_3 := h1767c.2.2.2
                                      linarith only [hlam, hphi, ht01, ht0b, ht5b, p1767_1, u1elo1, u5ehi2]
                                    · have p1767_0 := h1767c.1
                                      have p1767_1 := h1767c.2.1
                                      have p1767_2 := h1767c.2.2.1
                                      have p1767_3 := h1767c.2.2.2
                                      linarith only [h1720, hlam, p1767_0]
                                    · have p1767_0 := h1767c.1
                                      have p1767_1 := h1767c.2.1
                                      have p1767_2 := h1767c.2.2.1
                                      have p1767_3 := h1767c.2.2.2
                                      linarith only [h1750, hlam, p1767_0]
                                    · have p1767_0 := h1767c.1
                                      have p1767_1 := h1767c.2.1
                                      have p1767_2 := h1767c.2.2.1
                                      have p1767_3 := h1767c.2.2.2
                                      linarith only [hlam, p1767_0]
                                    · have p1767_0 := h1767c.1
                                      have p1767_1 := h1767c.2.1
                                      have p1767_2 := h1767c.2.2.1
                                      have p1767_3 := h1767c.2.2.2
                                      linarith only [h1757, hlam, p1767_1]
                                    · have p1767_0 := h1767c.1
                                      have p1767_1 := h1767c.2.1
                                      have p1767_2 := h1767c.2.2.1
                                      have p1767_3 := h1767c.2.2.2
                                      linarith only [h1761, hlam, p1767_1]
                                    · have p1767_0 := h1767c.1
                                      have p1767_1 := h1767c.2.1
                                      have p1767_2 := h1767c.2.2.1
                                      have p1767_3 := h1767c.2.2.2
                                      linarith only [h1721, hlam, p1767_0]
                                    · have p1767_0 := h1767c.1
                                      have p1767_1 := h1767c.2.1
                                      have p1767_2 := h1767c.2.2.1
                                      have p1767_3 := h1767c.2.2.2
                                      linarith only [h1751, hlam, p1767_0]
                                    · have p1767_0 := h1767c.1
                                      have p1767_1 := h1767c.2.1
                                      have p1767_2 := h1767c.2.2.1
                                      have p1767_3 := h1767c.2.2.2
                                      linarith only [h0, h1721, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1767_1, u1elo1]
                                    · have p1767_0 := h1767c.1
                                      have p1767_1 := h1767c.2.1
                                      have p1767_2 := h1767c.2.2.1
                                      have p1767_3 := h1767c.2.2.2
                                      linarith only [hlam, p1767_0]
                                    · have p1767_0 := h1767c.1
                                      have p1767_1 := h1767c.2.1
                                      have p1767_2 := h1767c.2.2.1
                                      have p1767_3 := h1767c.2.2.2
                                      linarith only [h1763, hlam, p1767_0]
                                    · have p1767_0 := h1767c.1
                                      have p1767_1 := h1767c.2.1
                                      have p1767_2 := h1767c.2.2.1
                                      have p1767_3 := h1767c.2.2.2
                                      linarith only [h1722, hlam, p1767_0]
                                    · have p1767_0 := h1767c.1
                                      have p1767_1 := h1767c.2.1
                                      have p1767_2 := h1767c.2.2.1
                                      have p1767_3 := h1767c.2.2.2
                                      linarith only [h1752, hlam, p1767_0]
                                    · have p1767_0 := h1767c.1
                                      have p1767_1 := h1767c.2.1
                                      have p1767_2 := h1767c.2.2.1
                                      have p1767_3 := h1767c.2.2.2
                                      linarith only [h0, h1722, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1767_1, u1elo1]
                                    · have p1767_0 := h1767c.1
                                      have p1767_1 := h1767c.2.1
                                      have p1767_2 := h1767c.2.2.1
                                      have p1767_3 := h1767c.2.2.2
                                      linarith only [h1750, h1754, h1761, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1767_1, u1elo1]
                                    · have p1767_0 := h1767c.1
                                      have p1767_1 := h1767c.2.1
                                      have p1767_2 := h1767c.2.2.1
                                      have p1767_3 := h1767c.2.2.2
                                      linarith only [hlam, p1767_0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1815 | h1815
                          · linarith only [h1561, h1724, h1815, hc01, hlam, hphi, u1elo3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1817 | h1817
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1818 | h1818
                              · linarith only [h0, h1720, h1818, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1820 | h1820
                                · linarith only [h1561, h1815, h1820, hc01, hc24, hlam, hphi, ht12]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1822 | h1822
                                  · linarith only [h1561, h1815, h1822, hc01, hc34, hlam, hphi, ht12, ht23]
                                  · rcases h2bigk with h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c | h1824c
                                    · have p1824_0 := h1824c.1
                                      have p1824_1 := h1824c.2.1
                                      have p1824_2 := h1824c.2.2.1
                                      have p1824_3 := h1824c.2.2.2
                                      linarith only [hlam, p1824_0]
                                    · have p1824_0 := h1824c.1
                                      have p1824_1 := h1824c.2.1
                                      have p1824_2 := h1824c.2.2.1
                                      have p1824_3 := h1824c.2.2.2
                                      linarith only [h0, hlam, p1824_0]
                                    · have p1824_0 := h1824c.1
                                      have p1824_1 := h1824c.2.1
                                      have p1824_2 := h1824c.2.2.1
                                      have p1824_3 := h1824c.2.2.2
                                      linarith only [h0, h1817, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1824_1, u1elo1]
                                    · have p1824_0 := h1824c.1
                                      have p1824_1 := h1824c.2.1
                                      have p1824_2 := h1824c.2.2.1
                                      have p1824_3 := h1824c.2.2.2
                                      rcases p1824_3 (m.d 0 2) (by simp) with h1828 | h1828
                                      · rcases p1824_3 (m.d 1 2) (by simp) with h1829 | h1829
                                        · rcases p1824_3 (m.d 2 3) (by simp) with h1830 | h1830
                                          · linarith only [h1720, h1830, hlam]
                                          · linarith only [h1817, h1830, hlam]
                                        · linarith only [h1751, h1829, hlam]
                                      · linarith only [h1828, hlam, p1824_0]
                                    · have p1824_0 := h1824c.1
                                      have p1824_1 := h1824c.2.1
                                      have p1824_2 := h1824c.2.2.1
                                      have p1824_3 := h1824c.2.2.2
                                      linarith only [h0, hlam, hphi, ht01, ht0b, ht5b, p1824_1, u1elo1, u5ehi2]
                                    · have p1824_0 := h1824c.1
                                      have p1824_1 := h1824c.2.1
                                      have p1824_2 := h1824c.2.2.1
                                      have p1824_3 := h1824c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, p1824_1, u1elo1]
                                    · have p1824_0 := h1824c.1
                                      have p1824_1 := h1824c.2.1
                                      have p1824_2 := h1824c.2.2.1
                                      have p1824_3 := h1824c.2.2.2
                                      linarith only [hlam, p1824_0]
                                    · have p1824_0 := h1824c.1
                                      have p1824_1 := h1824c.2.1
                                      have p1824_2 := h1824c.2.2.1
                                      have p1824_3 := h1824c.2.2.2
                                      linarith only [h1817, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1824_1, u1elo1]
                                    · have p1824_0 := h1824c.1
                                      have p1824_1 := h1824c.2.1
                                      have p1824_2 := h1824c.2.2.1
                                      have p1824_3 := h1824c.2.2.2
                                      rcases p1824_3 (m.d 0 2) (by simp) with h1839 | h1839
                                      · linarith only [h0, h1839, hlam]
                                      · linarith only [h1721, h1839, hlam]
                                    · have p1824_0 := h1824c.1
                                      have p1824_1 := h1824c.2.1
                                      have p1824_2 := h1824c.2.2.1
                                      have p1824_3 := h1824c.2.2.2
                                      linarith only [h1817, h1818, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1824_1, u1elo1]
                                    · have p1824_0 := h1824c.1
                                      have p1824_1 := h1824c.2.1
                                      have p1824_2 := h1824c.2.2.1
                                      have p1824_3 := h1824c.2.2.2
                                      linarith only [h1720, hlam, p1824_0]
                                    · have p1824_0 := h1824c.1
                                      have p1824_1 := h1824c.2.1
                                      have p1824_2 := h1824c.2.2.1
                                      have p1824_3 := h1824c.2.2.2
                                      linarith only [h1750, hlam, p1824_0]
                                    · have p1824_0 := h1824c.1
                                      have p1824_1 := h1824c.2.1
                                      have p1824_2 := h1824c.2.2.1
                                      have p1824_3 := h1824c.2.2.2
                                      linarith only [hlam, p1824_0]
                                    · have p1824_0 := h1824c.1
                                      have p1824_1 := h1824c.2.1
                                      have p1824_2 := h1824c.2.2.1
                                      have p1824_3 := h1824c.2.2.2
                                      linarith only [h0, h1722, h1817, h1818, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1824_1, u1elo1]
                                    · have p1824_0 := h1824c.1
                                      have p1824_1 := h1824c.2.1
                                      have p1824_2 := h1824c.2.2.1
                                      have p1824_3 := h1824c.2.2.2
                                      linarith only [h1818, hlam, p1824_1]
                                    · have p1824_0 := h1824c.1
                                      have p1824_1 := h1824c.2.1
                                      have p1824_2 := h1824c.2.2.1
                                      have p1824_3 := h1824c.2.2.2
                                      linarith only [h1721, hlam, p1824_0]
                                    · have p1824_0 := h1824c.1
                                      have p1824_1 := h1824c.2.1
                                      have p1824_2 := h1824c.2.2.1
                                      have p1824_3 := h1824c.2.2.2
                                      linarith only [h1751, hlam, p1824_0]
                                    · have p1824_0 := h1824c.1
                                      have p1824_1 := h1824c.2.1
                                      have p1824_2 := h1824c.2.2.1
                                      have p1824_3 := h1824c.2.2.2
                                      linarith only [h1817, hlam, p1824_0]
                                    · have p1824_0 := h1824c.1
                                      have p1824_1 := h1824c.2.1
                                      have p1824_2 := h1824c.2.2.1
                                      have p1824_3 := h1824c.2.2.2
                                      linarith only [hlam, p1824_0]
                                    · have p1824_0 := h1824c.1
                                      have p1824_1 := h1824c.2.1
                                      have p1824_2 := h1824c.2.2.1
                                      have p1824_3 := h1824c.2.2.2
                                      linarith only [h1820, hlam, p1824_0]
                                    · have p1824_0 := h1824c.1
                                      have p1824_1 := h1824c.2.1
                                      have p1824_2 := h1824c.2.2.1
                                      have p1824_3 := h1824c.2.2.2
                                      linarith only [h1722, hlam, p1824_0]
                                    · have p1824_0 := h1824c.1
                                      have p1824_1 := h1824c.2.1
                                      have p1824_2 := h1824c.2.2.1
                                      have p1824_3 := h1824c.2.2.2
                                      linarith only [h1752, hlam, p1824_0]
                                    · have p1824_0 := h1824c.1
                                      have p1824_1 := h1824c.2.1
                                      have p1824_2 := h1824c.2.2.1
                                      have p1824_3 := h1824c.2.2.2
                                      linarith only [h0, h1722, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1824_1, u1elo1]
                                    · have p1824_0 := h1824c.1
                                      have p1824_1 := h1824c.2.1
                                      have p1824_2 := h1824c.2.2.1
                                      have p1824_3 := h1824c.2.2.2
                                      linarith only [h0, h1722, h1817, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1824_1, u1elo1]
                                    · have p1824_0 := h1824c.1
                                      have p1824_1 := h1824c.2.1
                                      have p1824_2 := h1824c.2.2.1
                                      have p1824_3 := h1824c.2.2.2
                                      linarith only [hlam, p1824_0]
                            · linarith only [h1281, h1723, h1754, h1817, hc23, hc35, hlam, hphi]
                      · linarith only [h1281, h1561, h1723, h1753, hc01, hlam, hphi, u1elo3]
                    · linarith only [h0, h1722, h1752, hlam]
                  · linarith only [h0, h1721, h1751, hlam]
                · linarith only [h0, h1720, h1750, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1863 | h1863
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1864 | h1864
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1865 | h1865
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1866 | h1866
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1867 | h1867
                      · linarith only [h1281, h1723, h1867, hc01, hlam, hphi, u1elo2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1869 | h1869
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1870 | h1870
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1871 | h1871
                            · linarith only [h1867, h1869, h1871, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1873 | h1873
                              · linarith only [h0, h1721, h1871, h1873, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                              · linarith only [h1867, h1869, h1873, hc23, hc34, hlam, hphi]
                          · linarith only [h1561, h1863, h1870, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1877 | h1877
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1878 | h1878
                            · linarith only [h1281, h1867, h1878, hc01, hc23, hlam, hphi, ht12]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1880 | h1880
                              · linarith only [h0, h1281, h1721, h1869, h1878, h1880, hc01, hlam, hphi, u1elo1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1882 | h1882
                                · linarith only [h0, h1721, h1882, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1884 | h1884
                                  · rcases h2bigk with h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c
                                    · have p1885_0 := h1885c.1
                                      have p1885_1 := h1885c.2.1
                                      have p1885_2 := h1885c.2.2.1
                                      have p1885_3 := h1885c.2.2.2
                                      linarith only [hlam, p1885_0]
                                    · have p1885_0 := h1885c.1
                                      have p1885_1 := h1885c.2.1
                                      have p1885_2 := h1885c.2.2.1
                                      have p1885_3 := h1885c.2.2.2
                                      linarith only [h0, hlam, p1885_0]
                                    · have p1885_0 := h1885c.1
                                      have p1885_1 := h1885c.2.1
                                      have p1885_2 := h1885c.2.2.1
                                      have p1885_3 := h1885c.2.2.2
                                      rcases p1885_3 (m.d 0 2) (by simp) with h1888 | h1888
                                      · rcases p1885_3 (m.d 1 2) (by simp) with h1889 | h1889
                                        · rcases p1885_3 (m.d 2 3) (by simp) with h1890 | h1890
                                          · linarith only [h1890, hlam, p1885_0]
                                          · rcases p1885_3 (m.d 2 4) (by simp) with h1892 | h1892
                                            · linarith only [h1721, h1892, hlam]
                                            · linarith only [h1878, h1892, hlam]
                                        · linarith only [h1864, h1889, hlam]
                                      · linarith only [h1888, hlam, p1885_0]
                                    · have p1885_0 := h1885c.1
                                      have p1885_1 := h1885c.2.1
                                      have p1885_2 := h1885c.2.2.1
                                      have p1885_3 := h1885c.2.2.2
                                      rcases p1885_3 (m.d 0 2) (by simp) with h1897 | h1897
                                      · rcases p1885_3 (m.d 1 2) (by simp) with h1898 | h1898
                                        · rcases p1885_3 (m.d 2 3) (by simp) with h1899 | h1899
                                          · linarith only [h1720, h1899, hlam]
                                          · rcases p1885_3 (m.d 2 4) (by simp) with h1901 | h1901
                                            · linarith only [h1901, hlam, p1885_0]
                                            · rcases p1885_3 (m.d 2 5) (by simp) with h1903 | h1903
                                              · linarith only [h1722, h1903, hlam]
                                              · linarith only [h1882, h1903, hlam]
                                        · linarith only [h1865, h1898, hlam]
                                      · linarith only [h1897, hlam, p1885_0]
                                    · have p1885_0 := h1885c.1
                                      have p1885_1 := h1885c.2.1
                                      have p1885_2 := h1885c.2.2.1
                                      have p1885_3 := h1885c.2.2.2
                                      linarith only [h0, hlam, hphi, ht01, ht0b, ht5b, p1885_1, u1elo1, u5ehi2]
                                    · have p1885_0 := h1885c.1
                                      have p1885_1 := h1885c.2.1
                                      have p1885_2 := h1885c.2.2.1
                                      have p1885_3 := h1885c.2.2.2
                                      linarith only [h1721, h1863, hlam, hphi, ht01, ht0b, ht5b, p1885_1, u1elo1, u5ehi0]
                                    · have p1885_0 := h1885c.1
                                      have p1885_1 := h1885c.2.1
                                      have p1885_2 := h1885c.2.2.1
                                      have p1885_3 := h1885c.2.2.2
                                      linarith only [hlam, p1885_0]
                                    · have p1885_0 := h1885c.1
                                      have p1885_1 := h1885c.2.1
                                      have p1885_2 := h1885c.2.2.1
                                      have p1885_3 := h1885c.2.2.2
                                      rcases p1885_3 (m.d 0 2) (by simp) with h1911 | h1911
                                      · linarith only [h0, h1911, hlam]
                                      · linarith only [h1720, h1911, hlam]
                                    · have p1885_0 := h1885c.1
                                      have p1885_1 := h1885c.2.1
                                      have p1885_2 := h1885c.2.2.1
                                      have p1885_3 := h1885c.2.2.2
                                      rcases p1885_3 (m.d 0 2) (by simp) with h1914 | h1914
                                      · linarith only [h0, h1914, hlam]
                                      · linarith only [h1721, h1914, hlam]
                                    · have p1885_0 := h1885c.1
                                      have p1885_1 := h1885c.2.1
                                      have p1885_2 := h1885c.2.2.1
                                      have p1885_3 := h1885c.2.2.2
                                      linarith only [hlam, hphi, ht01, ht0b, ht5b, p1885_1, u1elo1, u5ehi2]
                                    · have p1885_0 := h1885c.1
                                      have p1885_1 := h1885c.2.1
                                      have p1885_2 := h1885c.2.2.1
                                      have p1885_3 := h1885c.2.2.2
                                      linarith only [h1720, hlam, p1885_0]
                                    · have p1885_0 := h1885c.1
                                      have p1885_1 := h1885c.2.1
                                      have p1885_2 := h1885c.2.2.1
                                      have p1885_3 := h1885c.2.2.2
                                      linarith only [h1864, hlam, p1885_0]
                                    · have p1885_0 := h1885c.1
                                      have p1885_1 := h1885c.2.1
                                      have p1885_2 := h1885c.2.2.1
                                      have p1885_3 := h1885c.2.2.2
                                      linarith only [hlam, p1885_0]
                                    · have p1885_0 := h1885c.1
                                      have p1885_1 := h1885c.2.1
                                      have p1885_2 := h1885c.2.2.1
                                      have p1885_3 := h1885c.2.2.2
                                      linarith only [h1878, hlam, p1885_1]
                                    · have p1885_0 := h1885c.1
                                      have p1885_1 := h1885c.2.1
                                      have p1885_2 := h1885c.2.2.1
                                      have p1885_3 := h1885c.2.2.2
                                      linarith only [h1880, hlam, p1885_1]
                                    · have p1885_0 := h1885c.1
                                      have p1885_1 := h1885c.2.1
                                      have p1885_2 := h1885c.2.2.1
                                      have p1885_3 := h1885c.2.2.2
                                      linarith only [h1721, hlam, p1885_0]
                                    · have p1885_0 := h1885c.1
                                      have p1885_1 := h1885c.2.1
                                      have p1885_2 := h1885c.2.2.1
                                      have p1885_3 := h1885c.2.2.2
                                      linarith only [h1865, hlam, p1885_0]
                                    · have p1885_0 := h1885c.1
                                      have p1885_1 := h1885c.2.1
                                      have p1885_2 := h1885c.2.2.1
                                      have p1885_3 := h1885c.2.2.2
                                      linarith only [h1721, h1863, h1882, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1885_1]
                                    · have p1885_0 := h1885c.1
                                      have p1885_1 := h1885c.2.1
                                      have p1885_2 := h1885c.2.2.1
                                      have p1885_3 := h1885c.2.2.2
                                      linarith only [hlam, p1885_0]
                                    · have p1885_0 := h1885c.1
                                      have p1885_1 := h1885c.2.1
                                      have p1885_2 := h1885c.2.2.1
                                      have p1885_3 := h1885c.2.2.2
                                      linarith only [h1882, hlam, p1885_0]
                                    · have p1885_0 := h1885c.1
                                      have p1885_1 := h1885c.2.1
                                      have p1885_2 := h1885c.2.2.1
                                      have p1885_3 := h1885c.2.2.2
                                      linarith only [h1722, hlam, p1885_0]
                                    · have p1885_0 := h1885c.1
                                      have p1885_1 := h1885c.2.1
                                      have p1885_2 := h1885c.2.2.1
                                      have p1885_3 := h1885c.2.2.2
                                      linarith only [h1866, hlam, p1885_0]
                                    · have p1885_0 := h1885c.1
                                      have p1885_1 := h1885c.2.1
                                      have p1885_2 := h1885c.2.2.1
                                      have p1885_3 := h1885c.2.2.2
                                      linarith only [h0, h1722, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1885_1, u1elo1]
                                    · have p1885_0 := h1885c.1
                                      have p1885_1 := h1885c.2.1
                                      have p1885_2 := h1885c.2.2.1
                                      have p1885_3 := h1885c.2.2.2
                                      linarith only [h0, h1721, h1863, h1882, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1885_1, u1elo1]
                                    · have p1885_0 := h1885c.1
                                      have p1885_1 := h1885c.2.1
                                      have p1885_2 := h1885c.2.2.1
                                      have p1885_3 := h1885c.2.2.2
                                      linarith only [hlam, p1885_0]
                                  · linarith only [h0, h1281, h1721, h1723, h1863, h1884, hc01, hlam, hphi, u1elo1]
                          · linarith only [h0, h1561, h1721, h1863, h1877, hc01, hlam, hphi, u1elo1]
                    · linarith only [h0, h1722, h1866, hlam]
                  · linarith only [h0, h1721, h1865, hlam]
                · linarith only [h0, h1720, h1864, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1938 | h1938
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1939 | h1939
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1940 | h1940
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1941 | h1941
                      · linarith only [h1281, h1723, h1941, hc01, hlam, hphi, u1elo2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1943 | h1943
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1944 | h1944
                          · linarith only [h1561, h1863, h1939, h1944, hc01, hlam, hphi, u1elo1]
                          · linarith only [h1941, h1943, h1944, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1947 | h1947
                          · linarith only [h1281, h1723, h1863, h1947, hc01, hlam, hphi, u1elo3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1949 | h1949
                            · linarith only [h1281, h1941, h1949, hc01, hc23, hlam, hphi, ht12]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1951 | h1951
                              · linarith only [h0, h1281, h1721, h1943, h1949, h1951, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1953 | h1953
                                · linarith only [h0, h1281, h1721, h1941, h1947, h1953, hc01, hlam, hphi, u1elo1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1955 | h1955
                                  · linarith only [h1281, h1941, h1947, h1955, hc01, hc34, hlam, hphi, ht12, ht23]
                                  · linarith only [h1281, h1941, h1955, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h1722, h1940, hlam]
                  · linarith only [h0, h1561, h1721, h1722, h1939, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi2]
                · linarith only [h0, h1720, h1938, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1961 | h1961
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1962 | h1962
              · linarith only [h1720, h1722, h1961, h1962, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1964 | h1964
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1965 | h1965
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1966 | h1966
                    · linarith only [h1720, h1722, h1966, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1968 | h1968
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1969 | h1969
                        · linarith only [h1964, h1966, h1969, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1971 | h1971
                          · linarith only [h1561, h1962, h1968, h1969, h1971, hc01, hc35, hlam, hphi, ht12, ht23]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1973 | h1973
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1974 | h1974
                              · linarith only [h0, h1720, h1966, h1969, h1974, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1976 | h1976
                                · linarith only [h1561, h1971, h1976, hc01, hc24, hlam, hphi, ht12]
                                · linarith only [h0, h1720, h1966, h1973, h1976, hc34, hc45, hlam, hphi]
                            · linarith only [h1281, h1961, h1969, h1973, hc23, hc35, hlam, hphi]
                      · linarith only [h1281, h1961, h1968, hlam]
                  · linarith only [h0, h1721, h1965, hlam]
                · linarith only [h0, h1720, h1964, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1983 | h1983
              · linarith only [h1721, h1722, h1983, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1985 | h1985
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1986 | h1986
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1987 | h1987
                    · linarith only [h0, h1722, h1987, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1989 | h1989
                      · linarith only [h1281, h1961, h1989, hc01, hlam, hphi, u1elo2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1991 | h1991
                        · linarith only [h1985, h1987, h1991, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1993 | h1993
                          · linarith only [h1281, h1961, h1983, h1986, h1993, hc01, hlam, hphi, u1elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1995 | h1995
                            · linarith only [h1720, h1961, h1995, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1997 | h1997
                              · linarith only [h1281, h1721, h1991, h1995, h1997, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1999 | h1999
                                · linarith only [h0, h1721, h1987, h1997, h1999, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2001 | h2001
                                  · linarith only [h0, h1721, h1987, h1995, h1999, h2001, hc23, hc34, hlam, hphi]
                                  · linarith only [h1281, h1989, h2001, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h0, h1721, h1986, hlam]
                · linarith only [h0, h1720, h1985, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2006 | h2006
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2007 | h2007
            · linarith only [h1720, h1721, h2007, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2009 | h2009
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2010 | h2010
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2011 | h2011
                  · linarith only [h1721, h2006, h2011, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2013 | h2013
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2014 | h2014
                      · linarith only [h1281, h2007, h2014, hc01, hlam, hphi, u1elo2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2016 | h2016
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2017 | h2017
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2018 | h2018
                            · linarith only [h2014, h2016, h2018, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2020 | h2020
                              · linarith only [h0, h1720, h2011, h2018, h2020, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                              · linarith only [h2010, h2011, h2016, h2018, h2020, hc23, hc34, hlam, hphi]
                          · linarith only [h1718, h2009, h2010, h2011, h2016, h2017, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2024 | h2024
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2025 | h2025
                            · linarith only [h0, h1720, h2007, h2011, h2025, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2027 | h2027
                              · linarith only [h0, h1720, h2011, h2025, h2027, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2029 | h2029
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2030 | h2030
                                  · rcases h2bigk with h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c
                                    · have p2031_0 := h2031c.1
                                      have p2031_1 := h2031c.2.1
                                      have p2031_2 := h2031c.2.2.1
                                      have p2031_3 := h2031c.2.2.2
                                      linarith only [hlam, p2031_0]
                                    · have p2031_0 := h2031c.1
                                      have p2031_1 := h2031c.2.1
                                      have p2031_2 := h2031c.2.2.1
                                      have p2031_3 := h2031c.2.2.2
                                      linarith only [h0, hlam, p2031_0]
                                    · have p2031_0 := h2031c.1
                                      have p2031_1 := h2031c.2.1
                                      have p2031_2 := h2031c.2.2.1
                                      have p2031_3 := h2031c.2.2.2
                                      linarith only [h0, h2011, h2025, hc23, hc34, hlam, hphi, p2031_1]
                                    · have p2031_0 := h2031c.1
                                      have p2031_1 := h2031c.2.1
                                      have p2031_2 := h2031c.2.2.1
                                      have p2031_3 := h2031c.2.2.2
                                      linarith only [h1721, hlam, p2031_0]
                                    · have p2031_0 := h2031c.1
                                      have p2031_1 := h2031c.2.1
                                      have p2031_2 := h2031c.2.2.1
                                      have p2031_3 := h2031c.2.2.2
                                      linarith only [h0, h2011, h2025, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2031_1, u5ehi2]
                                    · have p2031_0 := h2031c.1
                                      have p2031_1 := h2031c.2.1
                                      have p2031_2 := h2031c.2.2.1
                                      have p2031_3 := h2031c.2.2.2
                                      linarith only [h2011, h2025, hc02, hc34, hlam, hphi, ht23, p2031_1]
                                    · have p2031_0 := h2031c.1
                                      have p2031_1 := h2031c.2.1
                                      have p2031_2 := h2031c.2.2.1
                                      have p2031_3 := h2031c.2.2.2
                                      linarith only [hlam, p2031_0]
                                    · have p2031_0 := h2031c.1
                                      have p2031_1 := h2031c.2.1
                                      have p2031_2 := h2031c.2.2.1
                                      have p2031_3 := h2031c.2.2.2
                                      linarith only [h2011, h2025, hc23, hc34, hlam, hphi, p2031_1]
                                    · have p2031_0 := h2031c.1
                                      have p2031_1 := h2031c.2.1
                                      have p2031_2 := h2031c.2.2.1
                                      have p2031_3 := h2031c.2.2.2
                                      linarith only [h2011, hlam, p2031_0]
                                    · have p2031_0 := h2031c.1
                                      have p2031_1 := h2031c.2.1
                                      have p2031_2 := h2031c.2.2.1
                                      have p2031_3 := h2031c.2.2.2
                                      linarith only [h2011, h2025, h2029, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2031_1, u5ehi4]
                                    · have p2031_0 := h2031c.1
                                      have p2031_1 := h2031c.2.1
                                      have p2031_2 := h2031c.2.2.1
                                      have p2031_3 := h2031c.2.2.2
                                      linarith only [h1720, hlam, p2031_0]
                                    · have p2031_0 := h2031c.1
                                      have p2031_1 := h2031c.2.1
                                      have p2031_2 := h2031c.2.2.1
                                      have p2031_3 := h2031c.2.2.2
                                      linarith only [h2010, hlam, p2031_0]
                                    · have p2031_0 := h2031c.1
                                      have p2031_1 := h2031c.2.1
                                      have p2031_2 := h2031c.2.2.1
                                      have p2031_3 := h2031c.2.2.2
                                      linarith only [hlam, p2031_0]
                                    · have p2031_0 := h2031c.1
                                      have p2031_1 := h2031c.2.1
                                      have p2031_2 := h2031c.2.2.1
                                      have p2031_3 := h2031c.2.2.2
                                      linarith only [h2025, hlam, p2031_1]
                                    · have p2031_0 := h2031c.1
                                      have p2031_1 := h2031c.2.1
                                      have p2031_2 := h2031c.2.2.1
                                      have p2031_3 := h2031c.2.2.2
                                      linarith only [h2027, hlam, p2031_1]
                                    · have p2031_0 := h2031c.1
                                      have p2031_1 := h2031c.2.1
                                      have p2031_2 := h2031c.2.2.1
                                      have p2031_3 := h2031c.2.2.2
                                      linarith only [h2006, h2025, h2029, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2031_1, u5ehi4]
                                    · have p2031_0 := h2031c.1
                                      have p2031_1 := h2031c.2.1
                                      have p2031_2 := h2031c.2.2.1
                                      have p2031_3 := h2031c.2.2.2
                                      linarith only [h0, h2025, hc01, hc34, hlam, hphi, ht12, ht23, p2031_1]
                                    · have p2031_0 := h2031c.1
                                      have p2031_1 := h2031c.2.1
                                      have p2031_2 := h2031c.2.2.1
                                      have p2031_3 := h2031c.2.2.2
                                      rcases p2031_3 (m.d 0 2) (by simp) with h2049 | h2049
                                      · linarith only [h1721, h2049, hlam]
                                      · linarith only [h1720, h2049, hlam]
                                    · have p2031_0 := h2031c.1
                                      have p2031_1 := h2031c.2.1
                                      have p2031_2 := h2031c.2.2.1
                                      have p2031_3 := h2031c.2.2.2
                                      linarith only [hlam, p2031_0]
                                    · have p2031_0 := h2031c.1
                                      have p2031_1 := h2031c.2.1
                                      have p2031_2 := h2031c.2.2.1
                                      have p2031_3 := h2031c.2.2.2
                                      rcases p2031_3 (m.d 0 2) (by simp) with h2053 | h2053
                                      · linarith only [h1721, h2053, hlam]
                                      · linarith only [h2006, h2053, hlam]
                                    · have p2031_0 := h2031c.1
                                      have p2031_1 := h2031c.2.1
                                      have p2031_2 := h2031c.2.2.1
                                      have p2031_3 := h2031c.2.2.2
                                      linarith only [h2006, hlam, p2031_0]
                                    · have p2031_0 := h2031c.1
                                      have p2031_1 := h2031c.2.1
                                      have p2031_2 := h2031c.2.2.1
                                      have p2031_3 := h2031c.2.2.2
                                      linarith only [h2013, hlam, p2031_0]
                                    · have p2031_0 := h2031c.1
                                      have p2031_1 := h2031c.2.1
                                      have p2031_2 := h2031c.2.2.1
                                      have p2031_3 := h2031c.2.2.2
                                      linarith only [h0, h2006, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2031_1, u1elo1]
                                    · have p2031_0 := h2031c.1
                                      have p2031_1 := h2031c.2.1
                                      have p2031_2 := h2031c.2.2.1
                                      have p2031_3 := h2031c.2.2.2
                                      linarith only [h2029, hlam, p2031_1]
                                    · have p2031_0 := h2031c.1
                                      have p2031_1 := h2031c.2.1
                                      have p2031_2 := h2031c.2.2.1
                                      have p2031_3 := h2031c.2.2.2
                                      linarith only [hlam, p2031_0]
                                  · linarith only [h0, h2006, h2011, h2025, h2029, h2030, hlam]
                                · linarith only [h0, h2006, h2011, h2029, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                          · linarith only [h1718, h2009, h2011, h2013, h2024, hlam]
                    · linarith only [h0, h2006, h2013, hlam]
                · linarith only [h0, h1720, h2010, hlam]
              · linarith only [h1721, h2006, h2009, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2067 | h2067
            · linarith only [h1720, h1721, h2067, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2069 | h2069
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2070 | h2070
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2071 | h2071
                  · linarith only [h1720, h1721, h2071, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2073 | h2073
                    · linarith only [h1720, h2006, h2071, h2073, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2075 | h2075
                      · linarith only [h2067, h2069, h2070, h2071, h2075, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2077 | h2077
                        · linarith only [h2070, h2073, h2077, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2079 | h2079
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2080 | h2080
                            · linarith only [h0, h1720, h2067, h2080, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2082 | h2082
                              · linarith only [h0, h1720, h2071, h2080, h2082, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2084 | h2084
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2085 | h2085
                                  · rcases h2bigk with h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c | h2086c
                                    · have p2086_0 := h2086c.1
                                      have p2086_1 := h2086c.2.1
                                      have p2086_2 := h2086c.2.2.1
                                      have p2086_3 := h2086c.2.2.2
                                      linarith only [hlam, p2086_0]
                                    · have p2086_0 := h2086c.1
                                      have p2086_1 := h2086c.2.1
                                      have p2086_2 := h2086c.2.2.1
                                      have p2086_3 := h2086c.2.2.2
                                      linarith only [h0, hlam, p2086_0]
                                    · have p2086_0 := h2086c.1
                                      have p2086_1 := h2086c.2.1
                                      have p2086_2 := h2086c.2.2.1
                                      have p2086_3 := h2086c.2.2.2
                                      linarith only [h0, h2073, h2080, h2084, hc23, hc34, hlam, hphi, p2086_1]
                                    · have p2086_0 := h2086c.1
                                      have p2086_1 := h2086c.2.1
                                      have p2086_2 := h2086c.2.2.1
                                      have p2086_3 := h2086c.2.2.2
                                      linarith only [h1721, hlam, p2086_0]
                                    · have p2086_0 := h2086c.1
                                      have p2086_1 := h2086c.2.1
                                      have p2086_2 := h2086c.2.2.1
                                      have p2086_3 := h2086c.2.2.2
                                      linarith only [h2006, hlam, p2086_0]
                                    · have p2086_0 := h2086c.1
                                      have p2086_1 := h2086c.2.1
                                      have p2086_2 := h2086c.2.2.1
                                      have p2086_3 := h2086c.2.2.2
                                      linarith only [h2073, h2080, h2084, hc02, hc34, hlam, hphi, ht23, p2086_1]
                                    · have p2086_0 := h2086c.1
                                      have p2086_1 := h2086c.2.1
                                      have p2086_2 := h2086c.2.2.1
                                      have p2086_3 := h2086c.2.2.2
                                      linarith only [hlam, p2086_0]
                                    · have p2086_0 := h2086c.1
                                      have p2086_1 := h2086c.2.1
                                      have p2086_2 := h2086c.2.2.1
                                      have p2086_3 := h2086c.2.2.2
                                      linarith only [h2073, h2080, h2084, hc23, hc34, hlam, hphi, p2086_1]
                                    · have p2086_0 := h2086c.1
                                      have p2086_1 := h2086c.2.1
                                      have p2086_2 := h2086c.2.2.1
                                      have p2086_3 := h2086c.2.2.2
                                      linarith only [h2071, hlam, p2086_0]
                                    · have p2086_0 := h2086c.1
                                      have p2086_1 := h2086c.2.1
                                      have p2086_2 := h2086c.2.2.1
                                      have p2086_3 := h2086c.2.2.2
                                      linarith only [h2073, hlam, p2086_0]
                                    · have p2086_0 := h2086c.1
                                      have p2086_1 := h2086c.2.1
                                      have p2086_2 := h2086c.2.2.1
                                      have p2086_3 := h2086c.2.2.2
                                      linarith only [h1720, hlam, p2086_0]
                                    · have p2086_0 := h2086c.1
                                      have p2086_1 := h2086c.2.1
                                      have p2086_2 := h2086c.2.2.1
                                      have p2086_3 := h2086c.2.2.2
                                      linarith only [h2070, hlam, p2086_0]
                                    · have p2086_0 := h2086c.1
                                      have p2086_1 := h2086c.2.1
                                      have p2086_2 := h2086c.2.2.1
                                      have p2086_3 := h2086c.2.2.2
                                      linarith only [hlam, p2086_0]
                                    · have p2086_0 := h2086c.1
                                      have p2086_1 := h2086c.2.1
                                      have p2086_2 := h2086c.2.2.1
                                      have p2086_3 := h2086c.2.2.2
                                      linarith only [h2080, hlam, p2086_1]
                                    · have p2086_0 := h2086c.1
                                      have p2086_1 := h2086c.2.1
                                      have p2086_2 := h2086c.2.2.1
                                      have p2086_3 := h2086c.2.2.2
                                      linarith only [h2082, hlam, p2086_1]
                                    · have p2086_0 := h2086c.1
                                      have p2086_1 := h2086c.2.1
                                      have p2086_2 := h2086c.2.2.1
                                      have p2086_3 := h2086c.2.2.2
                                      linarith only [h1720, h2080, hc23, hc34, hlam, hphi, p2086_1]
                                    · have p2086_0 := h2086c.1
                                      have p2086_1 := h2086c.2.1
                                      have p2086_2 := h2086c.2.2.1
                                      have p2086_3 := h2086c.2.2.2
                                      linarith only [h0, h2080, hc01, hc34, hlam, hphi, ht12, ht23, p2086_1]
                                    · have p2086_0 := h2086c.1
                                      have p2086_1 := h2086c.2.1
                                      have p2086_2 := h2086c.2.2.1
                                      have p2086_3 := h2086c.2.2.2
                                      rcases p2086_3 (m.d 0 2) (by simp) with h2104 | h2104
                                      · linarith only [h1721, h2104, hlam]
                                      · linarith only [h1720, h2104, hlam]
                                    · have p2086_0 := h2086c.1
                                      have p2086_1 := h2086c.2.1
                                      have p2086_2 := h2086c.2.2.1
                                      have p2086_3 := h2086c.2.2.2
                                      linarith only [hlam, p2086_0]
                                    · have p2086_0 := h2086c.1
                                      have p2086_1 := h2086c.2.1
                                      have p2086_2 := h2086c.2.2.1
                                      have p2086_3 := h2086c.2.2.2
                                      linarith only [h1720, h2006, h2080, hc23, hc34, hlam, hphi, p2086_1]
                                    · have p2086_0 := h2086c.1
                                      have p2086_1 := h2086c.2.1
                                      have p2086_2 := h2086c.2.2.1
                                      have p2086_3 := h2086c.2.2.2
                                      linarith only [h1720, h2082, hc23, hc35, hlam, hphi, p2086_1]
                                    · have p2086_0 := h2086c.1
                                      have p2086_1 := h2086c.2.1
                                      have p2086_2 := h2086c.2.2.1
                                      have p2086_3 := h2086c.2.2.2
                                      linarith only [h1281, h2070, h2082, hc01, hc35, hlam, hphi, ht12, ht23, p2086_1]
                                    · have p2086_0 := h2086c.1
                                      have p2086_1 := h2086c.2.1
                                      have p2086_2 := h2086c.2.2.1
                                      have p2086_3 := h2086c.2.2.2
                                      rcases p2086_3 (m.d 0 2) (by simp) with h2111 | h2111
                                      · linarith only [h2006, h2111, hlam]
                                      · linarith only [h1720, h2111, hlam]
                                    · have p2086_0 := h2086c.1
                                      have p2086_1 := h2086c.2.1
                                      have p2086_2 := h2086c.2.2.1
                                      have p2086_3 := h2086c.2.2.2
                                      linarith only [h2084, hlam, p2086_1]
                                    · have p2086_0 := h2086c.1
                                      have p2086_1 := h2086c.2.1
                                      have p2086_2 := h2086c.2.2.1
                                      have p2086_3 := h2086c.2.2.2
                                      linarith only [hlam, p2086_0]
                                  · linarith only [h1720, h1721, h2080, h2085, hc23, hc45, hlam, hphi, ht34]
                                · linarith only [h1281, h1561, h2069, h2070, h2071, h2084, hc01, hlam, hphi, u1elo3]
                          · linarith only [h1561, h2069, h2079, hlam]
                · linarith only [h0, h1720, h2070, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2120 | h2120
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2121 | h2121
                  · linarith only [h0, h1721, h2121, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2123 | h2123
                    · linarith only [h1720, h2006, h2121, h2123, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2125 | h2125
                      · linarith only [h1281, h2067, h2125, hc01, hlam, hphi, u1elo2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2127 | h2127
                        · linarith only [h2120, h2123, h2127, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2129 | h2129
                          · linarith only [h1561, h2069, h2129, hc01, hlam, hphi, u1elo3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2131 | h2131
                            · linarith only [h1720, h2067, h2131, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2133 | h2133
                              · linarith only [h0, h1720, h2121, h2127, h2129, h2133, hc13, hc45, hlam, hphi, ht34]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2135 | h2135
                                · linarith only [h0, h1720, h2121, h2129, h2131, h2135, hc23, hc34, hlam, hphi]
                                · linarith only [h1720, h1721, h2135, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h1720, h1721, h2120, hc12, hc24, hlam, hphi]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2139 | h2139
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2140 | h2140
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2141 | h2141
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2142 | h2142
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2143 | h2143
                · linarith only [h1720, h2139, h2142, h2143, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2145 | h2145
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2146 | h2146
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2147 | h2147
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2148 | h2148
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2149 | h2149
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2150 | h2150
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2151 | h2151
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2152 | h2152
                                · linarith only [h0, h2139, h2152, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2154 | h2154
                                  · linarith only [h2150, h2152, h2154, hlam]
                                  · rcases h2bigk with h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c | h2156c
                                    · have p2156_0 := h2156c.1
                                      have p2156_1 := h2156c.2.1
                                      have p2156_2 := h2156c.2.2.1
                                      have p2156_3 := h2156c.2.2.2
                                      linarith only [hlam, p2156_0]
                                    · have p2156_0 := h2156c.1
                                      have p2156_1 := h2156c.2.1
                                      have p2156_2 := h2156c.2.2.1
                                      have p2156_3 := h2156c.2.2.2
                                      linarith only [h0, hlam, p2156_0]
                                    · have p2156_0 := h2156c.1
                                      have p2156_1 := h2156c.2.1
                                      have p2156_2 := h2156c.2.2.1
                                      have p2156_3 := h2156c.2.2.2
                                      linarith only [h1720, hlam, p2156_0]
                                    · have p2156_0 := h2156c.1
                                      have p2156_1 := h2156c.2.1
                                      have p2156_2 := h2156c.2.2.1
                                      have p2156_3 := h2156c.2.2.2
                                      rcases p2156_3 (m.d 0 2) (by simp) with h2160 | h2160
                                      · rcases p2156_3 (m.d 1 2) (by simp) with h2161 | h2161
                                        · rcases p2156_3 (m.d 2 3) (by simp) with h2162 | h2162
                                          · rcases p2156_3 (m.d 2 4) (by simp) with h2163 | h2163
                                            · linarith only [h2163, hlam, p2156_0]
                                            · rcases p2156_3 (m.d 2 5) (by simp) with h2165 | h2165
                                              · linarith only [h2140, h2165, hlam]
                                              · linarith only [h2152, h2165, hlam]
                                          · linarith only [h2150, h2162, hlam]
                                        · linarith only [h2145, h2161, hlam]
                                      · linarith only [h2160, hlam, p2156_0]
                                    · have p2156_0 := h2156c.1
                                      have p2156_1 := h2156c.2.1
                                      have p2156_2 := h2156c.2.2.1
                                      have p2156_3 := h2156c.2.2.2
                                      linarith only [h0, h2143, h2151, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2156_1, u5ehi3]
                                    · have p2156_0 := h2156c.1
                                      have p2156_1 := h2156c.2.1
                                      have p2156_2 := h2156c.2.2.1
                                      have p2156_3 := h2156c.2.2.2
                                      linarith only [h2143, hc02, hc23, hlam, hphi, p2156_1]
                                    · have p2156_0 := h2156c.1
                                      have p2156_1 := h2156c.2.1
                                      have p2156_2 := h2156c.2.2.1
                                      have p2156_3 := h2156c.2.2.2
                                      linarith only [hlam, p2156_0]
                                    · have p2156_0 := h2156c.1
                                      have p2156_1 := h2156c.2.1
                                      have p2156_2 := h2156c.2.2.1
                                      have p2156_3 := h2156c.2.2.2
                                      linarith only [h2143, hlam, p2156_0]
                                    · have p2156_0 := h2156c.1
                                      have p2156_1 := h2156c.2.1
                                      have p2156_2 := h2156c.2.2.1
                                      have p2156_3 := h2156c.2.2.2
                                      rcases p2156_3 (m.d 0 2) (by simp) with h2175 | h2175
                                      · linarith only [h0, h2175, hlam]
                                      · linarith only [h2139, h2175, hlam]
                                    · have p2156_0 := h2156c.1
                                      have p2156_1 := h2156c.2.1
                                      have p2156_2 := h2156c.2.2.1
                                      have p2156_3 := h2156c.2.2.2
                                      linarith only [h2143, h2151, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2156_1, u5ehi3]
                                    · have p2156_0 := h2156c.1
                                      have p2156_1 := h2156c.2.1
                                      have p2156_2 := h2156c.2.2.1
                                      have p2156_3 := h2156c.2.2.2
                                      linarith only [h2139, h2142, h2150, h2152, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2156_1]
                                    · have p2156_0 := h2156c.1
                                      have p2156_1 := h2156c.2.1
                                      have p2156_2 := h2156c.2.2.1
                                      have p2156_3 := h2156c.2.2.2
                                      linarith only [h0, hc01, hc23, hlam, hphi, ht12, p2156_1]
                                    · have p2156_0 := h2156c.1
                                      have p2156_1 := h2156c.2.1
                                      have p2156_2 := h2156c.2.2.1
                                      have p2156_3 := h2156c.2.2.2
                                      linarith only [hlam, p2156_0]
                                    · have p2156_0 := h2156c.1
                                      have p2156_1 := h2156c.2.1
                                      have p2156_2 := h2156c.2.2.1
                                      have p2156_3 := h2156c.2.2.2
                                      linarith only [h1720, h2139, h2142, h2152, hlam, p2156_2]
                                    · have p2156_0 := h2156c.1
                                      have p2156_1 := h2156c.2.1
                                      have p2156_2 := h2156c.2.2.1
                                      have p2156_3 := h2156c.2.2.2
                                      rcases p2156_3 (m.d 0 2) (by simp) with h2183 | h2183
                                      · linarith only [h1720, h2183, hlam]
                                      · linarith only [h2140, h2183, hlam]
                                    · have p2156_0 := h2156c.1
                                      have p2156_1 := h2156c.2.1
                                      have p2156_2 := h2156c.2.2.1
                                      have p2156_3 := h2156c.2.2.2
                                      linarith only [h2139, hlam, p2156_0]
                                    · have p2156_0 := h2156c.1
                                      have p2156_1 := h2156c.2.1
                                      have p2156_2 := h2156c.2.2.1
                                      have p2156_3 := h2156c.2.2.2
                                      linarith only [h2145, hlam, p2156_0]
                                    · have p2156_0 := h2156c.1
                                      have p2156_1 := h2156c.2.1
                                      have p2156_2 := h2156c.2.2.1
                                      have p2156_3 := h2156c.2.2.2
                                      linarith only [h2150, hlam, p2156_0]
                                    · have p2156_0 := h2156c.1
                                      have p2156_1 := h2156c.2.1
                                      have p2156_2 := h2156c.2.2.1
                                      have p2156_3 := h2156c.2.2.2
                                      linarith only [hlam, p2156_0]
                                    · have p2156_0 := h2156c.1
                                      have p2156_1 := h2156c.2.1
                                      have p2156_2 := h2156c.2.2.1
                                      have p2156_3 := h2156c.2.2.2
                                      linarith only [h2152, hlam, p2156_0]
                                    · have p2156_0 := h2156c.1
                                      have p2156_1 := h2156c.2.1
                                      have p2156_2 := h2156c.2.2.1
                                      have p2156_3 := h2156c.2.2.2
                                      linarith only [h2140, hlam, p2156_0]
                                    · have p2156_0 := h2156c.1
                                      have p2156_1 := h2156c.2.1
                                      have p2156_2 := h2156c.2.2.1
                                      have p2156_3 := h2156c.2.2.2
                                      linarith only [h2146, hlam, p2156_0]
                                    · have p2156_0 := h2156c.1
                                      have p2156_1 := h2156c.2.1
                                      have p2156_2 := h2156c.2.2.1
                                      have p2156_3 := h2156c.2.2.2
                                      linarith only [h2151, hlam, p2156_0]
                                    · have p2156_0 := h2156c.1
                                      have p2156_1 := h2156c.2.1
                                      have p2156_2 := h2156c.2.2.1
                                      have p2156_3 := h2156c.2.2.2
                                      linarith only [h0, h2140, h2150, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2156_1, u1elo1]
                                    · have p2156_0 := h2156c.1
                                      have p2156_1 := h2156c.2.1
                                      have p2156_2 := h2156c.2.2.1
                                      have p2156_3 := h2156c.2.2.2
                                      linarith only [hlam, p2156_0]
                              · linarith only [h0, h2143, h2151, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h0, h2139, h2142, h2143, h2150, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                          · linarith only [h1561, h2142, h2149, hlam]
                        · linarith only [h2143, h2146, h2148, hlam]
                      · linarith only [h1281, h2141, h2147, hlam]
                    · linarith only [h0, h1718, h2139, h2140, h2142, h2146, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi4]
                  · linarith only [h0, h2139, h2145, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2203 | h2203
                · linarith only [h1720, h2140, h2203, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2205 | h2205
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2206 | h2206
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2207 | h2207
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2208 | h2208
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2209 | h2209
                          · linarith only [h1561, h2142, h2209, hc01, hlam, hphi, u1elo3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2211 | h2211
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2212 | h2212
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2213 | h2213
                                · linarith only [h1561, h2209, h2213, hc01, hc24, hlam, hphi, ht12]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2215 | h2215
                                  · linarith only [h0, h2140, h2211, h2213, h2215, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                                  · rcases h2bigk with h2217c | h2217c | h2217c | h2217c | h2217c | h2217c | h2217c | h2217c | h2217c | h2217c | h2217c | h2217c | h2217c | h2217c | h2217c | h2217c | h2217c | h2217c | h2217c | h2217c | h2217c | h2217c | h2217c | h2217c | h2217c
                                    · have p2217_0 := h2217c.1
                                      have p2217_1 := h2217c.2.1
                                      have p2217_2 := h2217c.2.2.1
                                      have p2217_3 := h2217c.2.2.2
                                      linarith only [hlam, p2217_0]
                                    · have p2217_0 := h2217c.1
                                      have p2217_1 := h2217c.2.1
                                      have p2217_2 := h2217c.2.2.1
                                      have p2217_3 := h2217c.2.2.2
                                      linarith only [h0, hlam, p2217_0]
                                    · have p2217_0 := h2217c.1
                                      have p2217_1 := h2217c.2.1
                                      have p2217_2 := h2217c.2.2.1
                                      have p2217_3 := h2217c.2.2.2
                                      linarith only [h1720, hlam, p2217_0]
                                    · have p2217_0 := h2217c.1
                                      have p2217_1 := h2217c.2.1
                                      have p2217_2 := h2217c.2.2.1
                                      have p2217_3 := h2217c.2.2.2
                                      rcases p2217_3 (m.d 0 2) (by simp) with h2221 | h2221
                                      · rcases p2217_3 (m.d 1 2) (by simp) with h2222 | h2222
                                        · rcases p2217_3 (m.d 2 3) (by simp) with h2223 | h2223
                                          · rcases p2217_3 (m.d 2 4) (by simp) with h2224 | h2224
                                            · linarith only [h2224, hlam, p2217_0]
                                            · rcases p2217_3 (m.d 2 5) (by simp) with h2226 | h2226
                                              · linarith only [h2140, h2226, hlam]
                                              · linarith only [h2213, h2226, hlam]
                                          · linarith only [h2211, h2223, hlam]
                                        · linarith only [h2205, h2222, hlam]
                                      · linarith only [h2221, hlam, p2217_0]
                                    · have p2217_0 := h2217c.1
                                      have p2217_1 := h2217c.2.1
                                      have p2217_2 := h2217c.2.2.1
                                      have p2217_3 := h2217c.2.2.2
                                      linarith only [h0, h2203, hlam, hphi, ht01, ht0b, ht5b, p2217_1, u1elo2, u5ehi2]
                                    · have p2217_0 := h2217c.1
                                      have p2217_1 := h2217c.2.1
                                      have p2217_2 := h2217c.2.2.1
                                      have p2217_3 := h2217c.2.2.2
                                      linarith only [h0, h2203, hc01, hlam, hphi, p2217_1, u1elo2]
                                    · have p2217_0 := h2217c.1
                                      have p2217_1 := h2217c.2.1
                                      have p2217_2 := h2217c.2.2.1
                                      have p2217_3 := h2217c.2.2.2
                                      linarith only [hlam, p2217_0]
                                    · have p2217_0 := h2217c.1
                                      have p2217_1 := h2217c.2.1
                                      have p2217_2 := h2217c.2.2.1
                                      have p2217_3 := h2217c.2.2.2
                                      linarith only [h2203, hlam, p2217_0]
                                    · have p2217_0 := h2217c.1
                                      have p2217_1 := h2217c.2.1
                                      have p2217_2 := h2217c.2.2.1
                                      have p2217_3 := h2217c.2.2.2
                                      rcases p2217_3 (m.d 0 2) (by simp) with h2236 | h2236
                                      · linarith only [h0, h2236, hlam]
                                      · linarith only [h2139, h2236, hlam]
                                    · have p2217_0 := h2217c.1
                                      have p2217_1 := h2217c.2.1
                                      have p2217_2 := h2217c.2.2.1
                                      have p2217_3 := h2217c.2.2.2
                                      linarith only [h2203, h2212, hlam, hphi, ht01, ht0b, ht5b, p2217_1, u1elo2, u5ehi3]
                                    · have p2217_0 := h2217c.1
                                      have p2217_1 := h2217c.2.1
                                      have p2217_2 := h2217c.2.2.1
                                      have p2217_3 := h2217c.2.2.2
                                      linarith only [h2140, h2212, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2217_1, u5ehi3]
                                    · have p2217_0 := h2217c.1
                                      have p2217_1 := h2217c.2.1
                                      have p2217_2 := h2217c.2.2.1
                                      have p2217_3 := h2217c.2.2.2
                                      linarith only [h0, hc01, hc23, hlam, hphi, ht12, p2217_1]
                                    · have p2217_0 := h2217c.1
                                      have p2217_1 := h2217c.2.1
                                      have p2217_2 := h2217c.2.2.1
                                      have p2217_3 := h2217c.2.2.2
                                      linarith only [hlam, p2217_0]
                                    · have p2217_0 := h2217c.1
                                      have p2217_1 := h2217c.2.1
                                      have p2217_2 := h2217c.2.2.1
                                      have p2217_3 := h2217c.2.2.2
                                      rcases p2217_3 (m.d 0 2) (by simp) with h2243 | h2243
                                      · linarith only [h1720, h2243, hlam]
                                      · linarith only [h2139, h2243, hlam]
                                    · have p2217_0 := h2217c.1
                                      have p2217_1 := h2217c.2.1
                                      have p2217_2 := h2217c.2.2.1
                                      have p2217_3 := h2217c.2.2.2
                                      rcases p2217_3 (m.d 0 2) (by simp) with h2246 | h2246
                                      · linarith only [h1720, h2246, hlam]
                                      · linarith only [h2140, h2246, hlam]
                                    · have p2217_0 := h2217c.1
                                      have p2217_1 := h2217c.2.1
                                      have p2217_2 := h2217c.2.2.1
                                      have p2217_3 := h2217c.2.2.2
                                      linarith only [h2139, hlam, p2217_0]
                                    · have p2217_0 := h2217c.1
                                      have p2217_1 := h2217c.2.1
                                      have p2217_2 := h2217c.2.2.1
                                      have p2217_3 := h2217c.2.2.2
                                      linarith only [h2205, hlam, p2217_0]
                                    · have p2217_0 := h2217c.1
                                      have p2217_1 := h2217c.2.1
                                      have p2217_2 := h2217c.2.2.1
                                      have p2217_3 := h2217c.2.2.2
                                      linarith only [h2211, hlam, p2217_0]
                                    · have p2217_0 := h2217c.1
                                      have p2217_1 := h2217c.2.1
                                      have p2217_2 := h2217c.2.2.1
                                      have p2217_3 := h2217c.2.2.2
                                      linarith only [hlam, p2217_0]
                                    · have p2217_0 := h2217c.1
                                      have p2217_1 := h2217c.2.1
                                      have p2217_2 := h2217c.2.2.1
                                      have p2217_3 := h2217c.2.2.2
                                      linarith only [h2213, hlam, p2217_0]
                                    · have p2217_0 := h2217c.1
                                      have p2217_1 := h2217c.2.1
                                      have p2217_2 := h2217c.2.2.1
                                      have p2217_3 := h2217c.2.2.2
                                      linarith only [h2140, hlam, p2217_0]
                                    · have p2217_0 := h2217c.1
                                      have p2217_1 := h2217c.2.1
                                      have p2217_2 := h2217c.2.2.1
                                      have p2217_3 := h2217c.2.2.2
                                      linarith only [h2206, hlam, p2217_0]
                                    · have p2217_0 := h2217c.1
                                      have p2217_1 := h2217c.2.1
                                      have p2217_2 := h2217c.2.2.1
                                      have p2217_3 := h2217c.2.2.2
                                      linarith only [h2212, hlam, p2217_0]
                                    · have p2217_0 := h2217c.1
                                      have p2217_1 := h2217c.2.1
                                      have p2217_2 := h2217c.2.2.1
                                      have p2217_3 := h2217c.2.2.2
                                      linarith only [h0, h2140, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p2217_1, u1elo1]
                                    · have p2217_0 := h2217c.1
                                      have p2217_1 := h2217c.2.1
                                      have p2217_2 := h2217c.2.2.1
                                      have p2217_3 := h2217c.2.2.2
                                      linarith only [hlam, p2217_0]
                              · linarith only [h0, h2203, h2212, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h0, h2140, h2203, h2211, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · linarith only [h2203, h2206, h2208, hlam]
                      · linarith only [h0, h2140, h2141, h2203, h2207, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
                    · linarith only [h0, h2140, h2206, hlam]
                  · linarith only [h0, h2139, h2205, hlam]
            · linarith only [h1720, h2139, h2141, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2266 | h2266
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2267 | h2267
              · linarith only [h2139, h2140, h2267, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2269 | h2269
                · linarith only [h1720, h2139, h2269, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2271 | h2271
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2272 | h2272
                    · linarith only [h1561, h2139, h2140, h2269, h2272, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2274 | h2274
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2275 | h2275
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2276 | h2276
                          · linarith only [h1561, h2267, h2276, hc01, hlam, hphi, u1elo3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2278 | h2278
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2279 | h2279
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2280 | h2280
                                · linarith only [h0, h2139, h2272, h2275, h2276, h2280, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2282 | h2282
                                  · linarith only [h0, h2272, h2280, h2282, hc01, hc34, hlam, hphi, ht12, ht23]
                                  · rcases h2bigk with h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c | h2284c
                                    · have p2284_0 := h2284c.1
                                      have p2284_1 := h2284c.2.1
                                      have p2284_2 := h2284c.2.2.1
                                      have p2284_3 := h2284c.2.2.2
                                      linarith only [hlam, p2284_0]
                                    · have p2284_0 := h2284c.1
                                      have p2284_1 := h2284c.2.1
                                      have p2284_2 := h2284c.2.2.1
                                      have p2284_3 := h2284c.2.2.2
                                      linarith only [h0, hlam, p2284_0]
                                    · have p2284_0 := h2284c.1
                                      have p2284_1 := h2284c.2.1
                                      have p2284_2 := h2284c.2.2.1
                                      have p2284_3 := h2284c.2.2.2
                                      linarith only [h1720, hlam, p2284_0]
                                    · have p2284_0 := h2284c.1
                                      have p2284_1 := h2284c.2.1
                                      have p2284_2 := h2284c.2.2.1
                                      have p2284_3 := h2284c.2.2.2
                                      linarith only [h0, h2272, h2278, h2280, hc34, hc45, hlam, hphi, p2284_1]
                                    · have p2284_0 := h2284c.1
                                      have p2284_1 := h2284c.2.1
                                      have p2284_2 := h2284c.2.2.1
                                      have p2284_3 := h2284c.2.2.2
                                      linarith only [h2140, hlam, p2284_0]
                                    · have p2284_0 := h2284c.1
                                      have p2284_1 := h2284c.2.1
                                      have p2284_2 := h2284c.2.2.1
                                      have p2284_3 := h2284c.2.2.2
                                      linarith only [h2272, hc02, hc25, hlam, hphi, p2284_1]
                                    · have p2284_0 := h2284c.1
                                      have p2284_1 := h2284c.2.1
                                      have p2284_2 := h2284c.2.2.1
                                      have p2284_3 := h2284c.2.2.2
                                      linarith only [hlam, p2284_0]
                                    · have p2284_0 := h2284c.1
                                      have p2284_1 := h2284c.2.1
                                      have p2284_2 := h2284c.2.2.1
                                      have p2284_3 := h2284c.2.2.2
                                      linarith only [h2269, hlam, p2284_0]
                                    · have p2284_0 := h2284c.1
                                      have p2284_1 := h2284c.2.1
                                      have p2284_2 := h2284c.2.2.1
                                      have p2284_3 := h2284c.2.2.2
                                      linarith only [h2272, h2278, h2280, hc34, hc45, hlam, hphi, p2284_1]
                                    · have p2284_0 := h2284c.1
                                      have p2284_1 := h2284c.2.1
                                      have p2284_2 := h2284c.2.2.1
                                      have p2284_3 := h2284c.2.2.2
                                      linarith only [h2272, hlam, p2284_0]
                                    · have p2284_0 := h2284c.1
                                      have p2284_1 := h2284c.2.1
                                      have p2284_2 := h2284c.2.2.1
                                      have p2284_3 := h2284c.2.2.2
                                      rcases p2284_3 (m.d 0 2) (by simp) with h2295 | h2295
                                      · linarith only [h2295, hlam, p2284_0]
                                      · rcases p2284_3 (m.d 1 2) (by simp) with h2297 | h2297
                                        · linarith only [h2269, h2297, hlam]
                                        · linarith only [h0, h2297, hlam]
                                    · have p2284_0 := h2284c.1
                                      have p2284_1 := h2284c.2.1
                                      have p2284_2 := h2284c.2.2.1
                                      have p2284_3 := h2284c.2.2.2
                                      linarith only [h0, hc01, hc23, hlam, hphi, ht12, p2284_1]
                                    · have p2284_0 := h2284c.1
                                      have p2284_1 := h2284c.2.1
                                      have p2284_2 := h2284c.2.2.1
                                      have p2284_3 := h2284c.2.2.2
                                      linarith only [hlam, p2284_0]
                                    · have p2284_0 := h2284c.1
                                      have p2284_1 := h2284c.2.1
                                      have p2284_2 := h2284c.2.2.1
                                      have p2284_3 := h2284c.2.2.2
                                      rcases p2284_3 (m.d 0 2) (by simp) with h2302 | h2302
                                      · linarith only [h1720, h2302, hlam]
                                      · linarith only [h2139, h2302, hlam]
                                    · have p2284_0 := h2284c.1
                                      have p2284_1 := h2284c.2.1
                                      have p2284_2 := h2284c.2.2.1
                                      have p2284_3 := h2284c.2.2.2
                                      linarith only [h2139, h2140, h2278, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2284_1]
                                    · have p2284_0 := h2284c.1
                                      have p2284_1 := h2284c.2.1
                                      have p2284_2 := h2284c.2.2.1
                                      have p2284_3 := h2284c.2.2.2
                                      linarith only [h2139, hlam, p2284_0]
                                    · have p2284_0 := h2284c.1
                                      have p2284_1 := h2284c.2.1
                                      have p2284_2 := h2284c.2.2.1
                                      have p2284_3 := h2284c.2.2.2
                                      linarith only [h2271, hlam, p2284_0]
                                    · have p2284_0 := h2284c.1
                                      have p2284_1 := h2284c.2.1
                                      have p2284_2 := h2284c.2.2.1
                                      have p2284_3 := h2284c.2.2.2
                                      linarith only [h2278, hlam, p2284_0]
                                    · have p2284_0 := h2284c.1
                                      have p2284_1 := h2284c.2.1
                                      have p2284_2 := h2284c.2.2.1
                                      have p2284_3 := h2284c.2.2.2
                                      linarith only [hlam, p2284_0]
                                    · have p2284_0 := h2284c.1
                                      have p2284_1 := h2284c.2.1
                                      have p2284_2 := h2284c.2.2.1
                                      have p2284_3 := h2284c.2.2.2
                                      linarith only [h2280, hlam, p2284_0]
                                    · have p2284_0 := h2284c.1
                                      have p2284_1 := h2284c.2.1
                                      have p2284_2 := h2284c.2.2.1
                                      have p2284_3 := h2284c.2.2.2
                                      linarith only [h2139, h2278, h2280, hc34, hc45, hlam, hphi, p2284_1]
                                    · have p2284_0 := h2284c.1
                                      have p2284_1 := h2284c.2.1
                                      have p2284_2 := h2284c.2.2.1
                                      have p2284_3 := h2284c.2.2.2
                                      linarith only [h1561, h2271, hc01, hc25, hlam, hphi, ht12, p2284_1]
                                    · have p2284_0 := h2284c.1
                                      have p2284_1 := h2284c.2.1
                                      have p2284_2 := h2284c.2.2.1
                                      have p2284_3 := h2284c.2.2.2
                                      linarith only [h2279, hlam, p2284_0]
                                    · have p2284_0 := h2284c.1
                                      have p2284_1 := h2284c.2.1
                                      have p2284_2 := h2284c.2.2.1
                                      have p2284_3 := h2284c.2.2.2
                                      rcases p2284_3 (m.d 0 2) (by simp) with h2314 | h2314
                                      · linarith only [h2140, h2314, hlam]
                                      · linarith only [h2139, h2314, hlam]
                                    · have p2284_0 := h2284c.1
                                      have p2284_1 := h2284c.2.1
                                      have p2284_2 := h2284c.2.2.1
                                      have p2284_3 := h2284c.2.2.2
                                      linarith only [hlam, p2284_0]
                              · linarith only [h1720, h2139, h2275, h2278, h2279, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                            · linarith only [h1561, h2269, h2271, h2278, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2320 | h2320
                          · linarith only [h1561, h2267, h2271, h2320, hc01, hlam, hphi, u1elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2322 | h2322
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2323 | h2323
                              · linarith only [h0, h2269, h2275, h2323, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h1561, h2269, h2271, h2323, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h1561, h2269, h2271, h2322, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h1561, h2266, h2269, h2271, h2274, hlam]
                  · linarith only [h0, h2139, h2271, hlam]
            · linarith only [h1720, h2139, h2266, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2330 | h2330
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2331 | h2331
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2332 | h2332
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2333 | h2333
                · linarith only [h1720, h2330, h2333, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2335 | h2335
                  · linarith only [h2139, h2330, h2333, h2335, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2337 | h2337
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2338 | h2338
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2339 | h2339
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2340 | h2340
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2341 | h2341
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2342 | h2342
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2343 | h2343
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2344 | h2344
                                  · linarith only [h1281, h2331, h2344, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
                                  · rcases h2bigk with h2346c | h2346c | h2346c | h2346c | h2346c | h2346c | h2346c | h2346c | h2346c | h2346c | h2346c | h2346c | h2346c | h2346c | h2346c | h2346c | h2346c | h2346c | h2346c | h2346c | h2346c | h2346c | h2346c | h2346c | h2346c
                                    · have p2346_0 := h2346c.1
                                      have p2346_1 := h2346c.2.1
                                      have p2346_2 := h2346c.2.2.1
                                      have p2346_3 := h2346c.2.2.2
                                      linarith only [hlam, p2346_0]
                                    · have p2346_0 := h2346c.1
                                      have p2346_1 := h2346c.2.1
                                      have p2346_2 := h2346c.2.2.1
                                      have p2346_3 := h2346c.2.2.2
                                      linarith only [h0, hlam, p2346_0]
                                    · have p2346_0 := h2346c.1
                                      have p2346_1 := h2346c.2.1
                                      have p2346_2 := h2346c.2.2.1
                                      have p2346_3 := h2346c.2.2.2
                                      linarith only [h1720, hlam, p2346_0]
                                    · have p2346_0 := h2346c.1
                                      have p2346_1 := h2346c.2.1
                                      have p2346_2 := h2346c.2.2.1
                                      have p2346_3 := h2346c.2.2.2
                                      linarith only [h2139, hlam, p2346_0]
                                    · have p2346_0 := h2346c.1
                                      have p2346_1 := h2346c.2.1
                                      have p2346_2 := h2346c.2.2.1
                                      have p2346_3 := h2346c.2.2.2
                                      linarith only [h0, h2335, h2338, h2343, h2344, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2346_1, u1elo2]
                                    · have p2346_0 := h2346c.1
                                      have p2346_1 := h2346c.2.1
                                      have p2346_2 := h2346c.2.2.1
                                      have p2346_3 := h2346c.2.2.2
                                      linarith only [h2335, hc02, hc24, hlam, hphi, p2346_1]
                                    · have p2346_0 := h2346c.1
                                      have p2346_1 := h2346c.2.1
                                      have p2346_2 := h2346c.2.2.1
                                      have p2346_3 := h2346c.2.2.2
                                      linarith only [hlam, p2346_0]
                                    · have p2346_0 := h2346c.1
                                      have p2346_1 := h2346c.2.1
                                      have p2346_2 := h2346c.2.2.1
                                      have p2346_3 := h2346c.2.2.2
                                      linarith only [h2333, hlam, p2346_0]
                                    · have p2346_0 := h2346c.1
                                      have p2346_1 := h2346c.2.1
                                      have p2346_2 := h2346c.2.2.1
                                      have p2346_3 := h2346c.2.2.2
                                      linarith only [h2335, hlam, p2346_0]
                                    · have p2346_0 := h2346c.1
                                      have p2346_1 := h2346c.2.1
                                      have p2346_2 := h2346c.2.2.1
                                      have p2346_3 := h2346c.2.2.2
                                      linarith only [h2335, h2338, h2343, h2344, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2346_1, u1elo2]
                                    · have p2346_0 := h2346c.1
                                      have p2346_1 := h2346c.2.1
                                      have p2346_2 := h2346c.2.2.1
                                      have p2346_3 := h2346c.2.2.2
                                      linarith only [h2330, h2343, h2344, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2346_1]
                                    · have p2346_0 := h2346c.1
                                      have p2346_1 := h2346c.2.1
                                      have p2346_2 := h2346c.2.2.1
                                      have p2346_3 := h2346c.2.2.2
                                      linarith only [h0, hc01, hc23, hlam, hphi, ht12, p2346_1]
                                    · have p2346_0 := h2346c.1
                                      have p2346_1 := h2346c.2.1
                                      have p2346_2 := h2346c.2.2.1
                                      have p2346_3 := h2346c.2.2.2
                                      linarith only [hlam, p2346_0]
                                    · have p2346_0 := h2346c.1
                                      have p2346_1 := h2346c.2.1
                                      have p2346_2 := h2346c.2.2.1
                                      have p2346_3 := h2346c.2.2.2
                                      linarith only [h0, h2330, h2335, h2343, h2344, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2346_1]
                                    · have p2346_0 := h2346c.1
                                      have p2346_1 := h2346c.2.1
                                      have p2346_2 := h2346c.2.2.1
                                      have p2346_3 := h2346c.2.2.2
                                      rcases p2346_3 (m.d 0 2) (by simp) with h2361 | h2361
                                      · linarith only [h1720, h2361, hlam]
                                      · linarith only [h2330, h2361, hlam]
                                    · have p2346_0 := h2346c.1
                                      have p2346_1 := h2346c.2.1
                                      have p2346_2 := h2346c.2.2.1
                                      have p2346_3 := h2346c.2.2.2
                                      linarith only [h2330, h2343, h2344, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2346_1]
                                    · have p2346_0 := h2346c.1
                                      have p2346_1 := h2346c.2.1
                                      have p2346_2 := h2346c.2.2.1
                                      have p2346_3 := h2346c.2.2.2
                                      linarith only [h0, h2330, h2343, h2344, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2346_1]
                                    · have p2346_0 := h2346c.1
                                      have p2346_1 := h2346c.2.1
                                      have p2346_2 := h2346c.2.2.1
                                      have p2346_3 := h2346c.2.2.2
                                      linarith only [h2341, hlam, p2346_0]
                                    · have p2346_0 := h2346c.1
                                      have p2346_1 := h2346c.2.1
                                      have p2346_2 := h2346c.2.2.1
                                      have p2346_3 := h2346c.2.2.2
                                      linarith only [hlam, p2346_0]
                                    · have p2346_0 := h2346c.1
                                      have p2346_1 := h2346c.2.1
                                      have p2346_2 := h2346c.2.2.1
                                      have p2346_3 := h2346c.2.2.2
                                      rcases p2346_3 (m.d 0 2) (by simp) with h2368 | h2368
                                      · linarith only [h2139, h2368, hlam]
                                      · linarith only [h2330, h2368, hlam]
                                    · have p2346_0 := h2346c.1
                                      have p2346_1 := h2346c.2.1
                                      have p2346_2 := h2346c.2.2.1
                                      have p2346_3 := h2346c.2.2.2
                                      linarith only [h2330, hlam, p2346_0]
                                    · have p2346_0 := h2346c.1
                                      have p2346_1 := h2346c.2.1
                                      have p2346_2 := h2346c.2.2.1
                                      have p2346_3 := h2346c.2.2.2
                                      linarith only [h2337, hlam, p2346_0]
                                    · have p2346_0 := h2346c.1
                                      have p2346_1 := h2346c.2.1
                                      have p2346_2 := h2346c.2.2.1
                                      have p2346_3 := h2346c.2.2.2
                                      linarith only [h2342, hlam, p2346_0]
                                    · have p2346_0 := h2346c.1
                                      have p2346_1 := h2346c.2.1
                                      have p2346_2 := h2346c.2.2.1
                                      have p2346_3 := h2346c.2.2.2
                                      linarith only [h2343, hlam, p2346_1]
                                    · have p2346_0 := h2346c.1
                                      have p2346_1 := h2346c.2.1
                                      have p2346_2 := h2346c.2.2.1
                                      have p2346_3 := h2346c.2.2.2
                                      linarith only [hlam, p2346_0]
                                · linarith only [h2139, h2330, h2343, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                              · linarith only [h1720, h2330, h2342, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                            · linarith only [h0, h2330, h2333, h2341, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                          · linarith only [h1561, h2332, h2340, hlam]
                        · linarith only [h2333, h2337, h2339, hlam]
                      · linarith only [h0, h2330, h2331, h2333, h2338, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
                    · linarith only [h0, h2330, h2337, hlam]
              · linarith only [h2139, h2330, h2332, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2384 | h2384
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2385 | h2385
                · linarith only [h1720, h2330, h2385, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2387 | h2387
                  · linarith only [h2139, h2330, h2385, h2387, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2389 | h2389
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2390 | h2390
                      · linarith only [h1720, h2330, h2331, h2390, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2392 | h2392
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2393 | h2393
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2394 | h2394
                            · linarith only [h2390, h2392, h2394, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                            · linarith only [h1720, h2330, h2394, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                          · linarith only [h0, h2330, h2384, h2385, h2390, h2393, hc04, hlam, hphi, ht0b, ht5b, u5ehi2]
                        · linarith only [h2385, h2389, h2392, hlam]
                    · linarith only [h0, h2330, h2389, hlam]
              · linarith only [h2139, h2330, h2384, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2401 | h2401
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2402 | h2402
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2403 | h2403
                · linarith only [h0, h1720, h2403, hc01, hlam, hphi, u1elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2405 | h2405
                  · linarith only [h2139, h2402, h2405, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2407 | h2407
                    · linarith only [h0, h2330, h2403, h2407, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2409 | h2409
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2410 | h2410
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2411 | h2411
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2412 | h2412
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2413 | h2413
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2414 | h2414
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2415 | h2415
                                  · linarith only [h1281, h2401, h2415, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
                                  · rcases h2bigk with h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c | h2417c
                                    · have p2417_0 := h2417c.1
                                      have p2417_1 := h2417c.2.1
                                      have p2417_2 := h2417c.2.2.1
                                      have p2417_3 := h2417c.2.2.2
                                      linarith only [hlam, p2417_0]
                                    · have p2417_0 := h2417c.1
                                      have p2417_1 := h2417c.2.1
                                      have p2417_2 := h2417c.2.2.1
                                      have p2417_3 := h2417c.2.2.2
                                      linarith only [h0, hlam, p2417_0]
                                    · have p2417_0 := h2417c.1
                                      have p2417_1 := h2417c.2.1
                                      have p2417_2 := h2417c.2.2.1
                                      have p2417_3 := h2417c.2.2.2
                                      linarith only [h1720, hlam, p2417_0]
                                    · have p2417_0 := h2417c.1
                                      have p2417_1 := h2417c.2.1
                                      have p2417_2 := h2417c.2.2.1
                                      have p2417_3 := h2417c.2.2.2
                                      linarith only [h2139, hlam, p2417_0]
                                    · have p2417_0 := h2417c.1
                                      have p2417_1 := h2417c.2.1
                                      have p2417_2 := h2417c.2.2.1
                                      have p2417_3 := h2417c.2.2.2
                                      linarith only [h2330, hlam, p2417_0]
                                    · have p2417_0 := h2417c.1
                                      have p2417_1 := h2417c.2.1
                                      have p2417_2 := h2417c.2.2.1
                                      have p2417_3 := h2417c.2.2.2
                                      linarith only [h0, h2407, h2409, h2411, hc01, hlam, hphi, p2417_1, u1elo2]
                                    · have p2417_0 := h2417c.1
                                      have p2417_1 := h2417c.2.1
                                      have p2417_2 := h2417c.2.2.1
                                      have p2417_3 := h2417c.2.2.2
                                      linarith only [hlam, p2417_0]
                                    · have p2417_0 := h2417c.1
                                      have p2417_1 := h2417c.2.1
                                      have p2417_2 := h2417c.2.2.1
                                      have p2417_3 := h2417c.2.2.2
                                      linarith only [h2403, hlam, p2417_0]
                                    · have p2417_0 := h2417c.1
                                      have p2417_1 := h2417c.2.1
                                      have p2417_2 := h2417c.2.2.1
                                      have p2417_3 := h2417c.2.2.2
                                      linarith only [h2405, hlam, p2417_0]
                                    · have p2417_0 := h2417c.1
                                      have p2417_1 := h2417c.2.1
                                      have p2417_2 := h2417c.2.2.1
                                      have p2417_3 := h2417c.2.2.2
                                      linarith only [h2407, hlam, p2417_0]
                                    · have p2417_0 := h2417c.1
                                      have p2417_1 := h2417c.2.1
                                      have p2417_2 := h2417c.2.2.1
                                      have p2417_3 := h2417c.2.2.2
                                      rcases p2417_3 (m.d 0 2) (by simp) with h2428 | h2428
                                      · linarith only [h2428, hlam, p2417_0]
                                      · rcases p2417_3 (m.d 1 2) (by simp) with h2430 | h2430
                                        · linarith only [h2403, h2430, hlam]
                                        · linarith only [h0, h2430, hlam]
                                    · have p2417_0 := h2417c.1
                                      have p2417_1 := h2417c.2.1
                                      have p2417_2 := h2417c.2.2.1
                                      have p2417_3 := h2417c.2.2.2
                                      linarith only [h0, hc01, hc23, hlam, hphi, ht12, p2417_1]
                                    · have p2417_0 := h2417c.1
                                      have p2417_1 := h2417c.2.1
                                      have p2417_2 := h2417c.2.2.1
                                      have p2417_3 := h2417c.2.2.2
                                      linarith only [hlam, p2417_0]
                                    · have p2417_0 := h2417c.1
                                      have p2417_1 := h2417c.2.1
                                      have p2417_2 := h2417c.2.2.1
                                      have p2417_3 := h2417c.2.2.2
                                      linarith only [h0, h2407, h2414, hc01, hc23, hlam, hphi, ht12, p2417_1]
                                    · have p2417_0 := h2417c.1
                                      have p2417_1 := h2417c.2.1
                                      have p2417_2 := h2417c.2.2.1
                                      have p2417_3 := h2417c.2.2.2
                                      linarith only [h0, h2407, hc01, hc23, hlam, hphi, ht12, p2417_1]
                                    · have p2417_0 := h2417c.1
                                      have p2417_1 := h2417c.2.1
                                      have p2417_2 := h2417c.2.2.1
                                      have p2417_3 := h2417c.2.2.2
                                      rcases p2417_3 (m.d 0 2) (by simp) with h2437 | h2437
                                      · linarith only [h2437, hlam, p2417_0]
                                      · rcases p2417_3 (m.d 1 2) (by simp) with h2439 | h2439
                                        · linarith only [h2405, h2439, hlam]
                                        · linarith only [h0, h2439, hlam]
                                    · have p2417_0 := h2417c.1
                                      have p2417_1 := h2417c.2.1
                                      have p2417_2 := h2417c.2.2.1
                                      have p2417_3 := h2417c.2.2.2
                                      linarith only [h0, hc01, hc24, hlam, hphi, ht12, p2417_1]
                                    · have p2417_0 := h2417c.1
                                      have p2417_1 := h2417c.2.1
                                      have p2417_2 := h2417c.2.2.1
                                      have p2417_3 := h2417c.2.2.2
                                      linarith only [h2412, hlam, p2417_0]
                                    · have p2417_0 := h2417c.1
                                      have p2417_1 := h2417c.2.1
                                      have p2417_2 := h2417c.2.2.1
                                      have p2417_3 := h2417c.2.2.2
                                      linarith only [hlam, p2417_0]
                                    · have p2417_0 := h2417c.1
                                      have p2417_1 := h2417c.2.1
                                      have p2417_2 := h2417c.2.2.1
                                      have p2417_3 := h2417c.2.2.2
                                      linarith only [h0, h2407, h2412, hc01, hc23, hlam, hphi, ht12, p2417_1]
                                    · have p2417_0 := h2417c.1
                                      have p2417_1 := h2417c.2.1
                                      have p2417_2 := h2417c.2.2.1
                                      have p2417_3 := h2417c.2.2.2
                                      rcases p2417_3 (m.d 0 2) (by simp) with h2446 | h2446
                                      · linarith only [h2446, hlam, p2417_0]
                                      · rcases p2417_3 (m.d 1 2) (by simp) with h2448 | h2448
                                        · linarith only [h2407, h2448, hlam]
                                        · linarith only [h0, h2448, hlam]
                                    · have p2417_0 := h2417c.1
                                      have p2417_1 := h2417c.2.1
                                      have p2417_2 := h2417c.2.2.1
                                      have p2417_3 := h2417c.2.2.2
                                      linarith only [h0, hc01, hc25, hlam, hphi, ht12, p2417_1]
                                    · have p2417_0 := h2417c.1
                                      have p2417_1 := h2417c.2.1
                                      have p2417_2 := h2417c.2.2.1
                                      have p2417_3 := h2417c.2.2.2
                                      linarith only [h2413, hlam, p2417_0]
                                    · have p2417_0 := h2417c.1
                                      have p2417_1 := h2417c.2.1
                                      have p2417_2 := h2417c.2.2.1
                                      have p2417_3 := h2417c.2.2.2
                                      linarith only [h2414, hlam, p2417_1]
                                    · have p2417_0 := h2417c.1
                                      have p2417_1 := h2417c.2.1
                                      have p2417_2 := h2417c.2.2.1
                                      have p2417_3 := h2417c.2.2.2
                                      linarith only [hlam, p2417_0]
                                · linarith only [h0, h1561, h2139, h2402, h2409, h2414, hc01, hlam, hphi, u1elo2]
                              · linarith only [h0, h2403, h2413, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h0, h2403, h2412, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h1281, h1561, h2401, h2402, h2411, hc01, hlam, hphi, u1elo2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2459 | h2459
                          · linarith only [h2409, h2410, h2459, hlam]
                          · linarith only [h1281, h1561, h2401, h2402, h2410, h2459, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h1281, h2401, h2409, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2463 | h2463
                · linarith only [h0, h1720, h2463, hc01, hlam, hphi, u1elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2465 | h2465
                  · linarith only [h0, h2139, h2465, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2467 | h2467
                    · linarith only [h0, h2330, h2467, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2469 | h2469
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2470 | h2470
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2471 | h2471
                          · linarith only [h1561, h2402, h2469, h2471, hc01, hlam, hphi, u1elo2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2473 | h2473
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2474 | h2474
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2475 | h2475
                                · linarith only [h0, h2465, h2471, h2475, hc01, hc24, hlam, hphi, ht12]
                                · linarith only [h0, h2465, h2475, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                              · linarith only [h0, h1720, h2470, h2474, hc01, hlam, hphi, u1elo2]
                            · linarith only [h0, h2463, h2473, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2480 | h2480
                          · linarith only [h1561, h2402, h2469, h2470, h2480, hc01, hc35, hlam, hphi, ht12, ht23]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2482 | h2482
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2483 | h2483
                              · linarith only [h1281, h2470, h2483, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h0, h2463, h2483, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h0, h2401, h2463, h2482, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                      · linarith only [h1281, h1561, h2401, h2469, hc01, hlam, hphi, u1elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2488 | h2488
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2489 | h2489
                · linarith only [h0, h1720, h2489, hc01, hlam, hphi, u1elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2491 | h2491
                  · linarith only [h0, h2139, h2491, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2493 | h2493
                    · linarith only [h0, h2330, h2489, h2493, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2495 | h2495
                      · linarith only [h2401, h2488, h2495, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2497 | h2497
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2498 | h2498
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2499 | h2499
                            · linarith only [h2495, h2497, h2499, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                            · linarith only [h0, h2489, h2499, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h1561, h2488, h2498, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2503 | h2503
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2504 | h2504
                            · linarith only [h0, h2489, h2495, h2504, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h0, h2489, h2504, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h1561, h2488, h2503, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2508 | h2508
                · linarith only [h0, h1720, h2508, hc01, hlam, hphi, u1elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2510 | h2510
                  · linarith only [h0, h2139, h2508, h2510, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2512 | h2512
                    · linarith only [h0, h2330, h2508, h2512, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2514 | h2514
                      · linarith only [h0, h1720, h2401, h2514, hc01, hlam, hphi, u1elo2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2516 | h2516
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2517 | h2517
                          · linarith only [h1561, h2488, h2517, hc01, hlam, hphi, u1elo3]
                          · linarith only [h2514, h2516, h2517, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2520 | h2520
                          · linarith only [h0, h1720, h2401, h2488, h2520, hc01, hlam, hphi, u1elo3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2522 | h2522
                            · linarith only [h0, h2508, h2514, h2522, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h0, h2508, h2522, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 5050000 in
set_option maxHeartbeats 5050000 in
theorem r1l7_11_12_14_25_L_0_L_I_L_I_M_IR_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
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
  rcases m.htr 0 1 3 (by decide) (by decide) with h1281 | h1281
  · exact r1l7_11_12_14_25_L_0_L_I_L_I_M_IR_x1_x0 m hb1 hb2 hb4 hb5 h0 h1281
  · exact r1l7_11_12_14_25_L_0_L_I_L_I_M_IR_x1_x1 m hb1 hb2 hb4 hb5 h0 h1281

set_option maxHeartbeats 5050000 in
set_option maxHeartbeats 5050000 in
theorem r1l7_11_12_14_25_L_0_L_I_L_I_M_IR (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
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
  · exact r1l7_11_12_14_25_L_0_L_I_L_I_M_IR_x0 m hb1 hb2 hb4 hb5 h0
  · exact r1l7_11_12_14_25_L_0_L_I_L_I_M_IR_x1 m hb1 hb2 hb4 hb5 h0

end R2N4
