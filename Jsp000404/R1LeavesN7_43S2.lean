import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6344000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_0_H_I_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1570 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1571 | h1571
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1572 | h1572
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1573 | h1573
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1574 | h1574
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1575 | h1575
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1576 | h1576
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1577 | h1577
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1578 | h1578
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1579 | h1579
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1580 | h1580
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1581 | h1581
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1582 | h1582
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1583 | h1583
                          · linarith only [h0, h1570, h1583, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                          · linarith only [h0, h1570, h1577, h1579, h1583, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                        · linarith only [h0, h1582, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h0, h1581, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h0, h1570, h1574, h1577, h1580, hc12, hlam, hphi, ht23, u3elo1]
                  · linarith only [h0, h1570, h1573, h1579, hc12, hlam, hphi, ht23, u3elo1]
                · linarith only [h0, h1572, h1578, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1591 | h1591
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1592 | h1592
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1593 | h1593
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1594 | h1594
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1595 | h1595
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1596 | h1596
                          · linarith only [h1570, h1577, h1596, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1598 | h1598
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1599 | h1599
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1600 | h1600
                                · linarith only [h1570, h1577, h1592, h1600, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1602 | h1602
                                  · linarith only [h1570, h1577, h1592, h1598, h1602, hlam]
                                  · rcases h5bigk with h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c
                                    · have p1604_0 := h1604c.1
                                      have p1604_1 := h1604c.2.1
                                      have p1604_2 := h1604c.2.2.1
                                      have p1604_3 := h1604c.2.2.2
                                      linarith only [hlam, p1604_0]
                                    · have p1604_0 := h1604c.1
                                      have p1604_1 := h1604c.2.1
                                      have p1604_2 := h1604c.2.2.1
                                      have p1604_3 := h1604c.2.2.2
                                      linarith only [h0, h1571, h1596, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1604_1, u3elo1]
                                    · have p1604_0 := h1604c.1
                                      have p1604_1 := h1604c.2.1
                                      have p1604_2 := h1604c.2.2.1
                                      have p1604_3 := h1604c.2.2.2
                                      linarith only [h0, h1571, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1604_1, u3elo1]
                                    · have p1604_0 := h1604c.1
                                      have p1604_1 := h1604c.2.1
                                      have p1604_2 := h1604c.2.2.1
                                      have p1604_3 := h1604c.2.2.2
                                      linarith only [h0, h1571, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1604_1, u3elo1]
                                    · have p1604_0 := h1604c.1
                                      have p1604_1 := h1604c.2.1
                                      have p1604_2 := h1604c.2.2.1
                                      have p1604_3 := h1604c.2.2.2
                                      linarith only [h1577, hlam, p1604_1]
                                    · have p1604_0 := h1604c.1
                                      have p1604_1 := h1604c.2.1
                                      have p1604_2 := h1604c.2.2.1
                                      have p1604_3 := h1604c.2.2.2
                                      linarith only [h1571, hlam, p1604_0]
                                    · have p1604_0 := h1604c.1
                                      have p1604_1 := h1604c.2.1
                                      have p1604_2 := h1604c.2.2.1
                                      have p1604_3 := h1604c.2.2.2
                                      linarith only [hlam, p1604_0]
                                    · have p1604_0 := h1604c.1
                                      have p1604_1 := h1604c.2.1
                                      have p1604_2 := h1604c.2.2.1
                                      have p1604_3 := h1604c.2.2.2
                                      linarith only [h0, h1571, h1599, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1604_1, u3elo1]
                                    · have p1604_0 := h1604c.1
                                      have p1604_1 := h1604c.2.1
                                      have p1604_2 := h1604c.2.2.1
                                      have p1604_3 := h1604c.2.2.2
                                      linarith only [h0, h1571, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1604_1, u3elo1]
                                    · have p1604_0 := h1604c.1
                                      have p1604_1 := h1604c.2.1
                                      have p1604_2 := h1604c.2.2.1
                                      have p1604_3 := h1604c.2.2.2
                                      linarith only [h1596, hlam, p1604_1]
                                    · have p1604_0 := h1604c.1
                                      have p1604_1 := h1604c.2.1
                                      have p1604_2 := h1604c.2.2.1
                                      have p1604_3 := h1604c.2.2.2
                                      linarith only [h1574, hlam, p1604_1]
                                    · have p1604_0 := h1604c.1
                                      have p1604_1 := h1604c.2.1
                                      have p1604_2 := h1604c.2.2.1
                                      have p1604_3 := h1604c.2.2.2
                                      linarith only [h1593, hlam, p1604_1]
                                    · have p1604_0 := h1604c.1
                                      have p1604_1 := h1604c.2.1
                                      have p1604_2 := h1604c.2.2.1
                                      have p1604_3 := h1604c.2.2.2
                                      linarith only [hlam, p1604_0]
                                    · have p1604_0 := h1604c.1
                                      have p1604_1 := h1604c.2.1
                                      have p1604_2 := h1604c.2.2.1
                                      have p1604_3 := h1604c.2.2.2
                                      linarith only [h1574, hc02, hc35, hlam, hphi, ht0b, ht5b, p1604_1]
                                    · have p1604_0 := h1604c.1
                                      have p1604_1 := h1604c.2.1
                                      have p1604_2 := h1604c.2.2.1
                                      have p1604_3 := h1604c.2.2.2
                                      linarith only [h1600, hlam, p1604_1]
                                    · have p1604_0 := h1604c.1
                                      have p1604_1 := h1604c.2.1
                                      have p1604_2 := h1604c.2.2.1
                                      have p1604_3 := h1604c.2.2.2
                                      linarith only [h1576, hlam, p1604_0]
                                    · have p1604_0 := h1604c.1
                                      have p1604_1 := h1604c.2.1
                                      have p1604_2 := h1604c.2.2.1
                                      have p1604_3 := h1604c.2.2.2
                                      linarith only [h1595, hlam, p1604_0]
                                    · have p1604_0 := h1604c.1
                                      have p1604_1 := h1604c.2.1
                                      have p1604_2 := h1604c.2.2.1
                                      have p1604_3 := h1604c.2.2.2
                                      linarith only [h1599, hlam, p1604_0]
                                    · have p1604_0 := h1604c.1
                                      have p1604_1 := h1604c.2.1
                                      have p1604_2 := h1604c.2.2.1
                                      have p1604_3 := h1604c.2.2.2
                                      linarith only [hlam, p1604_0]
                                    · have p1604_0 := h1604c.1
                                      have p1604_1 := h1604c.2.1
                                      have p1604_2 := h1604c.2.2.1
                                      have p1604_3 := h1604c.2.2.2
                                      linarith only [h1602, hlam, p1604_1]
                                    · have p1604_0 := h1604c.1
                                      have p1604_1 := h1604c.2.1
                                      have p1604_2 := h1604c.2.2.1
                                      have p1604_3 := h1604c.2.2.2
                                      linarith only [h1570, h1577, h1592, h1598, hc34, hc45, hlam, hphi, p1604_1]
                                    · have p1604_0 := h1604c.1
                                      have p1604_1 := h1604c.2.1
                                      have p1604_2 := h1604c.2.2.1
                                      have p1604_3 := h1604c.2.2.2
                                      linarith only [h1592, h1596, h1598, hc34, hc45, hlam, hphi, p1604_1]
                                    · have p1604_0 := h1604c.1
                                      have p1604_1 := h1604c.2.1
                                      have p1604_2 := h1604c.2.2.1
                                      have p1604_3 := h1604c.2.2.2
                                      linarith only [h1598, h1600, hc34, hc45, hlam, hphi, p1604_1]
                                    · have p1604_0 := h1604c.1
                                      have p1604_1 := h1604c.2.1
                                      have p1604_2 := h1604c.2.2.1
                                      have p1604_3 := h1604c.2.2.2
                                      linarith only [h1602, hc34, hc45, hlam, hphi, p1604_1]
                                    · have p1604_0 := h1604c.1
                                      have p1604_1 := h1604c.2.1
                                      have p1604_2 := h1604c.2.2.1
                                      have p1604_3 := h1604c.2.2.2
                                      linarith only [hlam, p1604_0]
                              · linarith only [h0, h1576, h1599, hc23, hlam, hphi, u3elo1]
                            · linarith only [h0, h1575, h1598, hc23, hlam, hphi, u3elo1]
                        · linarith only [h0, h1595, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h0, h1594, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h0, h1571, h1574, h1593, hc12, hlam, hphi, ht23, u3elo1]
                  · linarith only [h0, h1570, h1573, h1591, h1592, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h1572, h1591, hlam]
            · linarith only [h0, h1571, h1576, hlam]
          · linarith only [h0, h1570, h1575, hlam]
        · linarith only [h0, h1571, h1572, h1574, hc23, hlam, hphi, u3elo1]
      · linarith only [h0, h1570, h1572, h1573, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1641 | h1641
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1642 | h1642
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1643 | h1643
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1644 | h1644
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1645 | h1645
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1646 | h1646
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1647 | h1647
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1648 | h1648
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1649 | h1649
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1650 | h1650
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1651 | h1651
                          · linarith only [h0, h1570, h1651, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                          · linarith only [h1572, h1641, h1645, h1646, h1651, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h1571, h1644, h1650, hc03, hc15, hlam, hphi, ht0b, ht5b]
                      · linarith only [h1572, h1641, h1645, h1646, h1649, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                    · linarith only [h1572, h1642, h1648, hc12, hc23, hlam, hphi]
                  · linarith only [h1572, h1641, h1646, h1647, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1658 | h1658
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1659 | h1659
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1660 | h1660
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1661 | h1661
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1662 | h1662
                          · linarith only [h0, h1570, h1662, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                          · linarith only [h0, h1570, h1645, h1646, h1662, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                        · linarith only [h0, h1661, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h0, h1660, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h1572, h1642, h1659, hc12, hlam, hphi, ht23, u3elo2]
                  · linarith only [h1572, h1641, h1658, hc12, hlam, hphi, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1669 | h1669
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1670 | h1670
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1671 | h1671
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1672 | h1672
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1673 | h1673
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1674 | h1674
                          · linarith only [h0, h1570, h1645, h1674, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1676 | h1676
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1677 | h1677
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1678 | h1678
                                · linarith only [h1570, h1645, h1670, h1678, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1680 | h1680
                                  · linarith only [h1570, h1645, h1670, h1676, h1680, hlam]
                                  · rcases h5bigk with h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c
                                    · have p1682_0 := h1682c.1
                                      have p1682_1 := h1682c.2.1
                                      have p1682_2 := h1682c.2.2.1
                                      have p1682_3 := h1682c.2.2.2
                                      linarith only [hlam, p1682_0]
                                    · have p1682_0 := h1682c.1
                                      have p1682_1 := h1682c.2.1
                                      have p1682_2 := h1682c.2.2.1
                                      have p1682_3 := h1682c.2.2.2
                                      linarith only [h1572, h1642, h1669, h1674, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1682_1, u3elo1]
                                    · have p1682_0 := h1682c.1
                                      have p1682_1 := h1682c.2.1
                                      have p1682_2 := h1682c.2.2.1
                                      have p1682_3 := h1682c.2.2.2
                                      linarith only [h1572, h1642, h1669, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1682_1, u3elo1]
                                    · have p1682_0 := h1682c.1
                                      have p1682_1 := h1682c.2.1
                                      have p1682_2 := h1682c.2.2.1
                                      have p1682_3 := h1682c.2.2.2
                                      linarith only [h1572, h1642, h1669, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1682_1, u3elo1]
                                    · have p1682_0 := h1682c.1
                                      have p1682_1 := h1682c.2.1
                                      have p1682_2 := h1682c.2.2.1
                                      have p1682_3 := h1682c.2.2.2
                                      linarith only [h1645, hlam, p1682_1]
                                    · have p1682_0 := h1682c.1
                                      have p1682_1 := h1682c.2.1
                                      have p1682_2 := h1682c.2.2.1
                                      have p1682_3 := h1682c.2.2.2
                                      linarith only [h1571, hlam, p1682_0]
                                    · have p1682_0 := h1682c.1
                                      have p1682_1 := h1682c.2.1
                                      have p1682_2 := h1682c.2.2.1
                                      have p1682_3 := h1682c.2.2.2
                                      linarith only [hlam, p1682_0]
                                    · have p1682_0 := h1682c.1
                                      have p1682_1 := h1682c.2.1
                                      have p1682_2 := h1682c.2.2.1
                                      have p1682_3 := h1682c.2.2.2
                                      linarith only [h0, h1571, h1677, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1682_1, u3elo1]
                                    · have p1682_0 := h1682c.1
                                      have p1682_1 := h1682c.2.1
                                      have p1682_2 := h1682c.2.2.1
                                      have p1682_3 := h1682c.2.2.2
                                      linarith only [h0, h1571, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1682_1, u3elo1]
                                    · have p1682_0 := h1682c.1
                                      have p1682_1 := h1682c.2.1
                                      have p1682_2 := h1682c.2.2.1
                                      have p1682_3 := h1682c.2.2.2
                                      linarith only [h1674, hlam, p1682_1]
                                    · have p1682_0 := h1682c.1
                                      have p1682_1 := h1682c.2.1
                                      have p1682_2 := h1682c.2.2.1
                                      have p1682_3 := h1682c.2.2.2
                                      linarith only [h1642, hlam, p1682_1]
                                    · have p1682_0 := h1682c.1
                                      have p1682_1 := h1682c.2.1
                                      have p1682_2 := h1682c.2.2.1
                                      have p1682_3 := h1682c.2.2.2
                                      linarith only [h1671, hlam, p1682_1]
                                    · have p1682_0 := h1682c.1
                                      have p1682_1 := h1682c.2.1
                                      have p1682_2 := h1682c.2.2.1
                                      have p1682_3 := h1682c.2.2.2
                                      linarith only [hlam, p1682_0]
                                    · have p1682_0 := h1682c.1
                                      have p1682_1 := h1682c.2.1
                                      have p1682_2 := h1682c.2.2.1
                                      have p1682_3 := h1682c.2.2.2
                                      linarith only [h1572, h1642, h1669, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1682_1, u3elo1]
                                    · have p1682_0 := h1682c.1
                                      have p1682_1 := h1682c.2.1
                                      have p1682_2 := h1682c.2.2.1
                                      have p1682_3 := h1682c.2.2.2
                                      linarith only [h1678, hlam, p1682_1]
                                    · have p1682_0 := h1682c.1
                                      have p1682_1 := h1682c.2.1
                                      have p1682_2 := h1682c.2.2.1
                                      have p1682_3 := h1682c.2.2.2
                                      linarith only [h1644, hlam, p1682_0]
                                    · have p1682_0 := h1682c.1
                                      have p1682_1 := h1682c.2.1
                                      have p1682_2 := h1682c.2.2.1
                                      have p1682_3 := h1682c.2.2.2
                                      linarith only [h1673, hlam, p1682_0]
                                    · have p1682_0 := h1682c.1
                                      have p1682_1 := h1682c.2.1
                                      have p1682_2 := h1682c.2.2.1
                                      have p1682_3 := h1682c.2.2.2
                                      linarith only [h1677, hlam, p1682_0]
                                    · have p1682_0 := h1682c.1
                                      have p1682_1 := h1682c.2.1
                                      have p1682_2 := h1682c.2.2.1
                                      have p1682_3 := h1682c.2.2.2
                                      linarith only [hlam, p1682_0]
                                    · have p1682_0 := h1682c.1
                                      have p1682_1 := h1682c.2.1
                                      have p1682_2 := h1682c.2.2.1
                                      have p1682_3 := h1682c.2.2.2
                                      linarith only [h1680, hlam, p1682_1]
                                    · have p1682_0 := h1682c.1
                                      have p1682_1 := h1682c.2.1
                                      have p1682_2 := h1682c.2.2.1
                                      have p1682_3 := h1682c.2.2.2
                                      linarith only [h1570, h1645, h1670, h1676, hc34, hc45, hlam, hphi, p1682_1]
                                    · have p1682_0 := h1682c.1
                                      have p1682_1 := h1682c.2.1
                                      have p1682_2 := h1682c.2.2.1
                                      have p1682_3 := h1682c.2.2.2
                                      linarith only [h1670, h1674, h1676, hc34, hc45, hlam, hphi, p1682_1]
                                    · have p1682_0 := h1682c.1
                                      have p1682_1 := h1682c.2.1
                                      have p1682_2 := h1682c.2.2.1
                                      have p1682_3 := h1682c.2.2.2
                                      linarith only [h1676, h1678, hc34, hc45, hlam, hphi, p1682_1]
                                    · have p1682_0 := h1682c.1
                                      have p1682_1 := h1682c.2.1
                                      have p1682_2 := h1682c.2.2.1
                                      have p1682_3 := h1682c.2.2.2
                                      linarith only [h1680, hc34, hc45, hlam, hphi, p1682_1]
                                    · have p1682_0 := h1682c.1
                                      have p1682_1 := h1682c.2.1
                                      have p1682_2 := h1682c.2.2.1
                                      have p1682_3 := h1682c.2.2.2
                                      linarith only [hlam, p1682_0]
                              · linarith only [h1572, h1677, hc02, hlam, hphi, ht23, u3elo4]
                            · linarith only [h1572, h1641, h1676, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h0, h1673, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h0, h1672, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h1572, h1642, h1669, h1671, hlam]
                  · linarith only [h1572, h1641, h1669, h1670, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1714 | h1714
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1715 | h1715
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1716 | h1716
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1717 | h1717
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1718 | h1718
                          · linarith only [h0, h1570, h1718, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1720 | h1720
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1721 | h1721
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1722 | h1722
                                · linarith only [h1570, h1645, h1714, h1722, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1724 | h1724
                                  · linarith only [h1570, h1645, h1714, h1720, h1724, hlam]
                                  · rcases h5bigk with h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c | h1726c
                                    · have p1726_0 := h1726c.1
                                      have p1726_1 := h1726c.2.1
                                      have p1726_2 := h1726c.2.2.1
                                      have p1726_3 := h1726c.2.2.2
                                      linarith only [hlam, p1726_0]
                                    · have p1726_0 := h1726c.1
                                      have p1726_1 := h1726c.2.1
                                      have p1726_2 := h1726c.2.2.1
                                      have p1726_3 := h1726c.2.2.2
                                      linarith only [h0, h1571, h1669, h1718, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1726_1, u3elo2]
                                    · have p1726_0 := h1726c.1
                                      have p1726_1 := h1726c.2.1
                                      have p1726_2 := h1726c.2.2.1
                                      have p1726_3 := h1726c.2.2.2
                                      linarith only [h0, h1571, h1669, h1720, h1722, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1726_1, u3elo2]
                                    · have p1726_0 := h1726c.1
                                      have p1726_1 := h1726c.2.1
                                      have p1726_2 := h1726c.2.2.1
                                      have p1726_3 := h1726c.2.2.2
                                      linarith only [h0, h1571, h1669, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1726_1, u3elo2]
                                    · have p1726_0 := h1726c.1
                                      have p1726_1 := h1726c.2.1
                                      have p1726_2 := h1726c.2.2.1
                                      have p1726_3 := h1726c.2.2.2
                                      linarith only [h1645, hlam, p1726_1]
                                    · have p1726_0 := h1726c.1
                                      have p1726_1 := h1726c.2.1
                                      have p1726_2 := h1726c.2.2.1
                                      have p1726_3 := h1726c.2.2.2
                                      linarith only [h1571, hlam, p1726_0]
                                    · have p1726_0 := h1726c.1
                                      have p1726_1 := h1726c.2.1
                                      have p1726_2 := h1726c.2.2.1
                                      have p1726_3 := h1726c.2.2.2
                                      linarith only [hlam, p1726_0]
                                    · have p1726_0 := h1726c.1
                                      have p1726_1 := h1726c.2.1
                                      have p1726_2 := h1726c.2.2.1
                                      have p1726_3 := h1726c.2.2.2
                                      linarith only [h0, h1571, h1669, h1720, h1722, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1726_1, u3elo2]
                                    · have p1726_0 := h1726c.1
                                      have p1726_1 := h1726c.2.1
                                      have p1726_2 := h1726c.2.2.1
                                      have p1726_3 := h1726c.2.2.2
                                      linarith only [h0, h1571, h1669, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1726_1, u3elo2]
                                    · have p1726_0 := h1726c.1
                                      have p1726_1 := h1726c.2.1
                                      have p1726_2 := h1726c.2.2.1
                                      have p1726_3 := h1726c.2.2.2
                                      linarith only [h1718, hlam, p1726_1]
                                    · have p1726_0 := h1726c.1
                                      have p1726_1 := h1726c.2.1
                                      have p1726_2 := h1726c.2.2.1
                                      have p1726_3 := h1726c.2.2.2
                                      linarith only [h1642, hlam, p1726_1]
                                    · have p1726_0 := h1726c.1
                                      have p1726_1 := h1726c.2.1
                                      have p1726_2 := h1726c.2.2.1
                                      have p1726_3 := h1726c.2.2.2
                                      linarith only [h1715, hlam, p1726_1]
                                    · have p1726_0 := h1726c.1
                                      have p1726_1 := h1726c.2.1
                                      have p1726_2 := h1726c.2.2.1
                                      have p1726_3 := h1726c.2.2.2
                                      linarith only [hlam, p1726_0]
                                    · have p1726_0 := h1726c.1
                                      have p1726_1 := h1726c.2.1
                                      have p1726_2 := h1726c.2.2.1
                                      have p1726_3 := h1726c.2.2.2
                                      linarith only [h1642, hc02, hc35, hlam, hphi, ht0b, ht5b, p1726_1]
                                    · have p1726_0 := h1726c.1
                                      have p1726_1 := h1726c.2.1
                                      have p1726_2 := h1726c.2.2.1
                                      have p1726_3 := h1726c.2.2.2
                                      linarith only [h1722, hlam, p1726_1]
                                    · have p1726_0 := h1726c.1
                                      have p1726_1 := h1726c.2.1
                                      have p1726_2 := h1726c.2.2.1
                                      have p1726_3 := h1726c.2.2.2
                                      linarith only [h1644, hlam, p1726_0]
                                    · have p1726_0 := h1726c.1
                                      have p1726_1 := h1726c.2.1
                                      have p1726_2 := h1726c.2.2.1
                                      have p1726_3 := h1726c.2.2.2
                                      linarith only [h1717, hlam, p1726_0]
                                    · have p1726_0 := h1726c.1
                                      have p1726_1 := h1726c.2.1
                                      have p1726_2 := h1726c.2.2.1
                                      have p1726_3 := h1726c.2.2.2
                                      linarith only [h1721, hlam, p1726_0]
                                    · have p1726_0 := h1726c.1
                                      have p1726_1 := h1726c.2.1
                                      have p1726_2 := h1726c.2.2.1
                                      have p1726_3 := h1726c.2.2.2
                                      linarith only [hlam, p1726_0]
                                    · have p1726_0 := h1726c.1
                                      have p1726_1 := h1726c.2.1
                                      have p1726_2 := h1726c.2.2.1
                                      have p1726_3 := h1726c.2.2.2
                                      linarith only [h1724, hlam, p1726_1]
                                    · have p1726_0 := h1726c.1
                                      have p1726_1 := h1726c.2.1
                                      have p1726_2 := h1726c.2.2.1
                                      have p1726_3 := h1726c.2.2.2
                                      linarith only [h1570, h1645, h1714, h1720, hc34, hc45, hlam, hphi, p1726_1]
                                    · have p1726_0 := h1726c.1
                                      have p1726_1 := h1726c.2.1
                                      have p1726_2 := h1726c.2.2.1
                                      have p1726_3 := h1726c.2.2.2
                                      linarith only [h1714, h1718, h1720, hc34, hc45, hlam, hphi, p1726_1]
                                    · have p1726_0 := h1726c.1
                                      have p1726_1 := h1726c.2.1
                                      have p1726_2 := h1726c.2.2.1
                                      have p1726_3 := h1726c.2.2.2
                                      linarith only [h1720, h1722, hc34, hc45, hlam, hphi, p1726_1]
                                    · have p1726_0 := h1726c.1
                                      have p1726_1 := h1726c.2.1
                                      have p1726_2 := h1726c.2.2.1
                                      have p1726_3 := h1726c.2.2.2
                                      linarith only [h1724, hc34, hc45, hlam, hphi, p1726_1]
                                    · have p1726_0 := h1726c.1
                                      have p1726_1 := h1726c.2.1
                                      have p1726_2 := h1726c.2.2.1
                                      have p1726_3 := h1726c.2.2.2
                                      linarith only [hlam, p1726_0]
                              · linarith only [h0, h1669, h1721, hc01, hlam, hphi, ht12, ht23, u3elo4]
                            · linarith only [h0, h1571, h1669, h1714, h1718, h1720, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h0, h1570, h1714, h1717, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · linarith only [h0, h1570, h1714, h1716, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h1572, h1642, h1715, hc12, hc23, hlam, hphi]
                  · linarith only [h0, h1570, h1641, h1669, h1714, hc12, hlam, hphi, ht23, u3elo2]
            · linarith only [h0, h1571, h1644, hlam]
          · linarith only [h0, h1570, h1643, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1760 | h1760
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1761 | h1761
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1762 | h1762
              · linarith only [h1641, h1642, h1762, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1764 | h1764
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1765 | h1765
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1766 | h1766
                    · linarith only [h0, h1571, h1642, h1766, hc02, hlam, hphi, ht23, u3elo0]
                    · linarith only [h1572, h1641, h1764, h1766, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h1572, h1641, h1764, h1765, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1770 | h1770
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1771 | h1771
                    · linarith only [h1641, h1642, h1764, h1771, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                    · linarith only [h0, h1571, h1771, hc12, hlam, hphi, ht23, u3elo1]
                  · linarith only [h0, h1571, h1641, h1642, h1764, h1770, hc12, hlam, hphi, ht23, u3elo2]
            · linarith only [h0, h1571, h1761, hlam]
          · linarith only [h0, h1571, h1641, h1642, h1760, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1777 | h1777
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1778 | h1778
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1779 | h1779
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1780 | h1780
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1781 | h1781
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1782 | h1782
                  · linarith only [h0, h1570, h1641, h1782, hc02, hlam, hphi, ht23, u3elo0]
                  · linarith only [h1572, h1777, h1781, h1782, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1785 | h1785
                  · linarith only [h1641, h1777, h1781, h1785, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h0, h1570, h1785, hc12, hlam, hphi, ht23, u3elo1]
              · linarith only [h1641, h1777, h1780, hlam]
            · linarith only [h0, h1570, h1641, h1777, h1779, hlam]
          · linarith only [h0, h1570, h1778, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1791 | h1791
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1792 | h1792
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1793 | h1793
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1794 | h1794
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1795 | h1795
                  · linarith only [h0, h1570, h1641, h1795, hc02, hlam, hphi, ht23, u3elo0]
                  · linarith only [h1572, h1794, h1795, hc02, hc24, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1798 | h1798
                  · linarith only [h1641, h1794, h1798, hc02, hlam, hphi, ht23, u3elo2]
                  · linarith only [h0, h1570, h1794, h1798, hc12, hlam, hphi, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1801 | h1801
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1802 | h1802
                  · linarith only [h0, h1570, h1641, h1802, hc02, hlam, hphi, ht23, u3elo1]
                  · linarith only [h1572, h1801, h1802, hc02, hc24, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1805 | h1805
                  · linarith only [h1641, h1801, h1805, hc02, hlam, hphi, ht23, u3elo2]
                  · linarith only [h0, h1570, h1801, h1805, hc12, hlam, hphi, ht23, u3elo2]
            · linarith only [h0, h1571, h1792, hlam]
          · linarith only [h0, h1570, h1791, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1810 | h1810
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1811 | h1811
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1812 | h1812
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1813 | h1813
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1814 | h1814
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1815 | h1815
              · linarith only [h1570, h1571, h1815, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1817 | h1817
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1818 | h1818
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1819 | h1819
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1820 | h1820
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1821 | h1821
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1822 | h1822
                          · linarith only [h1570, h1571, h1815, h1817, h1821, h1822, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1824 | h1824
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1825 | h1825
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1826 | h1826
                                · linarith only [h1570, h1571, h1818, h1822, h1826, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1828 | h1828
                                  · linarith only [h1570, h1571, h1818, h1822, h1824, h1828, hlam]
                                  · rcases h5bigk with h1830c | h1830c | h1830c | h1830c | h1830c | h1830c | h1830c | h1830c | h1830c | h1830c | h1830c | h1830c | h1830c | h1830c | h1830c | h1830c | h1830c | h1830c | h1830c | h1830c | h1830c | h1830c | h1830c | h1830c | h1830c
                                    · have p1830_0 := h1830c.1
                                      have p1830_1 := h1830c.2.1
                                      have p1830_2 := h1830c.2.2.1
                                      have p1830_3 := h1830c.2.2.2
                                      linarith only [hlam, p1830_0]
                                    · have p1830_0 := h1830c.1
                                      have p1830_1 := h1830c.2.1
                                      have p1830_2 := h1830c.2.2.1
                                      have p1830_3 := h1830c.2.2.2
                                      linarith only [h1571, hlam, p1830_1]
                                    · have p1830_0 := h1830c.1
                                      have p1830_1 := h1830c.2.1
                                      have p1830_2 := h1830c.2.2.1
                                      have p1830_3 := h1830c.2.2.2
                                      linarith only [h0, h1814, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1830_1, u3elo1]
                                    · have p1830_0 := h1830c.1
                                      have p1830_1 := h1830c.2.1
                                      have p1830_2 := h1830c.2.2.1
                                      have p1830_3 := h1830c.2.2.2
                                      linarith only [h0, h1814, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1830_1, u3elo1]
                                    · have p1830_0 := h1830c.1
                                      have p1830_1 := h1830c.2.1
                                      have p1830_2 := h1830c.2.2.1
                                      have p1830_3 := h1830c.2.2.2
                                      linarith only [h1815, hlam, p1830_1]
                                    · have p1830_0 := h1830c.1
                                      have p1830_1 := h1830c.2.1
                                      have p1830_2 := h1830c.2.2.1
                                      have p1830_3 := h1830c.2.2.2
                                      linarith only [h1821, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1830_1, u3elo1]
                                    · have p1830_0 := h1830c.1
                                      have p1830_1 := h1830c.2.1
                                      have p1830_2 := h1830c.2.2.1
                                      have p1830_3 := h1830c.2.2.2
                                      linarith only [hlam, p1830_0]
                                    · have p1830_0 := h1830c.1
                                      have p1830_1 := h1830c.2.1
                                      have p1830_2 := h1830c.2.2.1
                                      have p1830_3 := h1830c.2.2.2
                                      linarith only [h1821, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1830_1, u3elo1]
                                    · have p1830_0 := h1830c.1
                                      have p1830_1 := h1830c.2.1
                                      have p1830_2 := h1830c.2.2.1
                                      have p1830_3 := h1830c.2.2.2
                                      linarith only [h1821, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1830_1, u3elo1]
                                    · have p1830_0 := h1830c.1
                                      have p1830_1 := h1830c.2.1
                                      have p1830_2 := h1830c.2.2.1
                                      have p1830_3 := h1830c.2.2.2
                                      linarith only [h1822, hlam, p1830_1]
                                    · have p1830_0 := h1830c.1
                                      have p1830_1 := h1830c.2.1
                                      have p1830_2 := h1830c.2.2.1
                                      have p1830_3 := h1830c.2.2.2
                                      linarith only [h1812, hlam, p1830_1]
                                    · have p1830_0 := h1830c.1
                                      have p1830_1 := h1830c.2.1
                                      have p1830_2 := h1830c.2.2.1
                                      have p1830_3 := h1830c.2.2.2
                                      linarith only [h1819, hlam, p1830_1]
                                    · have p1830_0 := h1830c.1
                                      have p1830_1 := h1830c.2.1
                                      have p1830_2 := h1830c.2.2.1
                                      have p1830_3 := h1830c.2.2.2
                                      linarith only [hlam, p1830_0]
                                    · have p1830_0 := h1830c.1
                                      have p1830_1 := h1830c.2.1
                                      have p1830_2 := h1830c.2.2.1
                                      have p1830_3 := h1830c.2.2.2
                                      linarith only [h1812, hc02, hc35, hlam, hphi, ht0b, ht5b, p1830_1]
                                    · have p1830_0 := h1830c.1
                                      have p1830_1 := h1830c.2.1
                                      have p1830_2 := h1830c.2.2.1
                                      have p1830_3 := h1830c.2.2.2
                                      linarith only [h1826, hlam, p1830_1]
                                    · have p1830_0 := h1830c.1
                                      have p1830_1 := h1830c.2.1
                                      have p1830_2 := h1830c.2.2.1
                                      have p1830_3 := h1830c.2.2.2
                                      linarith only [h1814, hlam, p1830_0]
                                    · have p1830_0 := h1830c.1
                                      have p1830_1 := h1830c.2.1
                                      have p1830_2 := h1830c.2.2.1
                                      have p1830_3 := h1830c.2.2.2
                                      linarith only [h1821, hlam, p1830_0]
                                    · have p1830_0 := h1830c.1
                                      have p1830_1 := h1830c.2.1
                                      have p1830_2 := h1830c.2.2.1
                                      have p1830_3 := h1830c.2.2.2
                                      linarith only [h1825, hlam, p1830_0]
                                    · have p1830_0 := h1830c.1
                                      have p1830_1 := h1830c.2.1
                                      have p1830_2 := h1830c.2.2.1
                                      have p1830_3 := h1830c.2.2.2
                                      linarith only [hlam, p1830_0]
                                    · have p1830_0 := h1830c.1
                                      have p1830_1 := h1830c.2.1
                                      have p1830_2 := h1830c.2.2.1
                                      have p1830_3 := h1830c.2.2.2
                                      linarith only [h1828, hlam, p1830_1]
                                    · have p1830_0 := h1830c.1
                                      have p1830_1 := h1830c.2.1
                                      have p1830_2 := h1830c.2.2.1
                                      have p1830_3 := h1830c.2.2.2
                                      linarith only [h1570, h1571, h1818, h1824, hc34, hc45, hlam, hphi, p1830_1]
                                    · have p1830_0 := h1830c.1
                                      have p1830_1 := h1830c.2.1
                                      have p1830_2 := h1830c.2.2.1
                                      have p1830_3 := h1830c.2.2.2
                                      linarith only [h1570, h1571, h1818, h1824, hc34, hc45, hlam, hphi, p1830_1]
                                    · have p1830_0 := h1830c.1
                                      have p1830_1 := h1830c.2.1
                                      have p1830_2 := h1830c.2.2.1
                                      have p1830_3 := h1830c.2.2.2
                                      linarith only [h1824, h1826, hc34, hc45, hlam, hphi, p1830_1]
                                    · have p1830_0 := h1830c.1
                                      have p1830_1 := h1830c.2.1
                                      have p1830_2 := h1830c.2.2.1
                                      have p1830_3 := h1830c.2.2.2
                                      linarith only [h1828, hc34, hc45, hlam, hphi, p1830_1]
                                    · have p1830_0 := h1830c.1
                                      have p1830_1 := h1830c.2.1
                                      have p1830_2 := h1830c.2.2.1
                                      have p1830_3 := h1830c.2.2.2
                                      linarith only [hlam, p1830_0]
                              · linarith only [h0, h1814, h1825, hc23, hlam, hphi, u3elo1]
                            · linarith only [h0, h1813, h1824, hc23, hlam, hphi, u3elo1]
                        · linarith only [h0, h1814, h1821, hlam]
                      · linarith only [h0, h1570, h1818, h1820, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h0, h1570, h1812, h1817, h1818, h1819, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h1570, h1811, h1817, h1818, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h1810, h1817, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1863 | h1863
              · linarith only [h0, h1570, h1814, h1863, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1865 | h1865
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1866 | h1866
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1867 | h1867
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1868 | h1868
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1869 | h1869
                        · linarith only [h0, h1570, h1814, h1866, h1869, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                        · linarith only [h0, h1570, h1866, h1869, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · linarith only [h0, h1570, h1866, h1868, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h1812, h1814, h1865, h1867, hc23, hlam, hphi, u3elo4]
                  · linarith only [h0, h1570, h1811, h1865, h1866, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h1810, h1814, h1865, hc12, hlam, hphi, ht23, u3elo4]
          · linarith only [h0, h1570, h1813, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1877 | h1877
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1878 | h1878
            · linarith only [h1810, h1812, h1878, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1880 | h1880
              · linarith only [h0, h1570, h1810, h1812, h1880, hc23, hlam, hphi, u3elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1882 | h1882
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1883 | h1883
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1884 | h1884
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1885 | h1885
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1886 | h1886
                        · linarith only [h0, h1570, h1878, h1883, h1886, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                        · linarith only [h0, h1570, h1883, h1886, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · linarith only [h0, h1570, h1883, h1885, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1890 | h1890
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1891 | h1891
                        · linarith only [h0, h1570, h1878, h1883, h1891, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                        · linarith only [h0, h1570, h1883, h1891, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · linarith only [h0, h1570, h1883, h1890, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                  · linarith only [h0, h1570, h1811, h1883, hc12, hlam, hphi, ht23, u3elo1]
                · linarith only [h1810, h1878, h1882, hc12, hlam, hphi, ht23, u3elo4]
          · linarith only [h0, h1570, h1877, hlam]
      · linarith only [h0, h1570, h1810, h1811, hc23, hlam, hphi, u3elo1]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1899 | h1899
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1900 | h1900
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1901 | h1901
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1902 | h1902
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1903 | h1903
              · linarith only [h1570, h1571, h1903, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1905 | h1905
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1906 | h1906
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1907 | h1907
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1908 | h1908
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1909 | h1909
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1910 | h1910
                          · linarith only [h0, h1570, h1903, h1910, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1912 | h1912
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1913 | h1913
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1914 | h1914
                                · linarith only [h1570, h1571, h1810, h1900, h1905, h1906, h1910, h1914, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1916 | h1916
                                  · linarith only [h1570, h1571, h1906, h1910, h1912, h1916, hlam]
                                  · rcases h5bigk with h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c | h1918c
                                    · have p1918_0 := h1918c.1
                                      have p1918_1 := h1918c.2.1
                                      have p1918_2 := h1918c.2.2.1
                                      have p1918_3 := h1918c.2.2.2
                                      linarith only [hlam, p1918_0]
                                    · have p1918_0 := h1918c.1
                                      have p1918_1 := h1918c.2.1
                                      have p1918_2 := h1918c.2.2.1
                                      have p1918_3 := h1918c.2.2.2
                                      linarith only [h1571, hlam, p1918_1]
                                    · have p1918_0 := h1918c.1
                                      have p1918_1 := h1918c.2.1
                                      have p1918_2 := h1918c.2.2.1
                                      have p1918_3 := h1918c.2.2.2
                                      linarith only [h1810, h1900, h1905, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1918_1, u3elo1]
                                    · have p1918_0 := h1918c.1
                                      have p1918_1 := h1918c.2.1
                                      have p1918_2 := h1918c.2.2.1
                                      have p1918_3 := h1918c.2.2.2
                                      linarith only [h1810, h1900, h1905, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1918_1, u3elo1]
                                    · have p1918_0 := h1918c.1
                                      have p1918_1 := h1918c.2.1
                                      have p1918_2 := h1918c.2.2.1
                                      have p1918_3 := h1918c.2.2.2
                                      linarith only [h1903, hlam, p1918_1]
                                    · have p1918_0 := h1918c.1
                                      have p1918_1 := h1918c.2.1
                                      have p1918_2 := h1918c.2.2.1
                                      have p1918_3 := h1918c.2.2.2
                                      linarith only [h1571, hc01, hc15, hlam, hphi, p1918_1]
                                    · have p1918_0 := h1918c.1
                                      have p1918_1 := h1918c.2.1
                                      have p1918_2 := h1918c.2.2.1
                                      have p1918_3 := h1918c.2.2.2
                                      linarith only [hlam, p1918_0]
                                    · have p1918_0 := h1918c.1
                                      have p1918_1 := h1918c.2.1
                                      have p1918_2 := h1918c.2.2.1
                                      have p1918_3 := h1918c.2.2.2
                                      linarith only [h1909, h1913, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1918_1, u3elo1]
                                    · have p1918_0 := h1918c.1
                                      have p1918_1 := h1918c.2.1
                                      have p1918_2 := h1918c.2.2.1
                                      have p1918_3 := h1918c.2.2.2
                                      linarith only [h1909, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1918_1, u3elo1]
                                    · have p1918_0 := h1918c.1
                                      have p1918_1 := h1918c.2.1
                                      have p1918_2 := h1918c.2.2.1
                                      have p1918_3 := h1918c.2.2.2
                                      linarith only [h1910, hlam, p1918_1]
                                    · have p1918_0 := h1918c.1
                                      have p1918_1 := h1918c.2.1
                                      have p1918_2 := h1918c.2.2.1
                                      have p1918_3 := h1918c.2.2.2
                                      linarith only [h1900, hlam, p1918_1]
                                    · have p1918_0 := h1918c.1
                                      have p1918_1 := h1918c.2.1
                                      have p1918_2 := h1918c.2.2.1
                                      have p1918_3 := h1918c.2.2.2
                                      linarith only [h1907, hlam, p1918_1]
                                    · have p1918_0 := h1918c.1
                                      have p1918_1 := h1918c.2.1
                                      have p1918_2 := h1918c.2.2.1
                                      have p1918_3 := h1918c.2.2.2
                                      linarith only [hlam, p1918_0]
                                    · have p1918_0 := h1918c.1
                                      have p1918_1 := h1918c.2.1
                                      have p1918_2 := h1918c.2.2.1
                                      have p1918_3 := h1918c.2.2.2
                                      linarith only [h1900, hc02, hc35, hlam, hphi, ht0b, ht5b, p1918_1]
                                    · have p1918_0 := h1918c.1
                                      have p1918_1 := h1918c.2.1
                                      have p1918_2 := h1918c.2.2.1
                                      have p1918_3 := h1918c.2.2.2
                                      linarith only [h1914, hlam, p1918_1]
                                    · have p1918_0 := h1918c.1
                                      have p1918_1 := h1918c.2.1
                                      have p1918_2 := h1918c.2.2.1
                                      have p1918_3 := h1918c.2.2.2
                                      linarith only [h1902, hlam, p1918_0]
                                    · have p1918_0 := h1918c.1
                                      have p1918_1 := h1918c.2.1
                                      have p1918_2 := h1918c.2.2.1
                                      have p1918_3 := h1918c.2.2.2
                                      linarith only [h1909, hlam, p1918_0]
                                    · have p1918_0 := h1918c.1
                                      have p1918_1 := h1918c.2.1
                                      have p1918_2 := h1918c.2.2.1
                                      have p1918_3 := h1918c.2.2.2
                                      linarith only [h1913, hlam, p1918_0]
                                    · have p1918_0 := h1918c.1
                                      have p1918_1 := h1918c.2.1
                                      have p1918_2 := h1918c.2.2.1
                                      have p1918_3 := h1918c.2.2.2
                                      linarith only [hlam, p1918_0]
                                    · have p1918_0 := h1918c.1
                                      have p1918_1 := h1918c.2.1
                                      have p1918_2 := h1918c.2.2.1
                                      have p1918_3 := h1918c.2.2.2
                                      linarith only [h1916, hlam, p1918_1]
                                    · have p1918_0 := h1918c.1
                                      have p1918_1 := h1918c.2.1
                                      have p1918_2 := h1918c.2.2.1
                                      have p1918_3 := h1918c.2.2.2
                                      linarith only [h1570, h1571, h1906, h1912, hc34, hc45, hlam, hphi, p1918_1]
                                    · have p1918_0 := h1918c.1
                                      have p1918_1 := h1918c.2.1
                                      have p1918_2 := h1918c.2.2.1
                                      have p1918_3 := h1918c.2.2.2
                                      linarith only [h1570, h1571, h1906, h1912, hc34, hc45, hlam, hphi, p1918_1]
                                    · have p1918_0 := h1918c.1
                                      have p1918_1 := h1918c.2.1
                                      have p1918_2 := h1918c.2.2.1
                                      have p1918_3 := h1918c.2.2.2
                                      linarith only [h1912, h1914, hc34, hc45, hlam, hphi, p1918_1]
                                    · have p1918_0 := h1918c.1
                                      have p1918_1 := h1918c.2.1
                                      have p1918_2 := h1918c.2.2.1
                                      have p1918_3 := h1918c.2.2.2
                                      linarith only [h1916, hc34, hc45, hlam, hphi, p1918_1]
                                    · have p1918_0 := h1918c.1
                                      have p1918_1 := h1918c.2.1
                                      have p1918_2 := h1918c.2.2.1
                                      have p1918_3 := h1918c.2.2.2
                                      linarith only [hlam, p1918_0]
                              · linarith only [h1810, h1913, hc02, hlam, hphi, ht23, u3elo4]
                            · linarith only [h1571, h1810, h1900, h1912, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h1810, h1900, h1902, h1909, hc13, hlam, hphi, u3elo2]
                      · linarith only [h1570, h1571, h1810, h1900, h1905, h1906, h1908, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h1810, h1900, h1907, hc12, hc23, hlam, hphi]
                  · linarith only [h1571, h1810, h1900, h1905, h1906, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1950 | h1950
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1951 | h1951
                    · linarith only [h1571, h1905, h1951, hc01, hlam, hphi, ht12, ht23, u3elo2]
                    · linarith only [h1810, h1900, h1951, hc12, hlam, hphi, ht23, u3elo2]
                  · linarith only [h1810, h1899, h1950, hc12, hlam, hphi, ht23, u3elo2]
            · linarith only [h1810, h1900, h1902, hlam]
          · linarith only [h0, h1570, h1901, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1957 | h1957
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1958 | h1958
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1959 | h1959
              · linarith only [h1570, h1571, h1959, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1961 | h1961
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1962 | h1962
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1963 | h1963
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1964 | h1964
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1965 | h1965
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1966 | h1966
                          · linarith only [h1570, h1571, h1958, h1959, h1966, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1968 | h1968
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1969 | h1969
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1970 | h1970
                                · linarith only [h1570, h1571, h1962, h1966, h1970, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1972 | h1972
                                  · linarith only [h1570, h1571, h1962, h1966, h1968, h1972, hlam]
                                  · rcases h5bigk with h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c
                                    · have p1974_0 := h1974c.1
                                      have p1974_1 := h1974c.2.1
                                      have p1974_2 := h1974c.2.2.1
                                      have p1974_3 := h1974c.2.2.2
                                      linarith only [hlam, p1974_0]
                                    · have p1974_0 := h1974c.1
                                      have p1974_1 := h1974c.2.1
                                      have p1974_2 := h1974c.2.2.1
                                      have p1974_3 := h1974c.2.2.2
                                      linarith only [h1571, hlam, p1974_1]
                                    · have p1974_0 := h1974c.1
                                      have p1974_1 := h1974c.2.1
                                      have p1974_2 := h1974c.2.2.1
                                      have p1974_3 := h1974c.2.2.2
                                      linarith only [h1900, hlam, p1974_0]
                                    · have p1974_0 := h1974c.1
                                      have p1974_1 := h1974c.2.1
                                      have p1974_2 := h1974c.2.2.1
                                      have p1974_3 := h1974c.2.2.2
                                      linarith only [h1810, h1958, h1961, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1974_1, u3elo1]
                                    · have p1974_0 := h1974c.1
                                      have p1974_1 := h1974c.2.1
                                      have p1974_2 := h1974c.2.2.1
                                      have p1974_3 := h1974c.2.2.2
                                      linarith only [h1959, hlam, p1974_1]
                                    · have p1974_0 := h1974c.1
                                      have p1974_1 := h1974c.2.1
                                      have p1974_2 := h1974c.2.2.1
                                      have p1974_3 := h1974c.2.2.2
                                      linarith only [h1965, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1974_1, u3elo1]
                                    · have p1974_0 := h1974c.1
                                      have p1974_1 := h1974c.2.1
                                      have p1974_2 := h1974c.2.2.1
                                      have p1974_3 := h1974c.2.2.2
                                      linarith only [hlam, p1974_0]
                                    · have p1974_0 := h1974c.1
                                      have p1974_1 := h1974c.2.1
                                      have p1974_2 := h1974c.2.2.1
                                      have p1974_3 := h1974c.2.2.2
                                      linarith only [h1900, h1965, hc02, hlam, hphi, ht23, p1974_1, u3elo1]
                                    · have p1974_0 := h1974c.1
                                      have p1974_1 := h1974c.2.1
                                      have p1974_2 := h1974c.2.2.1
                                      have p1974_3 := h1974c.2.2.2
                                      linarith only [h1965, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1974_1, u3elo1]
                                    · have p1974_0 := h1974c.1
                                      have p1974_1 := h1974c.2.1
                                      have p1974_2 := h1974c.2.2.1
                                      have p1974_3 := h1974c.2.2.2
                                      linarith only [h1966, hlam, p1974_1]
                                    · have p1974_0 := h1974c.1
                                      have p1974_1 := h1974c.2.1
                                      have p1974_2 := h1974c.2.2.1
                                      have p1974_3 := h1974c.2.2.2
                                      linarith only [h1571, hc01, hc25, hlam, hphi, ht12, p1974_1]
                                    · have p1974_0 := h1974c.1
                                      have p1974_1 := h1974c.2.1
                                      have p1974_2 := h1974c.2.2.1
                                      have p1974_3 := h1974c.2.2.2
                                      linarith only [h1963, hlam, p1974_1]
                                    · have p1974_0 := h1974c.1
                                      have p1974_1 := h1974c.2.1
                                      have p1974_2 := h1974c.2.2.1
                                      have p1974_3 := h1974c.2.2.2
                                      linarith only [hlam, p1974_0]
                                    · have p1974_0 := h1974c.1
                                      have p1974_1 := h1974c.2.1
                                      have p1974_2 := h1974c.2.2.1
                                      have p1974_3 := h1974c.2.2.2
                                      linarith only [h1963, h1965, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1974_1, u3elo1]
                                    · have p1974_0 := h1974c.1
                                      have p1974_1 := h1974c.2.1
                                      have p1974_2 := h1974c.2.2.1
                                      have p1974_3 := h1974c.2.2.2
                                      linarith only [h1970, hlam, p1974_1]
                                    · have p1974_0 := h1974c.1
                                      have p1974_1 := h1974c.2.1
                                      have p1974_2 := h1974c.2.2.1
                                      have p1974_3 := h1974c.2.2.2
                                      linarith only [h1958, hlam, p1974_0]
                                    · have p1974_0 := h1974c.1
                                      have p1974_1 := h1974c.2.1
                                      have p1974_2 := h1974c.2.2.1
                                      have p1974_3 := h1974c.2.2.2
                                      linarith only [h1965, hlam, p1974_0]
                                    · have p1974_0 := h1974c.1
                                      have p1974_1 := h1974c.2.1
                                      have p1974_2 := h1974c.2.2.1
                                      have p1974_3 := h1974c.2.2.2
                                      linarith only [h1969, hlam, p1974_0]
                                    · have p1974_0 := h1974c.1
                                      have p1974_1 := h1974c.2.1
                                      have p1974_2 := h1974c.2.2.1
                                      have p1974_3 := h1974c.2.2.2
                                      linarith only [hlam, p1974_0]
                                    · have p1974_0 := h1974c.1
                                      have p1974_1 := h1974c.2.1
                                      have p1974_2 := h1974c.2.2.1
                                      have p1974_3 := h1974c.2.2.2
                                      linarith only [h1972, hlam, p1974_1]
                                    · have p1974_0 := h1974c.1
                                      have p1974_1 := h1974c.2.1
                                      have p1974_2 := h1974c.2.2.1
                                      have p1974_3 := h1974c.2.2.2
                                      linarith only [h1570, h1571, h1962, h1968, hc34, hc45, hlam, hphi, p1974_1]
                                    · have p1974_0 := h1974c.1
                                      have p1974_1 := h1974c.2.1
                                      have p1974_2 := h1974c.2.2.1
                                      have p1974_3 := h1974c.2.2.2
                                      linarith only [h1570, h1571, h1962, h1968, hc34, hc45, hlam, hphi, p1974_1]
                                    · have p1974_0 := h1974c.1
                                      have p1974_1 := h1974c.2.1
                                      have p1974_2 := h1974c.2.2.1
                                      have p1974_3 := h1974c.2.2.2
                                      linarith only [h1899, h1900, h1968, hc34, hc45, hlam, hphi, p1974_1]
                                    · have p1974_0 := h1974c.1
                                      have p1974_1 := h1974c.2.1
                                      have p1974_2 := h1974c.2.2.1
                                      have p1974_3 := h1974c.2.2.2
                                      linarith only [h1972, hc34, hc45, hlam, hphi, p1974_1]
                                    · have p1974_0 := h1974c.1
                                      have p1974_1 := h1974c.2.1
                                      have p1974_2 := h1974c.2.2.1
                                      have p1974_3 := h1974c.2.2.2
                                      linarith only [hlam, p1974_0]
                              · linarith only [h1810, h1899, h1968, h1969, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                            · linarith only [h1810, h1899, h1968, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h1958, h1965, hc13, hlam, hphi, u3elo0]
                      · linarith only [h0, h1964, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h1810, h1899, h1961, h1963, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h1810, h1899, h1961, h1962, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2006 | h2006
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2007 | h2007
                    · linarith only [h1899, h1900, h1961, h2007, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2009 | h2009
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2010 | h2010
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2011 | h2011
                          · linarith only [h1570, h1571, h2010, h2011, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2013 | h2013
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2014 | h2014
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2015 | h2015
                                · linarith only [h1570, h1571, h2006, h2011, h2015, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2017 | h2017
                                  · linarith only [h1570, h1571, h1961, h2006, h2007, h2010, h2013, h2015, h2017, hc12, hlam, hphi, ht23, u3elo2]
                                  · rcases h5bigk with h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c
                                    · have p2019_0 := h2019c.1
                                      have p2019_1 := h2019c.2.1
                                      have p2019_2 := h2019c.2.2.1
                                      have p2019_3 := h2019c.2.2.2
                                      linarith only [hlam, p2019_0]
                                    · have p2019_0 := h2019c.1
                                      have p2019_1 := h2019c.2.1
                                      have p2019_2 := h2019c.2.2.1
                                      have p2019_3 := h2019c.2.2.2
                                      linarith only [h1571, hlam, p2019_1]
                                    · have p2019_0 := h2019c.1
                                      have p2019_1 := h2019c.2.1
                                      have p2019_2 := h2019c.2.2.1
                                      have p2019_3 := h2019c.2.2.2
                                      linarith only [h1900, hlam, p2019_0]
                                    · have p2019_0 := h2019c.1
                                      have p2019_1 := h2019c.2.1
                                      have p2019_2 := h2019c.2.2.1
                                      have p2019_3 := h2019c.2.2.2
                                      linarith only [h1571, h1961, h2010, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2019_1, u3elo2]
                                    · have p2019_0 := h2019c.1
                                      have p2019_1 := h2019c.2.1
                                      have p2019_2 := h2019c.2.2.1
                                      have p2019_3 := h2019c.2.2.2
                                      linarith only [h1959, hlam, p2019_1]
                                    · have p2019_0 := h2019c.1
                                      have p2019_1 := h2019c.2.1
                                      have p2019_2 := h2019c.2.2.1
                                      have p2019_3 := h2019c.2.2.2
                                      linarith only [h1961, h2010, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2019_1, u3elo2]
                                    · have p2019_0 := h2019c.1
                                      have p2019_1 := h2019c.2.1
                                      have p2019_2 := h2019c.2.2.1
                                      have p2019_3 := h2019c.2.2.2
                                      linarith only [hlam, p2019_0]
                                    · have p2019_0 := h2019c.1
                                      have p2019_1 := h2019c.2.1
                                      have p2019_2 := h2019c.2.2.1
                                      have p2019_3 := h2019c.2.2.2
                                      linarith only [h2007, hlam, p2019_0]
                                    · have p2019_0 := h2019c.1
                                      have p2019_1 := h2019c.2.1
                                      have p2019_2 := h2019c.2.2.1
                                      have p2019_3 := h2019c.2.2.2
                                      linarith only [h1961, h2010, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2019_1, u3elo2]
                                    · have p2019_0 := h2019c.1
                                      have p2019_1 := h2019c.2.1
                                      have p2019_2 := h2019c.2.2.1
                                      have p2019_3 := h2019c.2.2.2
                                      linarith only [h2011, hlam, p2019_1]
                                    · have p2019_0 := h2019c.1
                                      have p2019_1 := h2019c.2.1
                                      have p2019_2 := h2019c.2.2.1
                                      have p2019_3 := h2019c.2.2.2
                                      linarith only [h1571, hc01, hc25, hlam, hphi, ht12, p2019_1]
                                    · have p2019_0 := h2019c.1
                                      have p2019_1 := h2019c.2.1
                                      have p2019_2 := h2019c.2.2.1
                                      have p2019_3 := h2019c.2.2.2
                                      linarith only [h1570, h1571, h2006, h2013, h2015, hc34, hc45, hlam, hphi, p2019_1]
                                    · have p2019_0 := h2019c.1
                                      have p2019_1 := h2019c.2.1
                                      have p2019_2 := h2019c.2.2.1
                                      have p2019_3 := h2019c.2.2.2
                                      linarith only [hlam, p2019_0]
                                    · have p2019_0 := h2019c.1
                                      have p2019_1 := h2019c.2.1
                                      have p2019_2 := h2019c.2.2.1
                                      have p2019_3 := h2019c.2.2.2
                                      linarith only [h2014, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2019_1, u3elo2]
                                    · have p2019_0 := h2019c.1
                                      have p2019_1 := h2019c.2.1
                                      have p2019_2 := h2019c.2.2.1
                                      have p2019_3 := h2019c.2.2.2
                                      linarith only [h2015, hlam, p2019_1]
                                    · have p2019_0 := h2019c.1
                                      have p2019_1 := h2019c.2.1
                                      have p2019_2 := h2019c.2.2.1
                                      have p2019_3 := h2019c.2.2.2
                                      linarith only [h1958, hlam, p2019_0]
                                    · have p2019_0 := h2019c.1
                                      have p2019_1 := h2019c.2.1
                                      have p2019_2 := h2019c.2.2.1
                                      have p2019_3 := h2019c.2.2.2
                                      linarith only [h2010, hlam, p2019_0]
                                    · have p2019_0 := h2019c.1
                                      have p2019_1 := h2019c.2.1
                                      have p2019_2 := h2019c.2.2.1
                                      have p2019_3 := h2019c.2.2.2
                                      linarith only [h2014, hlam, p2019_0]
                                    · have p2019_0 := h2019c.1
                                      have p2019_1 := h2019c.2.1
                                      have p2019_2 := h2019c.2.2.1
                                      have p2019_3 := h2019c.2.2.2
                                      linarith only [hlam, p2019_0]
                                    · have p2019_0 := h2019c.1
                                      have p2019_1 := h2019c.2.1
                                      have p2019_2 := h2019c.2.2.1
                                      have p2019_3 := h2019c.2.2.2
                                      linarith only [h2017, hlam, p2019_1]
                                    · have p2019_0 := h2019c.1
                                      have p2019_1 := h2019c.2.1
                                      have p2019_2 := h2019c.2.2.1
                                      have p2019_3 := h2019c.2.2.2
                                      linarith only [h1570, h1571, h2006, h2013, hc34, hc45, hlam, hphi, p2019_1]
                                    · have p2019_0 := h2019c.1
                                      have p2019_1 := h2019c.2.1
                                      have p2019_2 := h2019c.2.2.1
                                      have p2019_3 := h2019c.2.2.2
                                      linarith only [h1570, h1571, h2006, h2013, hc34, hc45, hlam, hphi, p2019_1]
                                    · have p2019_0 := h2019c.1
                                      have p2019_1 := h2019c.2.1
                                      have p2019_2 := h2019c.2.2.1
                                      have p2019_3 := h2019c.2.2.2
                                      linarith only [h1900, hc02, hc45, hlam, hphi, ht23, ht34, p2019_1]
                                    · have p2019_0 := h2019c.1
                                      have p2019_1 := h2019c.2.1
                                      have p2019_2 := h2019c.2.2.1
                                      have p2019_3 := h2019c.2.2.2
                                      linarith only [h2017, hc34, hc45, hlam, hphi, p2019_1]
                                    · have p2019_0 := h2019c.1
                                      have p2019_1 := h2019c.2.1
                                      have p2019_2 := h2019c.2.2.1
                                      have p2019_3 := h2019c.2.2.2
                                      linarith only [hlam, p2019_0]
                              · linarith only [h1570, h1571, h1961, h2006, h2010, h2013, h2014, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                            · linarith only [h1570, h1571, h1961, h2006, h2010, h2013, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h0, h1958, h2010, hlam]
                      · linarith only [h0, h1570, h2006, h2009, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                  · linarith only [h1810, h1899, h2006, hc12, hlam, hphi, ht23, u3elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2050 | h2050
              · linarith only [h0, h1570, h1958, h2050, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2052 | h2052
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2053 | h2053
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2054 | h2054
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2055 | h2055
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2056 | h2056
                        · linarith only [h0, h1570, h1958, h2053, h2056, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                        · linarith only [h0, h1570, h2053, h2056, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · linarith only [h0, h1570, h2053, h2055, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h1810, h1899, h2052, h2054, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h1810, h1899, h2052, h2053, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2062 | h2062
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2063 | h2063
                    · linarith only [h1899, h1900, h2052, h2063, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2065 | h2065
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2066 | h2066
                        · linarith only [h0, h1570, h1958, h2065, h2066, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                        · linarith only [h0, h1570, h2065, h2066, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · linarith only [h0, h1570, h2065, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                  · linarith only [h1810, h1899, h2062, hc12, hlam, hphi, ht23, u3elo2]
          · linarith only [h0, h1570, h1957, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2072 | h2072
        · linarith only [h1570, h1571, h1899, h2072, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2074 | h2074
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2075 | h2075
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2076 | h2076
              · linarith only [h1570, h1571, h2076, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2078 | h2078
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2079 | h2079
                  · linarith only [h1570, h1571, h1899, h2075, h2079, hc02, hlam, hphi, ht23, u3elo0]
                  · linarith only [h1810, h2078, h2079, hc02, hc24, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2082 | h2082
                  · linarith only [h1899, h2078, h2082, hc02, hc23, hlam, hphi]
                  · linarith only [h0, h1570, h2082, hc12, hlam, hphi, ht23, u3elo1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2085 | h2085
              · linarith only [h0, h1570, h2075, h2085, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2087 | h2087
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2088 | h2088
                  · linarith only [h0, h1570, h1899, h2075, h2088, hc02, hlam, hphi, ht23, u3elo4]
                  · linarith only [h1810, h2087, h2088, hc02, hc24, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2091 | h2091
                  · linarith only [h1899, h2087, h2091, hc02, hc23, hlam, hphi]
                  · linarith only [h0, h1570, h2075, h2091, hc12, hlam, hphi, ht23, u3elo4]
          · linarith only [h0, h1570, h2074, hlam]

set_option maxHeartbeats 6344000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_0_H_I_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1570 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2095 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h2096 | h2096
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2097 | h2097
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2098 | h2098
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2099 | h2099
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2100 | h2100
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2101 | h2101
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2102 | h2102
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2103 | h2103
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2104 | h2104
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2105 | h2105
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2106 | h2106
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2107 | h2107
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2108 | h2108
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2109 | h2109
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2110 | h2110
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2111 | h2111
                                · rcases h5bigk with h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c | h2112c
                                  · have p2112_0 := h2112c.1
                                    have p2112_1 := h2112c.2.1
                                    have p2112_2 := h2112c.2.2.1
                                    have p2112_3 := h2112c.2.2.2
                                    linarith only [hlam, p2112_0]
                                  · have p2112_0 := h2112c.1
                                    have p2112_1 := h2112c.2.1
                                    have p2112_2 := h2112c.2.2.1
                                    have p2112_3 := h2112c.2.2.2
                                    linarith only [h1570, h2095, h2104, h2105, h2109, h2111, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2112_1, u3elo1]
                                  · have p2112_0 := h2112c.1
                                    have p2112_1 := h2112c.2.1
                                    have p2112_2 := h2112c.2.2.1
                                    have p2112_3 := h2112c.2.2.2
                                    linarith only [h1570, h2095, h2105, h2109, h2111, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2112_1, u3elo1]
                                  · have p2112_0 := h2112c.1
                                    have p2112_1 := h2112c.2.1
                                    have p2112_2 := h2112c.2.2.1
                                    have p2112_3 := h2112c.2.2.2
                                    linarith only [h1570, h2095, h2105, h2111, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2112_1, u3elo1]
                                  · have p2112_0 := h2112c.1
                                    have p2112_1 := h2112c.2.1
                                    have p2112_2 := h2112c.2.2.1
                                    have p2112_3 := h2112c.2.2.2
                                    linarith only [h1570, h2095, h2105, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2112_1, u3elo1]
                                  · have p2112_0 := h2112c.1
                                    have p2112_1 := h2112c.2.1
                                    have p2112_2 := h2112c.2.2.1
                                    have p2112_3 := h2112c.2.2.2
                                    linarith only [h2095, hlam, p2112_0]
                                  · have p2112_0 := h2112c.1
                                    have p2112_1 := h2112c.2.1
                                    have p2112_2 := h2112c.2.2.1
                                    have p2112_3 := h2112c.2.2.2
                                    linarith only [hlam, p2112_0]
                                  · have p2112_0 := h2112c.1
                                    have p2112_1 := h2112c.2.1
                                    have p2112_2 := h2112c.2.2.1
                                    have p2112_3 := h2112c.2.2.2
                                    linarith only [h1570, h2095, h2105, h2109, h2111, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2112_1, u3elo1]
                                  · have p2112_0 := h2112c.1
                                    have p2112_1 := h2112c.2.1
                                    have p2112_2 := h2112c.2.2.1
                                    have p2112_3 := h2112c.2.2.2
                                    linarith only [h1570, h2095, h2105, h2111, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2112_1, u3elo1]
                                  · have p2112_0 := h2112c.1
                                    have p2112_1 := h2112c.2.1
                                    have p2112_2 := h2112c.2.2.1
                                    have p2112_3 := h2112c.2.2.2
                                    linarith only [h1570, h2095, h2105, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2112_1, u3elo1]
                                  · have p2112_0 := h2112c.1
                                    have p2112_1 := h2112c.2.1
                                    have p2112_2 := h2112c.2.2.1
                                    have p2112_3 := h2112c.2.2.2
                                    linarith only [h2098, hlam, p2112_1]
                                  · have p2112_0 := h2112c.1
                                    have p2112_1 := h2112c.2.1
                                    have p2112_2 := h2112c.2.2.1
                                    have p2112_3 := h2112c.2.2.2
                                    linarith only [h2104, hlam, p2112_1]
                                  · have p2112_0 := h2112c.1
                                    have p2112_1 := h2112c.2.1
                                    have p2112_2 := h2112c.2.2.1
                                    have p2112_3 := h2112c.2.2.2
                                    linarith only [hlam, p2112_0]
                                  · have p2112_0 := h2112c.1
                                    have p2112_1 := h2112c.2.1
                                    have p2112_2 := h2112c.2.2.1
                                    have p2112_3 := h2112c.2.2.2
                                    linarith only [h2098, h2111, hc02, hc45, hlam, hphi, ht0b, ht5b, p2112_1]
                                  · have p2112_0 := h2112c.1
                                    have p2112_1 := h2112c.2.1
                                    have p2112_2 := h2112c.2.2.1
                                    have p2112_3 := h2112c.2.2.2
                                    linarith only [h1570, h2095, h2104, h2105, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2112_1, u3elo1]
                                  · have p2112_0 := h2112c.1
                                    have p2112_1 := h2112c.2.1
                                    have p2112_2 := h2112c.2.2.1
                                    have p2112_3 := h2112c.2.2.2
                                    linarith only [h2100, hlam, p2112_0]
                                  · have p2112_0 := h2112c.1
                                    have p2112_1 := h2112c.2.1
                                    have p2112_2 := h2112c.2.2.1
                                    have p2112_3 := h2112c.2.2.2
                                    linarith only [h2106, hlam, p2112_0]
                                  · have p2112_0 := h2112c.1
                                    have p2112_1 := h2112c.2.1
                                    have p2112_2 := h2112c.2.2.1
                                    have p2112_3 := h2112c.2.2.2
                                    linarith only [h2109, hlam, p2112_0]
                                  · have p2112_0 := h2112c.1
                                    have p2112_1 := h2112c.2.1
                                    have p2112_2 := h2112c.2.2.1
                                    have p2112_3 := h2112c.2.2.2
                                    linarith only [hlam, p2112_0]
                                  · have p2112_0 := h2112c.1
                                    have p2112_1 := h2112c.2.1
                                    have p2112_2 := h2112c.2.2.1
                                    have p2112_3 := h2112c.2.2.2
                                    linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2112_1, u3elo4]
                                  · have p2112_0 := h2112c.1
                                    have p2112_1 := h2112c.2.1
                                    have p2112_2 := h2112c.2.2.1
                                    have p2112_3 := h2112c.2.2.2
                                    linarith only [h2101, hlam, p2112_0]
                                  · have p2112_0 := h2112c.1
                                    have p2112_1 := h2112c.2.1
                                    have p2112_2 := h2112c.2.2.1
                                    have p2112_3 := h2112c.2.2.2
                                    linarith only [h2107, hlam, p2112_0]
                                  · have p2112_0 := h2112c.1
                                    have p2112_1 := h2112c.2.1
                                    have p2112_2 := h2112c.2.2.1
                                    have p2112_3 := h2112c.2.2.2
                                    linarith only [h2110, hlam, p2112_0]
                                  · have p2112_0 := h2112c.1
                                    have p2112_1 := h2112c.2.1
                                    have p2112_2 := h2112c.2.2.1
                                    have p2112_3 := h2112c.2.2.2
                                    linarith only [h2111, hlam, p2112_0]
                                  · have p2112_0 := h2112c.1
                                    have p2112_1 := h2112c.2.1
                                    have p2112_2 := h2112c.2.2.1
                                    have p2112_3 := h2112c.2.2.2
                                    linarith only [hlam, p2112_0]
                                · linarith only [h1570, h2095, h2105, h2107, h2111, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                              · linarith only [h1570, h2095, h2105, h2107, h2110, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · linarith only [h0, h2100, h2109, hc23, hlam, hphi, u3elo1]
                          · linarith only [h0, h2099, h2108, hc23, hlam, hphi, u3elo1]
                        · linarith only [h1570, h2095, h2101, h2107, hc04, hc15, hlam, hphi, ht0b, ht5b]
                      · linarith only [h1570, h2095, h2104, h2105, h2106, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                    · linarith only [h0, h2099, h2105, hlam]
                  · linarith only [h0, h2095, h2098, h2102, h2104, hc02, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h2095, h2097, h2102, h2103, hc02, hc15, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h2096, h2102, hlam]
            · linarith only [h1570, h2095, h2101, hlam]
          · linarith only [h0, h2095, h2100, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2150 | h2150
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2151 | h2151
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2152 | h2152
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2153 | h2153
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2154 | h2154
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2155 | h2155
                    · linarith only [h0, h2095, h2099, h2154, h2155, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                    · linarith only [h0, h2095, h2154, h2155, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                  · linarith only [h0, h2095, h2098, h2152, h2154, hc02, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h2095, h2097, h2152, h2153, hc02, hc15, hlam, hphi, ht0b, ht5b]
              · linarith only [h2096, h2099, h2152, hc12, hlam, hphi, ht23, u3elo3]
            · linarith only [h1570, h2095, h2151, hlam]
          · linarith only [h0, h2095, h2150, hlam]
      · linarith only [h0, h2095, h2096, h2098, hc23, hlam, hphi, u3elo1]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2164 | h2164
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2165 | h2165
        · linarith only [h2096, h2097, h2165, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2167 | h2167
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2168 | h2168
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2169 | h2169
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2170 | h2170
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2171 | h2171
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2172 | h2172
                    · linarith only [h0, h2165, h2172, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h0, h2095, h2171, h2172, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                  · linarith only [h2097, h2170, h2171, hc02, hc25, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2176 | h2176
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2177 | h2177
                    · linarith only [h2165, h2177, hc03, hlam, hphi, u3elo1]
                    · linarith only [h0, h2177, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h2097, h2164, h2176, hc12, hc24, hlam, hphi]
              · linarith only [h2096, h2097, h2165, h2169, hc12, hlam, hphi, ht23, u3elo3]
            · linarith only [h0, h2095, h2096, h2097, h2168, hc23, hlam, hphi, u3elo1]
          · linarith only [h0, h2095, h2167, hlam]
      · linarith only [h0, h2095, h2096, h2164, hc23, hlam, hphi, u3elo1]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2185 | h2185
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2186 | h2186
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2187 | h2187
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2188 | h2188
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2189 | h2189
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2190 | h2190
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2191 | h2191
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2192 | h2192
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2193 | h2193
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2194 | h2194
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2195 | h2195
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2196 | h2196
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2197 | h2197
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2198 | h2198
                              · linarith only [h2096, h2185, h2190, h2198, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                              · linarith only [h2096, h2185, h2189, h2190, h2198, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · linarith only [h1570, h2096, h2185, h2197, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h1570, h2095, h2096, h2185, h2192, h2196, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                        · linarith only [h1570, h2095, h2185, h2189, h2192, h2195, hc02, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h2096, h2190, h2194, hc02, hlam, hphi, ht23, u3elo4]
                    · linarith only [h2096, h2185, h2187, h2190, h2193, hlam]
                  · linarith only [h2096, h2186, h2190, h2192, hc12, hlam, hphi, ht23, u3elo1]
                · linarith only [h2096, h2185, h2190, h2191, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2208 | h2208
                · linarith only [h1570, h2095, h2190, h2208, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                · linarith only [h2096, h2185, h2208, hc12, hlam, hphi, ht23, u3elo2]
            · linarith only [h1570, h2095, h2189, hlam]
          · linarith only [h1570, h2095, h2096, h2185, h2188, hlam]
        · linarith only [h2096, h2185, h2187, hlam]
      · linarith only [h1570, h2095, h2185, h2186, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2215 | h2215
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2216 | h2216
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2217 | h2217
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2218 | h2218
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2219 | h2219
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2220 | h2220
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2221 | h2221
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2222 | h2222
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2223 | h2223
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2224 | h2224
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2225 | h2225
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2226 | h2226
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2227 | h2227
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2228 | h2228
                                · rcases h5bigk with h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c | h2229c
                                  · have p2229_0 := h2229c.1
                                    have p2229_1 := h2229c.2.1
                                    have p2229_2 := h2229c.2.2.1
                                    have p2229_3 := h2229c.2.2.2
                                    linarith only [hlam, p2229_0]
                                  · have p2229_0 := h2229c.1
                                    have p2229_1 := h2229c.2.1
                                    have p2229_2 := h2229c.2.2.1
                                    have p2229_3 := h2229c.2.2.2
                                    linarith only [h2185, h2215, h2220, h2221, h2226, h2228, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p2229_1]
                                  · have p2229_0 := h2229c.1
                                    have p2229_1 := h2229c.2.1
                                    have p2229_2 := h2229c.2.2.1
                                    have p2229_3 := h2229c.2.2.2
                                    linarith only [h2096, h2215, h2219, h2226, h2228, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2229_1, u3elo1]
                                  · have p2229_0 := h2229c.1
                                    have p2229_1 := h2229c.2.1
                                    have p2229_2 := h2229c.2.2.1
                                    have p2229_3 := h2229c.2.2.2
                                    linarith only [h2096, h2215, h2219, h2228, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2229_1, u3elo1]
                                  · have p2229_0 := h2229c.1
                                    have p2229_1 := h2229c.2.1
                                    have p2229_2 := h2229c.2.2.1
                                    have p2229_3 := h2229c.2.2.2
                                    linarith only [h2096, h2215, h2219, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2229_1, u3elo1]
                                  · have p2229_0 := h2229c.1
                                    have p2229_1 := h2229c.2.1
                                    have p2229_2 := h2229c.2.2.1
                                    have p2229_3 := h2229c.2.2.2
                                    linarith only [h2095, hlam, p2229_0]
                                  · have p2229_0 := h2229c.1
                                    have p2229_1 := h2229c.2.1
                                    have p2229_2 := h2229c.2.2.1
                                    have p2229_3 := h2229c.2.2.2
                                    linarith only [hlam, p2229_0]
                                  · have p2229_0 := h2229c.1
                                    have p2229_1 := h2229c.2.1
                                    have p2229_2 := h2229c.2.2.1
                                    have p2229_3 := h2229c.2.2.2
                                    linarith only [h0, h2095, h2226, h2228, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2229_1, u3elo1]
                                  · have p2229_0 := h2229c.1
                                    have p2229_1 := h2229c.2.1
                                    have p2229_2 := h2229c.2.2.1
                                    have p2229_3 := h2229c.2.2.2
                                    linarith only [h1570, h2095, h2222, h2228, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2229_1, u3elo1]
                                  · have p2229_0 := h2229c.1
                                    have p2229_1 := h2229c.2.1
                                    have p2229_2 := h2229c.2.2.1
                                    have p2229_3 := h2229c.2.2.2
                                    linarith only [h1570, h2095, h2222, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2229_1, u3elo1]
                                  · have p2229_0 := h2229c.1
                                    have p2229_1 := h2229c.2.1
                                    have p2229_2 := h2229c.2.2.1
                                    have p2229_3 := h2229c.2.2.2
                                    linarith only [h2215, hlam, p2229_1]
                                  · have p2229_0 := h2229c.1
                                    have p2229_1 := h2229c.2.1
                                    have p2229_2 := h2229c.2.2.1
                                    have p2229_3 := h2229c.2.2.2
                                    linarith only [h2221, hlam, p2229_1]
                                  · have p2229_0 := h2229c.1
                                    have p2229_1 := h2229c.2.1
                                    have p2229_2 := h2229c.2.2.1
                                    have p2229_3 := h2229c.2.2.2
                                    linarith only [hlam, p2229_0]
                                  · have p2229_0 := h2229c.1
                                    have p2229_1 := h2229c.2.1
                                    have p2229_2 := h2229c.2.2.1
                                    have p2229_3 := h2229c.2.2.2
                                    linarith only [h2185, h2215, h2220, h2222, h2228, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2229_1, u3elo1]
                                  · have p2229_0 := h2229c.1
                                    have p2229_1 := h2229c.2.1
                                    have p2229_2 := h2229c.2.2.1
                                    have p2229_3 := h2229c.2.2.2
                                    linarith only [h2185, h2215, h2220, h2222, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2229_1, u3elo1]
                                  · have p2229_0 := h2229c.1
                                    have p2229_1 := h2229c.2.1
                                    have p2229_2 := h2229c.2.2.1
                                    have p2229_3 := h2229c.2.2.2
                                    linarith only [h2217, hlam, p2229_0]
                                  · have p2229_0 := h2229c.1
                                    have p2229_1 := h2229c.2.1
                                    have p2229_2 := h2229c.2.2.1
                                    have p2229_3 := h2229c.2.2.2
                                    linarith only [h2223, hlam, p2229_0]
                                  · have p2229_0 := h2229c.1
                                    have p2229_1 := h2229c.2.1
                                    have p2229_2 := h2229c.2.2.1
                                    have p2229_3 := h2229c.2.2.2
                                    linarith only [h2226, hlam, p2229_0]
                                  · have p2229_0 := h2229c.1
                                    have p2229_1 := h2229c.2.1
                                    have p2229_2 := h2229c.2.2.1
                                    have p2229_3 := h2229c.2.2.2
                                    linarith only [hlam, p2229_0]
                                  · have p2229_0 := h2229c.1
                                    have p2229_1 := h2229c.2.1
                                    have p2229_2 := h2229c.2.2.1
                                    have p2229_3 := h2229c.2.2.2
                                    linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2229_1, u3elo4]
                                  · have p2229_0 := h2229c.1
                                    have p2229_1 := h2229c.2.1
                                    have p2229_2 := h2229c.2.2.1
                                    have p2229_3 := h2229c.2.2.2
                                    linarith only [h2218, hlam, p2229_0]
                                  · have p2229_0 := h2229c.1
                                    have p2229_1 := h2229c.2.1
                                    have p2229_2 := h2229c.2.2.1
                                    have p2229_3 := h2229c.2.2.2
                                    linarith only [h2224, hlam, p2229_0]
                                  · have p2229_0 := h2229c.1
                                    have p2229_1 := h2229c.2.1
                                    have p2229_2 := h2229c.2.2.1
                                    have p2229_3 := h2229c.2.2.2
                                    linarith only [h2227, hlam, p2229_0]
                                  · have p2229_0 := h2229c.1
                                    have p2229_1 := h2229c.2.1
                                    have p2229_2 := h2229c.2.2.1
                                    have p2229_3 := h2229c.2.2.2
                                    linarith only [h2228, hlam, p2229_0]
                                  · have p2229_0 := h2229c.1
                                    have p2229_1 := h2229c.2.1
                                    have p2229_2 := h2229c.2.2.1
                                    have p2229_3 := h2229c.2.2.2
                                    linarith only [hlam, p2229_0]
                                · linarith only [h1570, h2095, h2222, h2224, h2228, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                              · linarith only [h1570, h2095, h2185, h2222, h2224, h2227, hc02, hlam, hphi, ht23, u3elo1]
                            · linarith only [h2096, h2215, h2226, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                          · linarith only [h2096, h2215, h2225, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                        · linarith only [h1570, h2095, h2218, h2224, hc04, hc15, hlam, hphi, ht0b, ht5b]
                      · linarith only [h0, h2095, h2221, h2223, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                    · linarith only [h0, h2095, h2221, h2222, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                  · linarith only [h2096, h2215, h2221, hc12, hc23, hlam, hphi]
                · linarith only [h2096, h2219, h2220, hc02, hc24, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2264 | h2264
                · linarith only [h2185, h2215, h2219, h2264, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2266 | h2266
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2267 | h2267
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2268 | h2268
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2269 | h2269
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2270 | h2270
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2271 | h2271
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2272 | h2272
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2273 | h2273
                                · rcases h5bigk with h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [hlam, p2274_0]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h1570, h2095, h2266, h2267, h2271, h2273, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p2274_1]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h1570, h2095, h2267, h2271, h2273, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2274_1, u3elo1]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h1570, h2095, h2267, h2273, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2274_1, u3elo1]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h1570, h2095, h2267, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2274_1, u3elo1]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h2095, hlam, p2274_0]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [hlam, p2274_0]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h1570, h2095, h2267, h2271, h2273, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2274_1, u3elo1]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h1570, h2095, h2219, h2267, h2273, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2274_1, u3elo2]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h1570, h2095, h2219, h2267, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2274_1, u3elo2]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h2215, hlam, p2274_1]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h2266, hlam, p2274_1]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [hlam, p2274_0]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h2215, h2273, hc02, hc45, hlam, hphi, ht0b, ht5b, p2274_1]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h1570, h2095, h2219, h2266, h2267, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2274_1, u3elo2]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h2217, hlam, p2274_0]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h2268, hlam, p2274_0]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h2271, hlam, p2274_0]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [hlam, p2274_0]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2274_1, u3elo4]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h2218, hlam, p2274_0]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h2269, hlam, p2274_0]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h2272, hlam, p2274_0]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h2273, hlam, p2274_0]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [hlam, p2274_0]
                                · linarith only [h1570, h2095, h2219, h2267, h2269, h2273, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                              · linarith only [h1570, h2095, h2185, h2219, h2267, h2269, h2272, hc02, hlam, hphi, ht23, u3elo2]
                            · linarith only [h1570, h2219, h2267, h2271, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h1570, h2219, h2267, h2270, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h1570, h2218, h2269, hlam]
                      · linarith only [h1570, h2095, h2267, h2268, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                    · linarith only [h0, h2216, h2267, hlam]
                  · linarith only [h2096, h2215, h2266, hc12, hlam, hphi, ht23, u3elo2]
            · linarith only [h1570, h2095, h2218, hlam]
          · linarith only [h0, h2095, h2217, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2310 | h2310
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2311 | h2311
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2312 | h2312
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2313 | h2313
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2314 | h2314
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2315 | h2315
                    · linarith only [h0, h2216, h2315, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h0, h2095, h2314, h2315, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                  · linarith only [h2096, h2312, h2314, hc02, hc25, hlam, hphi]
                · linarith only [h2096, h2312, h2313, hc02, hc24, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2320 | h2320
                · linarith only [h2185, h2215, h2312, h2320, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2322 | h2322
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2323 | h2323
                    · linarith only [h0, h2095, h2216, h2322, h2323, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                    · linarith only [h0, h2095, h2322, h2323, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                  · linarith only [h2096, h2215, h2322, hc12, hlam, hphi, ht23, u3elo2]
            · linarith only [h0, h2095, h2216, h2311, hlam]
          · linarith only [h0, h2095, h2310, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2329 | h2329
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2330 | h2330
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2331 | h2331
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2332 | h2332
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2333 | h2333
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2334 | h2334
                  · linarith only [h1570, h2095, h2215, h2329, h2334, hc02, hlam, hphi, ht23, u3elo0]
                  · linarith only [h2096, h2332, h2334, hc02, hc25, hlam, hphi]
                · linarith only [h2096, h2332, h2333, hc02, hc24, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2338 | h2338
                · linarith only [h2185, h2332, h2338, hc02, hlam, hphi, ht23, u3elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2340 | h2340
                  · linarith only [h2215, h2338, h2340, hc02, hc24, hlam, hphi]
                  · linarith only [h0, h2095, h2332, h2340, hc12, hlam, hphi, ht23, u3elo2]
            · linarith only [h1570, h2095, h2331, hlam]
          · linarith only [h1570, h2095, h2329, h2330, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2345 | h2345
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2346 | h2346
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2347 | h2347
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2348 | h2348
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2349 | h2349
                  · linarith only [h0, h2095, h2215, h2349, hc02, hlam, hphi, ht23, u3elo1]
                  · linarith only [h2096, h2347, h2349, hc02, hc25, hlam, hphi]
                · linarith only [h2096, h2347, h2348, hc02, hc24, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2353 | h2353
                · linarith only [h2185, h2347, h2353, hc02, hc23, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2355 | h2355
                  · linarith only [h2215, h2347, h2355, hc02, hlam, hphi, ht23, u3elo2]
                  · linarith only [h0, h2095, h2329, h2355, hc12, hlam, hphi, ht23, u3elo3]
            · linarith only [h0, h2095, h2329, h2346, hlam]
          · linarith only [h0, h2095, h2345, hlam]

end R2N4
