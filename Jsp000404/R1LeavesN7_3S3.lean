import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_3S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7932000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s9_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 2 5 (by decide) (by decide) with h1586 | h1586
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1587 | h1587
    · linarith only [h10, h11, h1587, hlam]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h1589 | h1589
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1590 | h1590
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1591 | h1591
          · linarith only [h0, h1587, h1589, h1591, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1593 | h1593
            · linarith only [h0, h10, h11, h1591, h1593, h4, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h10, h11, h1589, h1591, h1593, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · linarith only [h10, h11, h1589, h1590, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1597 | h1597
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1598 | h1598
          · linarith only [h0, h10, h11, h1598, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1600 | h1600
            · linarith only [h0, h10, h11, h1589, h1598, h1600, h4, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1602 | h1602
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1603 | h1603
                · rcases h1bigk with h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c
                  · have p1604_0 := h1604c.1
                    have p1604_1 := h1604c.2.1
                    have p1604_2 := h1604c.2.2.1
                    have p1604_3 := h1604c.2.2.2
                    linarith only [hlam, p1604_0]
                  · have p1604_0 := h1604c.1
                    have p1604_1 := h1604c.2.1
                    have p1604_2 := h1604c.2.2.1
                    have p1604_3 := h1604c.2.2.2
                    rcases p1604_3 (m.d 0 1) (by simp) with h1606 | h1606
                    · rcases p1604_3 (m.d 1 2) (by simp) with h1607 | h1607
                      · linarith only [h1607, hlam, p1604_0]
                      · rcases p1604_3 (m.d 1 3) (by simp) with h1609 | h1609
                        · linarith only [h1, h1609, hlam]
                        · rcases p1604_3 (m.d 1 4) (by simp) with h1611 | h1611
                          · linarith only [h1611, h2, hlam]
                          · linarith only [h11, h1611, hlam]
                    · linarith only [h1606, hlam, p1604_0]
                  · have p1604_0 := h1604c.1
                    have p1604_1 := h1604c.2.1
                    have p1604_2 := h1604c.2.2.1
                    have p1604_3 := h1604c.2.2.2
                    rcases p1604_3 (m.d 0 1) (by simp) with h1615 | h1615
                    · rcases p1604_3 (m.d 1 2) (by simp) with h1616 | h1616
                      · linarith only [h0, h1616, hlam]
                      · linarith only [h10, h1616, hlam]
                    · linarith only [h1615, hlam, p1604_0]
                  · have p1604_0 := h1604c.1
                    have p1604_1 := h1604c.2.1
                    have p1604_2 := h1604c.2.2.1
                    have p1604_3 := h1604c.2.2.2
                    rcases p1604_3 (m.d 0 1) (by simp) with h1620 | h1620
                    · rcases p1604_3 (m.d 1 2) (by simp) with h1621 | h1621
                      · linarith only [h0, h1621, hlam]
                      · rcases p1604_3 (m.d 1 3) (by simp) with h1623 | h1623
                        · linarith only [h1, h1623, hlam]
                        · rcases p1604_3 (m.d 1 4) (by simp) with h1625 | h1625
                          · linarith only [h1625, hlam, p1604_0]
                          · rcases p1604_3 (m.d 1 5) (by simp) with h1627 | h1627
                            · linarith only [h1627, h3, hlam]
                            · rcases h3bigk with h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c | h1629c
                              · have p1629_0 := h1629c.1
                                have p1629_1 := h1629c.2.1
                                have p1629_2 := h1629c.2.2.1
                                have p1629_3 := h1629c.2.2.2
                                linarith only [hlam, p1629_0]
                              · have p1629_0 := h1629c.1
                                have p1629_1 := h1629c.2.1
                                have p1629_2 := h1629c.2.2.1
                                have p1629_3 := h1629c.2.2.2
                                rcases p1629_3 (m.d 0 3) (by simp) with h1631 | h1631
                                · rcases p1629_3 (m.d 1 3) (by simp) with h1632 | h1632
                                  · linarith only [h1, h1632, hlam]
                                  · rcases p1629_3 (m.d 2 3) (by simp) with h1634 | h1634
                                    · linarith only [h1634, h4, hlam]
                                    · rcases p1629_3 (m.d 3 4) (by simp) with h1636 | h1636
                                      · linarith only [h1636, h7, hlam]
                                      · linarith only [h1587, h1636, hlam]
                                · linarith only [h1, h1631, hlam]
                              · have p1629_0 := h1629c.1
                                have p1629_1 := h1629c.2.1
                                have p1629_2 := h1629c.2.2.1
                                have p1629_3 := h1629c.2.2.2
                                linarith only [h10, h11, h1598, h7, hlam, p1629_2]
                              · have p1629_0 := h1629c.1
                                have p1629_1 := h1629c.2.1
                                have p1629_2 := h1629c.2.2.1
                                have p1629_3 := h1629c.2.2.2
                                linarith only [h0, h11, h1586, h1598, h4, hc01, hc25, hlam, hphi, ht0b, ht5b, p1629_1]
                              · have p1629_0 := h1629c.1
                                have p1629_1 := h1629c.2.1
                                have p1629_2 := h1629c.2.2.1
                                have p1629_3 := h1629c.2.2.2
                                rcases p1629_3 (m.d 0 3) (by simp) with h1642 | h1642
                                · rcases p1629_3 (m.d 1 3) (by simp) with h1643 | h1643
                                  · linarith only [h1, h1643, hlam]
                                  · rcases p1629_3 (m.d 2 3) (by simp) with h1645 | h1645
                                    · linarith only [h1645, h4, hlam]
                                    · rcases p1629_3 (m.d 3 4) (by simp) with h1647 | h1647
                                      · linarith only [h1647, h7, hlam]
                                      · linarith only [h1603, h1647, hlam]
                                · linarith only [h1642, hlam, p1629_0]
                              · have p1629_0 := h1629c.1
                                have p1629_1 := h1629c.2.1
                                have p1629_2 := h1629c.2.2.1
                                have p1629_3 := h1629c.2.2.2
                                linarith only [h1, hlam, p1629_0]
                              · have p1629_0 := h1629c.1
                                have p1629_1 := h1629c.2.1
                                have p1629_2 := h1629c.2.2.1
                                have p1629_3 := h1629c.2.2.2
                                linarith only [hlam, p1629_0]
                              · have p1629_0 := h1629c.1
                                have p1629_1 := h1629c.2.1
                                have p1629_2 := h1629c.2.2.1
                                have p1629_3 := h1629c.2.2.2
                                linarith only [h1589, hc23, hc35, hlam, hphi, p1629_1]
                              · have p1629_0 := h1629c.1
                                have p1629_1 := h1629c.2.1
                                have p1629_2 := h1629c.2.2.1
                                have p1629_3 := h1629c.2.2.2
                                linarith only [h1587, hlam, p1629_0]
                              · have p1629_0 := h1629c.1
                                have p1629_1 := h1629c.2.1
                                have p1629_2 := h1629c.2.2.1
                                have p1629_3 := h1629c.2.2.2
                                linarith only [h1589, hlam, p1629_0]
                              · have p1629_0 := h1629c.1
                                have p1629_1 := h1629c.2.1
                                have p1629_2 := h1629c.2.2.1
                                have p1629_3 := h1629c.2.2.2
                                linarith only [h4, hlam, p1629_0]
                              · have p1629_0 := h1629c.1
                                have p1629_1 := h1629c.2.1
                                have p1629_2 := h1629c.2.2.1
                                have p1629_3 := h1629c.2.2.2
                                linarith only [h10, hlam, p1629_0]
                              · have p1629_0 := h1629c.1
                                have p1629_1 := h1629c.2.1
                                have p1629_2 := h1629c.2.2.1
                                have p1629_3 := h1629c.2.2.2
                                linarith only [hlam, p1629_0]
                              · have p1629_0 := h1629c.1
                                have p1629_1 := h1629c.2.1
                                have p1629_2 := h1629c.2.2.1
                                have p1629_3 := h1629c.2.2.2
                                linarith only [h1598, hlam, p1629_0]
                              · have p1629_0 := h1629c.1
                                have p1629_1 := h1629c.2.1
                                have p1629_2 := h1629c.2.2.1
                                have p1629_3 := h1629c.2.2.2
                                linarith only [h1600, hlam, p1629_0]
                              · have p1629_0 := h1629c.1
                                have p1629_1 := h1629c.2.1
                                have p1629_2 := h1629c.2.2.1
                                have p1629_3 := h1629c.2.2.2
                                linarith only [h7, hlam, p1629_0]
                              · have p1629_0 := h1629c.1
                                have p1629_1 := h1629c.2.1
                                have p1629_2 := h1629c.2.2.1
                                have p1629_3 := h1629c.2.2.2
                                rcases p1629_3 (m.d 0 3) (by simp) with h1662 | h1662
                                · rcases p1629_3 (m.d 1 3) (by simp) with h1663 | h1663
                                  · linarith only [h1663, hlam, p1629_0]
                                  · rcases p1629_3 (m.d 2 3) (by simp) with h1665 | h1665
                                    · linarith only [h1598, h1665, hlam]
                                    · rcases p1629_3 (m.d 3 4) (by simp) with h1667 | h1667
                                      · rcases p1629_3 (m.d 3 5) (by simp) with h1668 | h1668
                                        · linarith only [h1603, h1668, hlam]
                                        · linarith only [h1589, h1668, hlam]
                                      · linarith only [h1667, hlam, p1629_0]
                                · linarith only [h1, h1662, hlam]
                              · have p1629_0 := h1629c.1
                                have p1629_1 := h1629c.2.1
                                have p1629_2 := h1629c.2.2.1
                                have p1629_3 := h1629c.2.2.2
                                rcases p1629_3 (m.d 0 3) (by simp) with h1673 | h1673
                                · rcases p1629_3 (m.d 1 3) (by simp) with h1674 | h1674
                                  · linarith only [h1587, h1674, hlam]
                                  · linarith only [h10, h1674, hlam]
                                · linarith only [h1673, h4, hlam]
                              · have p1629_0 := h1629c.1
                                have p1629_1 := h1629c.2.1
                                have p1629_2 := h1629c.2.2.1
                                have p1629_3 := h1629c.2.2.2
                                linarith only [hlam, p1629_0]
                              · have p1629_0 := h1629c.1
                                have p1629_1 := h1629c.2.1
                                have p1629_2 := h1629c.2.2.1
                                have p1629_3 := h1629c.2.2.2
                                linarith only [h0, h1589, h4, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1629_1]
                              · have p1629_0 := h1629c.1
                                have p1629_1 := h1629c.2.1
                                have p1629_2 := h1629c.2.2.1
                                have p1629_3 := h1629c.2.2.2
                                linarith only [h8, hlam, p1629_0]
                              · have p1629_0 := h1629c.1
                                have p1629_1 := h1629c.2.1
                                have p1629_2 := h1629c.2.2.1
                                have p1629_3 := h1629c.2.2.2
                                rcases p1629_3 (m.d 0 3) (by simp) with h1681 | h1681
                                · rcases p1629_3 (m.d 1 3) (by simp) with h1682 | h1682
                                  · linarith only [h1682, hlam, p1629_0]
                                  · rcases p1629_3 (m.d 2 3) (by simp) with h1684 | h1684
                                    · linarith only [h1600, h1684, hlam]
                                    · rcases p1629_3 (m.d 3 4) (by simp) with h1686 | h1686
                                      · rcases p1629_3 (m.d 3 5) (by simp) with h1687 | h1687
                                        · rcases h5bigk with h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c | h1688c
                                          · have p1688_0 := h1688c.1
                                            have p1688_1 := h1688c.2.1
                                            have p1688_2 := h1688c.2.2.1
                                            have p1688_3 := h1688c.2.2.2
                                            linarith only [hlam, p1688_0]
                                          · have p1688_0 := h1688c.1
                                            have p1688_1 := h1688c.2.1
                                            have p1688_2 := h1688c.2.2.1
                                            have p1688_3 := h1688c.2.2.2
                                            rcases p1688_3 (m.d 0 5) (by simp) with h1690 | h1690
                                            · rcases p1688_3 (m.d 1 5) (by simp) with h1691 | h1691
                                              · linarith only [h1691, h3, hlam]
                                              · rcases p1688_3 (m.d 2 5) (by simp) with h1693 | h1693
                                                · linarith only [h1693, h6, hlam]
                                                · rcases p1688_3 (m.d 3 5) (by simp) with h1695 | h1695
                                                  · linarith only [h1695, h8, hlam]
                                                  · linarith only [h1589, h1695, hlam]
                                            · linarith only [h1690, h3, hlam]
                                          · have p1688_0 := h1688c.1
                                            have p1688_1 := h1688c.2.1
                                            have p1688_2 := h1688c.2.2.1
                                            have p1688_3 := h1688c.2.2.2
                                            rcases p1688_3 (m.d 0 5) (by simp) with h1699 | h1699
                                            · rcases p1688_3 (m.d 1 5) (by simp) with h1700 | h1700
                                              · linarith only [h1700, h3, hlam]
                                              · linarith only [h1586, h1700, hlam]
                                            · linarith only [h1699, h6, hlam]
                                          · have p1688_0 := h1688c.1
                                            have p1688_1 := h1688c.2.1
                                            have p1688_2 := h1688c.2.2.1
                                            have p1688_3 := h1688c.2.2.2
                                            linarith only [h0, h10, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1629_1, p1688_1]
                                          · have p1688_0 := h1688c.1
                                            have p1688_1 := h1688c.2.1
                                            have p1688_2 := h1688c.2.2.1
                                            have p1688_3 := h1688c.2.2.2
                                            rcases p1688_3 (m.d 0 5) (by simp) with h1705 | h1705
                                            · rcases p1688_3 (m.d 1 5) (by simp) with h1706 | h1706
                                              · linarith only [h1706, h3, hlam]
                                              · linarith only [h1597, h1706, hlam]
                                            · linarith only [h1705, h9, hlam]
                                          · have p1688_0 := h1688c.1
                                            have p1688_1 := h1688c.2.1
                                            have p1688_2 := h1688c.2.2.1
                                            have p1688_3 := h1688c.2.2.2
                                            linarith only [h3, hlam, p1688_0]
                                          · have p1688_0 := h1688c.1
                                            have p1688_1 := h1688c.2.1
                                            have p1688_2 := h1688c.2.2.1
                                            have p1688_3 := h1688c.2.2.2
                                            linarith only [hlam, p1688_0]
                                          · have p1688_0 := h1688c.1
                                            have p1688_1 := h1688c.2.1
                                            have p1688_2 := h1688c.2.2.1
                                            have p1688_3 := h1688c.2.2.2
                                            linarith only [h1600, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1688_1]
                                          · have p1688_0 := h1688c.1
                                            have p1688_1 := h1688c.2.1
                                            have p1688_2 := h1688c.2.2.1
                                            have p1688_3 := h1688c.2.2.2
                                            linarith only [h1589, hlam, p1688_1]
                                          · have p1688_0 := h1688c.1
                                            have p1688_1 := h1688c.2.1
                                            have p1688_2 := h1688c.2.2.1
                                            have p1688_3 := h1688c.2.2.2
                                            linarith only [h11, h1586, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1688_1]
                                          · have p1688_0 := h1688c.1
                                            have p1688_1 := h1688c.2.1
                                            have p1688_2 := h1688c.2.2.1
                                            have p1688_3 := h1688c.2.2.2
                                            linarith only [h6, hlam, p1688_1]
                                          · have p1688_0 := h1688c.1
                                            have p1688_1 := h1688c.2.1
                                            have p1688_2 := h1688c.2.2.1
                                            have p1688_3 := h1688c.2.2.2
                                            linarith only [h1586, hlam, p1688_1]
                                          · have p1688_0 := h1688c.1
                                            have p1688_1 := h1688c.2.1
                                            have p1688_2 := h1688c.2.2.1
                                            have p1688_3 := h1688c.2.2.2
                                            linarith only [hlam, p1688_0]
                                          · have p1688_0 := h1688c.1
                                            have p1688_1 := h1688c.2.1
                                            have p1688_2 := h1688c.2.2.1
                                            have p1688_3 := h1688c.2.2.2
                                            linarith only [h1600, hlam, p1688_1]
                                          · have p1688_0 := h1688c.1
                                            have p1688_1 := h1688c.2.1
                                            have p1688_2 := h1688c.2.2.1
                                            have p1688_3 := h1688c.2.2.2
                                            linarith only [h0, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p1688_1]
                                          · have p1688_0 := h1688c.1
                                            have p1688_1 := h1688c.2.1
                                            have p1688_2 := h1688c.2.2.1
                                            have p1688_3 := h1688c.2.2.2
                                            linarith only [h8, hlam, p1688_0]
                                          · have p1688_0 := h1688c.1
                                            have p1688_1 := h1688c.2.1
                                            have p1688_2 := h1688c.2.2.1
                                            have p1688_3 := h1688c.2.2.2
                                            linarith only [h0, h4, h8, hc01, hc15, hlam, hphi, ht0b, ht5b, p1688_1]
                                          · have p1688_0 := h1688c.1
                                            have p1688_1 := h1688c.2.1
                                            have p1688_2 := h1688c.2.2.1
                                            have p1688_3 := h1688c.2.2.2
                                            linarith only [h0, h4, h8, hc01, hc25, hlam, hphi, ht0b, ht5b, p1688_1]
                                          · have p1688_0 := h1688c.1
                                            have p1688_1 := h1688c.2.1
                                            have p1688_2 := h1688c.2.2.1
                                            have p1688_3 := h1688c.2.2.2
                                            linarith only [hlam, p1688_0]
                                          · have p1688_0 := h1688c.1
                                            have p1688_1 := h1688c.2.1
                                            have p1688_2 := h1688c.2.2.1
                                            have p1688_3 := h1688c.2.2.2
                                            linarith only [h0, h1603, h4, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p1688_1]
                                          · have p1688_0 := h1688c.1
                                            have p1688_1 := h1688c.2.1
                                            have p1688_2 := h1688c.2.2.1
                                            have p1688_3 := h1688c.2.2.2
                                            linarith only [h9, hlam, p1688_0]
                                          · have p1688_0 := h1688c.1
                                            have p1688_1 := h1688c.2.1
                                            have p1688_2 := h1688c.2.2.1
                                            have p1688_3 := h1688c.2.2.2
                                            linarith only [h1597, hlam, p1688_0]
                                          · have p1688_0 := h1688c.1
                                            have p1688_1 := h1688c.2.1
                                            have p1688_2 := h1688c.2.2.1
                                            have p1688_3 := h1688c.2.2.2
                                            linarith only [h1602, hlam, p1688_0]
                                          · have p1688_0 := h1688c.1
                                            have p1688_1 := h1688c.2.1
                                            have p1688_2 := h1688c.2.2.1
                                            have p1688_3 := h1688c.2.2.2
                                            linarith only [h1603, hlam, p1688_0]
                                          · have p1688_0 := h1688c.1
                                            have p1688_1 := h1688c.2.1
                                            have p1688_2 := h1688c.2.2.1
                                            have p1688_3 := h1688c.2.2.2
                                            linarith only [hlam, p1688_0]
                                        · linarith only [h1687, hlam, p1629_0]
                                      · linarith only [h1587, h1686, hlam]
                                · linarith only [h1, h1681, hlam]
                              · have p1629_0 := h1629c.1
                                have p1629_1 := h1629c.2.1
                                have p1629_2 := h1629c.2.2.1
                                have p1629_3 := h1629c.2.2.2
                                rcases p1629_3 (m.d 0 3) (by simp) with h1733 | h1733
                                · rcases p1629_3 (m.d 1 3) (by simp) with h1734 | h1734
                                  · linarith only [h1589, h1734, hlam]
                                  · linarith only [h10, h1734, hlam]
                                · linarith only [h1733, h4, hlam]
                              · have p1629_0 := h1629c.1
                                have p1629_1 := h1629c.2.1
                                have p1629_2 := h1629c.2.2.1
                                have p1629_3 := h1629c.2.2.2
                                linarith only [h1603, hlam, p1629_0]
                              · have p1629_0 := h1629c.1
                                have p1629_1 := h1629c.2.1
                                have p1629_2 := h1629c.2.2.1
                                have p1629_3 := h1629c.2.2.2
                                linarith only [hlam, p1629_0]
                    · linarith only [h1620, hlam, p1604_0]
                  · have p1604_0 := h1604c.1
                    have p1604_1 := h1604c.2.1
                    have p1604_2 := h1604c.2.2.1
                    have p1604_3 := h1604c.2.2.2
                    rcases p1604_3 (m.d 0 1) (by simp) with h1741 | h1741
                    · rcases p1604_3 (m.d 1 2) (by simp) with h1742 | h1742
                      · linarith only [h0, h1742, hlam]
                      · linarith only [h1586, h1742, hlam]
                    · linarith only [h1741, hlam, p1604_0]
                  · have p1604_0 := h1604c.1
                    have p1604_1 := h1604c.2.1
                    have p1604_2 := h1604c.2.2.1
                    have p1604_3 := h1604c.2.2.2
                    linarith only [h0, hlam, p1604_0]
                  · have p1604_0 := h1604c.1
                    have p1604_1 := h1604c.2.1
                    have p1604_2 := h1604c.2.2.1
                    have p1604_3 := h1604c.2.2.2
                    linarith only [hlam, p1604_0]
                  · have p1604_0 := h1604c.1
                    have p1604_1 := h1604c.2.1
                    have p1604_2 := h1604c.2.2.1
                    have p1604_3 := h1604c.2.2.2
                    linarith only [h0, h10, h11, h1598, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1604_1]
                  · have p1604_0 := h1604c.1
                    have p1604_1 := h1604c.2.1
                    have p1604_2 := h1604c.2.2.1
                    have p1604_3 := h1604c.2.2.2
                    linarith only [h11, hlam, p1604_0]
                  · have p1604_0 := h1604c.1
                    have p1604_1 := h1604c.2.1
                    have p1604_2 := h1604c.2.2.1
                    have p1604_3 := h1604c.2.2.2
                    linarith only [h0, h11, h1598, h4, h7, hc01, hc15, hlam, hphi, ht0b, ht5b, p1604_1]
                  · have p1604_0 := h1604c.1
                    have p1604_1 := h1604c.2.1
                    have p1604_2 := h1604c.2.2.1
                    have p1604_3 := h1604c.2.2.2
                    linarith only [h1, hlam, p1604_0]
                  · have p1604_0 := h1604c.1
                    have p1604_1 := h1604c.2.1
                    have p1604_2 := h1604c.2.2.1
                    have p1604_3 := h1604c.2.2.2
                    linarith only [h10, hlam, p1604_1]
                  · have p1604_0 := h1604c.1
                    have p1604_1 := h1604c.2.1
                    have p1604_2 := h1604c.2.2.1
                    have p1604_3 := h1604c.2.2.2
                    linarith only [hlam, p1604_0]
                  · have p1604_0 := h1604c.1
                    have p1604_1 := h1604c.2.1
                    have p1604_2 := h1604c.2.2.1
                    have p1604_3 := h1604c.2.2.2
                    linarith only [h1587, hlam, p1604_1]
                  · have p1604_0 := h1604c.1
                    have p1604_1 := h1604c.2.1
                    have p1604_2 := h1604c.2.2.1
                    have p1604_3 := h1604c.2.2.2
                    linarith only [h1589, hlam, p1604_1]
                  · have p1604_0 := h1604c.1
                    have p1604_1 := h1604c.2.1
                    have p1604_2 := h1604c.2.2.1
                    have p1604_3 := h1604c.2.2.2
                    linarith only [h2, hlam, p1604_0]
                  · have p1604_0 := h1604c.1
                    have p1604_1 := h1604c.2.1
                    have p1604_2 := h1604c.2.2.1
                    have p1604_3 := h1604c.2.2.2
                    linarith only [h10, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1604_1]
                  · have p1604_0 := h1604c.1
                    have p1604_1 := h1604c.2.1
                    have p1604_2 := h1604c.2.2.1
                    have p1604_3 := h1604c.2.2.2
                    rcases p1604_3 (m.d 0 1) (by simp) with h1758 | h1758
                    · rcases p1604_3 (m.d 1 2) (by simp) with h1759 | h1759
                      · linarith only [h11, h1759, hlam]
                      · linarith only [h10, h1759, hlam]
                    · linarith only [h1, h1758, hlam]
                  · have p1604_0 := h1604c.1
                    have p1604_1 := h1604c.2.1
                    have p1604_2 := h1604c.2.2.1
                    have p1604_3 := h1604c.2.2.2
                    linarith only [hlam, p1604_0]
                  · have p1604_0 := h1604c.1
                    have p1604_1 := h1604c.2.1
                    have p1604_2 := h1604c.2.2.1
                    have p1604_3 := h1604c.2.2.2
                    rcases p1604_3 (m.d 0 1) (by simp) with h1764 | h1764
                    · rcases p1604_3 (m.d 1 2) (by simp) with h1765 | h1765
                      · linarith only [h11, h1765, hlam]
                      · linarith only [h1586, h1765, hlam]
                    · linarith only [h1764, h3, hlam]
                  · have p1604_0 := h1604c.1
                    have p1604_1 := h1604c.2.1
                    have p1604_2 := h1604c.2.2.1
                    have p1604_3 := h1604c.2.2.2
                    linarith only [h3, hlam, p1604_0]
                  · have p1604_0 := h1604c.1
                    have p1604_1 := h1604c.2.1
                    have p1604_2 := h1604c.2.2.1
                    have p1604_3 := h1604c.2.2.2
                    linarith only [h1586, hlam, p1604_1]
                  · have p1604_0 := h1604c.1
                    have p1604_1 := h1604c.2.1
                    have p1604_2 := h1604c.2.2.1
                    have p1604_3 := h1604c.2.2.2
                    linarith only [h0, h10, h11, h1586, h1598, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1604_1]
                  · have p1604_0 := h1604c.1
                    have p1604_1 := h1604c.2.1
                    have p1604_2 := h1604c.2.2.1
                    have p1604_3 := h1604c.2.2.2
                    linarith only [h1597, hlam, p1604_0]
                  · have p1604_0 := h1604c.1
                    have p1604_1 := h1604c.2.1
                    have p1604_2 := h1604c.2.2.1
                    have p1604_3 := h1604c.2.2.2
                    linarith only [hlam, p1604_0]
                · linarith only [h0, h10, h11, h1598, h1603, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h11, h1586, h1597, h1602, hlam]
        · linarith only [h11, h1586, h1597, hlam]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1777 | h1777
    · linarith only [h10, h11, h1777, hlam]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h1779 | h1779
      · linarith only [h10, h1586, h1779, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1781 | h1781
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1782 | h1782
          · linarith only [h0, h10, h11, h1777, h1782, h5, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1784 | h1784
            · linarith only [h10, h1586, h1779, h1784, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1786 | h1786
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1787 | h1787
                · rcases h1bigk with h1788c | h1788c | h1788c | h1788c | h1788c | h1788c | h1788c | h1788c | h1788c | h1788c | h1788c | h1788c | h1788c | h1788c | h1788c | h1788c | h1788c | h1788c | h1788c | h1788c | h1788c | h1788c | h1788c | h1788c | h1788c
                  · have p1788_0 := h1788c.1
                    have p1788_1 := h1788c.2.1
                    have p1788_2 := h1788c.2.2.1
                    have p1788_3 := h1788c.2.2.2
                    linarith only [hlam, p1788_0]
                  · have p1788_0 := h1788c.1
                    have p1788_1 := h1788c.2.1
                    have p1788_2 := h1788c.2.2.1
                    have p1788_3 := h1788c.2.2.2
                    rcases p1788_3 (m.d 0 1) (by simp) with h1790 | h1790
                    · rcases p1788_3 (m.d 1 2) (by simp) with h1791 | h1791
                      · linarith only [h1791, hlam, p1788_0]
                      · rcases p1788_3 (m.d 1 3) (by simp) with h1793 | h1793
                        · linarith only [h1, h1793, hlam]
                        · rcases p1788_3 (m.d 1 4) (by simp) with h1795 | h1795
                          · linarith only [h1795, h2, hlam]
                          · linarith only [h11, h1795, hlam]
                    · linarith only [h1790, hlam, p1788_0]
                  · have p1788_0 := h1788c.1
                    have p1788_1 := h1788c.2.1
                    have p1788_2 := h1788c.2.2.1
                    have p1788_3 := h1788c.2.2.2
                    rcases p1788_3 (m.d 0 1) (by simp) with h1799 | h1799
                    · rcases p1788_3 (m.d 1 2) (by simp) with h1800 | h1800
                      · linarith only [h0, h1800, hlam]
                      · linarith only [h10, h1800, hlam]
                    · linarith only [h1799, hlam, p1788_0]
                  · have p1788_0 := h1788c.1
                    have p1788_1 := h1788c.2.1
                    have p1788_2 := h1788c.2.2.1
                    have p1788_3 := h1788c.2.2.2
                    rcases p1788_3 (m.d 0 1) (by simp) with h1804 | h1804
                    · rcases p1788_3 (m.d 1 2) (by simp) with h1805 | h1805
                      · linarith only [h0, h1805, hlam]
                      · rcases p1788_3 (m.d 1 3) (by simp) with h1807 | h1807
                        · linarith only [h1, h1807, hlam]
                        · rcases p1788_3 (m.d 1 4) (by simp) with h1809 | h1809
                          · linarith only [h1809, hlam, p1788_0]
                          · rcases p1788_3 (m.d 1 5) (by simp) with h1811 | h1811
                            · linarith only [h1811, h3, hlam]
                            · rcases h3bigk with h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c
                              · have p1813_0 := h1813c.1
                                have p1813_1 := h1813c.2.1
                                have p1813_2 := h1813c.2.2.1
                                have p1813_3 := h1813c.2.2.2
                                linarith only [hlam, p1813_0]
                              · have p1813_0 := h1813c.1
                                have p1813_1 := h1813c.2.1
                                have p1813_2 := h1813c.2.2.1
                                have p1813_3 := h1813c.2.2.2
                                rcases p1813_3 (m.d 0 3) (by simp) with h1815 | h1815
                                · rcases p1813_3 (m.d 1 3) (by simp) with h1816 | h1816
                                  · linarith only [h1, h1816, hlam]
                                  · rcases p1813_3 (m.d 2 3) (by simp) with h1818 | h1818
                                    · linarith only [h1818, h4, hlam]
                                    · rcases p1813_3 (m.d 3 4) (by simp) with h1820 | h1820
                                      · linarith only [h1820, h7, hlam]
                                      · linarith only [h1777, h1820, hlam]
                                · linarith only [h1, h1815, hlam]
                              · have p1813_0 := h1813c.1
                                have p1813_1 := h1813c.2.1
                                have p1813_2 := h1813c.2.2.1
                                have p1813_3 := h1813c.2.2.2
                                linarith only [h10, h1586, h1782, h1786, h7, hlam, p1813_2]
                              · have p1813_0 := h1813c.1
                                have p1813_1 := h1813c.2.1
                                have p1813_2 := h1813c.2.2.1
                                have p1813_3 := h1813c.2.2.2
                                linarith only [h0, h10, h1586, h1782, h1786, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1813_1]
                              · have p1813_0 := h1813c.1
                                have p1813_1 := h1813c.2.1
                                have p1813_2 := h1813c.2.2.1
                                have p1813_3 := h1813c.2.2.2
                                linarith only [h0, h10, h1586, h1784, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1813_1]
                              · have p1813_0 := h1813c.1
                                have p1813_1 := h1813c.2.1
                                have p1813_2 := h1813c.2.2.1
                                have p1813_3 := h1813c.2.2.2
                                linarith only [h1, hlam, p1813_0]
                              · have p1813_0 := h1813c.1
                                have p1813_1 := h1813c.2.1
                                have p1813_2 := h1813c.2.2.1
                                have p1813_3 := h1813c.2.2.2
                                linarith only [hlam, p1813_0]
                              · have p1813_0 := h1813c.1
                                have p1813_1 := h1813c.2.1
                                have p1813_2 := h1813c.2.2.1
                                have p1813_3 := h1813c.2.2.2
                                linarith only [h10, h1586, h1782, h1786, hc23, hc34, hlam, hphi, p1813_1]
                              · have p1813_0 := h1813c.1
                                have p1813_1 := h1813c.2.1
                                have p1813_2 := h1813c.2.2.1
                                have p1813_3 := h1813c.2.2.2
                                linarith only [h1777, hlam, p1813_0]
                              · have p1813_0 := h1813c.1
                                have p1813_1 := h1813c.2.1
                                have p1813_2 := h1813c.2.2.1
                                have p1813_3 := h1813c.2.2.2
                                linarith only [h1779, hlam, p1813_0]
                              · have p1813_0 := h1813c.1
                                have p1813_1 := h1813c.2.1
                                have p1813_2 := h1813c.2.2.1
                                have p1813_3 := h1813c.2.2.2
                                linarith only [h4, hlam, p1813_0]
                              · have p1813_0 := h1813c.1
                                have p1813_1 := h1813c.2.1
                                have p1813_2 := h1813c.2.2.1
                                have p1813_3 := h1813c.2.2.2
                                linarith only [h10, hlam, p1813_0]
                              · have p1813_0 := h1813c.1
                                have p1813_1 := h1813c.2.1
                                have p1813_2 := h1813c.2.2.1
                                have p1813_3 := h1813c.2.2.2
                                linarith only [hlam, p1813_0]
                              · have p1813_0 := h1813c.1
                                have p1813_1 := h1813c.2.1
                                have p1813_2 := h1813c.2.2.1
                                have p1813_3 := h1813c.2.2.2
                                linarith only [h1782, hlam, p1813_0]
                              · have p1813_0 := h1813c.1
                                have p1813_1 := h1813c.2.1
                                have p1813_2 := h1813c.2.2.1
                                have p1813_3 := h1813c.2.2.2
                                linarith only [h1784, hlam, p1813_0]
                              · have p1813_0 := h1813c.1
                                have p1813_1 := h1813c.2.1
                                have p1813_2 := h1813c.2.2.1
                                have p1813_3 := h1813c.2.2.2
                                linarith only [h7, hlam, p1813_0]
                              · have p1813_0 := h1813c.1
                                have p1813_1 := h1813c.2.1
                                have p1813_2 := h1813c.2.2.1
                                have p1813_3 := h1813c.2.2.2
                                rcases p1813_3 (m.d 0 3) (by simp) with h1838 | h1838
                                · rcases p1813_3 (m.d 1 3) (by simp) with h1839 | h1839
                                  · linarith only [h1839, hlam, p1813_0]
                                  · rcases p1813_3 (m.d 2 3) (by simp) with h1841 | h1841
                                    · linarith only [h1782, h1841, hlam]
                                    · rcases p1813_3 (m.d 3 4) (by simp) with h1843 | h1843
                                      · rcases p1813_3 (m.d 3 5) (by simp) with h1844 | h1844
                                        · linarith only [h1787, h1844, hlam]
                                        · linarith only [h1779, h1844, hlam]
                                      · linarith only [h1843, hlam, p1813_0]
                                · linarith only [h1, h1838, hlam]
                              · have p1813_0 := h1813c.1
                                have p1813_1 := h1813c.2.1
                                have p1813_2 := h1813c.2.2.1
                                have p1813_3 := h1813c.2.2.2
                                rcases p1813_3 (m.d 0 3) (by simp) with h1849 | h1849
                                · rcases p1813_3 (m.d 1 3) (by simp) with h1850 | h1850
                                  · linarith only [h1777, h1850, hlam]
                                  · linarith only [h10, h1850, hlam]
                                · linarith only [h1849, h4, hlam]
                              · have p1813_0 := h1813c.1
                                have p1813_1 := h1813c.2.1
                                have p1813_2 := h1813c.2.2.1
                                have p1813_3 := h1813c.2.2.2
                                linarith only [hlam, p1813_0]
                              · have p1813_0 := h1813c.1
                                have p1813_1 := h1813c.2.1
                                have p1813_2 := h1813c.2.2.1
                                have p1813_3 := h1813c.2.2.2
                                linarith only [h0, h1779, h4, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1813_1]
                              · have p1813_0 := h1813c.1
                                have p1813_1 := h1813c.2.1
                                have p1813_2 := h1813c.2.2.1
                                have p1813_3 := h1813c.2.2.2
                                linarith only [h8, hlam, p1813_0]
                              · have p1813_0 := h1813c.1
                                have p1813_1 := h1813c.2.1
                                have p1813_2 := h1813c.2.2.1
                                have p1813_3 := h1813c.2.2.2
                                rcases p1813_3 (m.d 0 3) (by simp) with h1857 | h1857
                                · rcases p1813_3 (m.d 1 3) (by simp) with h1858 | h1858
                                  · linarith only [h1858, hlam, p1813_0]
                                  · rcases p1813_3 (m.d 2 3) (by simp) with h1860 | h1860
                                    · linarith only [h1784, h1860, hlam]
                                    · rcases p1813_3 (m.d 3 4) (by simp) with h1862 | h1862
                                      · rcases p1813_3 (m.d 3 5) (by simp) with h1863 | h1863
                                        · rcases h5bigk with h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c
                                          · have p1864_0 := h1864c.1
                                            have p1864_1 := h1864c.2.1
                                            have p1864_2 := h1864c.2.2.1
                                            have p1864_3 := h1864c.2.2.2
                                            linarith only [hlam, p1864_0]
                                          · have p1864_0 := h1864c.1
                                            have p1864_1 := h1864c.2.1
                                            have p1864_2 := h1864c.2.2.1
                                            have p1864_3 := h1864c.2.2.2
                                            linarith only [h0, h10, h1586, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1864_1]
                                          · have p1864_0 := h1864c.1
                                            have p1864_1 := h1864c.2.1
                                            have p1864_2 := h1864c.2.2.1
                                            have p1864_3 := h1864c.2.2.2
                                            linarith only [h0, h10, h1586, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1864_1]
                                          · have p1864_0 := h1864c.1
                                            have p1864_1 := h1864c.2.1
                                            have p1864_2 := h1864c.2.2.1
                                            have p1864_3 := h1864c.2.2.2
                                            linarith only [h0, h10, h1586, h1784, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1864_1]
                                          · have p1864_0 := h1864c.1
                                            have p1864_1 := h1864c.2.1
                                            have p1864_2 := h1864c.2.2.1
                                            have p1864_3 := h1864c.2.2.2
                                            rcases p1864_3 (m.d 0 5) (by simp) with h1869 | h1869
                                            · rcases p1864_3 (m.d 1 5) (by simp) with h1870 | h1870
                                              · linarith only [h1870, h3, hlam]
                                              · linarith only [h1781, h1870, hlam]
                                            · linarith only [h1869, h9, hlam]
                                          · have p1864_0 := h1864c.1
                                            have p1864_1 := h1864c.2.1
                                            have p1864_2 := h1864c.2.2.1
                                            have p1864_3 := h1864c.2.2.2
                                            linarith only [h3, hlam, p1864_0]
                                          · have p1864_0 := h1864c.1
                                            have p1864_1 := h1864c.2.1
                                            have p1864_2 := h1864c.2.2.1
                                            have p1864_3 := h1864c.2.2.2
                                            linarith only [hlam, p1864_0]
                                          · have p1864_0 := h1864c.1
                                            have p1864_1 := h1864c.2.1
                                            have p1864_2 := h1864c.2.2.1
                                            have p1864_3 := h1864c.2.2.2
                                            linarith only [h1586, hlam, p1864_0]
                                          · have p1864_0 := h1864c.1
                                            have p1864_1 := h1864c.2.1
                                            have p1864_2 := h1864c.2.2.1
                                            have p1864_3 := h1864c.2.2.2
                                            linarith only [h1779, hlam, p1864_1]
                                          · have p1864_0 := h1864c.1
                                            have p1864_1 := h1864c.2.1
                                            have p1864_2 := h1864c.2.2.1
                                            have p1864_3 := h1864c.2.2.2
                                            linarith only [h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p1864_1]
                                          · have p1864_0 := h1864c.1
                                            have p1864_1 := h1864c.2.1
                                            have p1864_2 := h1864c.2.2.1
                                            have p1864_3 := h1864c.2.2.2
                                            linarith only [h6, hlam, p1864_1]
                                          · have p1864_0 := h1864c.1
                                            have p1864_1 := h1864c.2.1
                                            have p1864_2 := h1864c.2.2.1
                                            have p1864_3 := h1864c.2.2.2
                                            linarith only [h0, h6, hc01, hc15, hlam, hphi, ht0b, ht5b, p1864_1]
                                          · have p1864_0 := h1864c.1
                                            have p1864_1 := h1864c.2.1
                                            have p1864_2 := h1864c.2.2.1
                                            have p1864_3 := h1864c.2.2.2
                                            linarith only [hlam, p1864_0]
                                          · have p1864_0 := h1864c.1
                                            have p1864_1 := h1864c.2.1
                                            have p1864_2 := h1864c.2.2.1
                                            have p1864_3 := h1864c.2.2.2
                                            linarith only [h1784, hlam, p1864_1]
                                          · have p1864_0 := h1864c.1
                                            have p1864_1 := h1864c.2.1
                                            have p1864_2 := h1864c.2.2.1
                                            have p1864_3 := h1864c.2.2.2
                                            linarith only [h0, h1782, h1786, h4, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p1864_1]
                                          · have p1864_0 := h1864c.1
                                            have p1864_1 := h1864c.2.1
                                            have p1864_2 := h1864c.2.2.1
                                            have p1864_3 := h1864c.2.2.2
                                            linarith only [h8, hlam, p1864_0]
                                          · have p1864_0 := h1864c.1
                                            have p1864_1 := h1864c.2.1
                                            have p1864_2 := h1864c.2.2.1
                                            have p1864_3 := h1864c.2.2.2
                                            linarith only [h0, h10, h1586, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1864_1]
                                          · have p1864_0 := h1864c.1
                                            have p1864_1 := h1864c.2.1
                                            have p1864_2 := h1864c.2.2.1
                                            have p1864_3 := h1864c.2.2.2
                                            linarith only [h0, h4, h8, hc01, hc25, hlam, hphi, ht0b, ht5b, p1864_1]
                                          · have p1864_0 := h1864c.1
                                            have p1864_1 := h1864c.2.1
                                            have p1864_2 := h1864c.2.2.1
                                            have p1864_3 := h1864c.2.2.2
                                            linarith only [hlam, p1864_0]
                                          · have p1864_0 := h1864c.1
                                            have p1864_1 := h1864c.2.1
                                            have p1864_2 := h1864c.2.2.1
                                            have p1864_3 := h1864c.2.2.2
                                            linarith only [h0, h1787, h4, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p1864_1]
                                          · have p1864_0 := h1864c.1
                                            have p1864_1 := h1864c.2.1
                                            have p1864_2 := h1864c.2.2.1
                                            have p1864_3 := h1864c.2.2.2
                                            linarith only [h9, hlam, p1864_0]
                                          · have p1864_0 := h1864c.1
                                            have p1864_1 := h1864c.2.1
                                            have p1864_2 := h1864c.2.2.1
                                            have p1864_3 := h1864c.2.2.2
                                            linarith only [h1781, hlam, p1864_0]
                                          · have p1864_0 := h1864c.1
                                            have p1864_1 := h1864c.2.1
                                            have p1864_2 := h1864c.2.2.1
                                            have p1864_3 := h1864c.2.2.2
                                            linarith only [h1786, hlam, p1864_0]
                                          · have p1864_0 := h1864c.1
                                            have p1864_1 := h1864c.2.1
                                            have p1864_2 := h1864c.2.2.1
                                            have p1864_3 := h1864c.2.2.2
                                            linarith only [h1787, hlam, p1864_0]
                                          · have p1864_0 := h1864c.1
                                            have p1864_1 := h1864c.2.1
                                            have p1864_2 := h1864c.2.2.1
                                            have p1864_3 := h1864c.2.2.2
                                            linarith only [hlam, p1864_0]
                                        · linarith only [h1863, hlam, p1813_0]
                                      · linarith only [h1777, h1862, hlam]
                                · linarith only [h1, h1857, hlam]
                              · have p1813_0 := h1813c.1
                                have p1813_1 := h1813c.2.1
                                have p1813_2 := h1813c.2.2.1
                                have p1813_3 := h1813c.2.2.2
                                rcases p1813_3 (m.d 0 3) (by simp) with h1897 | h1897
                                · rcases p1813_3 (m.d 1 3) (by simp) with h1898 | h1898
                                  · linarith only [h1779, h1898, hlam]
                                  · linarith only [h10, h1898, hlam]
                                · linarith only [h1897, h4, hlam]
                              · have p1813_0 := h1813c.1
                                have p1813_1 := h1813c.2.1
                                have p1813_2 := h1813c.2.2.1
                                have p1813_3 := h1813c.2.2.2
                                linarith only [h1787, hlam, p1813_0]
                              · have p1813_0 := h1813c.1
                                have p1813_1 := h1813c.2.1
                                have p1813_2 := h1813c.2.2.1
                                have p1813_3 := h1813c.2.2.2
                                linarith only [hlam, p1813_0]
                    · linarith only [h1804, hlam, p1788_0]
                  · have p1788_0 := h1788c.1
                    have p1788_1 := h1788c.2.1
                    have p1788_2 := h1788c.2.2.1
                    have p1788_3 := h1788c.2.2.2
                    rcases p1788_3 (m.d 0 1) (by simp) with h1905 | h1905
                    · rcases p1788_3 (m.d 1 2) (by simp) with h1906 | h1906
                      · linarith only [h0, h1906, hlam]
                      · rcases p1788_3 (m.d 1 3) (by simp) with h1908 | h1908
                        · linarith only [h1, h1908, hlam]
                        · rcases p1788_3 (m.d 1 4) (by simp) with h1910 | h1910
                          · linarith only [h1910, h2, hlam]
                          · linarith only [h1781, h1910, hlam]
                    · linarith only [h1905, hlam, p1788_0]
                  · have p1788_0 := h1788c.1
                    have p1788_1 := h1788c.2.1
                    have p1788_2 := h1788c.2.2.1
                    have p1788_3 := h1788c.2.2.2
                    linarith only [h0, hlam, p1788_0]
                  · have p1788_0 := h1788c.1
                    have p1788_1 := h1788c.2.1
                    have p1788_2 := h1788c.2.2.1
                    have p1788_3 := h1788c.2.2.2
                    linarith only [hlam, p1788_0]
                  · have p1788_0 := h1788c.1
                    have p1788_1 := h1788c.2.1
                    have p1788_2 := h1788c.2.2.1
                    have p1788_3 := h1788c.2.2.2
                    linarith only [h0, h10, h1586, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1788_1]
                  · have p1788_0 := h1788c.1
                    have p1788_1 := h1788c.2.1
                    have p1788_2 := h1788c.2.2.1
                    have p1788_3 := h1788c.2.2.2
                    linarith only [h11, hlam, p1788_0]
                  · have p1788_0 := h1788c.1
                    have p1788_1 := h1788c.2.1
                    have p1788_2 := h1788c.2.2.1
                    have p1788_3 := h1788c.2.2.2
                    linarith only [h1586, hlam, p1788_0]
                  · have p1788_0 := h1788c.1
                    have p1788_1 := h1788c.2.1
                    have p1788_2 := h1788c.2.2.1
                    have p1788_3 := h1788c.2.2.2
                    linarith only [h1, hlam, p1788_0]
                  · have p1788_0 := h1788c.1
                    have p1788_1 := h1788c.2.1
                    have p1788_2 := h1788c.2.2.1
                    have p1788_3 := h1788c.2.2.2
                    linarith only [h10, hlam, p1788_1]
                  · have p1788_0 := h1788c.1
                    have p1788_1 := h1788c.2.1
                    have p1788_2 := h1788c.2.2.1
                    have p1788_3 := h1788c.2.2.2
                    linarith only [hlam, p1788_0]
                  · have p1788_0 := h1788c.1
                    have p1788_1 := h1788c.2.1
                    have p1788_2 := h1788c.2.2.1
                    have p1788_3 := h1788c.2.2.2
                    linarith only [h1777, hlam, p1788_1]
                  · have p1788_0 := h1788c.1
                    have p1788_1 := h1788c.2.1
                    have p1788_2 := h1788c.2.2.1
                    have p1788_3 := h1788c.2.2.2
                    linarith only [h1779, hlam, p1788_1]
                  · have p1788_0 := h1788c.1
                    have p1788_1 := h1788c.2.1
                    have p1788_2 := h1788c.2.2.1
                    have p1788_3 := h1788c.2.2.2
                    linarith only [h2, hlam, p1788_0]
                  · have p1788_0 := h1788c.1
                    have p1788_1 := h1788c.2.1
                    have p1788_2 := h1788c.2.2.1
                    have p1788_3 := h1788c.2.2.2
                    linarith only [h10, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1788_1]
                  · have p1788_0 := h1788c.1
                    have p1788_1 := h1788c.2.1
                    have p1788_2 := h1788c.2.2.1
                    have p1788_3 := h1788c.2.2.2
                    rcases p1788_3 (m.d 0 1) (by simp) with h1926 | h1926
                    · rcases p1788_3 (m.d 1 2) (by simp) with h1927 | h1927
                      · linarith only [h11, h1927, hlam]
                      · linarith only [h10, h1927, hlam]
                    · linarith only [h1, h1926, hlam]
                  · have p1788_0 := h1788c.1
                    have p1788_1 := h1788c.2.1
                    have p1788_2 := h1788c.2.2.1
                    have p1788_3 := h1788c.2.2.2
                    linarith only [hlam, p1788_0]
                  · have p1788_0 := h1788c.1
                    have p1788_1 := h1788c.2.1
                    have p1788_2 := h1788c.2.2.1
                    have p1788_3 := h1788c.2.2.2
                    linarith only [h0, h10, h11, h1586, h1782, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1788_1]
                  · have p1788_0 := h1788c.1
                    have p1788_1 := h1788c.2.1
                    have p1788_2 := h1788c.2.2.1
                    have p1788_3 := h1788c.2.2.2
                    linarith only [h3, hlam, p1788_0]
                  · have p1788_0 := h1788c.1
                    have p1788_1 := h1788c.2.1
                    have p1788_2 := h1788c.2.2.1
                    have p1788_3 := h1788c.2.2.2
                    linarith only [h10, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1788_1]
                  · have p1788_0 := h1788c.1
                    have p1788_1 := h1788c.2.1
                    have p1788_2 := h1788c.2.2.1
                    have p1788_3 := h1788c.2.2.2
                    rcases p1788_3 (m.d 0 1) (by simp) with h1935 | h1935
                    · rcases p1788_3 (m.d 1 2) (by simp) with h1936 | h1936
                      · linarith only [h1586, h1936, hlam]
                      · linarith only [h10, h1936, hlam]
                    · linarith only [h1, h1935, hlam]
                  · have p1788_0 := h1788c.1
                    have p1788_1 := h1788c.2.1
                    have p1788_2 := h1788c.2.2.1
                    have p1788_3 := h1788c.2.2.2
                    linarith only [h1781, hlam, p1788_0]
                  · have p1788_0 := h1788c.1
                    have p1788_1 := h1788c.2.1
                    have p1788_2 := h1788c.2.2.1
                    have p1788_3 := h1788c.2.2.2
                    linarith only [hlam, p1788_0]
                · linarith only [h0, h10, h11, h1782, h1787, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h11, h1781, h1786, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1944 | h1944
          · linarith only [h0, h10, h11, h1944, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1946 | h1946
            · linarith only [h0, h10, h11, h1781, h1946, h4, h7, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1948 | h1948
              · linarith only [h0, h10, h11, h1781, h1944, h1948, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h10, h11, h1948, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]

set_option maxHeartbeats 7932000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s9_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
  · exact r1l7_11_13_25_L_I_L_I_H_I_s9_x0_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h11
  · exact r1l7_11_13_25_L_I_L_I_H_I_s9_x0_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h11

set_option maxHeartbeats 7932000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s9_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1951 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 2 5 (by decide) (by decide) with h1952 | h1952
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1953 | h1953
    · rcases m.htr 1 3 5 (by decide) (by decide) with h1954 | h1954
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1955 | h1955
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1956 | h1956
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1957 | h1957
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1958 | h1958
              · linarith only [h0, h10, h1951, h1958, h4, hc01, hc45, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h10, h1951, h1955, h1958, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h10, h1952, h1957, h4, h8, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · linarith only [h10, h1952, h1956, h7, hc03, hc25, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1963 | h1963
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1964 | h1964
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1965 | h1965
              · linarith only [h10, h1951, h1955, h1965, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1967 | h1967
                · linarith only [h0, h10, h1951, h1955, h1963, h1967, h4, hc01, hc15, hlam, hphi, ht0b, ht5b]
                · rcases h1bigk with h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c | h1969c
                  · have p1969_0 := h1969c.1
                    have p1969_1 := h1969c.2.1
                    have p1969_2 := h1969c.2.2.1
                    have p1969_3 := h1969c.2.2.2
                    linarith only [hlam, p1969_0]
                  · have p1969_0 := h1969c.1
                    have p1969_1 := h1969c.2.1
                    have p1969_2 := h1969c.2.2.1
                    have p1969_3 := h1969c.2.2.2
                    rcases p1969_3 (m.d 0 1) (by simp) with h1971 | h1971
                    · rcases p1969_3 (m.d 1 2) (by simp) with h1972 | h1972
                      · linarith only [h1972, hlam, p1969_0]
                      · rcases p1969_3 (m.d 1 3) (by simp) with h1974 | h1974
                        · linarith only [h1, h1974, hlam]
                        · linarith only [h10, h1974, hlam]
                    · linarith only [h1971, hlam, p1969_0]
                  · have p1969_0 := h1969c.1
                    have p1969_1 := h1969c.2.1
                    have p1969_2 := h1969c.2.2.1
                    have p1969_3 := h1969c.2.2.2
                    rcases p1969_3 (m.d 0 1) (by simp) with h1978 | h1978
                    · rcases p1969_3 (m.d 1 2) (by simp) with h1979 | h1979
                      · linarith only [h0, h1979, hlam]
                      · rcases p1969_3 (m.d 1 3) (by simp) with h1981 | h1981
                        · linarith only [h1981, hlam, p1969_0]
                        · rcases p1969_3 (m.d 1 4) (by simp) with h1983 | h1983
                          · linarith only [h1983, h2, hlam]
                          · rcases p1969_3 (m.d 1 5) (by simp) with h1985 | h1985
                            · linarith only [h1985, h3, hlam]
                            · rcases h3bigk with h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c
                              · have p1987_0 := h1987c.1
                                have p1987_1 := h1987c.2.1
                                have p1987_2 := h1987c.2.2.1
                                have p1987_3 := h1987c.2.2.2
                                linarith only [hlam, p1987_0]
                              · have p1987_0 := h1987c.1
                                have p1987_1 := h1987c.2.1
                                have p1987_2 := h1987c.2.2.1
                                have p1987_3 := h1987c.2.2.2
                                rcases p1987_3 (m.d 0 3) (by simp) with h1989 | h1989
                                · rcases p1987_3 (m.d 1 3) (by simp) with h1990 | h1990
                                  · linarith only [h1, h1990, hlam]
                                  · rcases p1987_3 (m.d 2 3) (by simp) with h1992 | h1992
                                    · linarith only [h1992, h4, hlam]
                                    · linarith only [h10, h1992, hlam]
                                · linarith only [h1, h1989, hlam]
                              · have p1987_0 := h1987c.1
                                have p1987_1 := h1987c.2.1
                                have p1987_2 := h1987c.2.2.1
                                have p1987_3 := h1987c.2.2.2
                                linarith only [h0, h10, h1952, h1965, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1987_1]
                              · have p1987_0 := h1987c.1
                                have p1987_1 := h1987c.2.1
                                have p1987_2 := h1987c.2.2.1
                                have p1987_3 := h1987c.2.2.2
                                rcases p1987_3 (m.d 0 3) (by simp) with h1997 | h1997
                                · rcases p1987_3 (m.d 1 3) (by simp) with h1998 | h1998
                                  · linarith only [h1, h1998, hlam]
                                  · linarith only [h1953, h1998, hlam]
                                · linarith only [h1997, hlam, p1987_0]
                              · have p1987_0 := h1987c.1
                                have p1987_1 := h1987c.2.1
                                have p1987_2 := h1987c.2.2.1
                                have p1987_3 := h1987c.2.2.2
                                rcases p1987_3 (m.d 0 3) (by simp) with h2002 | h2002
                                · rcases p1987_3 (m.d 1 3) (by simp) with h2003 | h2003
                                  · linarith only [h1, h2003, hlam]
                                  · linarith only [h1954, h2003, hlam]
                                · linarith only [h2002, hlam, p1987_0]
                              · have p1987_0 := h1987c.1
                                have p1987_1 := h1987c.2.1
                                have p1987_2 := h1987c.2.2.1
                                have p1987_3 := h1987c.2.2.2
                                linarith only [h1, hlam, p1987_0]
                              · have p1987_0 := h1987c.1
                                have p1987_1 := h1987c.2.1
                                have p1987_2 := h1987c.2.2.1
                                have p1987_3 := h1987c.2.2.2
                                linarith only [hlam, p1987_0]
                              · have p1987_0 := h1987c.1
                                have p1987_1 := h1987c.2.1
                                have p1987_2 := h1987c.2.2.1
                                have p1987_3 := h1987c.2.2.2
                                linarith only [h10, hlam, p1987_1]
                              · have p1987_0 := h1987c.1
                                have p1987_1 := h1987c.2.1
                                have p1987_2 := h1987c.2.2.1
                                have p1987_3 := h1987c.2.2.2
                                linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1969_1, p1987_1]
                              · have p1987_0 := h1987c.1
                                have p1987_1 := h1987c.2.1
                                have p1987_2 := h1987c.2.2.1
                                have p1987_3 := h1987c.2.2.2
                                linarith only [h1967, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1969_1, p1987_1]
                              · have p1987_0 := h1987c.1
                                have p1987_1 := h1987c.2.1
                                have p1987_2 := h1987c.2.2.1
                                have p1987_3 := h1987c.2.2.2
                                linarith only [h4, hlam, p1987_0]
                              · have p1987_0 := h1987c.1
                                have p1987_1 := h1987c.2.1
                                have p1987_2 := h1987c.2.2.1
                                have p1987_3 := h1987c.2.2.2
                                linarith only [h0, h4, hlam, p1969_2, p1987_1]
                              · have p1987_0 := h1987c.1
                                have p1987_1 := h1987c.2.1
                                have p1987_2 := h1987c.2.2.1
                                have p1987_3 := h1987c.2.2.2
                                linarith only [hlam, p1987_0]
                              · have p1987_0 := h1987c.1
                                have p1987_1 := h1987c.2.1
                                have p1987_2 := h1987c.2.2.1
                                have p1987_3 := h1987c.2.2.2
                                rcases p1987_3 (m.d 0 3) (by simp) with h2015 | h2015
                                · rcases p1987_3 (m.d 1 3) (by simp) with h2016 | h2016
                                  · linarith only [h10, h2016, hlam]
                                  · linarith only [h1953, h2016, hlam]
                                · linarith only [h2015, h7, hlam]
                              · have p1987_0 := h1987c.1
                                have p1987_1 := h1987c.2.1
                                have p1987_2 := h1987c.2.2.1
                                have p1987_3 := h1987c.2.2.2
                                rcases p1987_3 (m.d 0 3) (by simp) with h2020 | h2020
                                · rcases p1987_3 (m.d 1 3) (by simp) with h2021 | h2021
                                  · linarith only [h10, h2021, hlam]
                                  · linarith only [h1954, h2021, hlam]
                                · linarith only [h2020, h8, hlam]
                              · have p1987_0 := h1987c.1
                                have p1987_1 := h1987c.2.1
                                have p1987_2 := h1987c.2.2.1
                                have p1987_3 := h1987c.2.2.2
                                linarith only [h7, hlam, p1987_0]
                              · have p1987_0 := h1987c.1
                                have p1987_1 := h1987c.2.1
                                have p1987_2 := h1987c.2.2.1
                                have p1987_3 := h1987c.2.2.2
                                linarith only [h1953, hlam, p1987_0]
                              · have p1987_0 := h1987c.1
                                have p1987_1 := h1987c.2.1
                                have p1987_2 := h1987c.2.2.1
                                have p1987_3 := h1987c.2.2.2
                                linarith only [h1963, hlam, p1987_0]
                              · have p1987_0 := h1987c.1
                                have p1987_1 := h1987c.2.1
                                have p1987_2 := h1987c.2.2.1
                                have p1987_3 := h1987c.2.2.2
                                linarith only [hlam, p1987_0]
                              · have p1987_0 := h1987c.1
                                have p1987_1 := h1987c.2.1
                                have p1987_2 := h1987c.2.2.1
                                have p1987_3 := h1987c.2.2.2
                                linarith only [h1967, hlam, p1987_1]
                              · have p1987_0 := h1987c.1
                                have p1987_1 := h1987c.2.1
                                have p1987_2 := h1987c.2.2.1
                                have p1987_3 := h1987c.2.2.2
                                linarith only [h8, hlam, p1987_0]
                              · have p1987_0 := h1987c.1
                                have p1987_1 := h1987c.2.1
                                have p1987_2 := h1987c.2.2.1
                                have p1987_3 := h1987c.2.2.2
                                linarith only [h1954, hlam, p1987_0]
                              · have p1987_0 := h1987c.1
                                have p1987_1 := h1987c.2.1
                                have p1987_2 := h1987c.2.2.1
                                have p1987_3 := h1987c.2.2.2
                                linarith only [h1964, hlam, p1987_0]
                              · have p1987_0 := h1987c.1
                                have p1987_1 := h1987c.2.1
                                have p1987_2 := h1987c.2.2.1
                                have p1987_3 := h1987c.2.2.2
                                linarith only [h1954, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1969_1, p1987_1]
                              · have p1987_0 := h1987c.1
                                have p1987_1 := h1987c.2.1
                                have p1987_2 := h1987c.2.2.1
                                have p1987_3 := h1987c.2.2.2
                                linarith only [hlam, p1987_0]
                    · linarith only [h1978, hlam, p1969_0]
                  · have p1969_0 := h1969c.1
                    have p1969_1 := h1969c.2.1
                    have p1969_2 := h1969c.2.2.1
                    have p1969_3 := h1969c.2.2.2
                    rcases p1969_3 (m.d 0 1) (by simp) with h2036 | h2036
                    · rcases p1969_3 (m.d 1 2) (by simp) with h2037 | h2037
                      · linarith only [h0, h2037, hlam]
                      · linarith only [h1951, h2037, hlam]
                    · linarith only [h2036, hlam, p1969_0]
                  · have p1969_0 := h1969c.1
                    have p1969_1 := h1969c.2.1
                    have p1969_2 := h1969c.2.2.1
                    have p1969_3 := h1969c.2.2.2
                    rcases p1969_3 (m.d 0 1) (by simp) with h2041 | h2041
                    · rcases p1969_3 (m.d 1 2) (by simp) with h2042 | h2042
                      · linarith only [h0, h2042, hlam]
                      · linarith only [h1952, h2042, hlam]
                    · linarith only [h2041, hlam, p1969_0]
                  · have p1969_0 := h1969c.1
                    have p1969_1 := h1969c.2.1
                    have p1969_2 := h1969c.2.2.1
                    have p1969_3 := h1969c.2.2.2
                    linarith only [h0, hlam, p1969_0]
                  · have p1969_0 := h1969c.1
                    have p1969_1 := h1969c.2.1
                    have p1969_2 := h1969c.2.2.1
                    have p1969_3 := h1969c.2.2.2
                    linarith only [hlam, p1969_0]
                  · have p1969_0 := h1969c.1
                    have p1969_1 := h1969c.2.1
                    have p1969_2 := h1969c.2.2.1
                    have p1969_3 := h1969c.2.2.2
                    linarith only [h10, hlam, p1969_0]
                  · have p1969_0 := h1969c.1
                    have p1969_1 := h1969c.2.1
                    have p1969_2 := h1969c.2.2.1
                    have p1969_3 := h1969c.2.2.2
                    linarith only [h0, h10, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1969_1]
                  · have p1969_0 := h1969c.1
                    have p1969_1 := h1969c.2.1
                    have p1969_2 := h1969c.2.2.1
                    have p1969_3 := h1969c.2.2.2
                    linarith only [h0, h10, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p1969_1]
                  · have p1969_0 := h1969c.1
                    have p1969_1 := h1969c.2.1
                    have p1969_2 := h1969c.2.2.1
                    have p1969_3 := h1969c.2.2.2
                    linarith only [h1, hlam, p1969_0]
                  · have p1969_0 := h1969c.1
                    have p1969_1 := h1969c.2.1
                    have p1969_2 := h1969c.2.2.1
                    have p1969_3 := h1969c.2.2.2
                    linarith only [h1, h1951, h1963, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1969_1]
                  · have p1969_0 := h1969c.1
                    have p1969_1 := h1969c.2.1
                    have p1969_2 := h1969c.2.2.1
                    have p1969_3 := h1969c.2.2.2
                    linarith only [hlam, p1969_0]
                  · have p1969_0 := h1969c.1
                    have p1969_1 := h1969c.2.1
                    have p1969_2 := h1969c.2.2.1
                    have p1969_3 := h1969c.2.2.2
                    rcases p1969_3 (m.d 0 1) (by simp) with h2054 | h2054
                    · rcases p1969_3 (m.d 1 2) (by simp) with h2055 | h2055
                      · linarith only [h10, h2055, hlam]
                      · linarith only [h1951, h2055, hlam]
                    · linarith only [h2, h2054, hlam]
                  · have p1969_0 := h1969c.1
                    have p1969_1 := h1969c.2.1
                    have p1969_2 := h1969c.2.2.1
                    have p1969_3 := h1969c.2.2.2
                    rcases p1969_3 (m.d 0 1) (by simp) with h2059 | h2059
                    · rcases p1969_3 (m.d 1 2) (by simp) with h2060 | h2060
                      · linarith only [h10, h2060, hlam]
                      · linarith only [h1952, h2060, hlam]
                    · linarith only [h2059, h3, hlam]
                  · have p1969_0 := h1969c.1
                    have p1969_1 := h1969c.2.1
                    have p1969_2 := h1969c.2.2.1
                    have p1969_3 := h1969c.2.2.2
                    linarith only [h2, hlam, p1969_0]
                  · have p1969_0 := h1969c.1
                    have p1969_1 := h1969c.2.1
                    have p1969_2 := h1969c.2.2.1
                    have p1969_3 := h1969c.2.2.2
                    linarith only [h1951, hlam, p1969_1]
                  · have p1969_0 := h1969c.1
                    have p1969_1 := h1969c.2.1
                    have p1969_2 := h1969c.2.2.1
                    have p1969_3 := h1969c.2.2.2
                    linarith only [h1953, hlam, p1969_0]
                  · have p1969_0 := h1969c.1
                    have p1969_1 := h1969c.2.1
                    have p1969_2 := h1969c.2.2.1
                    have p1969_3 := h1969c.2.2.2
                    linarith only [hlam, p1969_0]
                  · have p1969_0 := h1969c.1
                    have p1969_1 := h1969c.2.1
                    have p1969_2 := h1969c.2.2.1
                    have p1969_3 := h1969c.2.2.2
                    linarith only [h1955, hlam, p1969_1]
                  · have p1969_0 := h1969c.1
                    have p1969_1 := h1969c.2.1
                    have p1969_2 := h1969c.2.2.1
                    have p1969_3 := h1969c.2.2.2
                    linarith only [h3, hlam, p1969_0]
                  · have p1969_0 := h1969c.1
                    have p1969_1 := h1969c.2.1
                    have p1969_2 := h1969c.2.2.1
                    have p1969_3 := h1969c.2.2.2
                    linarith only [h1952, hlam, p1969_1]
                  · have p1969_0 := h1969c.1
                    have p1969_1 := h1969c.2.1
                    have p1969_2 := h1969c.2.2.1
                    have p1969_3 := h1969c.2.2.2
                    linarith only [h1954, hlam, p1969_0]
                  · have p1969_0 := h1969c.1
                    have p1969_1 := h1969c.2.1
                    have p1969_2 := h1969c.2.2.1
                    have p1969_3 := h1969c.2.2.2
                    linarith only [h0, h10, h1951, h1952, h1963, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1969_1]
                  · have p1969_0 := h1969c.1
                    have p1969_1 := h1969c.2.1
                    have p1969_2 := h1969c.2.2.1
                    have p1969_3 := h1969c.2.2.2
                    linarith only [hlam, p1969_0]
            · linarith only [h0, h10, h1951, h1963, h1964, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h10, h1951, h1963, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · linarith only [h10, h1952, h1954, hlam]
    · linarith only [h10, h1951, h1953, hlam]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h2078 | h2078
    · rcases m.htr 1 3 5 (by decide) (by decide) with h2079 | h2079
      · rcases m.htr 1 4 5 (by decide) (by decide) with h2080 | h2080
        · linarith only [h1951, h1952, h2080, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h2082 | h2082
          · rcases m.htr 2 3 5 (by decide) (by decide) with h2083 | h2083
            · rcases m.htr 2 4 5 (by decide) (by decide) with h2084 | h2084
              · linarith only [h1951, h1952, h2080, h2084, h6, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h2086 | h2086
                · linarith only [h1951, h1952, h2082, h2084, h2086, hlam]
                · rcases h1bigk with h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c
                  · have p2088_0 := h2088c.1
                    have p2088_1 := h2088c.2.1
                    have p2088_2 := h2088c.2.2.1
                    have p2088_3 := h2088c.2.2.2
                    linarith only [hlam, p2088_0]
                  · have p2088_0 := h2088c.1
                    have p2088_1 := h2088c.2.1
                    have p2088_2 := h2088c.2.2.1
                    have p2088_3 := h2088c.2.2.2
                    rcases p2088_3 (m.d 0 1) (by simp) with h2090 | h2090
                    · rcases p2088_3 (m.d 1 2) (by simp) with h2091 | h2091
                      · linarith only [h2091, hlam, p2088_0]
                      · rcases p2088_3 (m.d 1 3) (by simp) with h2093 | h2093
                        · linarith only [h1, h2093, hlam]
                        · linarith only [h10, h2093, hlam]
                    · linarith only [h2090, hlam, p2088_0]
                  · have p2088_0 := h2088c.1
                    have p2088_1 := h2088c.2.1
                    have p2088_2 := h2088c.2.2.1
                    have p2088_3 := h2088c.2.2.2
                    rcases p2088_3 (m.d 0 1) (by simp) with h2097 | h2097
                    · rcases p2088_3 (m.d 1 2) (by simp) with h2098 | h2098
                      · linarith only [h0, h2098, hlam]
                      · rcases p2088_3 (m.d 1 3) (by simp) with h2100 | h2100
                        · linarith only [h2100, hlam, p2088_0]
                        · rcases p2088_3 (m.d 1 4) (by simp) with h2102 | h2102
                          · linarith only [h2, h2102, hlam]
                          · rcases p2088_3 (m.d 1 5) (by simp) with h2104 | h2104
                            · linarith only [h2104, h3, hlam]
                            · rcases h3bigk with h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c | h2106c
                              · have p2106_0 := h2106c.1
                                have p2106_1 := h2106c.2.1
                                have p2106_2 := h2106c.2.2.1
                                have p2106_3 := h2106c.2.2.2
                                linarith only [hlam, p2106_0]
                              · have p2106_0 := h2106c.1
                                have p2106_1 := h2106c.2.1
                                have p2106_2 := h2106c.2.2.1
                                have p2106_3 := h2106c.2.2.2
                                rcases p2106_3 (m.d 0 3) (by simp) with h2108 | h2108
                                · rcases p2106_3 (m.d 1 3) (by simp) with h2109 | h2109
                                  · linarith only [h1, h2109, hlam]
                                  · rcases p2106_3 (m.d 2 3) (by simp) with h2111 | h2111
                                    · linarith only [h2111, h4, hlam]
                                    · linarith only [h10, h2111, hlam]
                                · linarith only [h1, h2108, hlam]
                              · have p2106_0 := h2106c.1
                                have p2106_1 := h2106c.2.1
                                have p2106_2 := h2106c.2.2.1
                                have p2106_3 := h2106c.2.2.2
                                linarith only [h0, h10, h1951, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2106_1]
                              · have p2106_0 := h2106c.1
                                have p2106_1 := h2106c.2.1
                                have p2106_2 := h2106c.2.2.1
                                have p2106_3 := h2106c.2.2.2
                                linarith only [h1951, h1952, h2082, h2084, h7, h9, hlam, p2106_2]
                              · have p2106_0 := h2106c.1
                                have p2106_1 := h2106c.2.1
                                have p2106_2 := h2106c.2.2.1
                                have p2106_3 := h2106c.2.2.2
                                rcases p2106_3 (m.d 0 3) (by simp) with h2117 | h2117
                                · rcases p2106_3 (m.d 1 3) (by simp) with h2118 | h2118
                                  · linarith only [h1, h2118, hlam]
                                  · linarith only [h2079, h2118, hlam]
                                · linarith only [h2117, hlam, p2106_0]
                              · have p2106_0 := h2106c.1
                                have p2106_1 := h2106c.2.1
                                have p2106_2 := h2106c.2.2.1
                                have p2106_3 := h2106c.2.2.2
                                linarith only [h1, hlam, p2106_0]
                              · have p2106_0 := h2106c.1
                                have p2106_1 := h2106c.2.1
                                have p2106_2 := h2106c.2.2.1
                                have p2106_3 := h2106c.2.2.2
                                linarith only [hlam, p2106_0]
                              · have p2106_0 := h2106c.1
                                have p2106_1 := h2106c.2.1
                                have p2106_2 := h2106c.2.2.1
                                have p2106_3 := h2106c.2.2.2
                                linarith only [h10, hlam, p2106_1]
                              · have p2106_0 := h2106c.1
                                have p2106_1 := h2106c.2.1
                                have p2106_2 := h2106c.2.2.1
                                have p2106_3 := h2106c.2.2.2
                                linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2088_1, p2106_1]
                              · have p2106_0 := h2106c.1
                                have p2106_1 := h2106c.2.1
                                have p2106_2 := h2106c.2.2.1
                                have p2106_3 := h2106c.2.2.2
                                linarith only [hc01, hc35, hlam, hphi, ht0b, ht5b, p2088_1, p2106_1]
                              · have p2106_0 := h2106c.1
                                have p2106_1 := h2106c.2.1
                                have p2106_2 := h2106c.2.2.1
                                have p2106_3 := h2106c.2.2.2
                                linarith only [h4, hlam, p2106_0]
                              · have p2106_0 := h2106c.1
                                have p2106_1 := h2106c.2.1
                                have p2106_2 := h2106c.2.2.1
                                have p2106_3 := h2106c.2.2.2
                                linarith only [h0, h4, hlam, p2088_2, p2106_1]
                              · have p2106_0 := h2106c.1
                                have p2106_1 := h2106c.2.1
                                have p2106_2 := h2106c.2.2.1
                                have p2106_3 := h2106c.2.2.2
                                linarith only [hlam, p2106_0]
                              · have p2106_0 := h2106c.1
                                have p2106_1 := h2106c.2.1
                                have p2106_2 := h2106c.2.2.1
                                have p2106_3 := h2106c.2.2.2
                                rcases p2106_3 (m.d 0 3) (by simp) with h2130 | h2130
                                · rcases p2106_3 (m.d 1 3) (by simp) with h2131 | h2131
                                  · linarith only [h10, h2131, hlam]
                                  · linarith only [h2078, h2131, hlam]
                                · linarith only [h2130, h7, hlam]
                              · have p2106_0 := h2106c.1
                                have p2106_1 := h2106c.2.1
                                have p2106_2 := h2106c.2.2.1
                                have p2106_3 := h2106c.2.2.2
                                rcases p2106_3 (m.d 0 3) (by simp) with h2135 | h2135
                                · rcases p2106_3 (m.d 1 3) (by simp) with h2136 | h2136
                                  · linarith only [h10, h2136, hlam]
                                  · linarith only [h2079, h2136, hlam]
                                · linarith only [h2135, h8, hlam]
                              · have p2106_0 := h2106c.1
                                have p2106_1 := h2106c.2.1
                                have p2106_2 := h2106c.2.2.1
                                have p2106_3 := h2106c.2.2.2
                                linarith only [h7, hlam, p2106_0]
                              · have p2106_0 := h2106c.1
                                have p2106_1 := h2106c.2.1
                                have p2106_2 := h2106c.2.2.1
                                have p2106_3 := h2106c.2.2.2
                                linarith only [h2078, hlam, p2106_0]
                              · have p2106_0 := h2106c.1
                                have p2106_1 := h2106c.2.1
                                have p2106_2 := h2106c.2.2.1
                                have p2106_3 := h2106c.2.2.2
                                linarith only [h2082, hlam, p2106_0]
                              · have p2106_0 := h2106c.1
                                have p2106_1 := h2106c.2.1
                                have p2106_2 := h2106c.2.2.1
                                have p2106_3 := h2106c.2.2.2
                                linarith only [hlam, p2106_0]
                              · have p2106_0 := h2106c.1
                                have p2106_1 := h2106c.2.1
                                have p2106_2 := h2106c.2.2.1
                                have p2106_3 := h2106c.2.2.2
                                linarith only [h2086, hlam, p2106_1]
                              · have p2106_0 := h2106c.1
                                have p2106_1 := h2106c.2.1
                                have p2106_2 := h2106c.2.2.1
                                have p2106_3 := h2106c.2.2.2
                                linarith only [h8, hlam, p2106_0]
                              · have p2106_0 := h2106c.1
                                have p2106_1 := h2106c.2.1
                                have p2106_2 := h2106c.2.2.1
                                have p2106_3 := h2106c.2.2.2
                                linarith only [h2079, hlam, p2106_0]
                              · have p2106_0 := h2106c.1
                                have p2106_1 := h2106c.2.1
                                have p2106_2 := h2106c.2.2.1
                                have p2106_3 := h2106c.2.2.2
                                linarith only [h2083, hlam, p2106_0]
                              · have p2106_0 := h2106c.1
                                have p2106_1 := h2106c.2.1
                                have p2106_2 := h2106c.2.2.1
                                have p2106_3 := h2106c.2.2.2
                                linarith only [h2079, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2088_1, p2106_1]
                              · have p2106_0 := h2106c.1
                                have p2106_1 := h2106c.2.1
                                have p2106_2 := h2106c.2.2.1
                                have p2106_3 := h2106c.2.2.2
                                linarith only [hlam, p2106_0]
                    · linarith only [h2097, hlam, p2088_0]
                  · have p2088_0 := h2088c.1
                    have p2088_1 := h2088c.2.1
                    have p2088_2 := h2088c.2.2.1
                    have p2088_3 := h2088c.2.2.2
                    rcases p2088_3 (m.d 0 1) (by simp) with h2151 | h2151
                    · rcases p2088_3 (m.d 1 2) (by simp) with h2152 | h2152
                      · linarith only [h0, h2152, hlam]
                      · linarith only [h1951, h2152, hlam]
                    · linarith only [h2151, hlam, p2088_0]
                  · have p2088_0 := h2088c.1
                    have p2088_1 := h2088c.2.1
                    have p2088_2 := h2088c.2.2.1
                    have p2088_3 := h2088c.2.2.2
                    rcases p2088_3 (m.d 0 1) (by simp) with h2156 | h2156
                    · rcases p2088_3 (m.d 1 2) (by simp) with h2157 | h2157
                      · linarith only [h0, h2157, hlam]
                      · rcases p2088_3 (m.d 1 3) (by simp) with h2159 | h2159
                        · linarith only [h1, h2159, hlam]
                        · linarith only [h2079, h2159, hlam]
                    · linarith only [h2156, hlam, p2088_0]
                  · have p2088_0 := h2088c.1
                    have p2088_1 := h2088c.2.1
                    have p2088_2 := h2088c.2.2.1
                    have p2088_3 := h2088c.2.2.2
                    linarith only [h0, hlam, p2088_0]
                  · have p2088_0 := h2088c.1
                    have p2088_1 := h2088c.2.1
                    have p2088_2 := h2088c.2.2.1
                    have p2088_3 := h2088c.2.2.2
                    linarith only [hlam, p2088_0]
                  · have p2088_0 := h2088c.1
                    have p2088_1 := h2088c.2.1
                    have p2088_2 := h2088c.2.2.1
                    have p2088_3 := h2088c.2.2.2
                    linarith only [h10, hlam, p2088_0]
                  · have p2088_0 := h2088c.1
                    have p2088_1 := h2088c.2.1
                    have p2088_2 := h2088c.2.2.1
                    have p2088_3 := h2088c.2.2.2
                    linarith only [h0, h1952, h2084, h4, h7, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2088_1]
                  · have p2088_0 := h2088c.1
                    have p2088_1 := h2088c.2.1
                    have p2088_2 := h2088c.2.2.1
                    have p2088_3 := h2088c.2.2.2
                    linarith only [h1952, hlam, p2088_0]
                  · have p2088_0 := h2088c.1
                    have p2088_1 := h2088c.2.1
                    have p2088_2 := h2088c.2.2.1
                    have p2088_3 := h2088c.2.2.2
                    linarith only [h1, hlam, p2088_0]
                  · have p2088_0 := h2088c.1
                    have p2088_1 := h2088c.2.1
                    have p2088_2 := h2088c.2.2.1
                    have p2088_3 := h2088c.2.2.2
                    linarith only [h0, h10, h1951, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2088_1]
                  · have p2088_0 := h2088c.1
                    have p2088_1 := h2088c.2.1
                    have p2088_2 := h2088c.2.2.1
                    have p2088_3 := h2088c.2.2.2
                    linarith only [hlam, p2088_0]
                  · have p2088_0 := h2088c.1
                    have p2088_1 := h2088c.2.1
                    have p2088_2 := h2088c.2.2.1
                    have p2088_3 := h2088c.2.2.2
                    rcases p2088_3 (m.d 0 1) (by simp) with h2171 | h2171
                    · rcases p2088_3 (m.d 1 2) (by simp) with h2172 | h2172
                      · linarith only [h10, h2172, hlam]
                      · linarith only [h1951, h2172, hlam]
                    · linarith only [h2, h2171, hlam]
                  · have p2088_0 := h2088c.1
                    have p2088_1 := h2088c.2.1
                    have p2088_2 := h2088c.2.2.1
                    have p2088_3 := h2088c.2.2.2
                    linarith only [h0, h10, h1951, h1952, h2082, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2088_1]
                  · have p2088_0 := h2088c.1
                    have p2088_1 := h2088c.2.1
                    have p2088_2 := h2088c.2.2.1
                    have p2088_3 := h2088c.2.2.2
                    linarith only [h2, hlam, p2088_0]
                  · have p2088_0 := h2088c.1
                    have p2088_1 := h2088c.2.1
                    have p2088_2 := h2088c.2.2.1
                    have p2088_3 := h2088c.2.2.2
                    linarith only [h1951, hlam, p2088_1]
                  · have p2088_0 := h2088c.1
                    have p2088_1 := h2088c.2.1
                    have p2088_2 := h2088c.2.2.1
                    have p2088_3 := h2088c.2.2.2
                    linarith only [h2078, hlam, p2088_0]
                  · have p2088_0 := h2088c.1
                    have p2088_1 := h2088c.2.1
                    have p2088_2 := h2088c.2.2.1
                    have p2088_3 := h2088c.2.2.2
                    linarith only [hlam, p2088_0]
                  · have p2088_0 := h2088c.1
                    have p2088_1 := h2088c.2.1
                    have p2088_2 := h2088c.2.2.1
                    have p2088_3 := h2088c.2.2.2
                    linarith only [h2080, hlam, p2088_1]
                  · have p2088_0 := h2088c.1
                    have p2088_1 := h2088c.2.1
                    have p2088_2 := h2088c.2.2.1
                    have p2088_3 := h2088c.2.2.2
                    linarith only [h3, hlam, p2088_0]
                  · have p2088_0 := h2088c.1
                    have p2088_1 := h2088c.2.1
                    have p2088_2 := h2088c.2.2.1
                    have p2088_3 := h2088c.2.2.2
                    linarith only [h1951, h2082, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2088_1]
                  · have p2088_0 := h2088c.1
                    have p2088_1 := h2088c.2.1
                    have p2088_2 := h2088c.2.2.1
                    have p2088_3 := h2088c.2.2.2
                    linarith only [h2079, hlam, p2088_0]
                  · have p2088_0 := h2088c.1
                    have p2088_1 := h2088c.2.1
                    have p2088_2 := h2088c.2.2.1
                    have p2088_3 := h2088c.2.2.2
                    rcases p2088_3 (m.d 0 1) (by simp) with h2185 | h2185
                    · rcases p2088_3 (m.d 1 2) (by simp) with h2186 | h2186
                      · linarith only [h1952, h2186, hlam]
                      · linarith only [h1951, h2186, hlam]
                    · linarith only [h2, h2185, hlam]
                  · have p2088_0 := h2088c.1
                    have p2088_1 := h2088c.2.1
                    have p2088_2 := h2088c.2.2.1
                    have p2088_3 := h2088c.2.2.2
                    linarith only [hlam, p2088_0]
            · linarith only [h10, h2079, h2083, hlam]
          · linarith only [h0, h10, h1951, h2082, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h2193 | h2193
        · linarith only [h1951, h1952, h2193, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h2195 | h2195
          · rcases m.htr 2 3 5 (by decide) (by decide) with h2196 | h2196
            · linarith only [h0, h10, h1951, h2079, h2195, h2196, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h10, h1951, h2195, h2196, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h10, h1951, h2195, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
    · linarith only [h10, h1951, h2078, hlam]

set_option maxHeartbeats 7932000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s9_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1951 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h2201 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 3 4 (by decide) (by decide) with h2202 | h2202
  · rcases m.htr 1 3 5 (by decide) (by decide) with h2203 | h2203
    · rcases m.htr 1 4 5 (by decide) (by decide) with h2204 | h2204
      · rcases m.htr 2 3 4 (by decide) (by decide) with h2205 | h2205
        · rcases m.htr 2 3 5 (by decide) (by decide) with h2206 | h2206
          · rcases m.htr 2 4 5 (by decide) (by decide) with h2207 | h2207
            · rcases m.htr 3 4 5 (by decide) (by decide) with h2208 | h2208
              · rcases h1bigk with h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c
                · have p2209_0 := h2209c.1
                  have p2209_1 := h2209c.2.1
                  have p2209_2 := h2209c.2.2.1
                  have p2209_3 := h2209c.2.2.2
                  linarith only [hlam, p2209_0]
                · have p2209_0 := h2209c.1
                  have p2209_1 := h2209c.2.1
                  have p2209_2 := h2209c.2.2.1
                  have p2209_3 := h2209c.2.2.2
                  rcases p2209_3 (m.d 0 1) (by simp) with h2211 | h2211
                  · rcases p2209_3 (m.d 1 2) (by simp) with h2212 | h2212
                    · linarith only [h2212, hlam, p2209_0]
                    · rcases p2209_3 (m.d 1 3) (by simp) with h2214 | h2214
                      · linarith only [h1, h2214, hlam]
                      · linarith only [h10, h2214, hlam]
                  · linarith only [h2211, hlam, p2209_0]
                · have p2209_0 := h2209c.1
                  have p2209_1 := h2209c.2.1
                  have p2209_2 := h2209c.2.2.1
                  have p2209_3 := h2209c.2.2.2
                  linarith only [h2202, h2208, hc01, hc45, hlam, hphi, ht0b, ht5b, p2209_1]
                · have p2209_0 := h2209c.1
                  have p2209_1 := h2209c.2.1
                  have p2209_2 := h2209c.2.2.1
                  have p2209_3 := h2209c.2.2.2
                  rcases p2209_3 (m.d 0 1) (by simp) with h2219 | h2219
                  · rcases p2209_3 (m.d 1 2) (by simp) with h2220 | h2220
                    · linarith only [h0, h2220, hlam]
                    · rcases p2209_3 (m.d 1 3) (by simp) with h2222 | h2222
                      · linarith only [h1, h2222, hlam]
                      · linarith only [h2202, h2222, hlam]
                  · linarith only [h2219, hlam, p2209_0]
                · have p2209_0 := h2209c.1
                  have p2209_1 := h2209c.2.1
                  have p2209_2 := h2209c.2.2.1
                  have p2209_3 := h2209c.2.2.2
                  rcases p2209_3 (m.d 0 1) (by simp) with h2226 | h2226
                  · rcases p2209_3 (m.d 1 2) (by simp) with h2227 | h2227
                    · linarith only [h0, h2227, hlam]
                    · linarith only [h2201, h2227, hlam]
                  · linarith only [h2226, hlam, p2209_0]
                · have p2209_0 := h2209c.1
                  have p2209_1 := h2209c.2.1
                  have p2209_2 := h2209c.2.2.1
                  have p2209_3 := h2209c.2.2.2
                  linarith only [h0, hlam, p2209_0]
                · have p2209_0 := h2209c.1
                  have p2209_1 := h2209c.2.1
                  have p2209_2 := h2209c.2.2.1
                  have p2209_3 := h2209c.2.2.2
                  linarith only [hlam, p2209_0]
                · have p2209_0 := h2209c.1
                  have p2209_1 := h2209c.2.1
                  have p2209_2 := h2209c.2.2.1
                  have p2209_3 := h2209c.2.2.2
                  linarith only [h10, hlam, p2209_0]
                · have p2209_0 := h2209c.1
                  have p2209_1 := h2209c.2.1
                  have p2209_2 := h2209c.2.2.1
                  have p2209_3 := h2209c.2.2.2
                  linarith only [h1951, hlam, p2209_0]
                · have p2209_0 := h2209c.1
                  have p2209_1 := h2209c.2.1
                  have p2209_2 := h2209c.2.2.1
                  have p2209_3 := h2209c.2.2.2
                  linarith only [h0, h1951, h5, hc01, hc15, hlam, hphi, ht0b, ht5b, p2209_1]
                · have p2209_0 := h2209c.1
                  have p2209_1 := h2209c.2.1
                  have p2209_2 := h2209c.2.2.1
                  have p2209_3 := h2209c.2.2.2
                  linarith only [h1, hlam, p2209_0]
                · have p2209_0 := h2209c.1
                  have p2209_1 := h2209c.2.1
                  have p2209_2 := h2209c.2.2.1
                  have p2209_3 := h2209c.2.2.2
                  linarith only [h0, h10, h2201, h2206, h2208, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p2209_1]
                · have p2209_0 := h2209c.1
                  have p2209_1 := h2209c.2.1
                  have p2209_2 := h2209c.2.2.1
                  have p2209_3 := h2209c.2.2.2
                  linarith only [hlam, p2209_0]
                · have p2209_0 := h2209c.1
                  have p2209_1 := h2209c.2.1
                  have p2209_2 := h2209c.2.2.1
                  have p2209_3 := h2209c.2.2.2
                  linarith only [h0, h10, h1951, h2201, h2206, h2208, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p2209_1]
                · have p2209_0 := h2209c.1
                  have p2209_1 := h2209c.2.1
                  have p2209_2 := h2209c.2.2.1
                  have p2209_3 := h2209c.2.2.2
                  rcases p2209_3 (m.d 0 1) (by simp) with h2240 | h2240
                  · rcases p2209_3 (m.d 1 2) (by simp) with h2241 | h2241
                    · linarith only [h10, h2241, hlam]
                    · linarith only [h2201, h2241, hlam]
                  · linarith only [h2240, h3, hlam]
                · have p2209_0 := h2209c.1
                  have p2209_1 := h2209c.2.1
                  have p2209_2 := h2209c.2.2.1
                  have p2209_3 := h2209c.2.2.2
                  linarith only [h2, hlam, p2209_0]
                · have p2209_0 := h2209c.1
                  have p2209_1 := h2209c.2.1
                  have p2209_2 := h2209c.2.2.1
                  have p2209_3 := h2209c.2.2.2
                  linarith only [h2, h2201, h2206, h2208, hc01, hc45, hlam, hphi, ht0b, ht5b, p2209_1]
                · have p2209_0 := h2209c.1
                  have p2209_1 := h2209c.2.1
                  have p2209_2 := h2209c.2.2.1
                  have p2209_3 := h2209c.2.2.2
                  linarith only [h2202, hlam, p2209_0]
                · have p2209_0 := h2209c.1
                  have p2209_1 := h2209c.2.1
                  have p2209_2 := h2209c.2.2.1
                  have p2209_3 := h2209c.2.2.2
                  linarith only [hlam, p2209_0]
                · have p2209_0 := h2209c.1
                  have p2209_1 := h2209c.2.1
                  have p2209_2 := h2209c.2.2.1
                  have p2209_3 := h2209c.2.2.2
                  rcases p2209_3 (m.d 0 1) (by simp) with h2249 | h2249
                  · rcases p2209_3 (m.d 1 2) (by simp) with h2250 | h2250
                    · linarith only [h1951, h2250, hlam]
                    · linarith only [h2201, h2250, hlam]
                  · linarith only [h2249, h3, hlam]
                · have p2209_0 := h2209c.1
                  have p2209_1 := h2209c.2.1
                  have p2209_2 := h2209c.2.2.1
                  have p2209_3 := h2209c.2.2.2
                  linarith only [h3, hlam, p2209_0]
                · have p2209_0 := h2209c.1
                  have p2209_1 := h2209c.2.1
                  have p2209_2 := h2209c.2.2.1
                  have p2209_3 := h2209c.2.2.2
                  linarith only [h2201, hlam, p2209_1]
                · have p2209_0 := h2209c.1
                  have p2209_1 := h2209c.2.1
                  have p2209_2 := h2209c.2.2.1
                  have p2209_3 := h2209c.2.2.2
                  linarith only [h2203, hlam, p2209_0]
                · have p2209_0 := h2209c.1
                  have p2209_1 := h2209c.2.1
                  have p2209_2 := h2209c.2.2.1
                  have p2209_3 := h2209c.2.2.2
                  linarith only [h2204, hlam, p2209_0]
                · have p2209_0 := h2209c.1
                  have p2209_1 := h2209c.2.1
                  have p2209_2 := h2209c.2.2.1
                  have p2209_3 := h2209c.2.2.2
                  linarith only [hlam, p2209_0]
              · linarith only [h0, h1951, h2201, h2205, h2207, h2208, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h1951, h2201, h2207, h4, h7, h9, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · linarith only [h1951, h2201, h2205, h2206, h8, hc03, hc25, hlam, hphi, ht0b, ht5b]
        · linarith only [h0, h10, h2201, h2205, h4, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
      · linarith only [h1951, h2201, h2204, hlam]
    · linarith only [h1951, h2201, h2202, h2203, hlam]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h2265 | h2265
    · rcases m.htr 1 4 5 (by decide) (by decide) with h2266 | h2266
      · rcases m.htr 2 3 4 (by decide) (by decide) with h2267 | h2267
        · linarith only [h0, h2202, h2265, h2267, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
        · linarith only [h0, h10, h2201, h2267, h4, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
      · linarith only [h10, h2201, h2202, h2266, hlam]
    · linarith only [h10, h2201, h2265, hlam]

end R2N4
