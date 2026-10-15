import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_38S7

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7284000 in
set_option maxHeartbeats 7284000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1631 | h1631
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1632 | h1632
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1633 | h1633
      · linarith only [h0, h1, h1633, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1635 | h1635
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1636 | h1636
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1637 | h1637
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1638 | h1638
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1639 | h1639
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1640 | h1640
                  · linarith only [h0, h1, h1633, h1640, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1642 | h1642
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1643 | h1643
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1644 | h1644
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1645 | h1645
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1646 | h1646
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1647 | h1647
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1648 | h1648
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1649 | h1649
                                  · linarith only [h0, h1, h1640, h1642, h1649, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                  · linarith only [h1631, h1646, h1649, hc24, hlam, hphi, u4elo0]
                                · linarith only [h0, h1, h1640, h1648, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h0, h1, h1640, h1647, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h1639, h1646, hc14, hlam, hphi, u4elo0]
                          · linarith only [h0, h1, h1638, h1642, h1645, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h0, h1, h1642, h1644, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h1, h1636, h1642, h1643, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h1, h1635, h1640, h1642, hc12, hc23, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1659 | h1659
                  · linarith only [h0, h1, h1633, h1659, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1661 | h1661
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1662 | h1662
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1663 | h1663
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1664 | h1664
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1665 | h1665
                            · linarith only [h1631, h1639, h1665, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1667 | h1667
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1668 | h1668
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1669 | h1669
                                  · linarith only [h1631, h1639, h1669, hc14, hlam, hphi, u4elo2]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1671 | h1671
                                    · linarith only [h1631, h1639, h1661, h1667, h1671, hlam]
                                    · rcases h0bigk with h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c
                                      · have p1673_0 := h1673c.1
                                        have p1673_1 := h1673c.2.1
                                        have p1673_2 := h1673c.2.2.1
                                        have p1673_3 := h1673c.2.2.2
                                        linarith only [hlam, p1673_0]
                                      · have p1673_0 := h1673c.1
                                        have p1673_1 := h1673c.2.1
                                        have p1673_2 := h1673c.2.2.1
                                        have p1673_3 := h1673c.2.2.2
                                        linarith only [h1, h1659, hc02, hc23, hlam, hphi, p1673_1]
                                      · have p1673_0 := h1673c.1
                                        have p1673_1 := h1673c.2.1
                                        have p1673_2 := h1673c.2.2.1
                                        have p1673_3 := h1673c.2.2.2
                                        linarith only [h1, hlam, p1673_0]
                                      · have p1673_0 := h1673c.1
                                        have p1673_1 := h1673c.2.1
                                        have p1673_2 := h1673c.2.2.1
                                        have p1673_3 := h1673c.2.2.2
                                        linarith only [h1, h1659, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1673_1]
                                      · have p1673_0 := h1673c.1
                                        have p1673_1 := h1673c.2.1
                                        have p1673_2 := h1673c.2.2.1
                                        have p1673_3 := h1673c.2.2.2
                                        linarith only [h1, h1659, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1673_1]
                                      · have p1673_0 := h1673c.1
                                        have p1673_1 := h1673c.2.1
                                        have p1673_2 := h1673c.2.2.1
                                        have p1673_3 := h1673c.2.2.2
                                        linarith only [h0, hlam, p1673_0]
                                      · have p1673_0 := h1673c.1
                                        have p1673_1 := h1673c.2.1
                                        have p1673_2 := h1673c.2.2.1
                                        have p1673_3 := h1673c.2.2.2
                                        linarith only [hlam, p1673_0]
                                      · have p1673_0 := h1673c.1
                                        have p1673_1 := h1673c.2.1
                                        have p1673_2 := h1673c.2.2.1
                                        have p1673_3 := h1673c.2.2.2
                                        linarith only [h1633, hlam, p1673_0]
                                      · have p1673_0 := h1673c.1
                                        have p1673_1 := h1673c.2.1
                                        have p1673_2 := h1673c.2.2.1
                                        have p1673_3 := h1673c.2.2.2
                                        linarith only [h0, h1, h1631, h1659, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1673_1]
                                      · have p1673_0 := h1673c.1
                                        have p1673_1 := h1673c.2.1
                                        have p1673_2 := h1673c.2.2.1
                                        have p1673_3 := h1673c.2.2.2
                                        linarith only [h0, h1, h1632, h1659, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1673_1]
                                      · have p1673_0 := h1673c.1
                                        have p1673_1 := h1673c.2.1
                                        have p1673_2 := h1673c.2.2.1
                                        have p1673_3 := h1673c.2.2.2
                                        linarith only [h0, h1662, h1667, h1669, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1673_1]
                                      · have p1673_0 := h1673c.1
                                        have p1673_1 := h1673c.2.1
                                        have p1673_2 := h1673c.2.2.1
                                        have p1673_3 := h1673c.2.2.2
                                        linarith only [h1, h1659, hc02, hc23, hlam, hphi, p1673_1]
                                      · have p1673_0 := h1673c.1
                                        have p1673_1 := h1673c.2.1
                                        have p1673_2 := h1673c.2.2.1
                                        have p1673_3 := h1673c.2.2.2
                                        linarith only [hlam, p1673_0]
                                      · have p1673_0 := h1673c.1
                                        have p1673_1 := h1673c.2.1
                                        have p1673_2 := h1673c.2.2.1
                                        have p1673_3 := h1673c.2.2.2
                                        rcases p1673_3 (m.d 0 1) (by simp) with h1687 | h1687
                                        · linarith only [h1, h1687, hlam]
                                        · linarith only [h1631, h1687, hlam]
                                      · have p1673_0 := h1673c.1
                                        have p1673_1 := h1673c.2.1
                                        have p1673_2 := h1673c.2.2.1
                                        have p1673_3 := h1673c.2.2.2
                                        rcases p1673_3 (m.d 0 1) (by simp) with h1690 | h1690
                                        · linarith only [h1, h1690, hlam]
                                        · linarith only [h1632, h1690, hlam]
                                      · have p1673_0 := h1673c.1
                                        have p1673_1 := h1673c.2.1
                                        have p1673_2 := h1673c.2.2.1
                                        have p1673_3 := h1673c.2.2.2
                                        linarith only [h1631, hlam, p1673_0]
                                      · have p1673_0 := h1673c.1
                                        have p1673_1 := h1673c.2.1
                                        have p1673_2 := h1673c.2.2.1
                                        have p1673_3 := h1673c.2.2.2
                                        linarith only [h1635, hlam, p1673_0]
                                      · have p1673_0 := h1673c.1
                                        have p1673_1 := h1673c.2.1
                                        have p1673_2 := h1673c.2.2.1
                                        have p1673_3 := h1673c.2.2.2
                                        linarith only [h1637, hlam, p1673_0]
                                      · have p1673_0 := h1673c.1
                                        have p1673_1 := h1673c.2.1
                                        have p1673_2 := h1673c.2.2.1
                                        have p1673_3 := h1673c.2.2.2
                                        linarith only [hlam, p1673_0]
                                      · have p1673_0 := h1673c.1
                                        have p1673_1 := h1673c.2.1
                                        have p1673_2 := h1673c.2.2.1
                                        have p1673_3 := h1673c.2.2.2
                                        linarith only [h1639, hlam, p1673_0]
                                      · have p1673_0 := h1673c.1
                                        have p1673_1 := h1673c.2.1
                                        have p1673_2 := h1673c.2.2.1
                                        have p1673_3 := h1673c.2.2.2
                                        linarith only [h1632, hlam, p1673_0]
                                      · have p1673_0 := h1673c.1
                                        have p1673_1 := h1673c.2.1
                                        have p1673_2 := h1673c.2.2.1
                                        have p1673_3 := h1673c.2.2.2
                                        linarith only [h1636, hlam, p1673_1]
                                      · have p1673_0 := h1673c.1
                                        have p1673_1 := h1673c.2.1
                                        have p1673_2 := h1673c.2.2.1
                                        have p1673_3 := h1673c.2.2.2
                                        linarith only [h1638, hlam, p1673_0]
                                      · have p1673_0 := h1673c.1
                                        have p1673_1 := h1673c.2.1
                                        have p1673_2 := h1673c.2.2.1
                                        have p1673_3 := h1673c.2.2.2
                                        linarith only [h1, h1631, h1632, h1659, h1661, h1667, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1673_1]
                                      · have p1673_0 := h1673c.1
                                        have p1673_1 := h1673c.2.1
                                        have p1673_2 := h1673c.2.2.1
                                        have p1673_3 := h1673c.2.2.2
                                        linarith only [hlam, p1673_0]
                                · linarith only [h0, h1, h1659, h1668, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h0, h1, h1659, h1661, h1667, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1, h1661, h1664, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h1, h1661, h1663, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h1, h1636, h1661, h1662, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h1, h1635, h1659, h1661, hc12, hc23, hlam, hphi]
              · linarith only [h1, h1632, h1638, hlam]
            · linarith only [h0, h1, h1637, hc12, hlam, hphi, ht23, ht34, u4elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1711 | h1711
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1712 | h1712
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1713 | h1713
                · linarith only [h1635, h1636, h1713, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1715 | h1715
                  · linarith only [h0, h1, h1633, h1715, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1717 | h1717
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1718 | h1718
                      · linarith only [h0, h1636, h1718, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1720 | h1720
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1721 | h1721
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1722 | h1722
                            · linarith only [h1631, h1713, h1722, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1724 | h1724
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1725 | h1725
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1726 | h1726
                                  · linarith only [h0, h1631, h1636, h1713, h1717, h1726, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · linarith only [h1635, h1636, h1724, h1726, hc34, hlam, hphi, u4elo4]
                                · linarith only [h1, h1632, h1715, h1721, h1725, hlam]
                              · linarith only [h1, h1632, h1715, h1721, h1724, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                          · linarith only [h1, h1632, h1717, h1718, h1721, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h1, h1632, h1717, h1718, h1720, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h1635, h1636, h1713, h1717, hc12, hlam, hphi, ht23, ht34, u4elo4]
              · linarith only [h1, h1632, h1712, hlam]
            · linarith only [h1, h1631, h1711, hc14, hlam, hphi, u4elo3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1736 | h1736
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1737 | h1737
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1738 | h1738
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1739 | h1739
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1740 | h1740
                  · linarith only [h0, h1635, h1740, hc23, hlam, hphi, ht34, u4elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1742 | h1742
                    · linarith only [h0, h1635, h1742, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1744 | h1744
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1745 | h1745
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1746 | h1746
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1747 | h1747
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1748 | h1748
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1749 | h1749
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1750 | h1750
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1751 | h1751
                                    · rcases h0bigk with h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c | h1752c
                                      · have p1752_0 := h1752c.1
                                        have p1752_1 := h1752c.2.1
                                        have p1752_2 := h1752c.2.2.1
                                        have p1752_3 := h1752c.2.2.2
                                        linarith only [hlam, p1752_0]
                                      · have p1752_0 := h1752c.1
                                        have p1752_1 := h1752c.2.1
                                        have p1752_2 := h1752c.2.2.1
                                        have p1752_3 := h1752c.2.2.2
                                        linarith only [h0, h1744, h1749, h1751, hc01, hc45, hlam, hphi, ht0b, ht5b, p1752_1]
                                      · have p1752_0 := h1752c.1
                                        have p1752_1 := h1752c.2.1
                                        have p1752_2 := h1752c.2.2.1
                                        have p1752_3 := h1752c.2.2.2
                                        linarith only [h1, hlam, p1752_0]
                                      · have p1752_0 := h1752c.1
                                        have p1752_1 := h1752c.2.1
                                        have p1752_2 := h1752c.2.2.1
                                        have p1752_3 := h1752c.2.2.2
                                        linarith only [h0, h1, h1635, h1740, h1744, h1749, h1751, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1752_1]
                                      · have p1752_0 := h1752c.1
                                        have p1752_1 := h1752c.2.1
                                        have p1752_2 := h1752c.2.2.1
                                        have p1752_3 := h1752c.2.2.2
                                        linarith only [h1, h1740, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1752_1]
                                      · have p1752_0 := h1752c.1
                                        have p1752_1 := h1752c.2.1
                                        have p1752_2 := h1752c.2.2.1
                                        have p1752_3 := h1752c.2.2.2
                                        linarith only [h0, hlam, p1752_0]
                                      · have p1752_0 := h1752c.1
                                        have p1752_1 := h1752c.2.1
                                        have p1752_2 := h1752c.2.2.1
                                        have p1752_3 := h1752c.2.2.2
                                        linarith only [hlam, p1752_0]
                                      · have p1752_0 := h1752c.1
                                        have p1752_1 := h1752c.2.1
                                        have p1752_2 := h1752c.2.2.1
                                        have p1752_3 := h1752c.2.2.2
                                        linarith only [h1633, hlam, p1752_0]
                                      · have p1752_0 := h1752c.1
                                        have p1752_1 := h1752c.2.1
                                        have p1752_2 := h1752c.2.2.1
                                        have p1752_3 := h1752c.2.2.2
                                        linarith only [h1635, hlam, p1752_1]
                                      · have p1752_0 := h1752c.1
                                        have p1752_1 := h1752c.2.1
                                        have p1752_2 := h1752c.2.2.1
                                        have p1752_3 := h1752c.2.2.2
                                        linarith only [h1632, h1635, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1752_1, u4elo2]
                                      · have p1752_0 := h1752c.1
                                        have p1752_1 := h1752c.2.1
                                        have p1752_2 := h1752c.2.2.1
                                        have p1752_3 := h1752c.2.2.2
                                        linarith only [h1, h1740, hc01, hc23, hlam, hphi, ht12, p1752_1]
                                      · have p1752_0 := h1752c.1
                                        have p1752_1 := h1752c.2.1
                                        have p1752_2 := h1752c.2.2.1
                                        have p1752_3 := h1752c.2.2.2
                                        linarith only [h1, h1740, hc02, hc23, hlam, hphi, p1752_1]
                                      · have p1752_0 := h1752c.1
                                        have p1752_1 := h1752c.2.1
                                        have p1752_2 := h1752c.2.2.1
                                        have p1752_3 := h1752c.2.2.2
                                        linarith only [hlam, p1752_0]
                                      · have p1752_0 := h1752c.1
                                        have p1752_1 := h1752c.2.1
                                        have p1752_2 := h1752c.2.2.1
                                        have p1752_3 := h1752c.2.2.2
                                        linarith only [h0, h1, h1635, h1740, h1744, h1749, h1751, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1752_1]
                                      · have p1752_0 := h1752c.1
                                        have p1752_1 := h1752c.2.1
                                        have p1752_2 := h1752c.2.2.1
                                        have p1752_3 := h1752c.2.2.2
                                        rcases p1752_3 (m.d 0 1) (by simp) with h1767 | h1767
                                        · linarith only [h1, h1767, hlam]
                                        · linarith only [h1632, h1767, hlam]
                                      · have p1752_0 := h1752c.1
                                        have p1752_1 := h1752c.2.1
                                        have p1752_2 := h1752c.2.2.1
                                        have p1752_3 := h1752c.2.2.2
                                        linarith only [h1631, hlam, p1752_0]
                                      · have p1752_0 := h1752c.1
                                        have p1752_1 := h1752c.2.1
                                        have p1752_2 := h1752c.2.2.1
                                        have p1752_3 := h1752c.2.2.2
                                        linarith only [h0, h1744, h1749, h1751, hc04, hc45, hlam, hphi, ht0b, ht5b, p1752_1]
                                      · have p1752_0 := h1752c.1
                                        have p1752_1 := h1752c.2.1
                                        have p1752_2 := h1752c.2.2.1
                                        have p1752_3 := h1752c.2.2.2
                                        linarith only [h1737, hlam, p1752_0]
                                      · have p1752_0 := h1752c.1
                                        have p1752_1 := h1752c.2.1
                                        have p1752_2 := h1752c.2.2.1
                                        have p1752_3 := h1752c.2.2.2
                                        linarith only [hlam, p1752_0]
                                      · have p1752_0 := h1752c.1
                                        have p1752_1 := h1752c.2.1
                                        have p1752_2 := h1752c.2.2.1
                                        have p1752_3 := h1752c.2.2.2
                                        linarith only [h1632, h1635, h1744, h1749, h1751, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1752_1, u4elo2]
                                      · have p1752_0 := h1752c.1
                                        have p1752_1 := h1752c.2.1
                                        have p1752_2 := h1752c.2.2.1
                                        have p1752_3 := h1752c.2.2.2
                                        linarith only [h1632, hlam, p1752_0]
                                      · have p1752_0 := h1752c.1
                                        have p1752_1 := h1752c.2.1
                                        have p1752_2 := h1752c.2.2.1
                                        have p1752_3 := h1752c.2.2.2
                                        linarith only [h1736, hlam, p1752_1]
                                      · have p1752_0 := h1752c.1
                                        have p1752_1 := h1752c.2.1
                                        have p1752_2 := h1752c.2.2.1
                                        have p1752_3 := h1752c.2.2.2
                                        linarith only [h1738, hlam, p1752_0]
                                      · have p1752_0 := h1752c.1
                                        have p1752_1 := h1752c.2.1
                                        have p1752_2 := h1752c.2.2.1
                                        have p1752_3 := h1752c.2.2.2
                                        linarith only [h1739, hlam, p1752_1]
                                      · have p1752_0 := h1752c.1
                                        have p1752_1 := h1752c.2.1
                                        have p1752_2 := h1752c.2.2.1
                                        have p1752_3 := h1752c.2.2.2
                                        linarith only [hlam, p1752_0]
                                    · linarith only [h1739, h1751, hc34, hlam, hphi, u4elo0]
                                  · linarith only [h1635, h1750, hc02, hlam, hphi, ht23, ht34, u4elo4]
                                · linarith only [h1, h1631, h1740, h1747, h1749, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h1, h1631, h1740, h1742, h1744, h1748, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h1, h1631, h1739, h1742, h1744, h1747, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h0, h1, h1744, h1746, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h1, h1745, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                      · linarith only [h1635, h1736, h1744, hc12, hlam, hphi, ht23, ht34, u4elo2]
                · linarith only [h1635, h1736, h1739, hlam]
              · linarith only [h0, h1, h1736, h1738, hlam]
            · linarith only [h0, h1, h1737, hc12, hlam, hphi, ht23, ht34, u4elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1791 | h1791
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1792 | h1792
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1793 | h1793
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1794 | h1794
                  · linarith only [h0, h1635, h1794, hc23, hlam, hphi, ht34, u4elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1796 | h1796
                    · linarith only [h0, h1635, h1796, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1798 | h1798
                      · linarith only [h0, h1736, h1798, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1800 | h1800
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1801 | h1801
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1802 | h1802
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1803 | h1803
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1804 | h1804
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1805 | h1805
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1806 | h1806
                                    · rcases h0bigk with h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c
                                      · have p1807_0 := h1807c.1
                                        have p1807_1 := h1807c.2.1
                                        have p1807_2 := h1807c.2.2.1
                                        have p1807_3 := h1807c.2.2.2
                                        linarith only [hlam, p1807_0]
                                      · have p1807_0 := h1807c.1
                                        have p1807_1 := h1807c.2.1
                                        have p1807_2 := h1807c.2.2.1
                                        have p1807_3 := h1807c.2.2.2
                                        linarith only [h0, h1, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1807_1]
                                      · have p1807_0 := h1807c.1
                                        have p1807_1 := h1807c.2.1
                                        have p1807_2 := h1807c.2.2.1
                                        have p1807_3 := h1807c.2.2.2
                                        linarith only [h1, hlam, p1807_0]
                                      · have p1807_0 := h1807c.1
                                        have p1807_1 := h1807c.2.1
                                        have p1807_2 := h1807c.2.2.1
                                        have p1807_3 := h1807c.2.2.2
                                        linarith only [h1, h1794, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1807_1]
                                      · have p1807_0 := h1807c.1
                                        have p1807_1 := h1807c.2.1
                                        have p1807_2 := h1807c.2.2.1
                                        have p1807_3 := h1807c.2.2.2
                                        linarith only [h0, h1, h1736, h1794, hc12, hc23, hlam, hphi, p1807_1]
                                      · have p1807_0 := h1807c.1
                                        have p1807_1 := h1807c.2.1
                                        have p1807_2 := h1807c.2.2.1
                                        have p1807_3 := h1807c.2.2.2
                                        linarith only [h0, hlam, p1807_0]
                                      · have p1807_0 := h1807c.1
                                        have p1807_1 := h1807c.2.1
                                        have p1807_2 := h1807c.2.2.1
                                        have p1807_3 := h1807c.2.2.2
                                        linarith only [hlam, p1807_0]
                                      · have p1807_0 := h1807c.1
                                        have p1807_1 := h1807c.2.1
                                        have p1807_2 := h1807c.2.2.1
                                        have p1807_3 := h1807c.2.2.2
                                        linarith only [h1633, hlam, p1807_0]
                                      · have p1807_0 := h1807c.1
                                        have p1807_1 := h1807c.2.1
                                        have p1807_2 := h1807c.2.2.1
                                        have p1807_3 := h1807c.2.2.2
                                        linarith only [h1635, hlam, p1807_1]
                                      · have p1807_0 := h1807c.1
                                        have p1807_1 := h1807c.2.1
                                        have p1807_2 := h1807c.2.2.1
                                        have p1807_3 := h1807c.2.2.2
                                        linarith only [h1736, hlam, p1807_0]
                                      · have p1807_0 := h1807c.1
                                        have p1807_1 := h1807c.2.1
                                        have p1807_2 := h1807c.2.2.1
                                        have p1807_3 := h1807c.2.2.2
                                        linarith only [h1631, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b, p1807_1]
                                      · have p1807_0 := h1807c.1
                                        have p1807_1 := h1807c.2.1
                                        have p1807_2 := h1807c.2.2.1
                                        have p1807_3 := h1807c.2.2.2
                                        linarith only [h0, h1, h1794, hc12, hc23, hlam, hphi, p1807_1]
                                      · have p1807_0 := h1807c.1
                                        have p1807_1 := h1807c.2.1
                                        have p1807_2 := h1807c.2.2.1
                                        have p1807_3 := h1807c.2.2.2
                                        linarith only [hlam, p1807_0]
                                      · have p1807_0 := h1807c.1
                                        have p1807_1 := h1807c.2.1
                                        have p1807_2 := h1807c.2.2.1
                                        have p1807_3 := h1807c.2.2.2
                                        linarith only [h1, h1631, h1794, h1800, h1806, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1807_1]
                                      · have p1807_0 := h1807c.1
                                        have p1807_1 := h1807c.2.1
                                        have p1807_2 := h1807c.2.2.1
                                        have p1807_3 := h1807c.2.2.2
                                        linarith only [h0, h1, h1736, h1794, hc12, hc23, hlam, hphi, p1807_1]
                                      · have p1807_0 := h1807c.1
                                        have p1807_1 := h1807c.2.1
                                        have p1807_2 := h1807c.2.2.1
                                        have p1807_3 := h1807c.2.2.2
                                        linarith only [h1631, hlam, p1807_0]
                                      · have p1807_0 := h1807c.1
                                        have p1807_1 := h1807c.2.1
                                        have p1807_2 := h1807c.2.2.1
                                        have p1807_3 := h1807c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht23, ht34, p1807_1, u4elo0]
                                      · have p1807_0 := h1807c.1
                                        have p1807_1 := h1807c.2.1
                                        have p1807_2 := h1807c.2.2.1
                                        have p1807_3 := h1807c.2.2.2
                                        linarith only [h1791, hlam, p1807_0]
                                      · have p1807_0 := h1807c.1
                                        have p1807_1 := h1807c.2.1
                                        have p1807_2 := h1807c.2.2.1
                                        have p1807_3 := h1807c.2.2.2
                                        linarith only [hlam, p1807_0]
                                      · have p1807_0 := h1807c.1
                                        have p1807_1 := h1807c.2.1
                                        have p1807_2 := h1807c.2.2.1
                                        have p1807_3 := h1807c.2.2.2
                                        linarith only [h0, h1635, h1736, hc12, hlam, hphi, ht23, ht34, p1807_1, u4elo2]
                                      · have p1807_0 := h1807c.1
                                        have p1807_1 := h1807c.2.1
                                        have p1807_2 := h1807c.2.2.1
                                        have p1807_3 := h1807c.2.2.2
                                        linarith only [h1632, hlam, p1807_0]
                                      · have p1807_0 := h1807c.1
                                        have p1807_1 := h1807c.2.1
                                        have p1807_2 := h1807c.2.2.1
                                        have p1807_3 := h1807c.2.2.2
                                        linarith only [h0, h1, h1632, h1794, hc12, hc23, hlam, hphi, p1807_1]
                                      · have p1807_0 := h1807c.1
                                        have p1807_1 := h1807c.2.1
                                        have p1807_2 := h1807c.2.2.1
                                        have p1807_3 := h1807c.2.2.2
                                        linarith only [h1792, hlam, p1807_0]
                                      · have p1807_0 := h1807c.1
                                        have p1807_1 := h1807c.2.1
                                        have p1807_2 := h1807c.2.2.1
                                        have p1807_3 := h1807c.2.2.2
                                        linarith only [h1793, hlam, p1807_1]
                                      · have p1807_0 := h1807c.1
                                        have p1807_1 := h1807c.2.1
                                        have p1807_2 := h1807c.2.2.1
                                        have p1807_3 := h1807c.2.2.2
                                        linarith only [hlam, p1807_0]
                                    · linarith only [h1635, h1793, h1806, hc34, hlam, hphi, u4elo2]
                                  · linarith only [h1, h1631, h1635, h1794, h1802, h1805, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h1, h1631, h1794, h1801, h1802, h1804, hlam]
                              · linarith only [h1, h1631, h1794, h1802, h1803, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h1793, h1796, h1802, hc12, hlam, hphi, ht23, ht34, u4elo0]
                          · linarith only [h1, h1631, h1796, h1801, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h1631, h1796, h1800, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1840 | h1840
                  · linarith only [h0, h1635, h1840, hc23, hlam, hphi, ht34, u4elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1842 | h1842
                    · linarith only [h0, h1635, h1842, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1844 | h1844
                      · linarith only [h0, h1736, h1844, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1846 | h1846
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1847 | h1847
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1848 | h1848
                            · linarith only [h1, h1631, h1793, h1848, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1850 | h1850
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1851 | h1851
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1852 | h1852
                                  · linarith only [h1635, h1793, h1852, hc02, hlam, hphi, ht23, ht34, u4elo2]
                                  · linarith only [h0, h1635, h1852, hc12, hlam, hphi, ht23, ht34, u4elo4]
                                · linarith only [h1, h1632, h1840, h1847, h1851, hlam]
                              · linarith only [h1, h1840, h1850, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                          · linarith only [h0, h1, h1847, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h1846, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h1, h1632, h1792, hlam]
            · linarith only [h0, h1, h1791, hc12, hlam, hphi, ht23, ht34, u4elo3]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1861 | h1861
      · linarith only [h0, h1, h1861, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1863 | h1863
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1864 | h1864
          · linarith only [h0, h1632, h1864, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1866 | h1866
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1867 | h1867
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1868 | h1868
                · linarith only [h1631, h1632, h1868, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1870 | h1870
                  · linarith only [h0, h1, h1861, h1870, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1872 | h1872
                    · linarith only [h0, h1632, h1868, h1872, hc24, hlam, hphi, u4elo4]
                    · linarith only [h1863, h1864, h1872, hc12, hc25, hlam, hphi]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1875 | h1875
                · linarith only [h1, h1631, h1867, h1875, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1877 | h1877
                  · linarith only [h0, h1, h1867, h1875, h1877, hc23, hlam, hphi, ht34, u4elo4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1879 | h1879
                    · linarith only [h0, h1, h1867, h1875, h1879, hc24, hlam, hphi, u4elo4]
                    · linarith only [h0, h1, h1863, h1867, h1875, h1879, hc12, hlam, hphi, ht23, ht34, u4elo4]
            · linarith only [h0, h1, h1863, h1866, hc24, hlam, hphi, u4elo3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1883 | h1883
          · linarith only [h0, h1632, h1863, h1883, hc12, hlam, hphi, ht23, ht34, u4elo2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1885 | h1885
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1886 | h1886
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1887 | h1887
                · linarith only [h1631, h1632, h1887, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1889 | h1889
                  · linarith only [h0, h1863, h1887, h1889, hc23, hlam, hphi, ht34, u4elo4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1891 | h1891
                    · linarith only [h0, h1863, h1887, h1891, hc24, hlam, hphi, u4elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1893 | h1893
                      · linarith only [h1631, h1632, h1883, h1891, h1893, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1895 | h1895
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1896 | h1896
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1897 | h1897
                            · linarith only [h1631, h1632, h1887, h1897, hlam]
                            · linarith only [h1631, h1632, h1891, h1897, hc12, hlam, hphi, ht23, ht34, u4elo4]
                          · linarith only [h1, h1631, h1886, h1891, h1896, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                        · linarith only [h1, h1631, h1891, h1895, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1902 | h1902
                · linarith only [h1, h1631, h1886, h1902, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1904 | h1904
                  · linarith only [h0, h1, h1886, h1904, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1906 | h1906
                    · linarith only [h0, h1, h1886, h1902, h1906, hc24, hlam, hphi, u4elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1908 | h1908
                      · linarith only [h1, h1631, h1883, h1886, h1902, h1906, h1908, hc02, hlam, hphi, ht23, ht34, u4elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1910 | h1910
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1911 | h1911
                          · linarith only [h0, h1, h1886, h1904, h1911, hc12, hc23, hlam, hphi]
                          · linarith only [h1, h1631, h1906, h1911, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h1631, h1906, h1910, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h1, h1631, h1885, hc14, hlam, hphi, u4elo3]
  · linarith only [h0, h1631, hc12, hlam, hphi, ht23, ht34, u4elo1]

set_option maxHeartbeats 7284000 in
set_option maxHeartbeats 7284000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_0_x0_x0 m hb0 hb1 hb3 hb4 h0 h1
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_0_x0_x1 m hb0 hb1 hb3 hb4 h0 h1

set_option maxHeartbeats 7284000 in
set_option maxHeartbeats 7284000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_0_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1917 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0bigk := hb0.1
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1918 | h1918
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1919 | h1919
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1920 | h1920
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1921 | h1921
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1922 | h1922
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1923 | h1923
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1924 | h1924
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1925 | h1925
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1926 | h1926
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1927 | h1927
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1928 | h1928
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1929 | h1929
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1930 | h1930
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1931 | h1931
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1932 | h1932
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1933 | h1933
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1934 | h1934
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1935 | h1935
                                    · linarith only [h0, h1917, h1926, h1932, h1935, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                    · linarith only [h1918, h1927, h1934, h1935, hc34, hlam, hphi, u4elo0]
                                  · linarith only [h1925, h1934, hc24, hlam, hphi, u4elo0]
                                · linarith only [h0, h1917, h1930, h1933, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · linarith only [h0, h1917, h1929, h1932, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · linarith only [h1925, h1931, hc14, hlam, hphi, u4elo0]
                          · linarith only [h0, h1917, h1924, h1929, h1930, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1943 | h1943
                          · linarith only [h0, h1917, h1923, h1929, h1943, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1945 | h1945
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1946 | h1946
                              · linarith only [h1926, h1929, h1946, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1948 | h1948
                                · linarith only [h0, h1917, h1923, h1926, h1929, h1948, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1950 | h1950
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1951 | h1951
                                    · rcases h0bigk with h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c | h1952c
                                      · have p1952_0 := h1952c.1
                                        have p1952_1 := h1952c.2.1
                                        have p1952_2 := h1952c.2.2.1
                                        have p1952_3 := h1952c.2.2.2
                                        linarith only [hlam, p1952_0]
                                      · have p1952_0 := h1952c.1
                                        have p1952_1 := h1952c.2.1
                                        have p1952_2 := h1952c.2.2.1
                                        have p1952_3 := h1952c.2.2.2
                                        linarith only [h0, hlam, p1952_1]
                                      · have p1952_0 := h1952c.1
                                        have p1952_1 := h1952c.2.1
                                        have p1952_2 := h1952c.2.2.1
                                        have p1952_3 := h1952c.2.2.2
                                        linarith only [h0, h1923, h1926, h1943, h1951, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1952_1]
                                      · have p1952_0 := h1952c.1
                                        have p1952_1 := h1952c.2.1
                                        have p1952_2 := h1952c.2.2.1
                                        have p1952_3 := h1952c.2.2.2
                                        linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1952_1]
                                      · have p1952_0 := h1952c.1
                                        have p1952_1 := h1952c.2.1
                                        have p1952_2 := h1952c.2.2.1
                                        have p1952_3 := h1952c.2.2.2
                                        linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1952_1]
                                      · have p1952_0 := h1952c.1
                                        have p1952_1 := h1952c.2.1
                                        have p1952_2 := h1952c.2.2.1
                                        have p1952_3 := h1952c.2.2.2
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1952_1]
                                      · have p1952_0 := h1952c.1
                                        have p1952_1 := h1952c.2.1
                                        have p1952_2 := h1952c.2.2.1
                                        have p1952_3 := h1952c.2.2.2
                                        linarith only [hlam, p1952_0]
                                      · have p1952_0 := h1952c.1
                                        have p1952_1 := h1952c.2.1
                                        have p1952_2 := h1952c.2.2.1
                                        have p1952_3 := h1952c.2.2.2
                                        linarith only [h0, h1923, h1926, h1943, h1951, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1952_1]
                                      · have p1952_0 := h1952c.1
                                        have p1952_1 := h1952c.2.1
                                        have p1952_2 := h1952c.2.2.1
                                        have p1952_3 := h1952c.2.2.2
                                        linarith only [h0, h1921, h1950, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1952_1]
                                      · have p1952_0 := h1952c.1
                                        have p1952_1 := h1952c.2.1
                                        have p1952_2 := h1952c.2.2.1
                                        have p1952_3 := h1952c.2.2.2
                                        linarith only [h0, h1924, h1926, h1943, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1952_1]
                                      · have p1952_0 := h1952c.1
                                        have p1952_1 := h1952c.2.1
                                        have p1952_2 := h1952c.2.2.1
                                        have p1952_3 := h1952c.2.2.2
                                        linarith only [h1917, hlam, p1952_1]
                                      · have p1952_0 := h1952c.1
                                        have p1952_1 := h1952c.2.1
                                        have p1952_2 := h1952c.2.2.1
                                        have p1952_3 := h1952c.2.2.2
                                        linarith only [h1920, hlam, p1952_1]
                                      · have p1952_0 := h1952c.1
                                        have p1952_1 := h1952c.2.1
                                        have p1952_2 := h1952c.2.2.1
                                        have p1952_3 := h1952c.2.2.2
                                        linarith only [hlam, p1952_0]
                                      · have p1952_0 := h1952c.1
                                        have p1952_1 := h1952c.2.1
                                        have p1952_2 := h1952c.2.2.1
                                        have p1952_3 := h1952c.2.2.2
                                        linarith only [h1917, h1923, h1926, h1943, h1951, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1952_1]
                                      · have p1952_0 := h1952c.1
                                        have p1952_1 := h1952c.2.1
                                        have p1952_2 := h1952c.2.2.1
                                        have p1952_3 := h1952c.2.2.2
                                        linarith only [h0, h1917, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1952_1]
                                      · have p1952_0 := h1952c.1
                                        have p1952_1 := h1952c.2.1
                                        have p1952_2 := h1952c.2.2.1
                                        have p1952_3 := h1952c.2.2.2
                                        linarith only [h1918, hlam, p1952_0]
                                      · have p1952_0 := h1952c.1
                                        have p1952_1 := h1952c.2.1
                                        have p1952_2 := h1952c.2.2.1
                                        have p1952_3 := h1952c.2.2.2
                                        linarith only [h1921, hlam, p1952_0]
                                      · have p1952_0 := h1952c.1
                                        have p1952_1 := h1952c.2.1
                                        have p1952_2 := h1952c.2.2.1
                                        have p1952_3 := h1952c.2.2.2
                                        linarith only [h1923, hlam, p1952_0]
                                      · have p1952_0 := h1952c.1
                                        have p1952_1 := h1952c.2.1
                                        have p1952_2 := h1952c.2.2.1
                                        have p1952_3 := h1952c.2.2.2
                                        linarith only [hlam, p1952_0]
                                      · have p1952_0 := h1952c.1
                                        have p1952_1 := h1952c.2.1
                                        have p1952_2 := h1952c.2.2.1
                                        have p1952_3 := h1952c.2.2.2
                                        linarith only [h1924, h1926, h1943, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1952_1]
                                      · have p1952_0 := h1952c.1
                                        have p1952_1 := h1952c.2.1
                                        have p1952_2 := h1952c.2.2.1
                                        have p1952_3 := h1952c.2.2.2
                                        linarith only [h1919, hlam, p1952_0]
                                      · have p1952_0 := h1952c.1
                                        have p1952_1 := h1952c.2.1
                                        have p1952_2 := h1952c.2.2.1
                                        have p1952_3 := h1952c.2.2.2
                                        linarith only [h1922, hlam, p1952_1]
                                      · have p1952_0 := h1952c.1
                                        have p1952_1 := h1952c.2.1
                                        have p1952_2 := h1952c.2.2.1
                                        have p1952_3 := h1952c.2.2.2
                                        linarith only [h1924, hlam, p1952_0]
                                      · have p1952_0 := h1952c.1
                                        have p1952_1 := h1952c.2.1
                                        have p1952_2 := h1952c.2.2.1
                                        have p1952_3 := h1952c.2.2.2
                                        linarith only [h1925, hlam, p1952_1]
                                      · have p1952_0 := h1952c.1
                                        have p1952_1 := h1952c.2.1
                                        have p1952_2 := h1952c.2.2.1
                                        have p1952_3 := h1952c.2.2.2
                                        linarith only [hlam, p1952_0]
                                    · linarith only [h1929, h1950, h1951, hc14, hlam, hphi, u4elo2]
                                  · linarith only [h1945, h1946, h1950, hc23, hlam, hphi, ht34, u4elo1]
                            · linarith only [h1925, h1945, hc14, hlam, hphi, u4elo0]
                      · linarith only [h0, h1922, h1928, hlam]
                    · linarith only [h0, h1927, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h0, h1920, h1926, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1984 | h1984
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1985 | h1985
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1986 | h1986
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1987 | h1987
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1988 | h1988
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1989 | h1989
                            · linarith only [h1918, h1925, h1989, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1991 | h1991
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1992 | h1992
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1993 | h1993
                                  · linarith only [h1918, h1925, h1985, h1993, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1995 | h1995
                                    · linarith only [h1917, h1925, h1984, h1991, h1995, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                                    · rcases h0bigk with h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c | h1997c
                                      · have p1997_0 := h1997c.1
                                        have p1997_1 := h1997c.2.1
                                        have p1997_2 := h1997c.2.2.1
                                        have p1997_3 := h1997c.2.2.2
                                        linarith only [hlam, p1997_0]
                                      · have p1997_0 := h1997c.1
                                        have p1997_1 := h1997c.2.1
                                        have p1997_2 := h1997c.2.2.1
                                        have p1997_3 := h1997c.2.2.2
                                        linarith only [h0, hlam, p1997_1]
                                      · have p1997_0 := h1997c.1
                                        have p1997_1 := h1997c.2.1
                                        have p1997_2 := h1997c.2.2.1
                                        have p1997_3 := h1997c.2.2.2
                                        linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1997_1]
                                      · have p1997_0 := h1997c.1
                                        have p1997_1 := h1997c.2.1
                                        have p1997_2 := h1997c.2.2.1
                                        have p1997_3 := h1997c.2.2.2
                                        linarith only [h0, h1918, h1985, h1991, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1997_1]
                                      · have p1997_0 := h1997c.1
                                        have p1997_1 := h1997c.2.1
                                        have p1997_2 := h1997c.2.2.1
                                        have p1997_3 := h1997c.2.2.2
                                        linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1997_1]
                                      · have p1997_0 := h1997c.1
                                        have p1997_1 := h1997c.2.1
                                        have p1997_2 := h1997c.2.2.1
                                        have p1997_3 := h1997c.2.2.2
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1997_1]
                                      · have p1997_0 := h1997c.1
                                        have p1997_1 := h1997c.2.1
                                        have p1997_2 := h1997c.2.2.1
                                        have p1997_3 := h1997c.2.2.2
                                        linarith only [hlam, p1997_0]
                                      · have p1997_0 := h1997c.1
                                        have p1997_1 := h1997c.2.1
                                        have p1997_2 := h1997c.2.2.1
                                        have p1997_3 := h1997c.2.2.2
                                        linarith only [h0, h1917, h1984, h1992, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1997_1]
                                      · have p1997_0 := h1997c.1
                                        have p1997_1 := h1997c.2.1
                                        have p1997_2 := h1997c.2.2.1
                                        have p1997_3 := h1997c.2.2.2
                                        rcases p1997_3 (m.d 0 1) (by simp) with h2006 | h2006
                                        · linarith only [h0, h2006, hlam]
                                        · linarith only [h1918, h2006, hlam]
                                      · have p1997_0 := h1997c.1
                                        have p1997_1 := h1997c.2.1
                                        have p1997_2 := h1997c.2.2.1
                                        have p1997_3 := h1997c.2.2.2
                                        rcases p1997_3 (m.d 0 1) (by simp) with h2009 | h2009
                                        · linarith only [h0, h2009, hlam]
                                        · linarith only [h1919, h2009, hlam]
                                      · have p1997_0 := h1997c.1
                                        have p1997_1 := h1997c.2.1
                                        have p1997_2 := h1997c.2.2.1
                                        have p1997_3 := h1997c.2.2.2
                                        linarith only [h1917, hlam, p1997_1]
                                      · have p1997_0 := h1997c.1
                                        have p1997_1 := h1997c.2.1
                                        have p1997_2 := h1997c.2.2.1
                                        have p1997_3 := h1997c.2.2.2
                                        linarith only [h1920, hlam, p1997_1]
                                      · have p1997_0 := h1997c.1
                                        have p1997_1 := h1997c.2.1
                                        have p1997_2 := h1997c.2.2.1
                                        have p1997_3 := h1997c.2.2.2
                                        linarith only [hlam, p1997_0]
                                      · have p1997_0 := h1997c.1
                                        have p1997_1 := h1997c.2.1
                                        have p1997_2 := h1997c.2.2.1
                                        have p1997_3 := h1997c.2.2.2
                                        linarith only [h0, h1917, h1918, h1985, h1991, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1997_1]
                                      · have p1997_0 := h1997c.1
                                        have p1997_1 := h1997c.2.1
                                        have p1997_2 := h1997c.2.2.1
                                        have p1997_3 := h1997c.2.2.2
                                        linarith only [h0, h1917, h1918, h1925, h1985, h1991, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1997_1]
                                      · have p1997_0 := h1997c.1
                                        have p1997_1 := h1997c.2.1
                                        have p1997_2 := h1997c.2.2.1
                                        have p1997_3 := h1997c.2.2.2
                                        linarith only [h1918, hlam, p1997_0]
                                      · have p1997_0 := h1997c.1
                                        have p1997_1 := h1997c.2.1
                                        have p1997_2 := h1997c.2.2.1
                                        have p1997_3 := h1997c.2.2.2
                                        linarith only [h1921, hlam, p1997_0]
                                      · have p1997_0 := h1997c.1
                                        have p1997_1 := h1997c.2.1
                                        have p1997_2 := h1997c.2.2.1
                                        have p1997_3 := h1997c.2.2.2
                                        linarith only [h1923, hlam, p1997_0]
                                      · have p1997_0 := h1997c.1
                                        have p1997_1 := h1997c.2.1
                                        have p1997_2 := h1997c.2.2.1
                                        have p1997_3 := h1997c.2.2.2
                                        linarith only [hlam, p1997_0]
                                      · have p1997_0 := h1997c.1
                                        have p1997_1 := h1997c.2.1
                                        have p1997_2 := h1997c.2.2.1
                                        have p1997_3 := h1997c.2.2.2
                                        linarith only [h1925, hlam, p1997_0]
                                      · have p1997_0 := h1997c.1
                                        have p1997_1 := h1997c.2.1
                                        have p1997_2 := h1997c.2.2.1
                                        have p1997_3 := h1997c.2.2.2
                                        linarith only [h1919, hlam, p1997_0]
                                      · have p1997_0 := h1997c.1
                                        have p1997_1 := h1997c.2.1
                                        have p1997_2 := h1997c.2.2.1
                                        have p1997_3 := h1997c.2.2.2
                                        linarith only [h1922, hlam, p1997_1]
                                      · have p1997_0 := h1997c.1
                                        have p1997_1 := h1997c.2.1
                                        have p1997_2 := h1997c.2.2.1
                                        have p1997_3 := h1997c.2.2.2
                                        linarith only [h1924, hlam, p1997_0]
                                      · have p1997_0 := h1997c.1
                                        have p1997_1 := h1997c.2.1
                                        have p1997_2 := h1997c.2.2.1
                                        have p1997_3 := h1997c.2.2.2
                                        linarith only [h0, h1918, h1919, h1985, h1991, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1997_1]
                                      · have p1997_0 := h1997c.1
                                        have p1997_1 := h1997c.2.1
                                        have p1997_2 := h1997c.2.2.1
                                        have p1997_3 := h1997c.2.2.2
                                        linarith only [hlam, p1997_0]
                                · linarith only [h0, h1917, h1988, h1992, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · linarith only [h1923, h1925, h1991, hc23, hlam, hphi, ht34, u4elo4]
                          · linarith only [h0, h1917, h1924, h1987, h1988, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h1923, h1925, h1987, hc13, hlam, hphi, ht34, u4elo4]
                      · linarith only [h0, h1922, h1986, hlam]
                    · linarith only [h0, h1985, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h0, h1920, h1984, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2034 | h2034
                · linarith only [h1923, h1924, h2034, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2036 | h2036
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2037 | h2037
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2038 | h2038
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2039 | h2039
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2040 | h2040
                          · linarith only [h0, h1917, h1924, h2040, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2042 | h2042
                            · linarith only [h0, h1918, h1923, h1924, h2034, h2042, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2044 | h2044
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2045 | h2045
                                · linarith only [h1917, h1924, h2036, h2045, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2047 | h2047
                                  · linarith only [h2034, h2047, hc04, hlam, hphi, u4elo2]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2049 | h2049
                                    · linarith only [h1917, h1924, h2034, h2036, h2044, h2049, hlam]
                                    · linarith only [h1917, h1924, h2036, h2044, h2049, hc34, hlam, hphi, u4elo4]
                              · linarith only [h1923, h1924, h2044, hc23, hc35, hlam, hphi]
                        · linarith only [h1923, h1924, h2034, h2039, hc13, hlam, hphi, ht34, u4elo4]
                      · linarith only [h0, h1922, h2038, hlam]
                    · linarith only [h0, h2037, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h0, h1920, h2036, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2057 | h2057
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2058 | h2058
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2059 | h2059
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2060 | h2060
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2061 | h2061
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2062 | h2062
                        · linarith only [h0, h1917, h1923, h2062, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2064 | h2064
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2065 | h2065
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2066 | h2066
                              · linarith only [h1917, h1923, h2059, h2066, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2068 | h2068
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2069 | h2069
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2070 | h2070
                                    · rcases h0bigk with h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c | h2071c
                                      · have p2071_0 := h2071c.1
                                        have p2071_1 := h2071c.2.1
                                        have p2071_2 := h2071c.2.2.1
                                        have p2071_3 := h2071c.2.2.2
                                        linarith only [hlam, p2071_0]
                                      · have p2071_0 := h2071c.1
                                        have p2071_1 := h2071c.2.1
                                        have p2071_2 := h2071c.2.2.1
                                        have p2071_3 := h2071c.2.2.2
                                        linarith only [h0, hlam, p2071_1]
                                      · have p2071_0 := h2071c.1
                                        have p2071_1 := h2071c.2.1
                                        have p2071_2 := h2071c.2.2.1
                                        have p2071_3 := h2071c.2.2.2
                                        linarith only [h0, h1917, h2059, h2068, h2070, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2071_1]
                                      · have p2071_0 := h2071c.1
                                        have p2071_1 := h2071c.2.1
                                        have p2071_2 := h2071c.2.2.1
                                        have p2071_3 := h2071c.2.2.2
                                        linarith only [h0, h1917, h1923, h2059, h2068, h2070, hc04, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2071_1, u4elo3]
                                      · have p2071_0 := h2071c.1
                                        have p2071_1 := h2071c.2.1
                                        have p2071_2 := h2071c.2.2.1
                                        have p2071_3 := h2071c.2.2.2
                                        linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p2071_1]
                                      · have p2071_0 := h2071c.1
                                        have p2071_1 := h2071c.2.1
                                        have p2071_2 := h2071c.2.2.1
                                        have p2071_3 := h2071c.2.2.2
                                        linarith only [h0, hc01, hc12, hlam, hphi, p2071_1]
                                      · have p2071_0 := h2071c.1
                                        have p2071_1 := h2071c.2.1
                                        have p2071_2 := h2071c.2.2.1
                                        have p2071_3 := h2071c.2.2.2
                                        linarith only [hlam, p2071_0]
                                      · have p2071_0 := h2071c.1
                                        have p2071_1 := h2071c.2.1
                                        have p2071_2 := h2071c.2.2.1
                                        have p2071_3 := h2071c.2.2.2
                                        linarith only [h0, h1917, h2059, h2068, h2070, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2071_1]
                                      · have p2071_0 := h2071c.1
                                        have p2071_1 := h2071c.2.1
                                        have p2071_2 := h2071c.2.2.1
                                        have p2071_3 := h2071c.2.2.2
                                        linarith only [h0, h1917, h1923, h2059, h2068, h2070, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2071_1]
                                      · have p2071_0 := h2071c.1
                                        have p2071_1 := h2071c.2.1
                                        have p2071_2 := h2071c.2.2.1
                                        have p2071_3 := h2071c.2.2.2
                                        rcases p2071_3 (m.d 0 1) (by simp) with h2081 | h2081
                                        · linarith only [h0, h2081, hlam]
                                        · linarith only [h1919, h2081, hlam]
                                      · have p2071_0 := h2071c.1
                                        have p2071_1 := h2071c.2.1
                                        have p2071_2 := h2071c.2.2.1
                                        have p2071_3 := h2071c.2.2.2
                                        linarith only [h1917, hlam, p2071_1]
                                      · have p2071_0 := h2071c.1
                                        have p2071_1 := h2071c.2.1
                                        have p2071_2 := h2071c.2.2.1
                                        have p2071_3 := h2071c.2.2.2
                                        linarith only [h1920, hlam, p2071_1]
                                      · have p2071_0 := h2071c.1
                                        have p2071_1 := h2071c.2.1
                                        have p2071_2 := h2071c.2.2.1
                                        have p2071_3 := h2071c.2.2.2
                                        linarith only [hlam, p2071_0]
                                      · have p2071_0 := h2071c.1
                                        have p2071_1 := h2071c.2.1
                                        have p2071_2 := h2071c.2.2.1
                                        have p2071_3 := h2071c.2.2.2
                                        linarith only [h1923, hlam, p2071_1]
                                      · have p2071_0 := h2071c.1
                                        have p2071_1 := h2071c.2.1
                                        have p2071_2 := h2071c.2.2.1
                                        have p2071_3 := h2071c.2.2.2
                                        linarith only [h1919, h1923, h2061, h2068, h2070, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2071_1, u4elo3]
                                      · have p2071_0 := h2071c.1
                                        have p2071_1 := h2071c.2.1
                                        have p2071_2 := h2071c.2.2.1
                                        have p2071_3 := h2071c.2.2.2
                                        linarith only [h1918, hlam, p2071_0]
                                      · have p2071_0 := h2071c.1
                                        have p2071_1 := h2071c.2.1
                                        have p2071_2 := h2071c.2.2.1
                                        have p2071_3 := h2071c.2.2.2
                                        linarith only [h1921, hlam, p2071_0]
                                      · have p2071_0 := h2071c.1
                                        have p2071_1 := h2071c.2.1
                                        have p2071_2 := h2071c.2.2.1
                                        have p2071_3 := h2071c.2.2.2
                                        linarith only [hc03, hlam, hphi, ht34, p2071_1, u4elo0]
                                      · have p2071_0 := h2071c.1
                                        have p2071_1 := h2071c.2.1
                                        have p2071_2 := h2071c.2.2.1
                                        have p2071_3 := h2071c.2.2.2
                                        linarith only [hlam, p2071_0]
                                      · have p2071_0 := h2071c.1
                                        have p2071_1 := h2071c.2.1
                                        have p2071_2 := h2071c.2.2.1
                                        have p2071_3 := h2071c.2.2.2
                                        linarith only [h1919, h1923, h2061, h2068, h2070, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2071_1, u4elo3]
                                      · have p2071_0 := h2071c.1
                                        have p2071_1 := h2071c.2.1
                                        have p2071_2 := h2071c.2.2.1
                                        have p2071_3 := h2071c.2.2.2
                                        linarith only [h1919, hlam, p2071_0]
                                      · have p2071_0 := h2071c.1
                                        have p2071_1 := h2071c.2.1
                                        have p2071_2 := h2071c.2.2.1
                                        have p2071_3 := h2071c.2.2.2
                                        linarith only [h1922, hlam, p2071_1]
                                      · have p2071_0 := h2071c.1
                                        have p2071_1 := h2071c.2.1
                                        have p2071_2 := h2071c.2.2.1
                                        have p2071_3 := h2071c.2.2.2
                                        linarith only [h2057, hlam, p2071_0]
                                      · have p2071_0 := h2071c.1
                                        have p2071_1 := h2071c.2.1
                                        have p2071_2 := h2071c.2.2.1
                                        have p2071_3 := h2071c.2.2.2
                                        linarith only [h2058, hlam, p2071_1]
                                      · have p2071_0 := h2071c.1
                                        have p2071_1 := h2071c.2.1
                                        have p2071_2 := h2071c.2.2.1
                                        have p2071_3 := h2071c.2.2.2
                                        linarith only [hlam, p2071_0]
                                    · linarith only [h1923, h2070, hc03, hlam, hphi, ht34, u4elo4]
                                  · linarith only [h0, h1919, h2065, h2066, h2068, h2069, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h1923, h2057, h2068, hc23, hlam, hphi, ht34, u4elo3]
                            · linarith only [h1923, h2058, h2065, hc14, hlam, hphi, u4elo3]
                          · linarith only [h1923, h2057, h2064, hc13, hlam, hphi, ht34, u4elo3]
                      · linarith only [h0, h1922, h2061, hlam]
                    · linarith only [h0, h2060, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h0, h1920, h2059, hlam]
                · linarith only [h1923, h2057, h2058, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2108 | h2108
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2109 | h2109
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2110 | h2110
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2111 | h2111
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2112 | h2112
                        · linarith only [h1917, h1923, h2112, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2114 | h2114
                          · linarith only [h1917, h2057, h2114, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2116 | h2116
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2117 | h2117
                              · linarith only [h1917, h1923, h2109, h2117, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2119 | h2119
                                · linarith only [h1917, h2057, h2109, h2119, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2121 | h2121
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2122 | h2122
                                    · rcases h0bigk with h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c
                                      · have p2123_0 := h2123c.1
                                        have p2123_1 := h2123c.2.1
                                        have p2123_2 := h2123c.2.2.1
                                        have p2123_3 := h2123c.2.2.2
                                        linarith only [hlam, p2123_0]
                                      · have p2123_0 := h2123c.1
                                        have p2123_1 := h2123c.2.1
                                        have p2123_2 := h2123c.2.2.1
                                        have p2123_3 := h2123c.2.2.2
                                        linarith only [h0, hlam, p2123_1]
                                      · have p2123_0 := h2123c.1
                                        have p2123_1 := h2123c.2.1
                                        have p2123_2 := h2123c.2.2.1
                                        have p2123_3 := h2123c.2.2.2
                                        linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2123_1]
                                      · have p2123_0 := h2123c.1
                                        have p2123_1 := h2123c.2.1
                                        have p2123_2 := h2123c.2.2.1
                                        have p2123_3 := h2123c.2.2.2
                                        linarith only [h0, h1917, h2057, h2108, h2109, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2123_1]
                                      · have p2123_0 := h2123c.1
                                        have p2123_1 := h2123c.2.1
                                        have p2123_2 := h2123c.2.2.1
                                        have p2123_3 := h2123c.2.2.2
                                        linarith only [h0, h1917, h2057, h2109, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2123_1]
                                      · have p2123_0 := h2123c.1
                                        have p2123_1 := h2123c.2.1
                                        have p2123_2 := h2123c.2.2.1
                                        have p2123_3 := h2123c.2.2.2
                                        linarith only [h0, hc01, hc12, hlam, hphi, p2123_1]
                                      · have p2123_0 := h2123c.1
                                        have p2123_1 := h2123c.2.1
                                        have p2123_2 := h2123c.2.2.1
                                        have p2123_3 := h2123c.2.2.2
                                        linarith only [hlam, p2123_0]
                                      · have p2123_0 := h2123c.1
                                        have p2123_1 := h2123c.2.1
                                        have p2123_2 := h2123c.2.2.1
                                        have p2123_3 := h2123c.2.2.2
                                        rcases p2123_3 (m.d 0 1) (by simp) with h2131 | h2131
                                        · linarith only [h0, h2131, hlam]
                                        · linarith only [h1917, h2131, hlam]
                                      · have p2123_0 := h2123c.1
                                        have p2123_1 := h2123c.2.1
                                        have p2123_2 := h2123c.2.2.1
                                        have p2123_3 := h2123c.2.2.2
                                        linarith only [h0, h1918, h2110, h2121, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2123_1]
                                      · have p2123_0 := h2123c.1
                                        have p2123_1 := h2123c.2.1
                                        have p2123_2 := h2123c.2.2.1
                                        have p2123_3 := h2123c.2.2.2
                                        rcases p2123_3 (m.d 0 1) (by simp) with h2135 | h2135
                                        · linarith only [h0, h2135, hlam]
                                        · linarith only [h1919, h2135, hlam]
                                      · have p2123_0 := h2123c.1
                                        have p2123_1 := h2123c.2.1
                                        have p2123_2 := h2123c.2.2.1
                                        have p2123_3 := h2123c.2.2.2
                                        linarith only [h1917, hlam, p2123_1]
                                      · have p2123_0 := h2123c.1
                                        have p2123_1 := h2123c.2.1
                                        have p2123_2 := h2123c.2.2.1
                                        have p2123_3 := h2123c.2.2.2
                                        linarith only [h1920, hlam, p2123_1]
                                      · have p2123_0 := h2123c.1
                                        have p2123_1 := h2123c.2.1
                                        have p2123_2 := h2123c.2.2.1
                                        have p2123_3 := h2123c.2.2.2
                                        linarith only [hlam, p2123_0]
                                      · have p2123_0 := h2123c.1
                                        have p2123_1 := h2123c.2.1
                                        have p2123_2 := h2123c.2.2.1
                                        have p2123_3 := h2123c.2.2.2
                                        linarith only [h1923, hlam, p2123_1]
                                      · have p2123_0 := h2123c.1
                                        have p2123_1 := h2123c.2.1
                                        have p2123_2 := h2123c.2.2.1
                                        have p2123_3 := h2123c.2.2.2
                                        linarith only [h2057, hlam, p2123_1]
                                      · have p2123_0 := h2123c.1
                                        have p2123_1 := h2123c.2.1
                                        have p2123_2 := h2123c.2.2.1
                                        have p2123_3 := h2123c.2.2.2
                                        linarith only [h1918, hlam, p2123_0]
                                      · have p2123_0 := h2123c.1
                                        have p2123_1 := h2123c.2.1
                                        have p2123_2 := h2123c.2.2.1
                                        have p2123_3 := h2123c.2.2.2
                                        linarith only [h1921, hlam, p2123_0]
                                      · have p2123_0 := h2123c.1
                                        have p2123_1 := h2123c.2.1
                                        have p2123_2 := h2123c.2.2.1
                                        have p2123_3 := h2123c.2.2.2
                                        linarith only [h1917, h2109, hc23, hlam, hphi, ht34, p2123_1, u4elo0]
                                      · have p2123_0 := h2123c.1
                                        have p2123_1 := h2123c.2.1
                                        have p2123_2 := h2123c.2.2.1
                                        have p2123_3 := h2123c.2.2.2
                                        linarith only [hlam, p2123_0]
                                      · have p2123_0 := h2123c.1
                                        have p2123_1 := h2123c.2.1
                                        have p2123_2 := h2123c.2.2.1
                                        have p2123_3 := h2123c.2.2.2
                                        linarith only [h1917, h1923, h2057, h2109, hc23, hc34, hlam, hphi, p2123_1]
                                      · have p2123_0 := h2123c.1
                                        have p2123_1 := h2123c.2.1
                                        have p2123_2 := h2123c.2.2.1
                                        have p2123_3 := h2123c.2.2.2
                                        linarith only [h1919, hlam, p2123_0]
                                      · have p2123_0 := h2123c.1
                                        have p2123_1 := h2123c.2.1
                                        have p2123_2 := h2123c.2.2.1
                                        have p2123_3 := h2123c.2.2.2
                                        linarith only [h1922, hlam, p2123_1]
                                      · have p2123_0 := h2123c.1
                                        have p2123_1 := h2123c.2.1
                                        have p2123_2 := h2123c.2.2.1
                                        have p2123_3 := h2123c.2.2.2
                                        linarith only [h0, h1917, h1919, h2109, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2123_1]
                                      · have p2123_0 := h2123c.1
                                        have p2123_1 := h2123c.2.1
                                        have p2123_2 := h2123c.2.2.1
                                        have p2123_3 := h2123c.2.2.2
                                        linarith only [h2108, hlam, p2123_1]
                                      · have p2123_0 := h2123c.1
                                        have p2123_1 := h2123c.2.1
                                        have p2123_2 := h2123c.2.2.1
                                        have p2123_3 := h2123c.2.2.2
                                        linarith only [hlam, p2123_0]
                                    · linarith only [h1917, h1923, h2109, h2122, hc23, hlam, hphi, ht34, u4elo4]
                                  · linarith only [h1918, h2116, h2121, hc24, hlam, hphi, u4elo0]
                            · linarith only [h1923, h2108, h2116, hc14, hlam, hphi, u4elo3]
                      · linarith only [h0, h1922, h2111, hlam]
                    · linarith only [h0, h2110, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h0, h1920, h2109, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2159 | h2159
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2160 | h2160
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2161 | h2161
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2162 | h2162
                        · linarith only [h1917, h1923, h2162, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2164 | h2164
                          · linarith only [h1917, h2057, h2164, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2166 | h2166
                            · linarith only [h0, h1918, h1923, h2108, h2166, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2168 | h2168
                              · linarith only [h1917, h1923, h2159, h2168, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2170 | h2170
                                · linarith only [h1917, h2057, h2159, h2170, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2172 | h2172
                                  · linarith only [h1918, h2108, h2160, h2172, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2174 | h2174
                                    · linarith only [h1917, h1923, h2108, h2159, h2174, hc23, hlam, hphi, ht34, u4elo3]
                                    · linarith only [h1917, h1923, h2159, h2174, hc23, hlam, hphi, ht34, u4elo4]
                      · linarith only [h0, h1922, h2161, hlam]
                    · linarith only [h0, h2160, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h0, h1920, h2159, hlam]
          · linarith only [h0, h1919, h1922, hlam]
        · linarith only [h0, h1917, h1921, hc13, hlam, hphi, ht34, u4elo2]
      · linarith only [h0, h1917, h1920, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2183 | h2183
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2184 | h2184
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2185 | h2185
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2186 | h2186
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2187 | h2187
              · linarith only [h1917, h1919, h2187, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2189 | h2189
                · linarith only [h1918, h1919, h2189, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2191 | h2191
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2192 | h2192
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2193 | h2193
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2194 | h2194
                        · linarith only [h1917, h1919, h2189, h2194, hc34, hlam, hphi, u4elo4]
                        · linarith only [h1917, h1919, h2186, h2189, h2194, hc13, hlam, hphi, ht34, u4elo4]
                      · linarith only [h0, h1918, h2185, h2193, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h1917, h2191, h2192, hc23, hlam, hphi, ht34, u4elo2]
                  · linarith only [h0, h2183, h2191, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2200 | h2200
              · linarith only [h1917, h1919, h2200, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2202 | h2202
                · linarith only [h1918, h1919, h2202, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2204 | h2204
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2205 | h2205
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2206 | h2206
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2207 | h2207
                        · linarith only [h1917, h2186, h2202, h2207, hc34, hlam, hphi, u4elo4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2209 | h2209
                          · linarith only [h1917, h1919, h2200, h2209, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2211 | h2211
                            · linarith only [h2186, h2202, h2211, hc03, hlam, hphi, ht34, u4elo1]
                            · linarith only [h1917, h1919, h2204, h2211, hc23, hlam, hphi, ht34, u4elo4]
                      · linarith only [h0, h1917, h2185, h2202, h2204, h2206, hc23, hlam, hphi, ht34, u4elo4]
                    · linarith only [h0, h1917, h2204, h2205, hc23, hlam, hphi, ht34, u4elo2]
                  · linarith only [h0, h1917, h2183, h2204, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2217 | h2217
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2218 | h2218
              · linarith only [h0, h1917, h2185, h2218, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2220 | h2220
                · linarith only [h0, h1918, h2185, h2220, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2222 | h2222
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2223 | h2223
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2224 | h2224
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2225 | h2225
                        · linarith only [h0, h1917, h2185, h2224, h2225, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h1917, h2185, h2217, h2222, h2224, h2225, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2228 | h2228
                        · linarith only [h0, h1917, h2224, h2228, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h0, h1917, h2217, h2222, h2224, h2228, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h0, h2223, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h0, h1917, h2183, h2185, h2220, h2222, hc13, hlam, hphi, ht34, u4elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2233 | h2233
              · linarith only [h0, h1917, h2185, h2233, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2235 | h2235
                · linarith only [h0, h1918, h2185, h2235, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2237 | h2237
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2238 | h2238
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2239 | h2239
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2240 | h2240
                        · linarith only [h0, h1917, h2185, h2239, h2240, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2242 | h2242
                          · linarith only [h0, h1918, h2185, h2233, h2239, h2240, h2242, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2244 | h2244
                            · linarith only [h0, h1918, h2185, h2235, h2239, h2244, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h1918, h1919, h2244, hc14, hlam, hphi, u4elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2247 | h2247
                        · linarith only [h1917, h2217, h2247, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2249 | h2249
                          · linarith only [h0, h1918, h2239, h2247, h2249, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2251 | h2251
                            · linarith only [h0, h1918, h2185, h2235, h2239, h2251, hc02, hc25, hlam, hphi]
                            · linarith only [h0, h1918, h2237, h2239, h2247, h2251, hc23, hlam, hphi, ht34, u4elo4]
                    · linarith only [h0, h2238, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h0, h1917, h2183, h2237, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · linarith only [h0, h1917, h2184, hc13, hlam, hphi, ht34, u4elo2]
      · linarith only [h0, h1917, h2183, hlam]
  · linarith only [h1917, h1918, hc13, hlam, hphi, ht34, u4elo1]

end R2N4
