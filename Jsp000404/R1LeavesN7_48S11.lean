import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_48S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5836000 in
set_option maxHeartbeats 5836000 in
theorem r1l7_20_12_14_H_I_L_0_L_I_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h2elo := hb2.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1578 | h1578
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1579 | h1579
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1580 | h1580
      · linarith only [h0, h1, h1580, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1582 | h1582
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1583 | h1583
          · linarith only [h0, h1, h1579, h1580, h1583, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1585 | h1585
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1586 | h1586
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1587 | h1587
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1588 | h1588
                  · linarith only [h0, h1, h1580, h1588, hlam]
                  · linarith only [h0, h1, h1587, h1588, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h1579, h1587, hc12, hlam, hphi, u2elo0]
              · linarith only [h1, h1578, h1586, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1593 | h1593
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1594 | h1594
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1595 | h1595
                  · linarith only [h0, h1, h1580, h1595, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h0, h1, h1594, h1595, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h0, h1, h1579, h1580, h1594, hc12, hlam, hphi, u2elo3]
              · linarith only [h1, h1578, h1593, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1600 | h1600
          · linarith only [h0, h1, h1579, h1580, h1600, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1602 | h1602
            · linarith only [h1579, h1582, h1602, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1604 | h1604
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1605 | h1605
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1606 | h1606
                  · linarith only [h0, h1, h1580, h1606, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h0, h1, h1605, h1606, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h1579, h1605, hc12, hlam, hphi, u2elo0]
              · linarith only [h1, h1578, h1604, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1611 | h1611
      · linarith only [h0, h1, h1579, h1611, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1613 | h1613
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1614 | h1614
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1615 | h1615
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1616 | h1616
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1617 | h1617
                · linarith only [h0, h1, h1579, h1613, h1614, h1617, hc03, hc25, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1619 | h1619
                  · linarith only [h0, h1611, h1619, hlam]
                  · linarith only [h0, h1, h1619, hc12, hlam, hphi, u2elo3]
              · linarith only [h0, h1, h1613, h1616, hlam]
            · linarith only [h1579, h1613, h1615, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1624 | h1624
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1625 | h1625
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1626 | h1626
                · linarith only [h0, h1, h1579, h1626, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1628 | h1628
                  · linarith only [h0, h1, h1611, h1628, hlam]
                  · linarith only [h0, h1, h1628, hc12, hlam, hphi, u2elo3]
              · linarith only [h0, h1, h1579, h1613, h1625, hc12, hlam, hphi, u2elo2]
            · linarith only [h1579, h1613, h1624, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1633 | h1633
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1634 | h1634
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1635 | h1635
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1636 | h1636
                · linarith only [h1579, h1636, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1638 | h1638
                  · linarith only [h0, h1611, h1638, hlam]
                  · linarith only [h0, h1, h1638, hc12, hlam, hphi, u2elo3]
              · linarith only [h1, h1578, h1635, hlam]
            · linarith only [h1, h1578, h1633, h1634, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1643 | h1643
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1644 | h1644
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1645 | h1645
                · linarith only [h0, h1, h1579, h1643, h1645, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1647 | h1647
                  · linarith only [h0, h1611, h1647, hlam]
                  · linarith only [h0, h1, h1647, hc12, hlam, hphi, u2elo3]
              · linarith only [h1, h1578, h1644, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1651 | h1651
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1652 | h1652
                · linarith only [h1579, h1652, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1654 | h1654
                  · linarith only [h0, h1611, h1654, hlam]
                  · linarith only [h0, h1, h1654, hc12, hlam, hphi, u2elo3]
              · linarith only [h1, h1578, h1651, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1658 | h1658
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1659 | h1659
      · linarith only [h0, h1, h1659, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1661 | h1661
        · linarith only [h0, h1578, h1661, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1663 | h1663
          · linarith only [h0, h1, h1658, h1663, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1665 | h1665
            · linarith only [h0, h1578, h1658, h1665, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1667 | h1667
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1668 | h1668
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1669 | h1669
                  · linarith only [h0, h1, h1659, h1669, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h0, h1, h1668, h1669, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h1658, h1668, hc12, hlam, hphi, u2elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1673 | h1673
                · linarith only [h0, h1, h1667, h1673, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h1658, h1661, h1673, hc12, hlam, hphi, u2elo4]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1676 | h1676
      · linarith only [h0, h1, h1658, h1676, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1678 | h1678
        · linarith only [h0, h1578, h1658, h1678, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1680 | h1680
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1681 | h1681
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1682 | h1682
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1683 | h1683
                · linarith only [h0, h1, h1658, h1683, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1685 | h1685
                  · linarith only [h0, h1676, h1685, hlam]
                  · linarith only [h0, h1, h1685, hc12, hlam, hphi, u2elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1688 | h1688
                · linarith only [h0, h1, h1658, h1680, h1688, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1690 | h1690
                  · linarith only [h0, h1, h1682, h1690, hc24, hc45, hlam, hphi]
                  · linarith only [h0, h1, h1690, hc12, hlam, hphi, u2elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1693 | h1693
              · linarith only [h1680, h1681, h1693, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1695 | h1695
                · linarith only [h0, h1, h1658, h1693, h1695, hc03, hc45, hlam, hphi, ht34]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1697 | h1697
                  · linarith only [h0, h1, h1693, h1697, hc24, hc45, hlam, hphi]
                  · linarith only [h0, h1, h1697, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1700 | h1700
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1701 | h1701
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1702 | h1702
                · linarith only [h0, h1578, h1658, h1700, h1702, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1704 | h1704
                  · linarith only [h0, h1676, h1704, hlam]
                  · linarith only [h0, h1, h1704, hc12, hlam, hphi, u2elo3]
              · linarith only [h1680, h1700, h1701, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1708 | h1708
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1709 | h1709
                · linarith only [h0, h1658, h1709, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1711 | h1711
                  · linarith only [h0, h1578, h1676, h1708, h1711, hlam]
                  · linarith only [h0, h1, h1711, hc12, hlam, hphi, u2elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1714 | h1714
                · linarith only [h0, h1, h1658, h1714, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1716 | h1716
                  · linarith only [h0, h1, h1708, h1716, hc24, hc45, hlam, hphi]
                  · linarith only [h0, h1, h1716, hc12, hlam, hphi, u2elo3]

set_option maxHeartbeats 5836000 in
set_option maxHeartbeats 5836000 in
theorem r1l7_20_12_14_H_I_L_0_L_I_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h2elo := hb2.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
  · exact r1l7_20_12_14_H_I_L_0_L_I_x0_x0 m hb0 hb2 hb4 h0 h1
  · exact r1l7_20_12_14_H_I_L_0_L_I_x0_x1 m hb0 hb2 hb4 h0 h1

set_option maxHeartbeats 5836000 in
set_option maxHeartbeats 5836000 in
theorem r1l7_20_12_14_H_I_L_0_L_I_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1719 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h2elo := hb2.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1720 | h1720
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1721 | h1721
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1722 | h1722
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1723 | h1723
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1724 | h1724
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1725 | h1725
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1726 | h1726
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1727 | h1727
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1728 | h1728
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1729 | h1729
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1730 | h1730
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1731 | h1731
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1732 | h1732
                          · linarith only [h0, h1719, h1732, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · linarith only [h0, h1719, h1726, h1732, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · linarith only [h0, h1719, h1725, h1726, h1730, h1731, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1736 | h1736
                        · linarith only [h0, h1719, h1730, h1736, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1738 | h1738
                          · linarith only [h0, h1719, h1738, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · linarith only [h0, h1719, h1726, h1738, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1729, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h1728, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h1719, h1727, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1744 | h1744
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1745 | h1745
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1746 | h1746
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1747 | h1747
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1748 | h1748
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1749 | h1749
                          · linarith only [h0, h1719, h1726, h1749, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1751 | h1751
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1752 | h1752
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1753 | h1753
                                · linarith only [h0, h1719, h1726, h1745, h1753, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1755 | h1755
                                  · linarith only [h0, h1719, h1721, h1724, h1726, h1745, h1755, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                  · rcases h0bigk with h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c
                                    · have p1757_0 := h1757c.1
                                      have p1757_1 := h1757c.2.1
                                      have p1757_2 := h1757c.2.2.1
                                      have p1757_3 := h1757c.2.2.2
                                      linarith only [hlam, p1757_0]
                                    · have p1757_0 := h1757c.1
                                      have p1757_1 := h1757c.2.1
                                      have p1757_2 := h1757c.2.2.1
                                      have p1757_3 := h1757c.2.2.2
                                      linarith only [h0, hlam, p1757_1]
                                    · have p1757_0 := h1757c.1
                                      have p1757_1 := h1757c.2.1
                                      have p1757_2 := h1757c.2.2.1
                                      have p1757_3 := h1757c.2.2.2
                                      linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1757_1, u2elo1]
                                    · have p1757_0 := h1757c.1
                                      have p1757_1 := h1757c.2.1
                                      have p1757_2 := h1757c.2.2.1
                                      have p1757_3 := h1757c.2.2.2
                                      linarith only [h0, h1719, h1745, h1751, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1757_1, u2elo1]
                                    · have p1757_0 := h1757c.1
                                      have p1757_1 := h1757c.2.1
                                      have p1757_2 := h1757c.2.2.1
                                      have p1757_3 := h1757c.2.2.2
                                      linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1757_1, u2elo1]
                                    · have p1757_0 := h1757c.1
                                      have p1757_1 := h1757c.2.1
                                      have p1757_2 := h1757c.2.2.1
                                      have p1757_3 := h1757c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, ht12, p1757_1, u2elo1]
                                    · have p1757_0 := h1757c.1
                                      have p1757_1 := h1757c.2.1
                                      have p1757_2 := h1757c.2.2.1
                                      have p1757_3 := h1757c.2.2.2
                                      linarith only [hlam, p1757_0]
                                    · have p1757_0 := h1757c.1
                                      have p1757_1 := h1757c.2.1
                                      have p1757_2 := h1757c.2.2.1
                                      have p1757_3 := h1757c.2.2.2
                                      linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1757_1, u2elo1]
                                    · have p1757_0 := h1757c.1
                                      have p1757_1 := h1757c.2.1
                                      have p1757_2 := h1757c.2.2.1
                                      have p1757_3 := h1757c.2.2.2
                                      linarith only [h0, h1719, h1745, h1751, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1757_1, u2elo1]
                                    · have p1757_0 := h1757c.1
                                      have p1757_1 := h1757c.2.1
                                      have p1757_2 := h1757c.2.2.1
                                      have p1757_3 := h1757c.2.2.2
                                      linarith only [h0, h1720, h1746, h1752, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1757_1, u2elo1]
                                    · have p1757_0 := h1757c.1
                                      have p1757_1 := h1757c.2.1
                                      have p1757_2 := h1757c.2.2.1
                                      have p1757_3 := h1757c.2.2.2
                                      linarith only [h1720, h1745, h1749, h1751, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1757_1]
                                    · have p1757_0 := h1757c.1
                                      have p1757_1 := h1757c.2.1
                                      have p1757_2 := h1757c.2.2.1
                                      have p1757_3 := h1757c.2.2.2
                                      linarith only [h1721, hlam, p1757_1]
                                    · have p1757_0 := h1757c.1
                                      have p1757_1 := h1757c.2.1
                                      have p1757_2 := h1757c.2.2.1
                                      have p1757_3 := h1757c.2.2.2
                                      linarith only [hlam, p1757_0]
                                    · have p1757_0 := h1757c.1
                                      have p1757_1 := h1757c.2.1
                                      have p1757_2 := h1757c.2.2.1
                                      have p1757_3 := h1757c.2.2.2
                                      linarith only [h0, h1719, h1721, h1745, h1751, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1757_1, u2elo1]
                                    · have p1757_0 := h1757c.1
                                      have p1757_1 := h1757c.2.1
                                      have p1757_2 := h1757c.2.2.1
                                      have p1757_3 := h1757c.2.2.2
                                      linarith only [h0, h1719, h1721, h1726, h1745, h1751, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1757_1, u2elo1]
                                    · have p1757_0 := h1757c.1
                                      have p1757_1 := h1757c.2.1
                                      have p1757_2 := h1757c.2.2.1
                                      have p1757_3 := h1757c.2.2.2
                                      linarith only [h1719, hlam, p1757_0]
                                    · have p1757_0 := h1757c.1
                                      have p1757_1 := h1757c.2.1
                                      have p1757_2 := h1757c.2.2.1
                                      have p1757_3 := h1757c.2.2.2
                                      linarith only [h1722, hlam, p1757_0]
                                    · have p1757_0 := h1757c.1
                                      have p1757_1 := h1757c.2.1
                                      have p1757_2 := h1757c.2.2.1
                                      have p1757_3 := h1757c.2.2.2
                                      linarith only [h1724, hlam, p1757_0]
                                    · have p1757_0 := h1757c.1
                                      have p1757_1 := h1757c.2.1
                                      have p1757_2 := h1757c.2.2.1
                                      have p1757_3 := h1757c.2.2.2
                                      linarith only [hlam, p1757_0]
                                    · have p1757_0 := h1757c.1
                                      have p1757_1 := h1757c.2.1
                                      have p1757_2 := h1757c.2.2.1
                                      have p1757_3 := h1757c.2.2.2
                                      linarith only [h1726, hlam, p1757_0]
                                    · have p1757_0 := h1757c.1
                                      have p1757_1 := h1757c.2.1
                                      have p1757_2 := h1757c.2.2.1
                                      have p1757_3 := h1757c.2.2.2
                                      linarith only [h1720, hlam, p1757_0]
                                    · have p1757_0 := h1757c.1
                                      have p1757_1 := h1757c.2.1
                                      have p1757_2 := h1757c.2.2.1
                                      have p1757_3 := h1757c.2.2.2
                                      linarith only [h1723, hlam, p1757_1]
                                    · have p1757_0 := h1757c.1
                                      have p1757_1 := h1757c.2.1
                                      have p1757_2 := h1757c.2.2.1
                                      have p1757_3 := h1757c.2.2.2
                                      linarith only [h1725, hlam, p1757_0]
                                    · have p1757_0 := h1757c.1
                                      have p1757_1 := h1757c.2.1
                                      have p1757_2 := h1757c.2.2.1
                                      have p1757_3 := h1757c.2.2.2
                                      linarith only [h0, h1719, h1720, h1745, h1751, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1757_1, u2elo1]
                                    · have p1757_0 := h1757c.1
                                      have p1757_1 := h1757c.2.1
                                      have p1757_2 := h1757c.2.2.1
                                      have p1757_3 := h1757c.2.2.2
                                      linarith only [hlam, p1757_0]
                              · linarith only [h0, h1720, h1748, h1752, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · linarith only [h0, h1719, h1747, h1751, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h0, h1721, h1725, h1747, h1748, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1786 | h1786
                        · linarith only [h0, h1719, h1747, h1786, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1788 | h1788
                          · linarith only [h0, h1719, h1726, h1788, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1790 | h1790
                            · linarith only [h1744, h1747, h1790, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1792 | h1792
                              · linarith only [h1744, h1786, h1792, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1794 | h1794
                                · linarith only [h1724, h1726, h1744, h1747, h1794, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1796 | h1796
                                  · linarith only [h1724, h1726, h1796, hlam]
                                  · rcases h0bigk with h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c | h1798c
                                    · have p1798_0 := h1798c.1
                                      have p1798_1 := h1798c.2.1
                                      have p1798_2 := h1798c.2.2.1
                                      have p1798_3 := h1798c.2.2.2
                                      linarith only [hlam, p1798_0]
                                    · have p1798_0 := h1798c.1
                                      have p1798_1 := h1798c.2.1
                                      have p1798_2 := h1798c.2.2.1
                                      have p1798_3 := h1798c.2.2.2
                                      linarith only [h0, hlam, p1798_1]
                                    · have p1798_0 := h1798c.1
                                      have p1798_1 := h1798c.2.1
                                      have p1798_2 := h1798c.2.2.1
                                      have p1798_3 := h1798c.2.2.2
                                      linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1798_1, u2elo1]
                                    · have p1798_0 := h1798c.1
                                      have p1798_1 := h1798c.2.1
                                      have p1798_2 := h1798c.2.2.1
                                      have p1798_3 := h1798c.2.2.2
                                      linarith only [h0, h1724, h1744, h1747, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1798_1, u2elo1]
                                    · have p1798_0 := h1798c.1
                                      have p1798_1 := h1798c.2.1
                                      have p1798_2 := h1798c.2.2.1
                                      have p1798_3 := h1798c.2.2.2
                                      linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1798_1, u2elo1]
                                    · have p1798_0 := h1798c.1
                                      have p1798_1 := h1798c.2.1
                                      have p1798_2 := h1798c.2.2.1
                                      have p1798_3 := h1798c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, ht12, p1798_1, u2elo1]
                                    · have p1798_0 := h1798c.1
                                      have p1798_1 := h1798c.2.1
                                      have p1798_2 := h1798c.2.2.1
                                      have p1798_3 := h1798c.2.2.2
                                      linarith only [hlam, p1798_0]
                                    · have p1798_0 := h1798c.1
                                      have p1798_1 := h1798c.2.1
                                      have p1798_2 := h1798c.2.2.1
                                      have p1798_3 := h1798c.2.2.2
                                      linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1798_1, u2elo1]
                                    · have p1798_0 := h1798c.1
                                      have p1798_1 := h1798c.2.1
                                      have p1798_2 := h1798c.2.2.1
                                      have p1798_3 := h1798c.2.2.2
                                      linarith only [h0, h1724, h1744, h1747, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1798_1, u2elo1]
                                    · have p1798_0 := h1798c.1
                                      have p1798_1 := h1798c.2.1
                                      have p1798_2 := h1798c.2.2.1
                                      have p1798_3 := h1798c.2.2.2
                                      linarith only [h0, h1720, h1745, h1788, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1798_1, u2elo1]
                                    · have p1798_0 := h1798c.1
                                      have p1798_1 := h1798c.2.1
                                      have p1798_2 := h1798c.2.2.1
                                      have p1798_3 := h1798c.2.2.2
                                      linarith only [h1720, h1725, h1744, h1747, h1796, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1798_1]
                                    · have p1798_0 := h1798c.1
                                      have p1798_1 := h1798c.2.1
                                      have p1798_2 := h1798c.2.2.1
                                      have p1798_3 := h1798c.2.2.2
                                      linarith only [h1721, hlam, p1798_1]
                                    · have p1798_0 := h1798c.1
                                      have p1798_1 := h1798c.2.1
                                      have p1798_2 := h1798c.2.2.1
                                      have p1798_3 := h1798c.2.2.2
                                      linarith only [hlam, p1798_0]
                                    · have p1798_0 := h1798c.1
                                      have p1798_1 := h1798c.2.1
                                      have p1798_2 := h1798c.2.2.1
                                      have p1798_3 := h1798c.2.2.2
                                      linarith only [h0, h1721, h1724, h1744, h1747, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1798_1, u2elo1]
                                    · have p1798_0 := h1798c.1
                                      have p1798_1 := h1798c.2.1
                                      have p1798_2 := h1798c.2.2.1
                                      have p1798_3 := h1798c.2.2.2
                                      linarith only [h0, h1721, h1725, h1744, h1747, h1796, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1798_1, u2elo1]
                                    · have p1798_0 := h1798c.1
                                      have p1798_1 := h1798c.2.1
                                      have p1798_2 := h1798c.2.2.1
                                      have p1798_3 := h1798c.2.2.2
                                      linarith only [h1719, hlam, p1798_0]
                                    · have p1798_0 := h1798c.1
                                      have p1798_1 := h1798c.2.1
                                      have p1798_2 := h1798c.2.2.1
                                      have p1798_3 := h1798c.2.2.2
                                      linarith only [h1722, hlam, p1798_0]
                                    · have p1798_0 := h1798c.1
                                      have p1798_1 := h1798c.2.1
                                      have p1798_2 := h1798c.2.2.1
                                      have p1798_3 := h1798c.2.2.2
                                      linarith only [h1724, hlam, p1798_0]
                                    · have p1798_0 := h1798c.1
                                      have p1798_1 := h1798c.2.1
                                      have p1798_2 := h1798c.2.2.1
                                      have p1798_3 := h1798c.2.2.2
                                      linarith only [hlam, p1798_0]
                                    · have p1798_0 := h1798c.1
                                      have p1798_1 := h1798c.2.1
                                      have p1798_2 := h1798c.2.2.1
                                      have p1798_3 := h1798c.2.2.2
                                      linarith only [h1726, hlam, p1798_0]
                                    · have p1798_0 := h1798c.1
                                      have p1798_1 := h1798c.2.1
                                      have p1798_2 := h1798c.2.2.1
                                      have p1798_3 := h1798c.2.2.2
                                      linarith only [h1720, hlam, p1798_0]
                                    · have p1798_0 := h1798c.1
                                      have p1798_1 := h1798c.2.1
                                      have p1798_2 := h1798c.2.2.1
                                      have p1798_3 := h1798c.2.2.2
                                      linarith only [h1723, hlam, p1798_1]
                                    · have p1798_0 := h1798c.1
                                      have p1798_1 := h1798c.2.1
                                      have p1798_2 := h1798c.2.2.1
                                      have p1798_3 := h1798c.2.2.2
                                      linarith only [h1725, hlam, p1798_0]
                                    · have p1798_0 := h1798c.1
                                      have p1798_1 := h1798c.2.1
                                      have p1798_2 := h1798c.2.2.1
                                      have p1798_3 := h1798c.2.2.2
                                      linarith only [h1720, h1724, h1744, h1747, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1798_1]
                                    · have p1798_0 := h1798c.1
                                      have p1798_1 := h1798c.2.1
                                      have p1798_2 := h1798c.2.2.1
                                      have p1798_3 := h1798c.2.2.2
                                      linarith only [hlam, p1798_0]
                    · linarith only [h0, h1746, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h1719, h1745, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                · linarith only [h0, h1719, h1744, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1827 | h1827
              · linarith only [h1724, h1725, h1827, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1829 | h1829
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1830 | h1830
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1831 | h1831
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1832 | h1832
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1833 | h1833
                        · linarith only [h1724, h1725, h1829, h1833, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · linarith only [h0, h1720, h1832, h1833, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h1724, h1725, h1832, hc13, hc35, hlam, hphi]
                    · linarith only [h0, h1831, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h1830, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h1720, h1724, h1725, h1829, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1840 | h1840
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1841 | h1841
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1842 | h1842
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1843 | h1843
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1844 | h1844
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1845 | h1845
                      · linarith only [h1724, h1840, h1842, h1845, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1847 | h1847
                        · linarith only [h0, h1719, h1845, h1847, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · linarith only [h1724, h1840, h1847, hc13, hc34, hlam, hphi]
                    · linarith only [h0, h1844, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h1843, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h1719, h1724, h1840, h1842, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
              · linarith only [h1724, h1840, h1841, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1854 | h1854
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1855 | h1855
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1856 | h1856
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1857 | h1857
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1858 | h1858
                      · linarith only [h0, h1719, h1724, h1858, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1860 | h1860
                        · linarith only [h0, h1719, h1721, h1840, h1858, h1860, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1862 | h1862
                          · linarith only [h0, h1719, h1862, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · linarith only [h0, h1719, h1854, h1858, h1862, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1857, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h1856, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h1719, h1854, h1855, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1868 | h1868
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1869 | h1869
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1870 | h1870
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1871 | h1871
                      · linarith only [h0, h1719, h1721, h1724, h1871, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1873 | h1873
                        · linarith only [h0, h1719, h1871, h1873, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1875 | h1875
                          · linarith only [h0, h1719, h1854, h1875, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1877 | h1877
                            · linarith only [h1721, h1871, h1877, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1879 | h1879
                              · linarith only [h0, h1721, h1840, h1879, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1881 | h1881
                                · linarith only [h0, h1720, h1854, h1869, h1875, h1881, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1883 | h1883
                                  · rcases h0bigk with h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c | h1884c
                                    · have p1884_0 := h1884c.1
                                      have p1884_1 := h1884c.2.1
                                      have p1884_2 := h1884c.2.2.1
                                      have p1884_3 := h1884c.2.2.2
                                      linarith only [hlam, p1884_0]
                                    · have p1884_0 := h1884c.1
                                      have p1884_1 := h1884c.2.1
                                      have p1884_2 := h1884c.2.2.1
                                      have p1884_3 := h1884c.2.2.2
                                      linarith only [h0, hlam, p1884_1]
                                    · have p1884_0 := h1884c.1
                                      have p1884_1 := h1884c.2.1
                                      have p1884_2 := h1884c.2.2.1
                                      have p1884_3 := h1884c.2.2.2
                                      linarith only [h0, h1721, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1884_1, u2elo1]
                                    · have p1884_0 := h1884c.1
                                      have p1884_1 := h1884c.2.1
                                      have p1884_2 := h1884c.2.2.1
                                      have p1884_3 := h1884c.2.2.2
                                      linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1884_1, u2elo1]
                                    · have p1884_0 := h1884c.1
                                      have p1884_1 := h1884c.2.1
                                      have p1884_2 := h1884c.2.2.1
                                      have p1884_3 := h1884c.2.2.2
                                      linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1884_1, u2elo1]
                                    · have p1884_0 := h1884c.1
                                      have p1884_1 := h1884c.2.1
                                      have p1884_2 := h1884c.2.2.1
                                      have p1884_3 := h1884c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, ht12, p1884_1, u2elo1]
                                    · have p1884_0 := h1884c.1
                                      have p1884_1 := h1884c.2.1
                                      have p1884_2 := h1884c.2.2.1
                                      have p1884_3 := h1884c.2.2.2
                                      linarith only [hlam, p1884_0]
                                    · have p1884_0 := h1884c.1
                                      have p1884_1 := h1884c.2.1
                                      have p1884_2 := h1884c.2.2.1
                                      have p1884_3 := h1884c.2.2.2
                                      linarith only [h0, h1721, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1884_1, u2elo1]
                                    · have p1884_0 := h1884c.1
                                      have p1884_1 := h1884c.2.1
                                      have p1884_2 := h1884c.2.2.1
                                      have p1884_3 := h1884c.2.2.2
                                      linarith only [h0, h1719, h1871, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1884_1, u2elo1]
                                    · have p1884_0 := h1884c.1
                                      have p1884_1 := h1884c.2.1
                                      have p1884_2 := h1884c.2.2.1
                                      have p1884_3 := h1884c.2.2.2
                                      linarith only [h0, h1720, h1870, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1884_1, u2elo1]
                                    · have p1884_0 := h1884c.1
                                      have p1884_1 := h1884c.2.1
                                      have p1884_2 := h1884c.2.2.1
                                      have p1884_3 := h1884c.2.2.2
                                      linarith only [h1720, h1868, h1871, h1875, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1884_1]
                                    · have p1884_0 := h1884c.1
                                      have p1884_1 := h1884c.2.1
                                      have p1884_2 := h1884c.2.2.1
                                      have p1884_3 := h1884c.2.2.2
                                      linarith only [h1721, hlam, p1884_1]
                                    · have p1884_0 := h1884c.1
                                      have p1884_1 := h1884c.2.1
                                      have p1884_2 := h1884c.2.2.1
                                      have p1884_3 := h1884c.2.2.2
                                      linarith only [hlam, p1884_0]
                                    · have p1884_0 := h1884c.1
                                      have p1884_1 := h1884c.2.1
                                      have p1884_2 := h1884c.2.2.1
                                      have p1884_3 := h1884c.2.2.2
                                      linarith only [h1724, hlam, p1884_1]
                                    · have p1884_0 := h1884c.1
                                      have p1884_1 := h1884c.2.1
                                      have p1884_2 := h1884c.2.2.1
                                      have p1884_3 := h1884c.2.2.2
                                      linarith only [h1840, hlam, p1884_1]
                                    · have p1884_0 := h1884c.1
                                      have p1884_1 := h1884c.2.1
                                      have p1884_2 := h1884c.2.2.1
                                      have p1884_3 := h1884c.2.2.2
                                      linarith only [h1719, hlam, p1884_0]
                                    · have p1884_0 := h1884c.1
                                      have p1884_1 := h1884c.2.1
                                      have p1884_2 := h1884c.2.2.1
                                      have p1884_3 := h1884c.2.2.2
                                      linarith only [h1722, hlam, p1884_0]
                                    · have p1884_0 := h1884c.1
                                      have p1884_1 := h1884c.2.1
                                      have p1884_2 := h1884c.2.2.1
                                      have p1884_3 := h1884c.2.2.2
                                      linarith only [h1854, h1883, hc03, hc34, hlam, hphi, p1884_1]
                                    · have p1884_0 := h1884c.1
                                      have p1884_1 := h1884c.2.1
                                      have p1884_2 := h1884c.2.2.1
                                      have p1884_3 := h1884c.2.2.2
                                      linarith only [hlam, p1884_0]
                                    · have p1884_0 := h1884c.1
                                      have p1884_1 := h1884c.2.1
                                      have p1884_2 := h1884c.2.2.1
                                      have p1884_3 := h1884c.2.2.2
                                      linarith only [h1854, hlam, p1884_0]
                                    · have p1884_0 := h1884c.1
                                      have p1884_1 := h1884c.2.1
                                      have p1884_2 := h1884c.2.2.1
                                      have p1884_3 := h1884c.2.2.2
                                      linarith only [h1720, hlam, p1884_0]
                                    · have p1884_0 := h1884c.1
                                      have p1884_1 := h1884c.2.1
                                      have p1884_2 := h1884c.2.2.1
                                      have p1884_3 := h1884c.2.2.2
                                      linarith only [h1723, hlam, p1884_1]
                                    · have p1884_0 := h1884c.1
                                      have p1884_1 := h1884c.2.1
                                      have p1884_2 := h1884c.2.2.1
                                      have p1884_3 := h1884c.2.2.2
                                      linarith only [h0, h1720, h1721, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1884_1, u2elo1]
                                    · have p1884_0 := h1884c.1
                                      have p1884_1 := h1884c.2.1
                                      have p1884_2 := h1884c.2.2.1
                                      have p1884_3 := h1884c.2.2.2
                                      linarith only [h0, h1720, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1884_1, u2elo1]
                                    · have p1884_0 := h1884c.1
                                      have p1884_1 := h1884c.2.1
                                      have p1884_2 := h1884c.2.2.1
                                      have p1884_3 := h1884c.2.2.2
                                      linarith only [hlam, p1884_0]
                                  · rcases h0bigk with h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c | h1910c
                                    · have p1910_0 := h1910c.1
                                      have p1910_1 := h1910c.2.1
                                      have p1910_2 := h1910c.2.2.1
                                      have p1910_3 := h1910c.2.2.2
                                      linarith only [hlam, p1910_0]
                                    · have p1910_0 := h1910c.1
                                      have p1910_1 := h1910c.2.1
                                      have p1910_2 := h1910c.2.2.1
                                      have p1910_3 := h1910c.2.2.2
                                      linarith only [h0, hlam, p1910_1]
                                    · have p1910_0 := h1910c.1
                                      have p1910_1 := h1910c.2.1
                                      have p1910_2 := h1910c.2.2.1
                                      have p1910_3 := h1910c.2.2.2
                                      linarith only [h0, h1721, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1910_1, u2elo1]
                                    · have p1910_0 := h1910c.1
                                      have p1910_1 := h1910c.2.1
                                      have p1910_2 := h1910c.2.2.1
                                      have p1910_3 := h1910c.2.2.2
                                      linarith only [h0, h1719, h1868, h1871, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1910_1, u2elo1]
                                    · have p1910_0 := h1910c.1
                                      have p1910_1 := h1910c.2.1
                                      have p1910_2 := h1910c.2.2.1
                                      have p1910_3 := h1910c.2.2.2
                                      linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1910_1, u2elo1]
                                    · have p1910_0 := h1910c.1
                                      have p1910_1 := h1910c.2.1
                                      have p1910_2 := h1910c.2.2.1
                                      have p1910_3 := h1910c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, ht12, p1910_1, u2elo1]
                                    · have p1910_0 := h1910c.1
                                      have p1910_1 := h1910c.2.1
                                      have p1910_2 := h1910c.2.2.1
                                      have p1910_3 := h1910c.2.2.2
                                      linarith only [hlam, p1910_0]
                                    · have p1910_0 := h1910c.1
                                      have p1910_1 := h1910c.2.1
                                      have p1910_2 := h1910c.2.2.1
                                      have p1910_3 := h1910c.2.2.2
                                      linarith only [h0, h1721, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1910_1, u2elo1]
                                    · have p1910_0 := h1910c.1
                                      have p1910_1 := h1910c.2.1
                                      have p1910_2 := h1910c.2.2.1
                                      have p1910_3 := h1910c.2.2.2
                                      linarith only [h0, h1719, h1868, h1871, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1910_1, u2elo1]
                                    · have p1910_0 := h1910c.1
                                      have p1910_1 := h1910c.2.1
                                      have p1910_2 := h1910c.2.2.1
                                      have p1910_3 := h1910c.2.2.2
                                      linarith only [h0, h1720, h1868, h1871, h1875, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1910_1, u2elo1]
                                    · have p1910_0 := h1910c.1
                                      have p1910_1 := h1910c.2.1
                                      have p1910_2 := h1910c.2.2.1
                                      have p1910_3 := h1910c.2.2.2
                                      linarith only [h1720, h1868, h1871, h1875, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1910_1]
                                    · have p1910_0 := h1910c.1
                                      have p1910_1 := h1910c.2.1
                                      have p1910_2 := h1910c.2.2.1
                                      have p1910_3 := h1910c.2.2.2
                                      linarith only [h1721, hlam, p1910_1]
                                    · have p1910_0 := h1910c.1
                                      have p1910_1 := h1910c.2.1
                                      have p1910_2 := h1910c.2.2.1
                                      have p1910_3 := h1910c.2.2.2
                                      linarith only [hlam, p1910_0]
                                    · have p1910_0 := h1910c.1
                                      have p1910_1 := h1910c.2.1
                                      have p1910_2 := h1910c.2.2.1
                                      have p1910_3 := h1910c.2.2.2
                                      linarith only [h1724, hlam, p1910_1]
                                    · have p1910_0 := h1910c.1
                                      have p1910_1 := h1910c.2.1
                                      have p1910_2 := h1910c.2.2.1
                                      have p1910_3 := h1910c.2.2.2
                                      linarith only [h1840, hlam, p1910_1]
                                    · have p1910_0 := h1910c.1
                                      have p1910_1 := h1910c.2.1
                                      have p1910_2 := h1910c.2.2.1
                                      have p1910_3 := h1910c.2.2.2
                                      linarith only [h1719, hlam, p1910_0]
                                    · have p1910_0 := h1910c.1
                                      have p1910_1 := h1910c.2.1
                                      have p1910_2 := h1910c.2.2.1
                                      have p1910_3 := h1910c.2.2.2
                                      linarith only [h1722, hlam, p1910_0]
                                    · have p1910_0 := h1910c.1
                                      have p1910_1 := h1910c.2.1
                                      have p1910_2 := h1910c.2.2.1
                                      have p1910_3 := h1910c.2.2.2
                                      linarith only [h0, h1719, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1910_1, u2elo1]
                                    · have p1910_0 := h1910c.1
                                      have p1910_1 := h1910c.2.1
                                      have p1910_2 := h1910c.2.2.1
                                      have p1910_3 := h1910c.2.2.2
                                      linarith only [hlam, p1910_0]
                                    · have p1910_0 := h1910c.1
                                      have p1910_1 := h1910c.2.1
                                      have p1910_2 := h1910c.2.2.1
                                      have p1910_3 := h1910c.2.2.2
                                      linarith only [h1854, hlam, p1910_0]
                                    · have p1910_0 := h1910c.1
                                      have p1910_1 := h1910c.2.1
                                      have p1910_2 := h1910c.2.2.1
                                      have p1910_3 := h1910c.2.2.2
                                      linarith only [h1720, hlam, p1910_0]
                                    · have p1910_0 := h1910c.1
                                      have p1910_1 := h1910c.2.1
                                      have p1910_2 := h1910c.2.2.1
                                      have p1910_3 := h1910c.2.2.2
                                      linarith only [h1723, hlam, p1910_1]
                                    · have p1910_0 := h1910c.1
                                      have p1910_1 := h1910c.2.1
                                      have p1910_2 := h1910c.2.2.1
                                      have p1910_3 := h1910c.2.2.2
                                      linarith only [h0, h1720, h1721, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1910_1, u2elo1]
                                    · have p1910_0 := h1910c.1
                                      have p1910_1 := h1910c.2.1
                                      have p1910_2 := h1910c.2.2.1
                                      have p1910_3 := h1910c.2.2.2
                                      linarith only [h0, h1720, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1910_1, u2elo1]
                                    · have p1910_0 := h1910c.1
                                      have p1910_1 := h1910c.2.1
                                      have p1910_2 := h1910c.2.2.1
                                      have p1910_3 := h1910c.2.2.2
                                      linarith only [hlam, p1910_0]
                    · linarith only [h0, h1870, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h1719, h1869, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                · linarith only [h0, h1719, h1868, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
        · linarith only [h0, h1720, h1723, hlam]
      · linarith only [h0, h1719, h1722, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1941 | h1941
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1942 | h1942
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1943 | h1943
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1944 | h1944
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1945 | h1945
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1946 | h1946
                · linarith only [h0, h1719, h1721, h1945, h1946, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                · linarith only [h0, h1719, h1945, h1946, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1949 | h1949
                · linarith only [h0, h1721, h1949, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h1719, h1949, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · linarith only [h0, h1720, h1721, h1944, hlam]
          · linarith only [h0, h1719, h1721, h1943, hlam]
        · linarith only [h0, h1720, h1942, hlam]
      · linarith only [h0, h1719, h1941, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1956 | h1956
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1957 | h1957
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1958 | h1958
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1959 | h1959
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1960 | h1960
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1961 | h1961
              · linarith only [h1719, h1720, h1961, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1963 | h1963
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1964 | h1964
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1965 | h1965
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1966 | h1966
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1967 | h1967
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1968 | h1968
                          · linarith only [h1719, h1720, h1961, h1963, h1967, h1968, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1970 | h1970
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1971 | h1971
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1972 | h1972
                                · linarith only [h1719, h1720, h1964, h1968, h1972, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1974 | h1974
                                  · linarith only [h1719, h1720, h1964, h1968, h1970, h1974, hlam]
                                  · rcases h0bigk with h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c | h1976c
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [hlam, p1976_0]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [h0, hlam, p1976_1]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [h1720, h1963, h1967, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1976_1, u2elo1]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [h1720, h1963, h1967, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1976_1, u2elo1]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [h1720, hlam, p1976_1]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, ht12, p1976_1, u2elo1]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [hlam, p1976_0]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [h0, h1719, h1720, h1960, h1964, h1970, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1976_1, u2elo1]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [h0, h1719, h1964, h1970, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1976_1, u2elo1]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [h0, h1719, h1720, h1964, h1970, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1976_1, u2elo1]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [h1719, h1964, h1970, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1976_1]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [h1956, hlam, p1976_1]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [hlam, p1976_0]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [h0, h1719, h1956, h1964, h1970, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1976_1, u2elo1]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [h0, h1719, h1720, h1956, h1964, h1970, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1976_1, u2elo1]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [h1719, hlam, p1976_0]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [h1957, hlam, p1976_0]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [h1959, hlam, p1976_0]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [hlam, p1976_0]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [h1961, hlam, p1976_0]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [h1719, h1964, h1970, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p1976_1]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [h1958, hlam, p1976_1]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [h1960, hlam, p1976_0]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [h1719, h1720, h1963, h1964, h1967, h1970, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1976_1, u2elo1]
                                    · have p1976_0 := h1976c.1
                                      have p1976_1 := h1976c.2.1
                                      have p1976_2 := h1976c.2.2.1
                                      have p1976_3 := h1976c.2.2.2
                                      linarith only [hlam, p1976_0]
                              · linarith only [h0, h1956, h1960, h1970, h1971, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · linarith only [h1719, h1720, h1963, h1966, h1967, h1970, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h0, h1956, h1960, h1966, h1967, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2005 | h2005
                        · linarith only [h0, h1719, h1959, h1966, h2005, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · linarith only [h0, h1720, h1956, h1960, h2005, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1958, h1965, hlam]
                  · linarith only [h0, h1964, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h1719, h1963, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2011 | h2011
              · linarith only [h1719, h1720, h2011, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2013 | h2013
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2014 | h2014
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2015 | h2015
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2016 | h2016
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2017 | h2017
                        · linarith only [h1959, h1960, h2013, h2017, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2019 | h2019
                          · linarith only [h1719, h1720, h2011, h2019, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2021 | h2021
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2022 | h2022
                              · linarith only [h1956, h1960, h2022, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2024 | h2024
                                · linarith only [h1720, h2019, h2024, hc01, hlam, hphi, ht12, u2elo3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2026 | h2026
                                  · linarith only [h1719, h1720, h1956, h2019, h2021, h2026, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                  · rcases h0bigk with h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c | h2028c
                                    · have p2028_0 := h2028c.1
                                      have p2028_1 := h2028c.2.1
                                      have p2028_2 := h2028c.2.2.1
                                      have p2028_3 := h2028c.2.2.2
                                      linarith only [hlam, p2028_0]
                                    · have p2028_0 := h2028c.1
                                      have p2028_1 := h2028c.2.1
                                      have p2028_2 := h2028c.2.2.1
                                      have p2028_3 := h2028c.2.2.2
                                      linarith only [h0, hlam, p2028_1]
                                    · have p2028_0 := h2028c.1
                                      have p2028_1 := h2028c.2.1
                                      have p2028_2 := h2028c.2.2.1
                                      have p2028_3 := h2028c.2.2.2
                                      linarith only [h1720, h2015, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2028_1, u2elo1]
                                    · have p2028_0 := h2028c.1
                                      have p2028_1 := h2028c.2.1
                                      have p2028_2 := h2028c.2.2.1
                                      have p2028_3 := h2028c.2.2.2
                                      linarith only [h1720, h2015, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2028_1, u2elo1]
                                    · have p2028_0 := h2028c.1
                                      have p2028_1 := h2028c.2.1
                                      have p2028_2 := h2028c.2.2.1
                                      have p2028_3 := h2028c.2.2.2
                                      linarith only [h1720, hlam, p2028_1]
                                    · have p2028_0 := h2028c.1
                                      have p2028_1 := h2028c.2.1
                                      have p2028_2 := h2028c.2.2.1
                                      have p2028_3 := h2028c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, ht12, p2028_1, u2elo1]
                                    · have p2028_0 := h2028c.1
                                      have p2028_1 := h2028c.2.1
                                      have p2028_2 := h2028c.2.2.1
                                      have p2028_3 := h2028c.2.2.2
                                      linarith only [hlam, p2028_0]
                                    · have p2028_0 := h2028c.1
                                      have p2028_1 := h2028c.2.1
                                      have p2028_2 := h2028c.2.2.1
                                      have p2028_3 := h2028c.2.2.2
                                      linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2028_1, u2elo1]
                                    · have p2028_0 := h2028c.1
                                      have p2028_1 := h2028c.2.1
                                      have p2028_2 := h2028c.2.2.1
                                      have p2028_3 := h2028c.2.2.2
                                      linarith only [h0, h1719, h2014, h2021, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2028_1, u2elo1]
                                    · have p2028_0 := h2028c.1
                                      have p2028_1 := h2028c.2.1
                                      have p2028_2 := h2028c.2.2.1
                                      have p2028_3 := h2028c.2.2.2
                                      linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2028_1, u2elo1]
                                    · have p2028_0 := h2028c.1
                                      have p2028_1 := h2028c.2.1
                                      have p2028_2 := h2028c.2.2.1
                                      have p2028_3 := h2028c.2.2.2
                                      linarith only [h1719, h2014, h2021, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p2028_1]
                                    · have p2028_0 := h2028c.1
                                      have p2028_1 := h2028c.2.1
                                      have p2028_2 := h2028c.2.2.1
                                      have p2028_3 := h2028c.2.2.2
                                      linarith only [h1956, hlam, p2028_1]
                                    · have p2028_0 := h2028c.1
                                      have p2028_1 := h2028c.2.1
                                      have p2028_2 := h2028c.2.2.1
                                      have p2028_3 := h2028c.2.2.2
                                      linarith only [hlam, p2028_0]
                                    · have p2028_0 := h2028c.1
                                      have p2028_1 := h2028c.2.1
                                      have p2028_2 := h2028c.2.2.1
                                      have p2028_3 := h2028c.2.2.2
                                      linarith only [h0, h1719, h1956, h2014, h2021, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2028_1, u2elo1]
                                    · have p2028_0 := h2028c.1
                                      have p2028_1 := h2028c.2.1
                                      have p2028_2 := h2028c.2.2.1
                                      have p2028_3 := h2028c.2.2.2
                                      linarith only [h1960, hlam, p2028_1]
                                    · have p2028_0 := h2028c.1
                                      have p2028_1 := h2028c.2.1
                                      have p2028_2 := h2028c.2.2.1
                                      have p2028_3 := h2028c.2.2.2
                                      linarith only [h1719, hlam, p2028_0]
                                    · have p2028_0 := h2028c.1
                                      have p2028_1 := h2028c.2.1
                                      have p2028_2 := h2028c.2.2.1
                                      have p2028_3 := h2028c.2.2.2
                                      linarith only [h1957, hlam, p2028_0]
                                    · have p2028_0 := h2028c.1
                                      have p2028_1 := h2028c.2.1
                                      have p2028_2 := h2028c.2.2.1
                                      have p2028_3 := h2028c.2.2.2
                                      linarith only [h1959, hlam, p2028_0]
                                    · have p2028_0 := h2028c.1
                                      have p2028_1 := h2028c.2.1
                                      have p2028_2 := h2028c.2.2.1
                                      have p2028_3 := h2028c.2.2.2
                                      linarith only [hlam, p2028_0]
                                    · have p2028_0 := h2028c.1
                                      have p2028_1 := h2028c.2.1
                                      have p2028_2 := h2028c.2.2.1
                                      have p2028_3 := h2028c.2.2.2
                                      linarith only [h2011, hlam, p2028_0]
                                    · have p2028_0 := h2028c.1
                                      have p2028_1 := h2028c.2.1
                                      have p2028_2 := h2028c.2.2.1
                                      have p2028_3 := h2028c.2.2.2
                                      linarith only [h1719, h2014, h2021, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p2028_1]
                                    · have p2028_0 := h2028c.1
                                      have p2028_1 := h2028c.2.1
                                      have p2028_2 := h2028c.2.2.1
                                      have p2028_3 := h2028c.2.2.2
                                      linarith only [h1958, hlam, p2028_1]
                                    · have p2028_0 := h2028c.1
                                      have p2028_1 := h2028c.2.1
                                      have p2028_2 := h2028c.2.2.1
                                      have p2028_3 := h2028c.2.2.2
                                      linarith only [h1720, h2015, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2028_1, u2elo1]
                                    · have p2028_0 := h2028c.1
                                      have p2028_1 := h2028c.2.1
                                      have p2028_2 := h2028c.2.2.1
                                      have p2028_3 := h2028c.2.2.2
                                      linarith only [h1719, h1720, h2014, h2015, h2021, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2028_1, u2elo1]
                                    · have p2028_0 := h2028c.1
                                      have p2028_1 := h2028c.2.1
                                      have p2028_2 := h2028c.2.2.1
                                      have p2028_3 := h2028c.2.2.2
                                      linarith only [hlam, p2028_0]
                            · linarith only [h1959, h1960, h2021, hc23, hc35, hlam, hphi]
                      · linarith only [h1959, h1960, h2013, h2016, hc23, hc35, hlam, hphi]
                    · linarith only [h0, h1958, h2015, hlam]
                  · linarith only [h0, h2014, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h2013, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2059 | h2059
            · linarith only [h1719, h1720, h1959, h2059, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2061 | h2061
              · linarith only [h1719, h1720, h2061, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2063 | h2063
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2064 | h2064
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2065 | h2065
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2066 | h2066
                      · linarith only [h0, h1719, h1956, h1959, h2066, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2068 | h2068
                        · linarith only [h1719, h1720, h2059, h2066, h2068, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2070 | h2070
                          · linarith only [h1719, h1720, h2065, h2070, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2072 | h2072
                            · linarith only [h1956, h1959, h2072, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h2074 | h2074
                              · linarith only [h1720, h2068, h2074, hc01, hlam, hphi, ht12, u2elo2]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h2076 | h2076
                                · linarith only [h1719, h1720, h2064, h2070, h2076, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h2078 | h2078
                                  · linarith only [h1719, h1720, h2063, h2066, h2070, h2078, hc23, hc34, hlam, hphi]
                                  · rcases h0bigk with h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c | h2080c
                                    · have p2080_0 := h2080c.1
                                      have p2080_1 := h2080c.2.1
                                      have p2080_2 := h2080c.2.2.1
                                      have p2080_3 := h2080c.2.2.2
                                      linarith only [hlam, p2080_0]
                                    · have p2080_0 := h2080c.1
                                      have p2080_1 := h2080c.2.1
                                      have p2080_2 := h2080c.2.2.1
                                      have p2080_3 := h2080c.2.2.2
                                      linarith only [h0, hlam, p2080_1]
                                    · have p2080_0 := h2080c.1
                                      have p2080_1 := h2080c.2.1
                                      have p2080_2 := h2080c.2.2.1
                                      have p2080_3 := h2080c.2.2.2
                                      linarith only [h1720, h2065, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2080_1]
                                    · have p2080_0 := h2080c.1
                                      have p2080_1 := h2080c.2.1
                                      have p2080_2 := h2080c.2.2.1
                                      have p2080_3 := h2080c.2.2.2
                                      linarith only [h1720, h2065, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2080_1]
                                    · have p2080_0 := h2080c.1
                                      have p2080_1 := h2080c.2.1
                                      have p2080_2 := h2080c.2.2.1
                                      have p2080_3 := h2080c.2.2.2
                                      linarith only [h1720, hlam, p2080_1]
                                    · have p2080_0 := h2080c.1
                                      have p2080_1 := h2080c.2.1
                                      have p2080_2 := h2080c.2.2.1
                                      have p2080_3 := h2080c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, ht12, p2080_1, u2elo1]
                                    · have p2080_0 := h2080c.1
                                      have p2080_1 := h2080c.2.1
                                      have p2080_2 := h2080c.2.2.1
                                      have p2080_3 := h2080c.2.2.2
                                      linarith only [hlam, p2080_0]
                                    · have p2080_0 := h2080c.1
                                      have p2080_1 := h2080c.2.1
                                      have p2080_2 := h2080c.2.2.1
                                      have p2080_3 := h2080c.2.2.2
                                      linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2080_1, u2elo1]
                                    · have p2080_0 := h2080c.1
                                      have p2080_1 := h2080c.2.1
                                      have p2080_2 := h2080c.2.2.1
                                      have p2080_3 := h2080c.2.2.2
                                      linarith only [h0, h1719, h2063, h2066, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2080_1, u2elo1]
                                    · have p2080_0 := h2080c.1
                                      have p2080_1 := h2080c.2.1
                                      have p2080_2 := h2080c.2.2.1
                                      have p2080_3 := h2080c.2.2.2
                                      linarith only [h0, h1719, h1720, h2063, h2066, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2080_1, u2elo1]
                                    · have p2080_0 := h2080c.1
                                      have p2080_1 := h2080c.2.1
                                      have p2080_2 := h2080c.2.2.1
                                      have p2080_3 := h2080c.2.2.2
                                      linarith only [h1719, h2063, h2066, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2080_1]
                                    · have p2080_0 := h2080c.1
                                      have p2080_1 := h2080c.2.1
                                      have p2080_2 := h2080c.2.2.1
                                      have p2080_3 := h2080c.2.2.2
                                      linarith only [h1956, hlam, p2080_1]
                                    · have p2080_0 := h2080c.1
                                      have p2080_1 := h2080c.2.1
                                      have p2080_2 := h2080c.2.2.1
                                      have p2080_3 := h2080c.2.2.2
                                      linarith only [hlam, p2080_0]
                                    · have p2080_0 := h2080c.1
                                      have p2080_1 := h2080c.2.1
                                      have p2080_2 := h2080c.2.2.1
                                      have p2080_3 := h2080c.2.2.2
                                      linarith only [h1959, hlam, p2080_1]
                                    · have p2080_0 := h2080c.1
                                      have p2080_1 := h2080c.2.1
                                      have p2080_2 := h2080c.2.2.1
                                      have p2080_3 := h2080c.2.2.2
                                      linarith only [h2059, hlam, p2080_1]
                                    · have p2080_0 := h2080c.1
                                      have p2080_1 := h2080c.2.1
                                      have p2080_2 := h2080c.2.2.1
                                      have p2080_3 := h2080c.2.2.2
                                      linarith only [h1719, hlam, p2080_0]
                                    · have p2080_0 := h2080c.1
                                      have p2080_1 := h2080c.2.1
                                      have p2080_2 := h2080c.2.2.1
                                      have p2080_3 := h2080c.2.2.2
                                      linarith only [h1957, hlam, p2080_0]
                                    · have p2080_0 := h2080c.1
                                      have p2080_1 := h2080c.2.1
                                      have p2080_2 := h2080c.2.2.1
                                      have p2080_3 := h2080c.2.2.2
                                      linarith only [h0, h1719, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2080_1, u2elo1]
                                    · have p2080_0 := h2080c.1
                                      have p2080_1 := h2080c.2.1
                                      have p2080_2 := h2080c.2.2.1
                                      have p2080_3 := h2080c.2.2.2
                                      linarith only [hlam, p2080_0]
                                    · have p2080_0 := h2080c.1
                                      have p2080_1 := h2080c.2.1
                                      have p2080_2 := h2080c.2.2.1
                                      have p2080_3 := h2080c.2.2.2
                                      linarith only [h2061, hlam, p2080_0]
                                    · have p2080_0 := h2080c.1
                                      have p2080_1 := h2080c.2.1
                                      have p2080_2 := h2080c.2.2.1
                                      have p2080_3 := h2080c.2.2.2
                                      linarith only [h1719, h2063, h2066, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2080_1]
                                    · have p2080_0 := h2080c.1
                                      have p2080_1 := h2080c.2.1
                                      have p2080_2 := h2080c.2.2.1
                                      have p2080_3 := h2080c.2.2.2
                                      linarith only [h1958, hlam, p2080_1]
                                    · have p2080_0 := h2080c.1
                                      have p2080_1 := h2080c.2.1
                                      have p2080_2 := h2080c.2.2.1
                                      have p2080_3 := h2080c.2.2.2
                                      linarith only [h1720, h1956, h2065, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2080_1, u2elo1]
                                    · have p2080_0 := h2080c.1
                                      have p2080_1 := h2080c.2.1
                                      have p2080_2 := h2080c.2.2.1
                                      have p2080_3 := h2080c.2.2.2
                                      linarith only [h1720, h2065, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2080_1, u2elo1]
                                    · have p2080_0 := h2080c.1
                                      have p2080_1 := h2080c.2.1
                                      have p2080_2 := h2080c.2.2.1
                                      have p2080_3 := h2080c.2.2.2
                                      linarith only [hlam, p2080_0]
                    · linarith only [h0, h1958, h2065, hlam]
                  · linarith only [h0, h2064, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h2063, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2109 | h2109
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2110 | h2110
            · linarith only [h1956, h1958, h2110, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2112 | h2112
              · linarith only [h0, h1719, h1958, h2112, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2114 | h2114
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2115 | h2115
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2116 | h2116
                    · linarith only [h0, h1958, h2116, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1719, h2115, h2116, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                  · linarith only [h0, h2115, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h1719, h1956, h2114, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2121 | h2121
            · linarith only [h1719, h1720, h2109, h2121, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2123 | h2123
              · linarith only [h0, h1719, h1958, h2123, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2125 | h2125
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2126 | h2126
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2127 | h2127
                    · linarith only [h0, h1958, h2127, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1719, h2126, h2127, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                  · linarith only [h0, h2126, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h1719, h2125, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
      · linarith only [h0, h1719, h1957, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2133 | h2133
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2134 | h2134
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2135 | h2135
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2136 | h2136
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2137 | h2137
              · linarith only [h1719, h1720, h2137, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2139 | h2139
                · linarith only [h1719, h1720, h1956, h2134, h2139, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · linarith only [h0, h1719, h2139, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · linarith only [h1956, h2134, h2136, hlam]
          · linarith only [h1719, h1720, h1956, h2134, h2135, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2144 | h2144
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2145 | h2145
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2146 | h2146
              · linarith only [h0, h1719, h2134, h2146, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2148 | h2148
                · linarith only [h0, h1956, h2148, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h1719, h2148, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2151 | h2151
              · linarith only [h1719, h1720, h2151, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2153 | h2153
                · linarith only [h0, h1719, h1956, h2153, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · linarith only [h0, h1719, h2153, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
          · linarith only [h0, h1719, h1956, h2144, hlam]
      · linarith only [h0, h1719, h2133, hlam]

end R2N4
