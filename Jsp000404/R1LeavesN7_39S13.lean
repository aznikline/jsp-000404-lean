import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_39S12

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6948000 in
set_option maxHeartbeats 6948000 in
theorem r1l7_20_12_13_H_I_L_0_L_I_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h3bigk := hb3.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1591 | h1591
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1592 | h1592
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1593 | h1593
      · linarith only [h0, h1593, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1595 | h1595
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1596 | h1596
          · linarith only [h1, h1596, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1598 | h1598
            · linarith only [h1598, h2, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1600 | h1600
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1601 | h1601
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1602 | h1602
                  · linarith only [h0, h1593, h1596, h1600, h1602, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                  · linarith only [h0, h1600, h1602, h3, hc23, hc35, hlam, hphi]
                · linarith only [h1591, h1593, h1595, h1601, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
              · linarith only [h1591, h1593, h1600, hc12, hlam, hphi, u2elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1607 | h1607
          · linarith only [h0, h1592, h1593, h1595, h1607, h3, hc12, hlam, hphi, u2elo4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1609 | h1609
            · linarith only [h0, h1592, h1593, h1609, h3, hc12, hlam, hphi, u2elo4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1611 | h1611
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1612 | h1612
                · linarith only [h1, h1595, h1612, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1614 | h1614
                  · linarith only [h1, h1592, h1593, h1595, h1607, h1614, h3, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h1611, h1614, h3, hc23, hc35, hlam, hphi]
              · linarith only [h0, h1591, h1593, h1611, h3, hc12, hlam, hphi, u2elo4]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1618 | h1618
      · linarith only [h1592, h1618, h2, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1620 | h1620
        · linarith only [h1591, h1592, h1620, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1622 | h1622
          · linarith only [h1591, h1592, h1622, h2, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1624 | h1624
            · linarith only [h1624, h2, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1626 | h1626
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1627 | h1627
                · linarith only [h1, h1620, h1627, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1629 | h1629
                  · linarith only [h0, h1, h1591, h1592, h1622, h1626, h1629, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1626, h1629, h3, hc23, hc35, hlam, hphi]
              · linarith only [h1591, h1592, h1626, hc12, hlam, hphi, u2elo3]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1633 | h1633
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1634 | h1634
      · linarith only [h0, h1591, h1634, h3, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1636 | h1636
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1637 | h1637
          · linarith only [h1, h1637, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1639 | h1639
            · linarith only [h1, h1591, h1633, h1639, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1641 | h1641
              · linarith only [h0, h1591, h1641, h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1643 | h1643
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1644 | h1644
                  · linarith only [h1, h1634, h1637, h1644, h3, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1646 | h1646
                    · linarith only [h1, h1591, h1633, h1639, h1643, h1646, h2, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                    · linarith only [h1, h1643, h1646, h3, hc34, hc45, hlam, hphi]
                · linarith only [h1636, h1637, h1643, hc13, hc35, hlam, hphi]
        · linarith only [h1591, h1633, h1636, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1651 | h1651
      · linarith only [h0, h1591, h1651, h3, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1653 | h1653
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1654 | h1654
          · linarith only [h1, h1654, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1656 | h1656
            · linarith only [h1, h1653, h1656, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1658 | h1658
              · linarith only [h1591, h1658, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1660 | h1660
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1661 | h1661
                  · linarith only [h1, h1654, h1661, h3, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1663 | h1663
                    · linarith only [h1656, h1663, h2, h3, hlam]
                    · linarith only [h1, h1660, h1663, h3, hc34, hc45, hlam, hphi]
                · linarith only [h1653, h1654, h1660, hc13, hc35, hlam, hphi]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1667 | h1667
          · linarith only [h1653, h1667, h2, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1669 | h1669
            · linarith only [h1669, h2, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1671 | h1671
              · linarith only [h0, h1591, h1671, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1673 | h1673
                · linarith only [h1, h1651, h1653, h1673, h3, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1675 | h1675
                  · linarith only [h1, h1667, h1675, h3, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1677 | h1677
                    · linarith only [h1651, h1669, h1677, h2, h3, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1679 | h1679
                      · linarith only [h0, h1591, h1653, h1679, hc12, hlam, hphi, u2elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1681 | h1681
                        · linarith only [h1675, h1681, h3, hc01, hlam, hphi, ht12, u2elo2]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1683 | h1683
                          · linarith only [h1671, h1673, h1677, h1683, h2, h3, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h0, h1591, h1679, h1683, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 6948000 in
set_option maxHeartbeats 6948000 in
theorem r1l7_20_12_13_H_I_L_0_L_I_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h0bigk := hb0.1
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_20_12_13_H_I_L_0_L_I_x0_x0_x0_x0 m hb0 hb2 hb3 h0 h1 h2 h3
  · exact r1l7_20_12_13_H_I_L_0_L_I_x0_x0_x0_x1 m hb0 hb2 hb3 h0 h1 h2 h3

set_option maxHeartbeats 6948000 in
set_option maxHeartbeats 6948000 in
theorem r1l7_20_12_13_H_I_L_0_L_I_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h0bigk := hb0.1
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1686 | h1686
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1687 | h1687
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1688 | h1688
      · linarith only [h0, h1688, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1690 | h1690
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1691 | h1691
          · linarith only [h1, h1691, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1693 | h1693
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1694 | h1694
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1695 | h1695
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1696 | h1696
                  · linarith only [h1, h1691, h1696, h2, hlam]
                  · linarith only [h0, h1695, h1696, h2, hc23, hc34, hlam, hphi]
                · linarith only [h1687, h1695, hc12, hlam, hphi, u2elo0]
              · linarith only [h0, h1687, h1688, h1693, h1694, h2, hc12, hlam, hphi, u2elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1701 | h1701
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1702 | h1702
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1703 | h1703
                  · linarith only [h1, h1691, h1703, h2, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h1702, h1703, h2, hc23, hc34, hlam, hphi]
                · linarith only [h1687, h1688, h1702, hc12, hlam, hphi, u2elo3]
              · linarith only [h0, h1688, h1690, h1701, h2, hc12, hlam, hphi, u2elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1708 | h1708
          · linarith only [h1, h1708, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1710 | h1710
            · linarith only [h1687, h1690, h1710, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1712 | h1712
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1713 | h1713
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1714 | h1714
                  · linarith only [h0, h1708, h1713, h1714, h2, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h1713, h1714, h2, hc23, hc34, hlam, hphi]
                · linarith only [h1687, h1690, h1713, hc12, hlam, hphi, u2elo4]
              · linarith only [h1686, h1712, h2, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1719 | h1719
      · linarith only [h0, h1687, h1719, h2, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1721 | h1721
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1722 | h1722
          · linarith only [h1, h1722, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1724 | h1724
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1725 | h1725
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1726 | h1726
                · linarith only [h1687, h1726, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1728 | h1728
                  · linarith only [h1, h1687, h1721, h1722, h1728, hc01, hc25, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1730 | h1730
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1731 | h1731
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1732 | h1732
                        · linarith only [h1728, h1732, h2, hc01, hlam, hphi, ht12, u2elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1734 | h1734
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1735 | h1735
                            · rcases h0bigk with h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [hlam, p1736_0]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h1721, h1734, h1735, hc01, hc45, hlam, hphi, ht0b, ht5b, p1736_1]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h1687, h1721, h1728, h1734, h1735, h2, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1736_1]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h2, hlam, p1736_1]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h1728, h2, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1736_1]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h0, hlam, p1736_0]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [hlam, p1736_0]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h1687, hlam, p1736_0]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h1719, hlam, p1736_1]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h1686, h1730, h1735, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1736_1, u2elo0]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h1, hlam, p1736_1]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h1, h1728, h2, hc02, hc34, hlam, hphi, ht23, p1736_1]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [hlam, p1736_0]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h1722, hlam, p1736_1]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h1, h1686, h1728, h1730, h1735, h2, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1736_1]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h1719, hc01, hlam, hphi, ht12, p1736_1, u2elo3]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h1719, h1721, h1734, h1735, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1736_1, u2elo3]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h1719, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1736_1, u2elo3]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [hlam, p1736_0]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h1686, h1719, h1730, h1735, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1736_1, u2elo3]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h1686, hlam, p1736_0]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h1721, hlam, p1736_1]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h1724, hlam, p1736_0]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h1725, hlam, p1736_1]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [hlam, p1736_0]
                            · linarith only [h1, h1728, h1730, h1735, h2, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h1, h1730, h1734, h2, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h1, h1731, h2, hc13, hc45, hlam, hphi, ht34]
                    · linarith only [h1, h1719, h1724, h1726, h1730, h2, hc12, hlam, hphi, u2elo3]
              · linarith only [h0, h1721, h1725, h2, hlam]
            · linarith only [h1687, h1721, h1724, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1768 | h1768
          · linarith only [h1, h1768, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1770 | h1770
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1771 | h1771
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1772 | h1772
                · linarith only [h1687, h1772, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1774 | h1774
                  · linarith only [h1, h1768, h1774, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1776 | h1776
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1777 | h1777
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1778 | h1778
                        · linarith only [h1774, h1778, h2, hc01, hlam, hphi, ht12, u2elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1780 | h1780
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1781 | h1781
                            · rcases h0bigk with h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c | h1782c
                              · have p1782_0 := h1782c.1
                                have p1782_1 := h1782c.2.1
                                have p1782_2 := h1782c.2.2.1
                                have p1782_3 := h1782c.2.2.2
                                linarith only [hlam, p1782_0]
                              · have p1782_0 := h1782c.1
                                have p1782_1 := h1782c.2.1
                                have p1782_2 := h1782c.2.2.1
                                have p1782_3 := h1782c.2.2.2
                                linarith only [h0, h1719, h2, hc12, hlam, hphi, p1782_1, u2elo3]
                              · have p1782_0 := h1782c.1
                                have p1782_1 := h1782c.2.1
                                have p1782_2 := h1782c.2.2.1
                                have p1782_3 := h1782c.2.2.2
                                linarith only [h1, h1719, h1776, h1781, h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1782_1, u2elo3]
                              · have p1782_0 := h1782c.1
                                have p1782_1 := h1782c.2.1
                                have p1782_2 := h1782c.2.2.1
                                have p1782_3 := h1782c.2.2.2
                                linarith only [h2, hlam, p1782_1]
                              · have p1782_0 := h1782c.1
                                have p1782_1 := h1782c.2.1
                                have p1782_2 := h1782c.2.2.1
                                have p1782_3 := h1782c.2.2.2
                                linarith only [h0, h1719, h1721, h2, hc12, hlam, hphi, p1782_1, u2elo3]
                              · have p1782_0 := h1782c.1
                                have p1782_1 := h1782c.2.1
                                have p1782_2 := h1782c.2.2.1
                                have p1782_3 := h1782c.2.2.2
                                linarith only [h0, hlam, p1782_0]
                              · have p1782_0 := h1782c.1
                                have p1782_1 := h1782c.2.1
                                have p1782_2 := h1782c.2.2.1
                                have p1782_3 := h1782c.2.2.2
                                linarith only [hlam, p1782_0]
                              · have p1782_0 := h1782c.1
                                have p1782_1 := h1782c.2.1
                                have p1782_2 := h1782c.2.2.1
                                have p1782_3 := h1782c.2.2.2
                                linarith only [h1687, hlam, p1782_0]
                              · have p1782_0 := h1782c.1
                                have p1782_1 := h1782c.2.1
                                have p1782_2 := h1782c.2.2.1
                                have p1782_3 := h1782c.2.2.2
                                linarith only [h1719, hlam, p1782_1]
                              · have p1782_0 := h1782c.1
                                have p1782_1 := h1782c.2.1
                                have p1782_2 := h1782c.2.2.1
                                have p1782_3 := h1782c.2.2.2
                                linarith only [h1721, hlam, p1782_0]
                              · have p1782_0 := h1782c.1
                                have p1782_1 := h1782c.2.1
                                have p1782_2 := h1782c.2.2.1
                                have p1782_3 := h1782c.2.2.2
                                linarith only [h1, hlam, p1782_1]
                              · have p1782_0 := h1782c.1
                                have p1782_1 := h1782c.2.1
                                have p1782_2 := h1782c.2.2.1
                                have p1782_3 := h1782c.2.2.2
                                linarith only [h0, h1, h1719, h2, hc12, hlam, hphi, p1782_1, u2elo3]
                              · have p1782_0 := h1782c.1
                                have p1782_1 := h1782c.2.1
                                have p1782_2 := h1782c.2.2.1
                                have p1782_3 := h1782c.2.2.2
                                linarith only [hlam, p1782_0]
                              · have p1782_0 := h1782c.1
                                have p1782_1 := h1782c.2.1
                                have p1782_2 := h1782c.2.2.1
                                have p1782_3 := h1782c.2.2.2
                                linarith only [h1768, hlam, p1782_1]
                              · have p1782_0 := h1782c.1
                                have p1782_1 := h1782c.2.1
                                have p1782_2 := h1782c.2.2.1
                                have p1782_3 := h1782c.2.2.2
                                linarith only [h0, h1, h1719, h1721, h2, hc12, hlam, hphi, p1782_1, u2elo3]
                              · have p1782_0 := h1782c.1
                                have p1782_1 := h1782c.2.1
                                have p1782_2 := h1782c.2.2.1
                                have p1782_3 := h1782c.2.2.2
                                linarith only [h1719, hc01, hlam, hphi, ht12, p1782_1, u2elo3]
                              · have p1782_0 := h1782c.1
                                have p1782_1 := h1782c.2.1
                                have p1782_2 := h1782c.2.2.1
                                have p1782_3 := h1782c.2.2.2
                                linarith only [h0, h1719, hc12, hlam, hphi, p1782_1, u2elo3]
                              · have p1782_0 := h1782c.1
                                have p1782_1 := h1782c.2.1
                                have p1782_2 := h1782c.2.2.1
                                have p1782_3 := h1782c.2.2.2
                                linarith only [h1, h1719, h1774, h1776, h1781, h2, hc03, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1782_1, u2elo3]
                              · have p1782_0 := h1782c.1
                                have p1782_1 := h1782c.2.1
                                have p1782_2 := h1782c.2.2.1
                                have p1782_3 := h1782c.2.2.2
                                linarith only [hlam, p1782_0]
                              · have p1782_0 := h1782c.1
                                have p1782_1 := h1782c.2.1
                                have p1782_2 := h1782c.2.2.1
                                have p1782_3 := h1782c.2.2.2
                                linarith only [h0, h1719, h1721, hc12, hlam, hphi, p1782_1, u2elo3]
                              · have p1782_0 := h1782c.1
                                have p1782_1 := h1782c.2.1
                                have p1782_2 := h1782c.2.2.1
                                have p1782_3 := h1782c.2.2.2
                                linarith only [h1686, hlam, p1782_0]
                              · have p1782_0 := h1782c.1
                                have p1782_1 := h1782c.2.1
                                have p1782_2 := h1782c.2.2.1
                                have p1782_3 := h1782c.2.2.2
                                linarith only [h0, h1686, h1774, h2, hc12, hc34, hlam, hphi, ht23, p1782_1]
                              · have p1782_0 := h1782c.1
                                have p1782_1 := h1782c.2.1
                                have p1782_2 := h1782c.2.2.1
                                have p1782_3 := h1782c.2.2.2
                                linarith only [h1770, hlam, p1782_0]
                              · have p1782_0 := h1782c.1
                                have p1782_1 := h1782c.2.1
                                have p1782_2 := h1782c.2.2.1
                                have p1782_3 := h1782c.2.2.2
                                linarith only [h1771, hlam, p1782_1]
                              · have p1782_0 := h1782c.1
                                have p1782_1 := h1782c.2.1
                                have p1782_2 := h1782c.2.2.1
                                have p1782_3 := h1782c.2.2.2
                                linarith only [hlam, p1782_0]
                            · linarith only [h1, h1774, h1781, h2, hc13, hc45, hlam, hphi, ht34]
                          · linarith only [h1, h1774, h1776, h1780, h2, hc23, hc34, hlam, hphi]
                      · linarith only [h1, h1777, h2, hc13, hc45, hlam, hphi, ht34]
                    · linarith only [h1, h1770, h1774, h1776, h2, hc13, hc34, hlam, hphi]
              · linarith only [h1, h1770, h1771, h2, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1813 | h1813
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1814 | h1814
                · linarith only [h0, h1687, h1814, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1816 | h1816
                  · linarith only [h1, h1768, h1816, h2, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1818 | h1818
                    · linarith only [h1, h1770, h1818, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1820 | h1820
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1821 | h1821
                        · linarith only [h1816, h1821, h2, hc01, hlam, hphi, ht12, u2elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1823 | h1823
                          · linarith only [h1770, h1821, h1823, hc03, hc34, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1825 | h1825
                            · rcases h0bigk with h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c | h1826c
                              · have p1826_0 := h1826c.1
                                have p1826_1 := h1826c.2.1
                                have p1826_2 := h1826c.2.2.1
                                have p1826_3 := h1826c.2.2.2
                                linarith only [hlam, p1826_0]
                              · have p1826_0 := h1826c.1
                                have p1826_1 := h1826c.2.1
                                have p1826_2 := h1826c.2.2.1
                                have p1826_3 := h1826c.2.2.2
                                linarith only [h0, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1826_1]
                              · have p1826_0 := h1826c.1
                                have p1826_1 := h1826c.2.1
                                have p1826_2 := h1826c.2.2.1
                                have p1826_3 := h1826c.2.2.2
                                linarith only [h1, h1814, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1826_1]
                              · have p1826_0 := h1826c.1
                                have p1826_1 := h1826c.2.1
                                have p1826_2 := h1826c.2.2.1
                                have p1826_3 := h1826c.2.2.2
                                linarith only [h2, hlam, p1826_1]
                              · have p1826_0 := h1826c.1
                                have p1826_1 := h1826c.2.1
                                have p1826_2 := h1826c.2.2.1
                                have p1826_3 := h1826c.2.2.2
                                linarith only [h2, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p1826_1]
                              · have p1826_0 := h1826c.1
                                have p1826_1 := h1826c.2.1
                                have p1826_2 := h1826c.2.2.1
                                have p1826_3 := h1826c.2.2.2
                                linarith only [h0, hlam, p1826_0]
                              · have p1826_0 := h1826c.1
                                have p1826_1 := h1826c.2.1
                                have p1826_2 := h1826c.2.2.1
                                have p1826_3 := h1826c.2.2.2
                                linarith only [hlam, p1826_0]
                              · have p1826_0 := h1826c.1
                                have p1826_1 := h1826c.2.1
                                have p1826_2 := h1826c.2.2.1
                                have p1826_3 := h1826c.2.2.2
                                linarith only [h1687, hlam, p1826_0]
                              · have p1826_0 := h1826c.1
                                have p1826_1 := h1826c.2.1
                                have p1826_2 := h1826c.2.2.1
                                have p1826_3 := h1826c.2.2.2
                                linarith only [h1719, hlam, p1826_1]
                              · have p1826_0 := h1826c.1
                                have p1826_1 := h1826c.2.1
                                have p1826_2 := h1826c.2.2.1
                                have p1826_3 := h1826c.2.2.2
                                linarith only [h1721, hlam, p1826_0]
                              · have p1826_0 := h1826c.1
                                have p1826_1 := h1826c.2.1
                                have p1826_2 := h1826c.2.2.1
                                have p1826_3 := h1826c.2.2.2
                                linarith only [h1, hlam, p1826_1]
                              · have p1826_0 := h1826c.1
                                have p1826_1 := h1826c.2.1
                                have p1826_2 := h1826c.2.2.1
                                have p1826_3 := h1826c.2.2.2
                                linarith only [h0, h1, h1719, h2, hc12, hlam, hphi, p1826_1, u2elo3]
                              · have p1826_0 := h1826c.1
                                have p1826_1 := h1826c.2.1
                                have p1826_2 := h1826c.2.2.1
                                have p1826_3 := h1826c.2.2.2
                                linarith only [hlam, p1826_0]
                              · have p1826_0 := h1826c.1
                                have p1826_1 := h1826c.2.1
                                have p1826_2 := h1826c.2.2.1
                                have p1826_3 := h1826c.2.2.2
                                linarith only [h1768, hlam, p1826_1]
                              · have p1826_0 := h1826c.1
                                have p1826_1 := h1826c.2.1
                                have p1826_2 := h1826c.2.2.1
                                have p1826_3 := h1826c.2.2.2
                                linarith only [h1770, hlam, p1826_1]
                              · have p1826_0 := h1826c.1
                                have p1826_1 := h1826c.2.1
                                have p1826_2 := h1826c.2.2.1
                                have p1826_3 := h1826c.2.2.2
                                linarith only [h1719, hc01, hlam, hphi, ht12, p1826_1, u2elo3]
                              · have p1826_0 := h1826c.1
                                have p1826_1 := h1826c.2.1
                                have p1826_2 := h1826c.2.2.1
                                have p1826_3 := h1826c.2.2.2
                                linarith only [h0, h1719, hc12, hlam, hphi, p1826_1, u2elo3]
                              · have p1826_0 := h1826c.1
                                have p1826_1 := h1826c.2.1
                                have p1826_2 := h1826c.2.2.1
                                have p1826_3 := h1826c.2.2.2
                                linarith only [h1719, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1826_1, u2elo3]
                              · have p1826_0 := h1826c.1
                                have p1826_1 := h1826c.2.1
                                have p1826_2 := h1826c.2.2.1
                                have p1826_3 := h1826c.2.2.2
                                linarith only [hlam, p1826_0]
                              · have p1826_0 := h1826c.1
                                have p1826_1 := h1826c.2.1
                                have p1826_2 := h1826c.2.2.1
                                have p1826_3 := h1826c.2.2.2
                                linarith only [h1686, h1719, h1814, h1818, hc12, hlam, hphi, p1826_1, u2elo3]
                              · have p1826_0 := h1826c.1
                                have p1826_1 := h1826c.2.1
                                have p1826_2 := h1826c.2.2.1
                                have p1826_3 := h1826c.2.2.2
                                linarith only [h1686, hlam, p1826_0]
                              · have p1826_0 := h1826c.1
                                have p1826_1 := h1826c.2.1
                                have p1826_2 := h1826c.2.2.1
                                have p1826_3 := h1826c.2.2.2
                                linarith only [h0, h1686, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1826_1]
                              · have p1826_0 := h1826c.1
                                have p1826_1 := h1826c.2.1
                                have p1826_2 := h1826c.2.2.1
                                have p1826_3 := h1826c.2.2.2
                                linarith only [h1, h1686, h1719, h1814, h2, hc12, hlam, hphi, p1826_1, u2elo3]
                              · have p1826_0 := h1826c.1
                                have p1826_1 := h1826c.2.1
                                have p1826_2 := h1826c.2.2.1
                                have p1826_3 := h1826c.2.2.2
                                linarith only [h1813, hlam, p1826_1]
                              · have p1826_0 := h1826c.1
                                have p1826_1 := h1826c.2.1
                                have p1826_2 := h1826c.2.2.1
                                have p1826_3 := h1826c.2.2.2
                                linarith only [hlam, p1826_0]
                            · linarith only [h0, h1816, h1825, h2, hc12, hc45, hlam, hphi, ht23, ht34]
                      · linarith only [h1686, h1719, h1813, h1814, h1818, h1820, h2, hc12, hlam, hphi, u2elo3]
              · linarith only [h1686, h1813, h2, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1855 | h1855
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1856 | h1856
      · linarith only [h0, h1856, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1858 | h1858
        · linarith only [h0, h1686, h1858, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1860 | h1860
          · linarith only [h1, h1860, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1862 | h1862
            · linarith only [h0, h1686, h1855, h1856, h1862, hc12, hlam, hphi, u2elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1864 | h1864
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1865 | h1865
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1866 | h1866
                  · linarith only [h0, h1, h1686, h1855, h1860, h1864, h1865, h1866, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · linarith only [h0, h1865, h1866, h2, hc23, hc34, hlam, hphi]
                · linarith only [h1855, h1856, h1865, hc12, hlam, hphi, u2elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1870 | h1870
                · linarith only [h0, h1864, h1870, h2, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h1855, h1856, h1870, hc12, hlam, hphi, u2elo3]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1873 | h1873
      · linarith only [h0, h1855, h1873, h2, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1875 | h1875
        · linarith only [h1, h1686, h1855, h1875, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1877 | h1877
          · linarith only [h1, h1877, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1879 | h1879
            · linarith only [h1, h1686, h1879, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1881 | h1881
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1882 | h1882
                · linarith only [h0, h1855, h1882, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1884 | h1884
                  · linarith only [h1, h1686, h1873, h1877, h1881, h1884, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1886 | h1886
                    · linarith only [h1, h1686, h1879, h1886, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1888 | h1888
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1889 | h1889
                        · linarith only [h1686, h1884, h1888, h1889, hc01, hlam, hphi, ht12, u2elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1891 | h1891
                          · linarith only [h1, h1686, h1882, h1886, h1891, hc12, hlam, hphi, u2elo2]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1893 | h1893
                            · rcases h0bigk with h1894c | h1894c | h1894c | h1894c | h1894c | h1894c | h1894c | h1894c | h1894c | h1894c | h1894c | h1894c | h1894c | h1894c | h1894c | h1894c | h1894c | h1894c | h1894c | h1894c | h1894c | h1894c | h1894c | h1894c | h1894c
                              · have p1894_0 := h1894c.1
                                have p1894_1 := h1894c.2.1
                                have p1894_2 := h1894c.2.2.1
                                have p1894_3 := h1894c.2.2.2
                                linarith only [hlam, p1894_0]
                              · have p1894_0 := h1894c.1
                                have p1894_1 := h1894c.2.1
                                have p1894_2 := h1894c.2.2.1
                                have p1894_3 := h1894c.2.2.2
                                linarith only [h0, h1686, h1888, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1894_1]
                              · have p1894_0 := h1894c.1
                                have p1894_1 := h1894c.2.1
                                have p1894_2 := h1894c.2.2.1
                                have p1894_3 := h1894c.2.2.2
                                linarith only [h0, h1686, h1855, h1888, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1894_1]
                              · have p1894_0 := h1894c.1
                                have p1894_1 := h1894c.2.1
                                have p1894_2 := h1894c.2.2.1
                                have p1894_3 := h1894c.2.2.2
                                linarith only [h2, hlam, p1894_1]
                              · have p1894_0 := h1894c.1
                                have p1894_1 := h1894c.2.1
                                have p1894_2 := h1894c.2.2.1
                                have p1894_3 := h1894c.2.2.2
                                linarith only [h1686, hlam, p1894_1]
                              · have p1894_0 := h1894c.1
                                have p1894_1 := h1894c.2.1
                                have p1894_2 := h1894c.2.2.1
                                have p1894_3 := h1894c.2.2.2
                                linarith only [h0, hlam, p1894_0]
                              · have p1894_0 := h1894c.1
                                have p1894_1 := h1894c.2.1
                                have p1894_2 := h1894c.2.2.1
                                have p1894_3 := h1894c.2.2.2
                                linarith only [hlam, p1894_0]
                              · have p1894_0 := h1894c.1
                                have p1894_1 := h1894c.2.1
                                have p1894_2 := h1894c.2.2.1
                                have p1894_3 := h1894c.2.2.2
                                linarith only [h1855, hlam, p1894_0]
                              · have p1894_0 := h1894c.1
                                have p1894_1 := h1894c.2.1
                                have p1894_2 := h1894c.2.2.1
                                have p1894_3 := h1894c.2.2.2
                                linarith only [h1873, hlam, p1894_1]
                              · have p1894_0 := h1894c.1
                                have p1894_1 := h1894c.2.1
                                have p1894_2 := h1894c.2.2.1
                                have p1894_3 := h1894c.2.2.2
                                linarith only [h1875, hlam, p1894_0]
                              · have p1894_0 := h1894c.1
                                have p1894_1 := h1894c.2.1
                                have p1894_2 := h1894c.2.2.1
                                have p1894_3 := h1894c.2.2.2
                                linarith only [h1, hlam, p1894_1]
                              · have p1894_0 := h1894c.1
                                have p1894_1 := h1894c.2.1
                                have p1894_2 := h1894c.2.2.1
                                have p1894_3 := h1894c.2.2.2
                                linarith only [h0, h1, h1686, h1888, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1894_1]
                              · have p1894_0 := h1894c.1
                                have p1894_1 := h1894c.2.1
                                have p1894_2 := h1894c.2.2.1
                                have p1894_3 := h1894c.2.2.2
                                linarith only [hlam, p1894_0]
                              · have p1894_0 := h1894c.1
                                have p1894_1 := h1894c.2.1
                                have p1894_2 := h1894c.2.2.1
                                have p1894_3 := h1894c.2.2.2
                                linarith only [h1877, hlam, p1894_1]
                              · have p1894_0 := h1894c.1
                                have p1894_1 := h1894c.2.1
                                have p1894_2 := h1894c.2.2.1
                                have p1894_3 := h1894c.2.2.2
                                linarith only [h1879, hlam, p1894_1]
                              · have p1894_0 := h1894c.1
                                have p1894_1 := h1894c.2.1
                                have p1894_2 := h1894c.2.2.1
                                have p1894_3 := h1894c.2.2.2
                                linarith only [h1873, hc01, hlam, hphi, ht12, p1894_1, u2elo3]
                              · have p1894_0 := h1894c.1
                                have p1894_1 := h1894c.2.1
                                have p1894_2 := h1894c.2.2.1
                                have p1894_3 := h1894c.2.2.2
                                linarith only [h0, h1873, hc12, hlam, hphi, p1894_1, u2elo3]
                              · have p1894_0 := h1894c.1
                                have p1894_1 := h1894c.2.1
                                have p1894_2 := h1894c.2.2.1
                                have p1894_3 := h1894c.2.2.2
                                linarith only [h1873, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1894_1, u2elo3]
                              · have p1894_0 := h1894c.1
                                have p1894_1 := h1894c.2.1
                                have p1894_2 := h1894c.2.2.1
                                have p1894_3 := h1894c.2.2.2
                                linarith only [hlam, p1894_0]
                              · have p1894_0 := h1894c.1
                                have p1894_1 := h1894c.2.1
                                have p1894_2 := h1894c.2.2.1
                                have p1894_3 := h1894c.2.2.2
                                linarith only [h1873, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1894_1, u2elo3]
                              · have p1894_0 := h1894c.1
                                have p1894_1 := h1894c.2.1
                                have p1894_2 := h1894c.2.2.1
                                have p1894_3 := h1894c.2.2.2
                                linarith only [h1, h1882, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1894_1]
                              · have p1894_0 := h1894c.1
                                have p1894_1 := h1894c.2.1
                                have p1894_2 := h1894c.2.2.1
                                have p1894_3 := h1894c.2.2.2
                                linarith only [h0, h1875, hc12, hlam, hphi, p1894_1, u2elo4]
                              · have p1894_0 := h1894c.1
                                have p1894_1 := h1894c.2.1
                                have p1894_2 := h1894c.2.2.1
                                have p1894_3 := h1894c.2.2.2
                                linarith only [h1, h1875, h1882, hc12, hlam, hphi, p1894_1, u2elo4]
                              · have p1894_0 := h1894c.1
                                have p1894_1 := h1894c.2.1
                                have p1894_2 := h1894c.2.2.1
                                have p1894_3 := h1894c.2.2.2
                                linarith only [h1881, hlam, p1894_1]
                              · have p1894_0 := h1894c.1
                                have p1894_1 := h1894c.2.1
                                have p1894_2 := h1894c.2.2.1
                                have p1894_3 := h1894c.2.2.2
                                linarith only [hlam, p1894_0]
                            · linarith only [h1, h1873, h1881, h1882, h1884, h1893, h2, hc12, hlam, hphi, u2elo3]
                      · linarith only [h1, h1873, h1881, h1882, h1888, h2, hc12, hlam, hphi, u2elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1922 | h1922
                · linarith only [h0, h1855, h1922, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1924 | h1924
                  · linarith only [h1, h1881, h1924, h2, hc34, hc45, hlam, hphi]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1926 | h1926
                    · linarith only [h1, h1879, h1926, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1928 | h1928
                      · linarith only [h1, h1881, h1924, h1928, h2, hc13, hc34, hlam, hphi]
                      · linarith only [h1, h1922, h1928, h2, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 6948000 in
set_option maxHeartbeats 6948000 in
theorem r1l7_20_12_13_H_I_L_0_L_I_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h0bigk := hb0.1
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_20_12_13_H_I_L_0_L_I_x0_x0_x0 m hb0 hb2 hb3 h0 h1 h2
  · exact r1l7_20_12_13_H_I_L_0_L_I_x0_x0_x1 m hb0 hb2 hb3 h0 h1 h2

set_option maxHeartbeats 6948000 in
set_option maxHeartbeats 6948000 in
theorem r1l7_20_12_13_H_I_L_0_L_I_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1931 | h1931
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1932 | h1932
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1933 | h1933
      · linarith only [h0, h1, h1933, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1935 | h1935
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1936 | h1936
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1937 | h1937
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1938 | h1938
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1939 | h1939
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1940 | h1940
                  · linarith only [h1933, h1935, h1940, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h1, h1940, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1943 | h1943
                  · linarith only [h0, h1, h1933, h1943, hlam]
                  · linarith only [h0, h1, h1943, hc12, hlam, hphi, u2elo2]
              · linarith only [h1, h1932, h1938, hlam]
            · linarith only [h1, h1931, h1937, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1948 | h1948
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1949 | h1949
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1950 | h1950
                · linarith only [h1935, h1936, h1950, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1952 | h1952
                  · linarith only [h0, h1933, h1952, hlam]
                  · linarith only [h0, h1, h1952, hc12, hlam, hphi, u2elo2]
              · linarith only [h1, h1932, h1949, hlam]
            · linarith only [h0, h1, h1935, h1936, h1948, hc12, hlam, hphi, u2elo4]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1957 | h1957
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1958 | h1958
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1959 | h1959
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1960 | h1960
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1961 | h1961
                  · linarith only [h0, h1, h1933, h1961, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h0, h1, h1961, hc12, hlam, hphi, u2elo2]
                · linarith only [h1935, h1957, h1960, hlam]
              · linarith only [h0, h1, h1957, h1959, hlam]
            · linarith only [h1, h1931, h1958, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1967 | h1967
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1968 | h1968
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1969 | h1969
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1970 | h1970
                  · linarith only [h0, h1, h1933, h1970, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h0, h1, h1970, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1973 | h1973
                  · linarith only [h0, h1, h1933, h1973, hlam]
                  · linarith only [h0, h1, h1973, hc12, hlam, hphi, u2elo2]
              · linarith only [h1, h1932, h1968, hlam]
            · linarith only [h1, h1931, h1967, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1978 | h1978
      · linarith only [h0, h1, h1978, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1980 | h1980
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1981 | h1981
          · linarith only [h0, h1932, h1981, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1983 | h1983
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1984 | h1984
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1985 | h1985
                · linarith only [h0, h1932, h1980, h1985, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1987 | h1987
                  · linarith only [h0, h1, h1978, h1987, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h0, h1, h1987, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1990 | h1990
                · linarith only [h0, h1, h1980, h1984, h1990, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1992 | h1992
                  · linarith only [h0, h1, h1984, h1992, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h1, h1992, hc12, hlam, hphi, u2elo2]
            · linarith only [h0, h1, h1980, h1981, h1983, hc12, hlam, hphi, u2elo4]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1996 | h1996
          · linarith only [h1931, h1932, h1980, h1996, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1998 | h1998
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1999 | h1999
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2000 | h2000
                · linarith only [h1931, h1932, h2000, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2002 | h2002
                  · linarith only [h0, h1, h1978, h2002, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h0, h1, h2002, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2005 | h2005
                · linarith only [h1, h1931, h1999, h2005, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2007 | h2007
                  · linarith only [h0, h1, h1999, h2007, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h1, h2007, hc12, hlam, hphi, u2elo2]
            · linarith only [h1, h1931, h1998, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2011 | h2011
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2012 | h2012
      · linarith only [h0, h1, h2012, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2014 | h2014
        · linarith only [h0, h1931, h2014, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2016 | h2016
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2017 | h2017
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2018 | h2018
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2019 | h2019
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2020 | h2020
                  · linarith only [h0, h1, h2012, h2020, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h0, h1, h2020, hc12, hlam, hphi, u2elo2]
                · linarith only [h0, h1931, h2016, h2019, hlam]
              · linarith only [h0, h1, h2016, h2018, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2025 | h2025
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2026 | h2026
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2027 | h2027
                  · linarith only [h0, h1, h2017, h2027, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h1, h2027, hc12, hlam, hphi, u2elo2]
                · linarith only [h0, h1, h2014, h2016, h2017, h2026, hc12, hlam, hphi, u2elo3]
              · linarith only [h0, h1, h2014, h2016, h2025, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2032 | h2032
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2033 | h2033
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2034 | h2034
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2035 | h2035
                  · linarith only [h0, h1, h2012, h2035, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h0, h1, h2035, hc12, hlam, hphi, u2elo2]
                · linarith only [h1931, h2011, h2034, hlam]
              · linarith only [h1, h2011, h2033, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2040 | h2040
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2041 | h2041
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2042 | h2042
                  · linarith only [h0, h1, h2032, h2042, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h1, h2042, hc12, hlam, hphi, u2elo2]
                · linarith only [h1, h2011, h2032, h2041, hlam]
              · linarith only [h1, h2011, h2040, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2047 | h2047
      · linarith only [h0, h1, h2047, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2049 | h2049
        · linarith only [h0, h1931, h2049, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2051 | h2051
          · linarith only [h0, h2011, h2051, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2053 | h2053
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2054 | h2054
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2055 | h2055
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2056 | h2056
                  · linarith only [h0, h1, h2047, h2056, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h0, h1, h2056, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2059 | h2059
                  · linarith only [h0, h1, h2047, h2053, h2059, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h0, h1, h2059, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2062 | h2062
                · linarith only [h2053, h2054, h2062, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2064 | h2064
                  · linarith only [h0, h1931, h2053, h2054, h2064, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h1, h2064, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2067 | h2067
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2068 | h2068
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2069 | h2069
                  · linarith only [h0, h2011, h2053, h2067, h2069, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h1, h2069, hc12, hlam, hphi, u2elo2]
                · linarith only [h2053, h2067, h2068, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2073 | h2073
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2074 | h2074
                  · linarith only [h0, h1, h2053, h2074, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h1, h2074, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2077 | h2077
                  · linarith only [h0, h1, h2053, h2077, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h1, h2077, hc12, hlam, hphi, u2elo2]

set_option maxHeartbeats 6948000 in
set_option maxHeartbeats 6948000 in
theorem r1l7_20_12_13_H_I_L_0_L_I_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h3bigk := hb3.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_20_12_13_H_I_L_0_L_I_x0_x0 m hb0 hb2 hb3 h0 h1
  · exact r1l7_20_12_13_H_I_L_0_L_I_x0_x1 m hb0 hb2 hb3 h0 h1

end R2N4
