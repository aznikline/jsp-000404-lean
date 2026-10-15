import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5360000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s6_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h1617 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 4 5 (by decide) (by decide) with h1618 | h1618
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1619 | h1619
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1620 | h1620
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1621 | h1621
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1622 | h1622
          · linarith only [h1, h1617, h1622, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1624 | h1624
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1625 | h1625
              · linarith only [h1, h1619, h1624, h1625, h7, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1627 | h1627
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1628 | h1628
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1629 | h1629
                    · rcases h0bigk with h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c | h1630c
                      · have p1630_0 := h1630c.1
                        have p1630_1 := h1630c.2.1
                        have p1630_2 := h1630c.2.2.1
                        have p1630_3 := h1630c.2.2.2
                        linarith only [hlam, p1630_0]
                      · have p1630_0 := h1630c.1
                        have p1630_1 := h1630c.2.1
                        have p1630_2 := h1630c.2.2.1
                        have p1630_3 := h1630c.2.2.2
                        linarith only [h1627, h1629, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p1630_1]
                      · have p1630_0 := h1630c.1
                        have p1630_1 := h1630c.2.1
                        have p1630_2 := h1630c.2.2.1
                        have p1630_3 := h1630c.2.2.2
                        linarith only [h1, h1619, h1627, h1629, hc01, hc45, hlam, hphi, ht0b, ht5b, p1630_1]
                      · have p1630_0 := h1630c.1
                        have p1630_1 := h1630c.2.1
                        have p1630_2 := h1630c.2.2.1
                        have p1630_3 := h1630c.2.2.2
                        linarith only [h1, h1619, h1627, h1629, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p1630_1]
                      · have p1630_0 := h1630c.1
                        have p1630_1 := h1630c.2.1
                        have p1630_2 := h1630c.2.2.1
                        have p1630_3 := h1630c.2.2.2
                        rcases p1630_3 (m.d 0 1) (by simp) with h1635 | h1635
                        · rcases p1630_3 (m.d 0 2) (by simp) with h1636 | h1636
                          · linarith only [h0, h1636, hlam]
                          · linarith only [h1636, h6, hlam]
                        · linarith only [h1635, h3, hlam]
                      · have p1630_0 := h1630c.1
                        have p1630_1 := h1630c.2.1
                        have p1630_2 := h1630c.2.2.1
                        have p1630_3 := h1630c.2.2.2
                        linarith only [h0, hlam, p1630_0]
                      · have p1630_0 := h1630c.1
                        have p1630_1 := h1630c.2.1
                        have p1630_2 := h1630c.2.2.1
                        have p1630_3 := h1630c.2.2.2
                        linarith only [hlam, p1630_0]
                      · have p1630_0 := h1630c.1
                        have p1630_1 := h1630c.2.1
                        have p1630_2 := h1630c.2.2.1
                        have p1630_3 := h1630c.2.2.2
                        linarith only [h1, h1619, h1627, h1629, hc02, hc45, hlam, hphi, ht0b, ht5b, p1630_1]
                      · have p1630_0 := h1630c.1
                        have p1630_1 := h1630c.2.1
                        have p1630_2 := h1630c.2.2.1
                        have p1630_3 := h1630c.2.2.2
                        linarith only [h0, h1, h1619, h1627, h1629, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p1630_1]
                      · have p1630_0 := h1630c.1
                        have p1630_1 := h1630c.2.1
                        have p1630_2 := h1630c.2.2.1
                        have p1630_3 := h1630c.2.2.2
                        rcases p1630_3 (m.d 0 1) (by simp) with h1644 | h1644
                        · rcases p1630_3 (m.d 0 2) (by simp) with h1645 | h1645
                          · rcases p1630_3 (m.d 0 3) (by simp) with h1646 | h1646
                            · linarith only [h1646, h4, hlam]
                            · linarith only [h1617, h1646, hlam]
                          · linarith only [h1645, h6, hlam]
                        · linarith only [h1644, h3, hlam]
                      · have p1630_0 := h1630c.1
                        have p1630_1 := h1630c.2.1
                        have p1630_2 := h1630c.2.2.1
                        have p1630_3 := h1630c.2.2.2
                        linarith only [h1, hlam, p1630_1]
                      · have p1630_0 := h1630c.1
                        have p1630_1 := h1630c.2.1
                        have p1630_2 := h1630c.2.2.1
                        have p1630_3 := h1630c.2.2.2
                        linarith only [h4, hlam, p1630_1]
                      · have p1630_0 := h1630c.1
                        have p1630_1 := h1630c.2.1
                        have p1630_2 := h1630c.2.2.1
                        have p1630_3 := h1630c.2.2.2
                        linarith only [hlam, p1630_0]
                      · have p1630_0 := h1630c.1
                        have p1630_1 := h1630c.2.1
                        have p1630_2 := h1630c.2.2.1
                        have p1630_3 := h1630c.2.2.2
                        linarith only [h7, hlam, p1630_1]
                      · have p1630_0 := h1630c.1
                        have p1630_1 := h1630c.2.1
                        have p1630_2 := h1630c.2.2.1
                        have p1630_3 := h1630c.2.2.2
                        linarith only [h1621, h3, h7, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1630_1]
                      · have p1630_0 := h1630c.1
                        have p1630_1 := h1630c.2.1
                        have p1630_2 := h1630c.2.2.1
                        have p1630_3 := h1630c.2.2.2
                        linarith only [h2, hlam, p1630_0]
                      · have p1630_0 := h1630c.1
                        have p1630_1 := h1630c.2.1
                        have p1630_2 := h1630c.2.2.1
                        have p1630_3 := h1630c.2.2.2
                        linarith only [h5, hlam, p1630_0]
                      · have p1630_0 := h1630c.1
                        have p1630_1 := h1630c.2.1
                        have p1630_2 := h1630c.2.2.1
                        have p1630_3 := h1630c.2.2.2
                        linarith only [h1627, h2, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p1630_1]
                      · have p1630_0 := h1630c.1
                        have p1630_1 := h1630c.2.1
                        have p1630_2 := h1630c.2.2.1
                        have p1630_3 := h1630c.2.2.2
                        linarith only [hlam, p1630_0]
                      · have p1630_0 := h1630c.1
                        have p1630_1 := h1630c.2.1
                        have p1630_2 := h1630c.2.2.1
                        have p1630_3 := h1630c.2.2.2
                        rcases p1630_3 (m.d 0 1) (by simp) with h1660 | h1660
                        · rcases p1630_3 (m.d 0 2) (by simp) with h1661 | h1661
                          · rcases p1630_3 (m.d 0 3) (by simp) with h1662 | h1662
                            · linarith only [h1662, h7, hlam]
                            · linarith only [h1617, h1662, hlam]
                          · linarith only [h1661, h6, hlam]
                        · linarith only [h1660, h3, hlam]
                      · have p1630_0 := h1630c.1
                        have p1630_1 := h1630c.2.1
                        have p1630_2 := h1630c.2.2.1
                        have p1630_3 := h1630c.2.2.2
                        linarith only [h3, hlam, p1630_0]
                      · have p1630_0 := h1630c.1
                        have p1630_1 := h1630c.2.1
                        have p1630_2 := h1630c.2.2.1
                        have p1630_3 := h1630c.2.2.2
                        linarith only [h6, hlam, p1630_1]
                      · have p1630_0 := h1630c.1
                        have p1630_1 := h1630c.2.1
                        have p1630_2 := h1630c.2.2.1
                        have p1630_3 := h1630c.2.2.2
                        linarith only [h1617, hlam, p1630_0]
                      · have p1630_0 := h1630c.1
                        have p1630_1 := h1630c.2.1
                        have p1630_2 := h1630c.2.2.1
                        have p1630_3 := h1630c.2.2.2
                        linarith only [h1618, hlam, p1630_1]
                      · have p1630_0 := h1630c.1
                        have p1630_1 := h1630c.2.1
                        have p1630_2 := h1630c.2.2.1
                        have p1630_3 := h1630c.2.2.2
                        linarith only [hlam, p1630_0]
                    · linarith only [h1618, h1629, h7, hlam]
                  · linarith only [h1625, h1627, h1628, hlam]
                · linarith only [h1617, h1627, h7, hc23, hc34, hlam, hphi]
            · linarith only [h1617, h1624, h7, hc13, hc34, hlam, hphi]
        · linarith only [h1617, h1619, h1621, h6, h7, hc23, hc34, hlam, hphi]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1677 | h1677
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1678 | h1678
          · linarith only [h1, h1617, h1678, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1680 | h1680
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1681 | h1681
              · linarith only [h1619, h1620, h1681, h5, h7, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1683 | h1683
                · linarith only [h0, h1619, h1620, h1683, h5, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · linarith only [h1, h1680, h1683, h7, hc23, hc34, hlam, hphi]
            · linarith only [h1617, h1680, h7, hc13, hc34, hlam, hphi]
        · linarith only [h1617, h1619, h1677, h6, h7, hc23, hc34, hlam, hphi]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1688 | h1688
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1689 | h1689
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1690 | h1690
          · linarith only [h1619, h1690, h4, h7, hlam]
          · linarith only [h1619, h1688, h1690, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1693 | h1693
          · linarith only [h1617, h1688, h1689, h1693, h6, h7, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
          · linarith only [h1619, h1688, h1693, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1696 | h1696
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1697 | h1697
          · linarith only [h1, h1617, h1697, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1699 | h1699
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1700 | h1700
              · linarith only [h1700, h4, h7, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1702 | h1702
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1703 | h1703
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1704 | h1704
                    · rcases h0bigk with h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c | h1705c
                      · have p1705_0 := h1705c.1
                        have p1705_1 := h1705c.2.1
                        have p1705_2 := h1705c.2.2.1
                        have p1705_3 := h1705c.2.2.2
                        linarith only [hlam, p1705_0]
                      · have p1705_0 := h1705c.1
                        have p1705_1 := h1705c.2.1
                        have p1705_2 := h1705c.2.2.1
                        have p1705_3 := h1705c.2.2.2
                        linarith only [h0, h1696, h1702, h1704, hc01, hc45, hlam, hphi, ht0b, ht5b, p1705_1]
                      · have p1705_0 := h1705c.1
                        have p1705_1 := h1705c.2.1
                        have p1705_2 := h1705c.2.2.1
                        have p1705_3 := h1705c.2.2.2
                        linarith only [h1619, h1696, h1702, h1704, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p1705_1]
                      · have p1705_0 := h1705c.1
                        have p1705_1 := h1705c.2.1
                        have p1705_2 := h1705c.2.2.1
                        have p1705_3 := h1705c.2.2.2
                        linarith only [h1619, h1696, h1702, h1704, h4, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p1705_1]
                      · have p1705_0 := h1705c.1
                        have p1705_1 := h1705c.2.1
                        have p1705_2 := h1705c.2.2.1
                        have p1705_3 := h1705c.2.2.2
                        rcases p1705_3 (m.d 0 1) (by simp) with h1710 | h1710
                        · rcases p1705_3 (m.d 0 2) (by simp) with h1711 | h1711
                          · linarith only [h0, h1711, hlam]
                          · linarith only [h1711, h6, hlam]
                        · linarith only [h1710, h3, hlam]
                      · have p1705_0 := h1705c.1
                        have p1705_1 := h1705c.2.1
                        have p1705_2 := h1705c.2.2.1
                        have p1705_3 := h1705c.2.2.2
                        linarith only [h0, hlam, p1705_0]
                      · have p1705_0 := h1705c.1
                        have p1705_1 := h1705c.2.1
                        have p1705_2 := h1705c.2.2.1
                        have p1705_3 := h1705c.2.2.2
                        linarith only [hlam, p1705_0]
                      · have p1705_0 := h1705c.1
                        have p1705_1 := h1705c.2.1
                        have p1705_2 := h1705c.2.2.1
                        have p1705_3 := h1705c.2.2.2
                        linarith only [h1619, h1696, h1702, h1704, h4, hc02, hc45, hlam, hphi, ht0b, ht5b, p1705_1]
                      · have p1705_0 := h1705c.1
                        have p1705_1 := h1705c.2.1
                        have p1705_2 := h1705c.2.2.1
                        have p1705_3 := h1705c.2.2.2
                        linarith only [h0, h1619, h1696, h1702, h1704, h4, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p1705_1]
                      · have p1705_0 := h1705c.1
                        have p1705_1 := h1705c.2.1
                        have p1705_2 := h1705c.2.2.1
                        have p1705_3 := h1705c.2.2.2
                        rcases p1705_3 (m.d 0 1) (by simp) with h1719 | h1719
                        · rcases p1705_3 (m.d 0 2) (by simp) with h1720 | h1720
                          · rcases p1705_3 (m.d 0 3) (by simp) with h1721 | h1721
                            · linarith only [h1721, h4, hlam]
                            · linarith only [h1617, h1721, hlam]
                          · linarith only [h1720, h6, hlam]
                        · linarith only [h1719, h3, hlam]
                      · have p1705_0 := h1705c.1
                        have p1705_1 := h1705c.2.1
                        have p1705_2 := h1705c.2.2.1
                        have p1705_3 := h1705c.2.2.2
                        linarith only [h1, hlam, p1705_1]
                      · have p1705_0 := h1705c.1
                        have p1705_1 := h1705c.2.1
                        have p1705_2 := h1705c.2.2.1
                        have p1705_3 := h1705c.2.2.2
                        linarith only [h4, hlam, p1705_1]
                      · have p1705_0 := h1705c.1
                        have p1705_1 := h1705c.2.1
                        have p1705_2 := h1705c.2.2.1
                        have p1705_3 := h1705c.2.2.2
                        linarith only [hlam, p1705_0]
                      · have p1705_0 := h1705c.1
                        have p1705_1 := h1705c.2.1
                        have p1705_2 := h1705c.2.2.1
                        have p1705_3 := h1705c.2.2.2
                        linarith only [h7, hlam, p1705_1]
                      · have p1705_0 := h1705c.1
                        have p1705_1 := h1705c.2.1
                        have p1705_2 := h1705c.2.2.1
                        have p1705_3 := h1705c.2.2.2
                        linarith only [h7, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1705_1]
                      · have p1705_0 := h1705c.1
                        have p1705_1 := h1705c.2.1
                        have p1705_2 := h1705c.2.2.1
                        have p1705_3 := h1705c.2.2.2
                        linarith only [h2, hlam, p1705_0]
                      · have p1705_0 := h1705c.1
                        have p1705_1 := h1705c.2.1
                        have p1705_2 := h1705c.2.2.1
                        have p1705_3 := h1705c.2.2.2
                        linarith only [h5, hlam, p1705_0]
                      · have p1705_0 := h1705c.1
                        have p1705_1 := h1705c.2.1
                        have p1705_2 := h1705c.2.2.1
                        have p1705_3 := h1705c.2.2.2
                        linarith only [h1619, h4, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1705_1]
                      · have p1705_0 := h1705c.1
                        have p1705_1 := h1705c.2.1
                        have p1705_2 := h1705c.2.2.1
                        have p1705_3 := h1705c.2.2.2
                        linarith only [hlam, p1705_0]
                      · have p1705_0 := h1705c.1
                        have p1705_1 := h1705c.2.1
                        have p1705_2 := h1705c.2.2.1
                        have p1705_3 := h1705c.2.2.2
                        rcases p1705_3 (m.d 0 1) (by simp) with h1735 | h1735
                        · rcases p1705_3 (m.d 0 2) (by simp) with h1736 | h1736
                          · rcases p1705_3 (m.d 0 3) (by simp) with h1737 | h1737
                            · linarith only [h1737, h7, hlam]
                            · linarith only [h1617, h1737, hlam]
                          · linarith only [h1736, h6, hlam]
                        · linarith only [h1735, h3, hlam]
                      · have p1705_0 := h1705c.1
                        have p1705_1 := h1705c.2.1
                        have p1705_2 := h1705c.2.2.1
                        have p1705_3 := h1705c.2.2.2
                        linarith only [h3, hlam, p1705_0]
                      · have p1705_0 := h1705c.1
                        have p1705_1 := h1705c.2.1
                        have p1705_2 := h1705c.2.2.1
                        have p1705_3 := h1705c.2.2.2
                        linarith only [h6, hlam, p1705_1]
                      · have p1705_0 := h1705c.1
                        have p1705_1 := h1705c.2.1
                        have p1705_2 := h1705c.2.2.1
                        have p1705_3 := h1705c.2.2.2
                        linarith only [h1617, hlam, p1705_0]
                      · have p1705_0 := h1705c.1
                        have p1705_1 := h1705c.2.1
                        have p1705_2 := h1705c.2.2.1
                        have p1705_3 := h1705c.2.2.2
                        linarith only [h1618, hlam, p1705_1]
                      · have p1705_0 := h1705c.1
                        have p1705_1 := h1705c.2.1
                        have p1705_2 := h1705c.2.2.1
                        have p1705_3 := h1705c.2.2.2
                        linarith only [hlam, p1705_0]
                    · linarith only [h1619, h1704, h4, h7, hc12, hc45, hlam, hphi, ht23, ht34]
                  · linarith only [h1617, h1618, h1619, h1696, h1700, h1702, h1703, h7, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                · linarith only [h1617, h1619, h1702, h7, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h1617, h1619, h1696, h1699, h7, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1751 | h1751
          · linarith only [h1, h1617, h1751, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1753 | h1753
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1754 | h1754
              · linarith only [h1754, h4, h7, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1756 | h1756
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1757 | h1757
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1758 | h1758
                    · rcases h0bigk with h1759c | h1759c | h1759c | h1759c | h1759c | h1759c | h1759c | h1759c | h1759c | h1759c | h1759c | h1759c | h1759c | h1759c | h1759c | h1759c | h1759c | h1759c | h1759c | h1759c | h1759c | h1759c | h1759c | h1759c | h1759c
                      · have p1759_0 := h1759c.1
                        have p1759_1 := h1759c.2.1
                        have p1759_2 := h1759c.2.2.1
                        have p1759_3 := h1759c.2.2.2
                        linarith only [hlam, p1759_0]
                      · have p1759_0 := h1759c.1
                        have p1759_1 := h1759c.2.1
                        have p1759_2 := h1759c.2.2.1
                        have p1759_3 := h1759c.2.2.2
                        linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1759_1]
                      · have p1759_0 := h1759c.1
                        have p1759_1 := h1759c.2.1
                        have p1759_2 := h1759c.2.2.1
                        have p1759_3 := h1759c.2.2.2
                        linarith only [h1617, h1696, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1759_1]
                      · have p1759_0 := h1759c.1
                        have p1759_1 := h1759c.2.1
                        have p1759_2 := h1759c.2.2.1
                        have p1759_3 := h1759c.2.2.2
                        linarith only [h1751, h1753, h1758, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1759_1]
                      · have p1759_0 := h1759c.1
                        have p1759_1 := h1759c.2.1
                        have p1759_2 := h1759c.2.2.1
                        have p1759_3 := h1759c.2.2.2
                        linarith only [h1696, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1759_1]
                      · have p1759_0 := h1759c.1
                        have p1759_1 := h1759c.2.1
                        have p1759_2 := h1759c.2.2.1
                        have p1759_3 := h1759c.2.2.2
                        linarith only [h0, hlam, p1759_0]
                      · have p1759_0 := h1759c.1
                        have p1759_1 := h1759c.2.1
                        have p1759_2 := h1759c.2.2.1
                        have p1759_3 := h1759c.2.2.2
                        linarith only [hlam, p1759_0]
                      · have p1759_0 := h1759c.1
                        have p1759_1 := h1759c.2.1
                        have p1759_2 := h1759c.2.2.1
                        have p1759_3 := h1759c.2.2.2
                        linarith only [h1617, h1696, h6, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1759_1]
                      · have p1759_0 := h1759c.1
                        have p1759_1 := h1759c.2.1
                        have p1759_2 := h1759c.2.2.1
                        have p1759_3 := h1759c.2.2.2
                        linarith only [h0, h1751, h1753, h1758, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1759_1]
                      · have p1759_0 := h1759c.1
                        have p1759_1 := h1759c.2.1
                        have p1759_2 := h1759c.2.2.1
                        have p1759_3 := h1759c.2.2.2
                        linarith only [h0, h1696, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1759_1]
                      · have p1759_0 := h1759c.1
                        have p1759_1 := h1759c.2.1
                        have p1759_2 := h1759c.2.2.1
                        have p1759_3 := h1759c.2.2.2
                        linarith only [h1, hlam, p1759_1]
                      · have p1759_0 := h1759c.1
                        have p1759_1 := h1759c.2.1
                        have p1759_2 := h1759c.2.2.1
                        have p1759_3 := h1759c.2.2.2
                        linarith only [h4, hlam, p1759_1]
                      · have p1759_0 := h1759c.1
                        have p1759_1 := h1759c.2.1
                        have p1759_2 := h1759c.2.2.1
                        have p1759_3 := h1759c.2.2.2
                        linarith only [hlam, p1759_0]
                      · have p1759_0 := h1759c.1
                        have p1759_1 := h1759c.2.1
                        have p1759_2 := h1759c.2.2.1
                        have p1759_3 := h1759c.2.2.2
                        linarith only [h7, hlam, p1759_1]
                      · have p1759_0 := h1759c.1
                        have p1759_1 := h1759c.2.1
                        have p1759_2 := h1759c.2.2.1
                        have p1759_3 := h1759c.2.2.2
                        linarith only [h1696, h6, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1759_1]
                      · have p1759_0 := h1759c.1
                        have p1759_1 := h1759c.2.1
                        have p1759_2 := h1759c.2.2.1
                        have p1759_3 := h1759c.2.2.2
                        linarith only [h2, hlam, p1759_0]
                      · have p1759_0 := h1759c.1
                        have p1759_1 := h1759c.2.1
                        have p1759_2 := h1759c.2.2.1
                        have p1759_3 := h1759c.2.2.2
                        linarith only [h5, hlam, p1759_0]
                      · have p1759_0 := h1759c.1
                        have p1759_1 := h1759c.2.1
                        have p1759_2 := h1759c.2.2.1
                        have p1759_3 := h1759c.2.2.2
                        linarith only [h1, h1753, h1758, hc04, hc45, hlam, hphi, ht0b, ht5b, p1759_1]
                      · have p1759_0 := h1759c.1
                        have p1759_1 := h1759c.2.1
                        have p1759_2 := h1759c.2.2.1
                        have p1759_3 := h1759c.2.2.2
                        linarith only [hlam, p1759_0]
                      · have p1759_0 := h1759c.1
                        have p1759_1 := h1759c.2.1
                        have p1759_2 := h1759c.2.2.1
                        have p1759_3 := h1759c.2.2.2
                        linarith only [h1696, h6, h7, hc12, hc34, hlam, hphi, ht23, p1759_1]
                      · have p1759_0 := h1759c.1
                        have p1759_1 := h1759c.2.1
                        have p1759_2 := h1759c.2.2.1
                        have p1759_3 := h1759c.2.2.2
                        linarith only [h3, hlam, p1759_0]
                      · have p1759_0 := h1759c.1
                        have p1759_1 := h1759c.2.1
                        have p1759_2 := h1759c.2.2.1
                        have p1759_3 := h1759c.2.2.2
                        linarith only [h6, hlam, p1759_1]
                      · have p1759_0 := h1759c.1
                        have p1759_1 := h1759c.2.1
                        have p1759_2 := h1759c.2.2.1
                        have p1759_3 := h1759c.2.2.2
                        linarith only [h1617, hlam, p1759_0]
                      · have p1759_0 := h1759c.1
                        have p1759_1 := h1759c.2.1
                        have p1759_2 := h1759c.2.2.1
                        have p1759_3 := h1759c.2.2.2
                        linarith only [h1618, hlam, p1759_1]
                      · have p1759_0 := h1759c.1
                        have p1759_1 := h1759c.2.1
                        have p1759_2 := h1759c.2.2.1
                        have p1759_3 := h1759c.2.2.2
                        linarith only [hlam, p1759_0]
                    · linarith only [h1617, h1696, h1758, h6, h7, hc12, hc45, hlam, hphi, ht23, ht34]
                  · linarith only [h1617, h1618, h1696, h1754, h1756, h1757, h7, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h1619, h1753, h1756, hlam]
            · linarith only [h1617, h1753, h7, hc13, hc34, hlam, hphi]
  · linarith only [h1617, h1618, h7, hlam]

set_option maxHeartbeats 5360000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s6_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h1617 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h1790 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 2 3 (by decide) (by decide) with h1791 | h1791
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1792 | h1792
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1793 | h1793
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1794 | h1794
        · linarith only [h1, h1794, h7, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1796 | h1796
          · linarith only [h1, h1617, h1796, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1798 | h1798
            · linarith only [h1798, h4, h7, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1800 | h1800
              · linarith only [h1, h1617, h1791, h1800, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1802 | h1802
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1803 | h1803
                  · rcases h0bigk with h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c | h1804c
                    · have p1804_0 := h1804c.1
                      have p1804_1 := h1804c.2.1
                      have p1804_2 := h1804c.2.2.1
                      have p1804_3 := h1804c.2.2.2
                      linarith only [hlam, p1804_0]
                    · have p1804_0 := h1804c.1
                      have p1804_1 := h1804c.2.1
                      have p1804_2 := h1804c.2.2.1
                      have p1804_3 := h1804c.2.2.2
                      linarith only [h0, h1792, h1802, hc01, hc45, hlam, hphi, ht0b, ht5b, p1804_1]
                    · have p1804_0 := h1804c.1
                      have p1804_1 := h1804c.2.1
                      have p1804_2 := h1804c.2.2.1
                      have p1804_3 := h1804c.2.2.2
                      rcases p1804_3 (m.d 0 1) (by simp) with h1807 | h1807
                      · rcases p1804_3 (m.d 0 2) (by simp) with h1808 | h1808
                        · linarith only [h0, h1808, hlam]
                        · linarith only [h1808, h4, hlam]
                      · linarith only [h1, h1807, hlam]
                    · have p1804_0 := h1804c.1
                      have p1804_1 := h1804c.2.1
                      have p1804_2 := h1804c.2.2.1
                      have p1804_3 := h1804c.2.2.2
                      linarith only [h1792, h1802, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1804_1]
                    · have p1804_0 := h1804c.1
                      have p1804_1 := h1804c.2.1
                      have p1804_2 := h1804c.2.2.1
                      have p1804_3 := h1804c.2.2.2
                      rcases p1804_3 (m.d 0 1) (by simp) with h1813 | h1813
                      · rcases p1804_3 (m.d 0 2) (by simp) with h1814 | h1814
                        · linarith only [h0, h1814, hlam]
                        · linarith only [h1814, h6, hlam]
                      · linarith only [h1813, h3, hlam]
                    · have p1804_0 := h1804c.1
                      have p1804_1 := h1804c.2.1
                      have p1804_2 := h1804c.2.2.1
                      have p1804_3 := h1804c.2.2.2
                      linarith only [h0, hlam, p1804_0]
                    · have p1804_0 := h1804c.1
                      have p1804_1 := h1804c.2.1
                      have p1804_2 := h1804c.2.2.1
                      have p1804_3 := h1804c.2.2.2
                      linarith only [hlam, p1804_0]
                    · have p1804_0 := h1804c.1
                      have p1804_1 := h1804c.2.1
                      have p1804_2 := h1804c.2.2.1
                      have p1804_3 := h1804c.2.2.2
                      rcases p1804_3 (m.d 0 1) (by simp) with h1820 | h1820
                      · rcases p1804_3 (m.d 0 2) (by simp) with h1821 | h1821
                        · rcases p1804_3 (m.d 0 3) (by simp) with h1822 | h1822
                          · linarith only [h1822, h4, hlam]
                          · rcases p1804_3 (m.d 0 4) (by simp) with h1824 | h1824
                            · linarith only [h1824, h5, hlam]
                            · linarith only [h1824, h7, hlam]
                        · linarith only [h1821, h4, hlam]
                      · linarith only [h1, h1820, hlam]
                    · have p1804_0 := h1804c.1
                      have p1804_1 := h1804c.2.1
                      have p1804_2 := h1804c.2.2.1
                      have p1804_3 := h1804c.2.2.2
                      linarith only [h1792, h1802, h2, hc02, hc45, hlam, hphi, ht0b, ht5b, p1804_1]
                    · have p1804_0 := h1804c.1
                      have p1804_1 := h1804c.2.1
                      have p1804_2 := h1804c.2.2.1
                      have p1804_3 := h1804c.2.2.2
                      rcases p1804_3 (m.d 0 1) (by simp) with h1830 | h1830
                      · rcases p1804_3 (m.d 0 2) (by simp) with h1831 | h1831
                        · rcases p1804_3 (m.d 0 3) (by simp) with h1832 | h1832
                          · linarith only [h1832, h4, hlam]
                          · rcases p1804_3 (m.d 0 4) (by simp) with h1834 | h1834
                            · linarith only [h1834, h5, hlam]
                            · linarith only [h1790, h1834, hlam]
                        · linarith only [h1831, h6, hlam]
                      · linarith only [h1830, h3, hlam]
                    · have p1804_0 := h1804c.1
                      have p1804_1 := h1804c.2.1
                      have p1804_2 := h1804c.2.2.1
                      have p1804_3 := h1804c.2.2.2
                      linarith only [h1, hlam, p1804_1]
                    · have p1804_0 := h1804c.1
                      have p1804_1 := h1804c.2.1
                      have p1804_2 := h1804c.2.2.1
                      have p1804_3 := h1804c.2.2.2
                      linarith only [h4, hlam, p1804_1]
                    · have p1804_0 := h1804c.1
                      have p1804_1 := h1804c.2.1
                      have p1804_2 := h1804c.2.2.1
                      have p1804_3 := h1804c.2.2.2
                      linarith only [hlam, p1804_0]
                    · have p1804_0 := h1804c.1
                      have p1804_1 := h1804c.2.1
                      have p1804_2 := h1804c.2.2.1
                      have p1804_3 := h1804c.2.2.2
                      linarith only [h7, hlam, p1804_1]
                    · have p1804_0 := h1804c.1
                      have p1804_1 := h1804c.2.1
                      have p1804_2 := h1804c.2.2.1
                      have p1804_3 := h1804c.2.2.2
                      linarith only [h1617, hlam, p1804_1]
                    · have p1804_0 := h1804c.1
                      have p1804_1 := h1804c.2.1
                      have p1804_2 := h1804c.2.2.1
                      have p1804_3 := h1804c.2.2.2
                      linarith only [h2, hlam, p1804_0]
                    · have p1804_0 := h1804c.1
                      have p1804_1 := h1804c.2.1
                      have p1804_2 := h1804c.2.2.1
                      have p1804_3 := h1804c.2.2.2
                      linarith only [h5, hlam, p1804_0]
                    · have p1804_0 := h1804c.1
                      have p1804_1 := h1804c.2.1
                      have p1804_2 := h1804c.2.2.1
                      have p1804_3 := h1804c.2.2.2
                      linarith only [h1, h1791, h7, hc23, hc34, hlam, hphi, p1804_1]
                    · have p1804_0 := h1804c.1
                      have p1804_1 := h1804c.2.1
                      have p1804_2 := h1804c.2.2.1
                      have p1804_3 := h1804c.2.2.2
                      linarith only [hlam, p1804_0]
                    · have p1804_0 := h1804c.1
                      have p1804_1 := h1804c.2.1
                      have p1804_2 := h1804c.2.2.1
                      have p1804_3 := h1804c.2.2.2
                      linarith only [h1, h1617, h1791, h7, hc23, hc34, hlam, hphi, p1804_1]
                    · have p1804_0 := h1804c.1
                      have p1804_1 := h1804c.2.1
                      have p1804_2 := h1804c.2.2.1
                      have p1804_3 := h1804c.2.2.2
                      linarith only [h3, hlam, p1804_0]
                    · have p1804_0 := h1804c.1
                      have p1804_1 := h1804c.2.1
                      have p1804_2 := h1804c.2.2.1
                      have p1804_3 := h1804c.2.2.2
                      linarith only [h6, hlam, p1804_1]
                    · have p1804_0 := h1804c.1
                      have p1804_1 := h1804c.2.1
                      have p1804_2 := h1804c.2.2.1
                      have p1804_3 := h1804c.2.2.2
                      linarith only [h1, h1617, h1791, hc23, hc35, hlam, hphi, p1804_1]
                    · have p1804_0 := h1804c.1
                      have p1804_1 := h1804c.2.1
                      have p1804_2 := h1804c.2.2.1
                      have p1804_3 := h1804c.2.2.2
                      linarith only [h1790, hlam, p1804_1]
                    · have p1804_0 := h1804c.1
                      have p1804_1 := h1804c.2.1
                      have p1804_2 := h1804c.2.2.1
                      have p1804_3 := h1804c.2.2.2
                      linarith only [hlam, p1804_0]
                  · linarith only [h1792, h1802, h1803, h2, h7, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1855 | h1855
                  · rcases h0bigk with h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c | h1856c
                    · have p1856_0 := h1856c.1
                      have p1856_1 := h1856c.2.1
                      have p1856_2 := h1856c.2.2.1
                      have p1856_3 := h1856c.2.2.2
                      linarith only [hlam, p1856_0]
                    · have p1856_0 := h1856c.1
                      have p1856_1 := h1856c.2.1
                      have p1856_2 := h1856c.2.2.1
                      have p1856_3 := h1856c.2.2.2
                      linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1856_1]
                    · have p1856_0 := h1856c.1
                      have p1856_1 := h1856c.2.1
                      have p1856_2 := h1856c.2.2.1
                      have p1856_3 := h1856c.2.2.2
                      rcases p1856_3 (m.d 0 1) (by simp) with h1859 | h1859
                      · rcases p1856_3 (m.d 0 2) (by simp) with h1860 | h1860
                        · linarith only [h0, h1860, hlam]
                        · linarith only [h1860, h4, hlam]
                      · linarith only [h1, h1859, hlam]
                    · have p1856_0 := h1856c.1
                      have p1856_1 := h1856c.2.1
                      have p1856_2 := h1856c.2.2.1
                      have p1856_3 := h1856c.2.2.2
                      linarith only [h1790, h1798, h1802, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1856_1]
                    · have p1856_0 := h1856c.1
                      have p1856_1 := h1856c.2.1
                      have p1856_2 := h1856c.2.2.1
                      have p1856_3 := h1856c.2.2.2
                      linarith only [h1790, h1798, h1802, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1856_1]
                    · have p1856_0 := h1856c.1
                      have p1856_1 := h1856c.2.1
                      have p1856_2 := h1856c.2.2.1
                      have p1856_3 := h1856c.2.2.2
                      linarith only [h0, hlam, p1856_0]
                    · have p1856_0 := h1856c.1
                      have p1856_1 := h1856c.2.1
                      have p1856_2 := h1856c.2.2.1
                      have p1856_3 := h1856c.2.2.2
                      linarith only [hlam, p1856_0]
                    · have p1856_0 := h1856c.1
                      have p1856_1 := h1856c.2.1
                      have p1856_2 := h1856c.2.2.1
                      have p1856_3 := h1856c.2.2.2
                      rcases p1856_3 (m.d 0 1) (by simp) with h1868 | h1868
                      · rcases p1856_3 (m.d 0 2) (by simp) with h1869 | h1869
                        · rcases p1856_3 (m.d 0 3) (by simp) with h1870 | h1870
                          · linarith only [h1870, h4, hlam]
                          · rcases p1856_3 (m.d 0 4) (by simp) with h1872 | h1872
                            · linarith only [h1872, h5, hlam]
                            · linarith only [h1872, h7, hlam]
                        · linarith only [h1869, h4, hlam]
                      · linarith only [h1, h1868, hlam]
                    · have p1856_0 := h1856c.1
                      have p1856_1 := h1856c.2.1
                      have p1856_2 := h1856c.2.2.1
                      have p1856_3 := h1856c.2.2.2
                      linarith only [h1790, h1798, h1802, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1856_1]
                    · have p1856_0 := h1856c.1
                      have p1856_1 := h1856c.2.1
                      have p1856_2 := h1856c.2.2.1
                      have p1856_3 := h1856c.2.2.2
                      linarith only [h0, h1790, h1798, h1802, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1856_1]
                    · have p1856_0 := h1856c.1
                      have p1856_1 := h1856c.2.1
                      have p1856_2 := h1856c.2.2.1
                      have p1856_3 := h1856c.2.2.2
                      linarith only [h1, hlam, p1856_1]
                    · have p1856_0 := h1856c.1
                      have p1856_1 := h1856c.2.1
                      have p1856_2 := h1856c.2.2.1
                      have p1856_3 := h1856c.2.2.2
                      linarith only [h4, hlam, p1856_1]
                    · have p1856_0 := h1856c.1
                      have p1856_1 := h1856c.2.1
                      have p1856_2 := h1856c.2.2.1
                      have p1856_3 := h1856c.2.2.2
                      linarith only [hlam, p1856_0]
                    · have p1856_0 := h1856c.1
                      have p1856_1 := h1856c.2.1
                      have p1856_2 := h1856c.2.2.1
                      have p1856_3 := h1856c.2.2.2
                      linarith only [h7, hlam, p1856_1]
                    · have p1856_0 := h1856c.1
                      have p1856_1 := h1856c.2.1
                      have p1856_2 := h1856c.2.2.1
                      have p1856_3 := h1856c.2.2.2
                      linarith only [h1617, hlam, p1856_1]
                    · have p1856_0 := h1856c.1
                      have p1856_1 := h1856c.2.1
                      have p1856_2 := h1856c.2.2.1
                      have p1856_3 := h1856c.2.2.2
                      linarith only [h2, hlam, p1856_0]
                    · have p1856_0 := h1856c.1
                      have p1856_1 := h1856c.2.1
                      have p1856_2 := h1856c.2.2.1
                      have p1856_3 := h1856c.2.2.2
                      linarith only [h5, hlam, p1856_0]
                    · have p1856_0 := h1856c.1
                      have p1856_1 := h1856c.2.1
                      have p1856_2 := h1856c.2.2.1
                      have p1856_3 := h1856c.2.2.2
                      linarith only [h1, h1791, h7, hc23, hc34, hlam, hphi, p1856_1]
                    · have p1856_0 := h1856c.1
                      have p1856_1 := h1856c.2.1
                      have p1856_2 := h1856c.2.2.1
                      have p1856_3 := h1856c.2.2.2
                      linarith only [hlam, p1856_0]
                    · have p1856_0 := h1856c.1
                      have p1856_1 := h1856c.2.1
                      have p1856_2 := h1856c.2.2.1
                      have p1856_3 := h1856c.2.2.2
                      linarith only [h1790, h1798, h1802, h7, hc23, hc34, hlam, hphi, p1856_1]
                    · have p1856_0 := h1856c.1
                      have p1856_1 := h1856c.2.1
                      have p1856_2 := h1856c.2.2.1
                      have p1856_3 := h1856c.2.2.2
                      linarith only [h3, hlam, p1856_0]
                    · have p1856_0 := h1856c.1
                      have p1856_1 := h1856c.2.1
                      have p1856_2 := h1856c.2.2.1
                      have p1856_3 := h1856c.2.2.2
                      linarith only [h6, hlam, p1856_1]
                    · have p1856_0 := h1856c.1
                      have p1856_1 := h1856c.2.1
                      have p1856_2 := h1856c.2.2.1
                      have p1856_3 := h1856c.2.2.2
                      linarith only [h1, h1617, h1791, h1855, hc23, hc34, hlam, hphi, p1856_1]
                    · have p1856_0 := h1856c.1
                      have p1856_1 := h1856c.2.1
                      have p1856_2 := h1856c.2.2.1
                      have p1856_3 := h1856c.2.2.2
                      linarith only [h1790, hlam, p1856_1]
                    · have p1856_0 := h1856c.1
                      have p1856_1 := h1856c.2.1
                      have p1856_2 := h1856c.2.2.1
                      have p1856_3 := h1856c.2.2.2
                      linarith only [hlam, p1856_0]
                  · linarith only [h1790, h1855, h7, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1895 | h1895
        · linarith only [h1, h1790, h1791, h1793, h1895, h6, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1897 | h1897
          · linarith only [h1, h1617, h1897, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1899 | h1899
            · linarith only [h1, h1791, h1899, h7, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1901 | h1901
              · linarith only [h1617, h1792, h1793, h1899, h1901, h6, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1903 | h1903
                · linarith only [h0, h1792, h1793, h1903, h6, hc01, hc45, hlam, hphi, ht0b, ht5b]
                · linarith only [h1790, h1792, h1793, h1899, h1903, h7, hc23, hc34, hlam, hphi]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1906 | h1906
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1907 | h1907
        · linarith only [h1, h1617, h1791, h1792, h1907, h2, h7, hc23, hc35, hlam, hphi]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1909 | h1909
          · linarith only [h1, h1617, h1909, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1911 | h1911
            · linarith only [h1, h1617, h1791, h1792, h1911, h5, h7, hc12, hc35, hlam, hphi, ht23]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1913 | h1913
              · linarith only [h1617, h1791, h1792, h1913, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1915 | h1915
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1916 | h1916
                  · rcases h0bigk with h1917c | h1917c | h1917c | h1917c | h1917c | h1917c | h1917c | h1917c | h1917c | h1917c | h1917c | h1917c | h1917c | h1917c | h1917c | h1917c | h1917c | h1917c | h1917c | h1917c | h1917c | h1917c | h1917c | h1917c | h1917c
                    · have p1917_0 := h1917c.1
                      have p1917_1 := h1917c.2.1
                      have p1917_2 := h1917c.2.2.1
                      have p1917_3 := h1917c.2.2.2
                      linarith only [hlam, p1917_0]
                    · have p1917_0 := h1917c.1
                      have p1917_1 := h1917c.2.1
                      have p1917_2 := h1917c.2.2.1
                      have p1917_3 := h1917c.2.2.2
                      linarith only [h1792, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1917_1]
                    · have p1917_0 := h1917c.1
                      have p1917_1 := h1917c.2.1
                      have p1917_2 := h1917c.2.2.1
                      have p1917_3 := h1917c.2.2.2
                      rcases p1917_3 (m.d 0 1) (by simp) with h1920 | h1920
                      · rcases p1917_3 (m.d 0 2) (by simp) with h1921 | h1921
                        · linarith only [h0, h1921, hlam]
                        · linarith only [h1921, h4, hlam]
                      · linarith only [h1, h1920, hlam]
                    · have p1917_0 := h1917c.1
                      have p1917_1 := h1917c.2.1
                      have p1917_2 := h1917c.2.2.1
                      have p1917_3 := h1917c.2.2.2
                      linarith only [h1792, h1906, h1913, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1917_1]
                    · have p1917_0 := h1917c.1
                      have p1917_1 := h1917c.2.1
                      have p1917_2 := h1917c.2.2.1
                      have p1917_3 := h1917c.2.2.2
                      rcases p1917_3 (m.d 0 1) (by simp) with h1926 | h1926
                      · rcases p1917_3 (m.d 0 2) (by simp) with h1927 | h1927
                        · linarith only [h0, h1927, hlam]
                        · linarith only [h1927, h6, hlam]
                      · linarith only [h1926, h3, hlam]
                    · have p1917_0 := h1917c.1
                      have p1917_1 := h1917c.2.1
                      have p1917_2 := h1917c.2.2.1
                      have p1917_3 := h1917c.2.2.2
                      linarith only [h0, hlam, p1917_0]
                    · have p1917_0 := h1917c.1
                      have p1917_1 := h1917c.2.1
                      have p1917_2 := h1917c.2.2.1
                      have p1917_3 := h1917c.2.2.2
                      linarith only [hlam, p1917_0]
                    · have p1917_0 := h1917c.1
                      have p1917_1 := h1917c.2.1
                      have p1917_2 := h1917c.2.2.1
                      have p1917_3 := h1917c.2.2.2
                      rcases p1917_3 (m.d 0 1) (by simp) with h1933 | h1933
                      · rcases p1917_3 (m.d 0 2) (by simp) with h1934 | h1934
                        · rcases p1917_3 (m.d 0 3) (by simp) with h1935 | h1935
                          · linarith only [h1935, h4, hlam]
                          · rcases p1917_3 (m.d 0 4) (by simp) with h1937 | h1937
                            · linarith only [h1937, h5, hlam]
                            · linarith only [h1937, h7, hlam]
                        · linarith only [h1934, h4, hlam]
                      · linarith only [h1, h1933, hlam]
                    · have p1917_0 := h1917c.1
                      have p1917_1 := h1917c.2.1
                      have p1917_2 := h1917c.2.2.1
                      have p1917_3 := h1917c.2.2.2
                      linarith only [h1792, h1906, h1913, h5, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1917_1]
                    · have p1917_0 := h1917c.1
                      have p1917_1 := h1917c.2.1
                      have p1917_2 := h1917c.2.2.1
                      have p1917_3 := h1917c.2.2.2
                      rcases p1917_3 (m.d 0 1) (by simp) with h1943 | h1943
                      · rcases p1917_3 (m.d 0 2) (by simp) with h1944 | h1944
                        · rcases p1917_3 (m.d 0 3) (by simp) with h1945 | h1945
                          · linarith only [h1945, h4, hlam]
                          · rcases p1917_3 (m.d 0 4) (by simp) with h1947 | h1947
                            · linarith only [h1947, h5, hlam]
                            · linarith only [h1790, h1947, hlam]
                        · linarith only [h1944, h6, hlam]
                      · linarith only [h1943, h3, hlam]
                    · have p1917_0 := h1917c.1
                      have p1917_1 := h1917c.2.1
                      have p1917_2 := h1917c.2.2.1
                      have p1917_3 := h1917c.2.2.2
                      linarith only [h1, hlam, p1917_1]
                    · have p1917_0 := h1917c.1
                      have p1917_1 := h1917c.2.1
                      have p1917_2 := h1917c.2.2.1
                      have p1917_3 := h1917c.2.2.2
                      linarith only [h4, hlam, p1917_1]
                    · have p1917_0 := h1917c.1
                      have p1917_1 := h1917c.2.1
                      have p1917_2 := h1917c.2.2.1
                      have p1917_3 := h1917c.2.2.2
                      linarith only [hlam, p1917_0]
                    · have p1917_0 := h1917c.1
                      have p1917_1 := h1917c.2.1
                      have p1917_2 := h1917c.2.2.1
                      have p1917_3 := h1917c.2.2.2
                      linarith only [h7, hlam, p1917_1]
                    · have p1917_0 := h1917c.1
                      have p1917_1 := h1917c.2.1
                      have p1917_2 := h1917c.2.2.1
                      have p1917_3 := h1917c.2.2.2
                      linarith only [h1617, hlam, p1917_1]
                    · have p1917_0 := h1917c.1
                      have p1917_1 := h1917c.2.1
                      have p1917_2 := h1917c.2.2.1
                      have p1917_3 := h1917c.2.2.2
                      linarith only [h2, hlam, p1917_0]
                    · have p1917_0 := h1917c.1
                      have p1917_1 := h1917c.2.1
                      have p1917_2 := h1917c.2.2.1
                      have p1917_3 := h1917c.2.2.2
                      linarith only [h5, hlam, p1917_0]
                    · have p1917_0 := h1917c.1
                      have p1917_1 := h1917c.2.1
                      have p1917_2 := h1917c.2.2.1
                      have p1917_3 := h1917c.2.2.2
                      linarith only [h1, h1791, h7, hc23, hc34, hlam, hphi, p1917_1]
                    · have p1917_0 := h1917c.1
                      have p1917_1 := h1917c.2.1
                      have p1917_2 := h1917c.2.2.1
                      have p1917_3 := h1917c.2.2.2
                      linarith only [hlam, p1917_0]
                    · have p1917_0 := h1917c.1
                      have p1917_1 := h1917c.2.1
                      have p1917_2 := h1917c.2.2.1
                      have p1917_3 := h1917c.2.2.2
                      linarith only [h1, h1617, h1791, h7, hc23, hc34, hlam, hphi, p1917_1]
                    · have p1917_0 := h1917c.1
                      have p1917_1 := h1917c.2.1
                      have p1917_2 := h1917c.2.2.1
                      have p1917_3 := h1917c.2.2.2
                      linarith only [h3, hlam, p1917_0]
                    · have p1917_0 := h1917c.1
                      have p1917_1 := h1917c.2.1
                      have p1917_2 := h1917c.2.2.1
                      have p1917_3 := h1917c.2.2.2
                      linarith only [h6, hlam, p1917_1]
                    · have p1917_0 := h1917c.1
                      have p1917_1 := h1917c.2.1
                      have p1917_2 := h1917c.2.2.1
                      have p1917_3 := h1917c.2.2.2
                      linarith only [h1, h1617, h1791, hc23, hc35, hlam, hphi, p1917_1]
                    · have p1917_0 := h1917c.1
                      have p1917_1 := h1917c.2.1
                      have p1917_2 := h1917c.2.2.1
                      have p1917_3 := h1917c.2.2.2
                      linarith only [h1790, hlam, p1917_1]
                    · have p1917_0 := h1917c.1
                      have p1917_1 := h1917c.2.1
                      have p1917_2 := h1917c.2.2.1
                      have p1917_3 := h1917c.2.2.2
                      linarith only [hlam, p1917_0]
                  · linarith only [h1792, h1906, h1913, h1916, h5, h7, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h1790, h1792, h1906, h1913, h1915, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1969 | h1969
        · linarith only [h1, h1969, h7, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1971 | h1971
          · linarith only [h1617, h1790, h1791, h1906, h1971, h6, h7, hc03, hc34, hlam, hphi]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1973 | h1973
            · linarith only [h1, h1791, h1973, h7, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1975 | h1975
              · linarith only [h0, h1617, h1791, h1792, h1975, h5, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1977 | h1977
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1978 | h1978
                  · rcases h0bigk with h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c
                    · have p1979_0 := h1979c.1
                      have p1979_1 := h1979c.2.1
                      have p1979_2 := h1979c.2.2.1
                      have p1979_3 := h1979c.2.2.2
                      linarith only [hlam, p1979_0]
                    · have p1979_0 := h1979c.1
                      have p1979_1 := h1979c.2.1
                      have p1979_2 := h1979c.2.2.1
                      have p1979_3 := h1979c.2.2.2
                      linarith only [h1906, h1977, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1979_1]
                    · have p1979_0 := h1979c.1
                      have p1979_1 := h1979c.2.1
                      have p1979_2 := h1979c.2.2.1
                      have p1979_3 := h1979c.2.2.2
                      rcases p1979_3 (m.d 0 1) (by simp) with h1982 | h1982
                      · rcases p1979_3 (m.d 0 2) (by simp) with h1983 | h1983
                        · linarith only [h0, h1983, hlam]
                        · linarith only [h1983, h4, hlam]
                      · linarith only [h1, h1982, hlam]
                    · have p1979_0 := h1979c.1
                      have p1979_1 := h1979c.2.1
                      have p1979_2 := h1979c.2.2.1
                      have p1979_3 := h1979c.2.2.2
                      linarith only [h1791, h1906, h1977, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1979_1]
                    · have p1979_0 := h1979c.1
                      have p1979_1 := h1979c.2.1
                      have p1979_2 := h1979c.2.2.1
                      have p1979_3 := h1979c.2.2.2
                      linarith only [h1791, h1906, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1979_1]
                    · have p1979_0 := h1979c.1
                      have p1979_1 := h1979c.2.1
                      have p1979_2 := h1979c.2.2.1
                      have p1979_3 := h1979c.2.2.2
                      linarith only [h0, hlam, p1979_0]
                    · have p1979_0 := h1979c.1
                      have p1979_1 := h1979c.2.1
                      have p1979_2 := h1979c.2.2.1
                      have p1979_3 := h1979c.2.2.2
                      linarith only [hlam, p1979_0]
                    · have p1979_0 := h1979c.1
                      have p1979_1 := h1979c.2.1
                      have p1979_2 := h1979c.2.2.1
                      have p1979_3 := h1979c.2.2.2
                      rcases p1979_3 (m.d 0 1) (by simp) with h1991 | h1991
                      · rcases p1979_3 (m.d 0 2) (by simp) with h1992 | h1992
                        · rcases p1979_3 (m.d 0 3) (by simp) with h1993 | h1993
                          · linarith only [h1993, h4, hlam]
                          · rcases p1979_3 (m.d 0 4) (by simp) with h1995 | h1995
                            · linarith only [h1995, h5, hlam]
                            · linarith only [h1995, h7, hlam]
                        · linarith only [h1992, h4, hlam]
                      · linarith only [h1, h1991, hlam]
                    · have p1979_0 := h1979c.1
                      have p1979_1 := h1979c.2.1
                      have p1979_2 := h1979c.2.2.1
                      have p1979_3 := h1979c.2.2.2
                      linarith only [h1791, h1906, h1977, h5, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1979_1]
                    · have p1979_0 := h1979c.1
                      have p1979_1 := h1979c.2.1
                      have p1979_2 := h1979c.2.2.1
                      have p1979_3 := h1979c.2.2.2
                      linarith only [h0, h1791, h1906, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1979_1]
                    · have p1979_0 := h1979c.1
                      have p1979_1 := h1979c.2.1
                      have p1979_2 := h1979c.2.2.1
                      have p1979_3 := h1979c.2.2.2
                      linarith only [h1, hlam, p1979_1]
                    · have p1979_0 := h1979c.1
                      have p1979_1 := h1979c.2.1
                      have p1979_2 := h1979c.2.2.1
                      have p1979_3 := h1979c.2.2.2
                      linarith only [h4, hlam, p1979_1]
                    · have p1979_0 := h1979c.1
                      have p1979_1 := h1979c.2.1
                      have p1979_2 := h1979c.2.2.1
                      have p1979_3 := h1979c.2.2.2
                      linarith only [hlam, p1979_0]
                    · have p1979_0 := h1979c.1
                      have p1979_1 := h1979c.2.1
                      have p1979_2 := h1979c.2.2.1
                      have p1979_3 := h1979c.2.2.2
                      linarith only [h7, hlam, p1979_1]
                    · have p1979_0 := h1979c.1
                      have p1979_1 := h1979c.2.1
                      have p1979_2 := h1979c.2.2.1
                      have p1979_3 := h1979c.2.2.2
                      linarith only [h1617, hlam, p1979_1]
                    · have p1979_0 := h1979c.1
                      have p1979_1 := h1979c.2.1
                      have p1979_2 := h1979c.2.2.1
                      have p1979_3 := h1979c.2.2.2
                      linarith only [h2, hlam, p1979_0]
                    · have p1979_0 := h1979c.1
                      have p1979_1 := h1979c.2.1
                      have p1979_2 := h1979c.2.2.1
                      have p1979_3 := h1979c.2.2.2
                      linarith only [h5, hlam, p1979_0]
                    · have p1979_0 := h1979c.1
                      have p1979_1 := h1979c.2.1
                      have p1979_2 := h1979c.2.2.1
                      have p1979_3 := h1979c.2.2.2
                      linarith only [h1, h1791, h7, hc23, hc34, hlam, hphi, p1979_1]
                    · have p1979_0 := h1979c.1
                      have p1979_1 := h1979c.2.1
                      have p1979_2 := h1979c.2.2.1
                      have p1979_3 := h1979c.2.2.2
                      linarith only [hlam, p1979_0]
                    · have p1979_0 := h1979c.1
                      have p1979_1 := h1979c.2.1
                      have p1979_2 := h1979c.2.2.1
                      have p1979_3 := h1979c.2.2.2
                      linarith only [h1791, h1906, h6, h7, hc23, hc34, hlam, hphi, p1979_1]
                    · have p1979_0 := h1979c.1
                      have p1979_1 := h1979c.2.1
                      have p1979_2 := h1979c.2.2.1
                      have p1979_3 := h1979c.2.2.2
                      linarith only [h3, hlam, p1979_0]
                    · have p1979_0 := h1979c.1
                      have p1979_1 := h1979c.2.1
                      have p1979_2 := h1979c.2.2.1
                      have p1979_3 := h1979c.2.2.2
                      linarith only [h6, hlam, p1979_1]
                    · have p1979_0 := h1979c.1
                      have p1979_1 := h1979c.2.1
                      have p1979_2 := h1979c.2.2.1
                      have p1979_3 := h1979c.2.2.2
                      linarith only [h1, h1617, h1791, hc23, hc35, hlam, hphi, p1979_1]
                    · have p1979_0 := h1979c.1
                      have p1979_1 := h1979c.2.1
                      have p1979_2 := h1979c.2.2.1
                      have p1979_3 := h1979c.2.2.2
                      linarith only [h1790, hlam, p1979_1]
                    · have p1979_0 := h1979c.1
                      have p1979_1 := h1979c.2.1
                      have p1979_2 := h1979c.2.2.1
                      have p1979_3 := h1979c.2.2.2
                      linarith only [hlam, p1979_0]
                  · linarith only [h0, h1791, h1792, h1977, h1978, h2, h5, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h1790, h1791, h1792, h1977, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h2019 | h2019
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2020 | h2020
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2021 | h2021
        · linarith only [h1791, h2021, h4, h7, hlam]
        · linarith only [h1791, h2019, h2021, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2024 | h2024
        · linarith only [h1791, h2019, h2024, h4, h7, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
        · linarith only [h1791, h2019, h2024, hlam]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2027 | h2027
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2028 | h2028
        · linarith only [h1791, h2027, h2028, h4, h7, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2030 | h2030
          · linarith only [h1617, h1791, h2027, h2030, h4, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
          · linarith only [h1791, h2027, h2030, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2033 | h2033
        · linarith only [h1, h1791, h2033, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2035 | h2035
          · linarith only [h1, h1617, h1791, h2035, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2037 | h2037
            · linarith only [h2037, h4, h7, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2039 | h2039
              · linarith only [h1617, h2039, h4, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2041 | h2041
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2042 | h2042
                  · rcases h0bigk with h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c | h2043c
                    · have p2043_0 := h2043c.1
                      have p2043_1 := h2043c.2.1
                      have p2043_2 := h2043c.2.2.1
                      have p2043_3 := h2043c.2.2.2
                      linarith only [hlam, p2043_0]
                    · have p2043_0 := h2043c.1
                      have p2043_1 := h2043c.2.1
                      have p2043_2 := h2043c.2.2.1
                      have p2043_3 := h2043c.2.2.2
                      linarith only [h1791, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2043_1]
                    · have p2043_0 := h2043c.1
                      have p2043_1 := h2043c.2.1
                      have p2043_2 := h2043c.2.2.1
                      have p2043_3 := h2043c.2.2.2
                      linarith only [h1791, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2043_1]
                    · have p2043_0 := h2043c.1
                      have p2043_1 := h2043c.2.1
                      have p2043_2 := h2043c.2.2.1
                      have p2043_3 := h2043c.2.2.2
                      linarith only [h2041, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p2043_1]
                    · have p2043_0 := h2043c.1
                      have p2043_1 := h2043c.2.1
                      have p2043_2 := h2043c.2.2.1
                      have p2043_3 := h2043c.2.2.2
                      linarith only [h1617, h1791, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2043_1]
                    · have p2043_0 := h2043c.1
                      have p2043_1 := h2043c.2.1
                      have p2043_2 := h2043c.2.2.1
                      have p2043_3 := h2043c.2.2.2
                      linarith only [h0, hlam, p2043_0]
                    · have p2043_0 := h2043c.1
                      have p2043_1 := h2043c.2.1
                      have p2043_2 := h2043c.2.2.1
                      have p2043_3 := h2043c.2.2.2
                      linarith only [hlam, p2043_0]
                    · have p2043_0 := h2043c.1
                      have p2043_1 := h2043c.2.1
                      have p2043_2 := h2043c.2.2.1
                      have p2043_3 := h2043c.2.2.2
                      linarith only [h1791, h4, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2043_1]
                    · have p2043_0 := h2043c.1
                      have p2043_1 := h2043c.2.1
                      have p2043_2 := h2043c.2.2.1
                      have p2043_3 := h2043c.2.2.2
                      linarith only [h0, h2041, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p2043_1]
                    · have p2043_0 := h2043c.1
                      have p2043_1 := h2043c.2.1
                      have p2043_2 := h2043c.2.2.1
                      have p2043_3 := h2043c.2.2.2
                      linarith only [h0, h1617, h1791, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2043_1]
                    · have p2043_0 := h2043c.1
                      have p2043_1 := h2043c.2.1
                      have p2043_2 := h2043c.2.2.1
                      have p2043_3 := h2043c.2.2.2
                      linarith only [h1, hlam, p2043_1]
                    · have p2043_0 := h2043c.1
                      have p2043_1 := h2043c.2.1
                      have p2043_2 := h2043c.2.2.1
                      have p2043_3 := h2043c.2.2.2
                      linarith only [h4, hlam, p2043_1]
                    · have p2043_0 := h2043c.1
                      have p2043_1 := h2043c.2.1
                      have p2043_2 := h2043c.2.2.1
                      have p2043_3 := h2043c.2.2.2
                      linarith only [hlam, p2043_0]
                    · have p2043_0 := h2043c.1
                      have p2043_1 := h2043c.2.1
                      have p2043_2 := h2043c.2.2.1
                      have p2043_3 := h2043c.2.2.2
                      linarith only [h7, hlam, p2043_1]
                    · have p2043_0 := h2043c.1
                      have p2043_1 := h2043c.2.1
                      have p2043_2 := h2043c.2.2.1
                      have p2043_3 := h2043c.2.2.2
                      linarith only [h1617, hlam, p2043_1]
                    · have p2043_0 := h2043c.1
                      have p2043_1 := h2043c.2.1
                      have p2043_2 := h2043c.2.2.1
                      have p2043_3 := h2043c.2.2.2
                      linarith only [h2, hlam, p2043_0]
                    · have p2043_0 := h2043c.1
                      have p2043_1 := h2043c.2.1
                      have p2043_2 := h2043c.2.2.1
                      have p2043_3 := h2043c.2.2.2
                      linarith only [h5, hlam, p2043_0]
                    · have p2043_0 := h2043c.1
                      have p2043_1 := h2043c.2.1
                      have p2043_2 := h2043c.2.2.1
                      have p2043_3 := h2043c.2.2.2
                      linarith only [h1791, h4, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2043_1]
                    · have p2043_0 := h2043c.1
                      have p2043_1 := h2043c.2.1
                      have p2043_2 := h2043c.2.2.1
                      have p2043_3 := h2043c.2.2.2
                      linarith only [hlam, p2043_0]
                    · have p2043_0 := h2043c.1
                      have p2043_1 := h2043c.2.1
                      have p2043_2 := h2043c.2.2.1
                      have p2043_3 := h2043c.2.2.2
                      linarith only [h1617, h1791, h4, h7, hc12, hc34, hlam, hphi, ht23, p2043_1]
                    · have p2043_0 := h2043c.1
                      have p2043_1 := h2043c.2.1
                      have p2043_2 := h2043c.2.2.1
                      have p2043_3 := h2043c.2.2.2
                      linarith only [h3, hlam, p2043_0]
                    · have p2043_0 := h2043c.1
                      have p2043_1 := h2043c.2.1
                      have p2043_2 := h2043c.2.2.1
                      have p2043_3 := h2043c.2.2.2
                      linarith only [h6, hlam, p2043_1]
                    · have p2043_0 := h2043c.1
                      have p2043_1 := h2043c.2.1
                      have p2043_2 := h2043c.2.2.1
                      have p2043_3 := h2043c.2.2.2
                      linarith only [h1791, h4, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2043_1]
                    · have p2043_0 := h2043c.1
                      have p2043_1 := h2043c.2.1
                      have p2043_2 := h2043c.2.2.1
                      have p2043_3 := h2043c.2.2.2
                      linarith only [h1790, hlam, p2043_1]
                    · have p2043_0 := h2043c.1
                      have p2043_1 := h2043c.2.1
                      have p2043_2 := h2043c.2.2.1
                      have p2043_3 := h2043c.2.2.2
                      linarith only [hlam, p2043_0]
                  · linarith only [h1791, h2042, h4, h7, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h1790, h2019, h2041, h7, hc12, hc34, hlam, hphi, ht23]

end R2N4
