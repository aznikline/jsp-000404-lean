import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s7_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg7 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1464 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1586 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h1647 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 3 5 (by decide) (by decide) with h1648 | h1648
  · rcases m.htr 1 4 5 (by decide) (by decide) with h1649 | h1649
    · rcases m.htr 2 3 4 (by decide) (by decide) with h1650 | h1650
      · rcases m.htr 2 3 5 (by decide) (by decide) with h1651 | h1651
        · rcases m.htr 2 4 5 (by decide) (by decide) with h1652 | h1652
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1653 | h1653
            · rcases h2bigk with h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c | h1654c
              · have p1654_0 := h1654c.1
                have p1654_1 := h1654c.2.1
                have p1654_2 := h1654c.2.2.1
                have p1654_3 := h1654c.2.2.2
                linarith only [hlam, p1654_0]
              · have p1654_0 := h1654c.1
                have p1654_1 := h1654c.2.1
                have p1654_2 := h1654c.2.2.1
                have p1654_3 := h1654c.2.2.2
                rcases p1654_3 (m.d 0 2) (by simp) with h1656 | h1656
                · rcases p1654_3 (m.d 1 2) (by simp) with h1657 | h1657
                  · linarith only [h0, h1657, hlam]
                  · rcases p1654_3 (m.d 2 3) (by simp) with h1659 | h1659
                    · linarith only [h1659, h2, hlam]
                    · linarith only [h1659, h8, hlam]
                · linarith only [h0, h1656, hlam]
              · have p1654_0 := h1654c.1
                have p1654_1 := h1654c.2.1
                have p1654_2 := h1654c.2.2.1
                have p1654_3 := h1654c.2.2.2
                linarith only [h0, h1647, h1653, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p1654_1]
              · have p1654_0 := h1654c.1
                have p1654_1 := h1654c.2.1
                have p1654_2 := h1654c.2.2.1
                have p1654_3 := h1654c.2.2.2
                rcases p1654_3 (m.d 0 2) (by simp) with h1664 | h1664
                · rcases p1654_3 (m.d 1 2) (by simp) with h1665 | h1665
                  · linarith only [h0, h1665, hlam]
                  · rcases p1654_3 (m.d 2 3) (by simp) with h1667 | h1667
                    · linarith only [h1667, h2, hlam]
                    · linarith only [h1650, h1667, hlam]
                · linarith only [h1664, hlam, p1654_0]
              · have p1654_0 := h1654c.1
                have p1654_1 := h1654c.2.1
                have p1654_2 := h1654c.2.2.1
                have p1654_3 := h1654c.2.2.2
                rcases p1654_3 (m.d 0 2) (by simp) with h1671 | h1671
                · rcases p1654_3 (m.d 1 2) (by simp) with h1672 | h1672
                  · linarith only [h0, h1672, hlam]
                  · rcases p1654_3 (m.d 2 3) (by simp) with h1674 | h1674
                    · linarith only [h1674, h2, hlam]
                    · linarith only [h1651, h1674, hlam]
                · linarith only [h1671, hlam, p1654_0]
              · have p1654_0 := h1654c.1
                have p1654_1 := h1654c.2.1
                have p1654_2 := h1654c.2.2.1
                have p1654_3 := h1654c.2.2.2
                linarith only [h0, hlam, p1654_0]
              · have p1654_0 := h1654c.1
                have p1654_1 := h1654c.2.1
                have p1654_2 := h1654c.2.2.1
                have p1654_3 := h1654c.2.2.2
                linarith only [hlam, p1654_0]
              · have p1654_0 := h1654c.1
                have p1654_1 := h1654c.2.1
                have p1654_2 := h1654c.2.2.1
                have p1654_3 := h1654c.2.2.2
                linarith only [h8, hlam, p1654_0]
              · have p1654_0 := h1654c.1
                have p1654_1 := h1654c.2.1
                have p1654_2 := h1654c.2.2.1
                have p1654_3 := h1654c.2.2.2
                linarith only [h1464, hlam, p1654_0]
              · have p1654_0 := h1654c.1
                have p1654_1 := h1654c.2.1
                have p1654_2 := h1654c.2.2.1
                have p1654_3 := h1654c.2.2.2
                linarith only [h1586, hlam, p1654_0]
              · have p1654_0 := h1654c.1
                have p1654_1 := h1654c.2.1
                have p1654_2 := h1654c.2.2.1
                have p1654_3 := h1654c.2.2.2
                linarith only [h2, hlam, p1654_0]
              · have p1654_0 := h1654c.1
                have p1654_1 := h1654c.2.1
                have p1654_2 := h1654c.2.2.1
                have p1654_3 := h1654c.2.2.2
                rcases p1654_3 (m.d 0 2) (by simp) with h1684 | h1684
                · rcases p1654_3 (m.d 1 2) (by simp) with h1685 | h1685
                  · linarith only [h1685, hlam, p1654_0]
                  · rcases p1654_3 (m.d 2 3) (by simp) with h1687 | h1687
                    · rcases p1654_3 (m.d 2 4) (by simp) with h1688 | h1688
                      · linarith only [h1650, h1688, hlam]
                      · linarith only [h1464, h1688, hlam]
                    · linarith only [h1687, hlam, p1654_0]
                · linarith only [h0, h1684, hlam]
              · have p1654_0 := h1654c.1
                have p1654_1 := h1654c.2.1
                have p1654_2 := h1654c.2.2.1
                have p1654_3 := h1654c.2.2.2
                linarith only [hlam, p1654_0]
              · have p1654_0 := h1654c.1
                have p1654_1 := h1654c.2.1
                have p1654_2 := h1654c.2.2.1
                have p1654_3 := h1654c.2.2.2
                linarith only [h1586, h1652, hc12, hc23, hlam, hphi, p1654_1]
              · have p1654_0 := h1654c.1
                have p1654_1 := h1654c.2.1
                have p1654_2 := h1654c.2.2.1
                have p1654_3 := h1654c.2.2.2
                linarith only [h0, h1586, h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1654_1]
              · have p1654_0 := h1654c.1
                have p1654_1 := h1654c.2.1
                have p1654_2 := h1654c.2.2.1
                have p1654_3 := h1654c.2.2.2
                linarith only [h3, hlam, p1654_0]
              · have p1654_0 := h1654c.1
                have p1654_1 := h1654c.2.1
                have p1654_2 := h1654c.2.2.1
                have p1654_3 := h1654c.2.2.2
                rcases p1654_3 (m.d 0 2) (by simp) with h1697 | h1697
                · rcases p1654_3 (m.d 1 2) (by simp) with h1698 | h1698
                  · linarith only [h1698, hlam, p1654_0]
                  · rcases p1654_3 (m.d 2 3) (by simp) with h1700 | h1700
                    · rcases p1654_3 (m.d 2 4) (by simp) with h1701 | h1701
                      · rcases p1654_3 (m.d 2 5) (by simp) with h1702 | h1702
                        · linarith only [h1652, h1702, hlam]
                        · linarith only [h1586, h1702, hlam]
                      · linarith only [h1701, hlam, p1654_0]
                    · linarith only [h1700, h8, hlam]
                · linarith only [h0, h1697, hlam]
              · have p1654_0 := h1654c.1
                have p1654_1 := h1654c.2.1
                have p1654_2 := h1654c.2.2.1
                have p1654_3 := h1654c.2.2.2
                linarith only [h1650, hlam, p1654_1]
              · have p1654_0 := h1654c.1
                have p1654_1 := h1654c.2.1
                have p1654_2 := h1654c.2.2.1
                have p1654_3 := h1654c.2.2.2
                linarith only [hlam, p1654_0]
              · have p1654_0 := h1654c.1
                have p1654_1 := h1654c.2.1
                have p1654_2 := h1654c.2.2.1
                have p1654_3 := h1654c.2.2.2
                linarith only [h1586, hc12, hc24, hlam, hphi, p1654_1]
              · have p1654_0 := h1654c.1
                have p1654_1 := h1654c.2.1
                have p1654_2 := h1654c.2.2.1
                have p1654_3 := h1654c.2.2.2
                linarith only [h4, hlam, p1654_0]
              · have p1654_0 := h1654c.1
                have p1654_1 := h1654c.2.1
                have p1654_2 := h1654c.2.2.1
                have p1654_3 := h1654c.2.2.2
                rcases p1654_3 (m.d 0 2) (by simp) with h1712 | h1712
                · rcases p1654_3 (m.d 1 2) (by simp) with h1713 | h1713
                  · linarith only [h1713, hlam, p1654_0]
                  · rcases p1654_3 (m.d 2 3) (by simp) with h1715 | h1715
                    · rcases p1654_3 (m.d 2 4) (by simp) with h1716 | h1716
                      · rcases p1654_3 (m.d 2 5) (by simp) with h1717 | h1717
                        · rcases h3bigk with h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c | h1718c
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [hlam, p1718_0]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [h0, h1647, h1653, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1718_1]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [h0, h1647, h1653, h2, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p1718_1]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            rcases p1718_3 (m.d 0 3) (by simp) with h1722 | h1722
                            · rcases p1718_3 (m.d 1 3) (by simp) with h1723 | h1723
                              · linarith only [h1, h1723, hlam]
                              · linarith only [h1647, h1723, hlam]
                            · linarith only [h1722, hlam, p1718_0]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            rcases p1718_3 (m.d 0 3) (by simp) with h1727 | h1727
                            · rcases p1718_3 (m.d 1 3) (by simp) with h1728 | h1728
                              · linarith only [h1, h1728, hlam]
                              · linarith only [h1648, h1728, hlam]
                            · linarith only [h1727, hlam, p1718_0]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [h1, hlam, p1718_0]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [hlam, p1718_0]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [h8, hlam, p1718_1]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [h1, h1653, hc01, hc45, hlam, hphi, ht0b, ht5b, p1718_1]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            rcases p1718_3 (m.d 0 3) (by simp) with h1736 | h1736
                            · rcases p1718_3 (m.d 1 3) (by simp) with h1737 | h1737
                              · rcases p1718_3 (m.d 2 3) (by simp) with h1738 | h1738
                                · rcases p1718_3 (m.d 3 4) (by simp) with h1739 | h1739
                                  · linarith only [h1647, h1739, hlam]
                                  · linarith only [h1653, h1739, hlam]
                                · linarith only [h1651, h1738, hlam]
                              · linarith only [h1737, hlam, p1718_0]
                            · linarith only [h1736, h6, hlam]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [h2, hlam, p1718_0]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [h1647, h1653, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1718_1]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [hlam, p1718_0]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [h0, h1653, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1718_1]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            rcases p1718_3 (m.d 0 3) (by simp) with h1749 | h1749
                            · rcases p1718_3 (m.d 1 3) (by simp) with h1750 | h1750
                              · linarith only [h1750, h8, hlam]
                              · linarith only [h1648, h1750, hlam]
                            · linarith only [h1749, h6, hlam]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [h5, hlam, p1718_0]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [h1647, hlam, p1718_0]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [h1650, hlam, p1718_0]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [hlam, p1718_0]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [h1, h1647, h1653, hc01, hc45, hlam, hphi, ht0b, ht5b, p1718_1]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [h6, hlam, p1718_0]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [h1648, hlam, p1718_0]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [h1651, hlam, p1718_0]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [h1653, hlam, p1718_0]
                          · have p1718_0 := h1718c.1
                            have p1718_1 := h1718c.2.1
                            have p1718_2 := h1718c.2.2.1
                            have p1718_3 := h1718c.2.2.2
                            linarith only [hlam, p1718_0]
                        · linarith only [h1717, hlam, p1654_0]
                      · linarith only [h1464, h1716, hlam]
                    · linarith only [h1715, h8, hlam]
                · linarith only [h0, h1712, hlam]
              · have p1654_0 := h1654c.1
                have p1654_1 := h1654c.2.1
                have p1654_2 := h1654c.2.2.1
                have p1654_3 := h1654c.2.2.2
                linarith only [h1651, hlam, p1654_1]
              · have p1654_0 := h1654c.1
                have p1654_1 := h1654c.2.1
                have p1654_2 := h1654c.2.2.1
                have p1654_3 := h1654c.2.2.2
                linarith only [h1652, hlam, p1654_0]
              · have p1654_0 := h1654c.1
                have p1654_1 := h1654c.2.1
                have p1654_2 := h1654c.2.2.1
                have p1654_3 := h1654c.2.2.2
                linarith only [hlam, p1654_0]
            · rcases h2bigk with h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c
              · have p1771_0 := h1771c.1
                have p1771_1 := h1771c.2.1
                have p1771_2 := h1771c.2.2.1
                have p1771_3 := h1771c.2.2.2
                linarith only [hlam, p1771_0]
              · have p1771_0 := h1771c.1
                have p1771_1 := h1771c.2.1
                have p1771_2 := h1771c.2.2.1
                have p1771_3 := h1771c.2.2.2
                rcases p1771_3 (m.d 0 2) (by simp) with h1773 | h1773
                · rcases p1771_3 (m.d 1 2) (by simp) with h1774 | h1774
                  · linarith only [h0, h1774, hlam]
                  · rcases p1771_3 (m.d 2 3) (by simp) with h1776 | h1776
                    · linarith only [h1776, h2, hlam]
                    · linarith only [h1776, h8, hlam]
                · linarith only [h0, h1773, hlam]
              · have p1771_0 := h1771c.1
                have p1771_1 := h1771c.2.1
                have p1771_2 := h1771c.2.2.1
                have p1771_3 := h1771c.2.2.2
                linarith only [h0, h1464, h1649, h1650, h1653, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1771_1]
              · have p1771_0 := h1771c.1
                have p1771_1 := h1771c.2.1
                have p1771_2 := h1771c.2.2.1
                have p1771_3 := h1771c.2.2.2
                linarith only [h0, h1464, h1649, h1653, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1771_1]
              · have p1771_0 := h1771c.1
                have p1771_1 := h1771c.2.1
                have p1771_2 := h1771c.2.2.1
                have p1771_3 := h1771c.2.2.2
                rcases p1771_3 (m.d 0 2) (by simp) with h1782 | h1782
                · rcases p1771_3 (m.d 1 2) (by simp) with h1783 | h1783
                  · linarith only [h0, h1783, hlam]
                  · rcases p1771_3 (m.d 2 3) (by simp) with h1785 | h1785
                    · linarith only [h1785, h2, hlam]
                    · linarith only [h1651, h1785, hlam]
                · linarith only [h1782, hlam, p1771_0]
              · have p1771_0 := h1771c.1
                have p1771_1 := h1771c.2.1
                have p1771_2 := h1771c.2.2.1
                have p1771_3 := h1771c.2.2.2
                linarith only [h0, hlam, p1771_0]
              · have p1771_0 := h1771c.1
                have p1771_1 := h1771c.2.1
                have p1771_2 := h1771c.2.2.1
                have p1771_3 := h1771c.2.2.2
                linarith only [hlam, p1771_0]
              · have p1771_0 := h1771c.1
                have p1771_1 := h1771c.2.1
                have p1771_2 := h1771c.2.2.1
                have p1771_3 := h1771c.2.2.2
                linarith only [h8, hlam, p1771_0]
              · have p1771_0 := h1771c.1
                have p1771_1 := h1771c.2.1
                have p1771_2 := h1771c.2.2.1
                have p1771_3 := h1771c.2.2.2
                linarith only [h1464, hlam, p1771_0]
              · have p1771_0 := h1771c.1
                have p1771_1 := h1771c.2.1
                have p1771_2 := h1771c.2.2.1
                have p1771_3 := h1771c.2.2.2
                linarith only [h1586, hlam, p1771_0]
              · have p1771_0 := h1771c.1
                have p1771_1 := h1771c.2.1
                have p1771_2 := h1771c.2.2.1
                have p1771_3 := h1771c.2.2.2
                linarith only [h2, hlam, p1771_0]
              · have p1771_0 := h1771c.1
                have p1771_1 := h1771c.2.1
                have p1771_2 := h1771c.2.2.1
                have p1771_3 := h1771c.2.2.2
                rcases p1771_3 (m.d 0 2) (by simp) with h1795 | h1795
                · rcases p1771_3 (m.d 1 2) (by simp) with h1796 | h1796
                  · linarith only [h1796, hlam, p1771_0]
                  · rcases p1771_3 (m.d 2 3) (by simp) with h1798 | h1798
                    · rcases p1771_3 (m.d 2 4) (by simp) with h1799 | h1799
                      · linarith only [h1650, h1799, hlam]
                      · linarith only [h1464, h1799, hlam]
                    · linarith only [h1798, hlam, p1771_0]
                · linarith only [h0, h1795, hlam]
              · have p1771_0 := h1771c.1
                have p1771_1 := h1771c.2.1
                have p1771_2 := h1771c.2.2.1
                have p1771_3 := h1771c.2.2.2
                linarith only [hlam, p1771_0]
              · have p1771_0 := h1771c.1
                have p1771_1 := h1771c.2.1
                have p1771_2 := h1771c.2.2.1
                have p1771_3 := h1771c.2.2.2
                linarith only [h1464, h1649, h1653, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1771_1]
              · have p1771_0 := h1771c.1
                have p1771_1 := h1771c.2.1
                have p1771_2 := h1771c.2.2.1
                have p1771_3 := h1771c.2.2.2
                linarith only [h0, h1586, h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1771_1]
              · have p1771_0 := h1771c.1
                have p1771_1 := h1771c.2.1
                have p1771_2 := h1771c.2.2.1
                have p1771_3 := h1771c.2.2.2
                linarith only [h3, hlam, p1771_0]
              · have p1771_0 := h1771c.1
                have p1771_1 := h1771c.2.1
                have p1771_2 := h1771c.2.2.1
                have p1771_3 := h1771c.2.2.2
                rcases p1771_3 (m.d 0 2) (by simp) with h1808 | h1808
                · rcases p1771_3 (m.d 1 2) (by simp) with h1809 | h1809
                  · linarith only [h1809, hlam, p1771_0]
                  · rcases p1771_3 (m.d 2 3) (by simp) with h1811 | h1811
                    · rcases p1771_3 (m.d 2 4) (by simp) with h1812 | h1812
                      · rcases p1771_3 (m.d 2 5) (by simp) with h1813 | h1813
                        · linarith only [h1652, h1813, hlam]
                        · linarith only [h1586, h1813, hlam]
                      · linarith only [h1812, hlam, p1771_0]
                    · linarith only [h1811, h8, hlam]
                · linarith only [h0, h1808, hlam]
              · have p1771_0 := h1771c.1
                have p1771_1 := h1771c.2.1
                have p1771_2 := h1771c.2.2.1
                have p1771_3 := h1771c.2.2.2
                linarith only [h1650, hlam, p1771_1]
              · have p1771_0 := h1771c.1
                have p1771_1 := h1771c.2.1
                have p1771_2 := h1771c.2.2.1
                have p1771_3 := h1771c.2.2.2
                linarith only [hlam, p1771_0]
              · have p1771_0 := h1771c.1
                have p1771_1 := h1771c.2.1
                have p1771_2 := h1771c.2.2.1
                have p1771_3 := h1771c.2.2.2
                linarith only [h1586, hc12, hc24, hlam, hphi, p1771_1]
              · have p1771_0 := h1771c.1
                have p1771_1 := h1771c.2.1
                have p1771_2 := h1771c.2.2.1
                have p1771_3 := h1771c.2.2.2
                linarith only [h4, hlam, p1771_0]
              · have p1771_0 := h1771c.1
                have p1771_1 := h1771c.2.1
                have p1771_2 := h1771c.2.2.1
                have p1771_3 := h1771c.2.2.2
                rcases p1771_3 (m.d 0 2) (by simp) with h1823 | h1823
                · rcases p1771_3 (m.d 1 2) (by simp) with h1824 | h1824
                  · linarith only [h1824, hlam, p1771_0]
                  · rcases p1771_3 (m.d 2 3) (by simp) with h1826 | h1826
                    · rcases p1771_3 (m.d 2 4) (by simp) with h1827 | h1827
                      · rcases p1771_3 (m.d 2 5) (by simp) with h1828 | h1828
                        · rcases h3bigk with h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c | h1829c
                          · have p1829_0 := h1829c.1
                            have p1829_1 := h1829c.2.1
                            have p1829_2 := h1829c.2.2.1
                            have p1829_3 := h1829c.2.2.2
                            linarith only [hlam, p1829_0]
                          · have p1829_0 := h1829c.1
                            have p1829_1 := h1829c.2.1
                            have p1829_2 := h1829c.2.2.1
                            have p1829_3 := h1829c.2.2.2
                            linarith only [h0, h1647, h1649, h1653, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1829_1]
                          · have p1829_0 := h1829c.1
                            have p1829_1 := h1829c.2.1
                            have p1829_2 := h1829c.2.2.1
                            have p1829_3 := h1829c.2.2.2
                            linarith only [h0, h1464, h1649, h1650, h1653, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1829_1]
                          · have p1829_0 := h1829c.1
                            have p1829_1 := h1829c.2.1
                            have p1829_2 := h1829c.2.2.1
                            have p1829_3 := h1829c.2.2.2
                            rcases p1829_3 (m.d 0 3) (by simp) with h1833 | h1833
                            · rcases p1829_3 (m.d 1 3) (by simp) with h1834 | h1834
                              · linarith only [h1, h1834, hlam]
                              · linarith only [h1647, h1834, hlam]
                            · linarith only [h1833, hlam, p1829_0]
                          · have p1829_0 := h1829c.1
                            have p1829_1 := h1829c.2.1
                            have p1829_2 := h1829c.2.2.1
                            have p1829_3 := h1829c.2.2.2
                            rcases p1829_3 (m.d 0 3) (by simp) with h1838 | h1838
                            · rcases p1829_3 (m.d 1 3) (by simp) with h1839 | h1839
                              · linarith only [h1, h1839, hlam]
                              · linarith only [h1648, h1839, hlam]
                            · linarith only [h1838, hlam, p1829_0]
                          · have p1829_0 := h1829c.1
                            have p1829_1 := h1829c.2.1
                            have p1829_2 := h1829c.2.2.1
                            have p1829_3 := h1829c.2.2.2
                            linarith only [h1, hlam, p1829_0]
                          · have p1829_0 := h1829c.1
                            have p1829_1 := h1829c.2.1
                            have p1829_2 := h1829c.2.2.1
                            have p1829_3 := h1829c.2.2.2
                            linarith only [hlam, p1829_0]
                          · have p1829_0 := h1829c.1
                            have p1829_1 := h1829c.2.1
                            have p1829_2 := h1829c.2.2.1
                            have p1829_3 := h1829c.2.2.2
                            linarith only [h8, hlam, p1829_1]
                          · have p1829_0 := h1829c.1
                            have p1829_1 := h1829c.2.1
                            have p1829_2 := h1829c.2.2.1
                            have p1829_3 := h1829c.2.2.2
                            rcases p1829_3 (m.d 0 3) (by simp) with h1846 | h1846
                            · rcases p1829_3 (m.d 1 3) (by simp) with h1847 | h1847
                              · rcases p1829_3 (m.d 2 3) (by simp) with h1848 | h1848
                                · rcases p1829_3 (m.d 3 4) (by simp) with h1849 | h1849
                                  · linarith only [h1849, hlam, p1829_0]
                                  · rcases p1829_3 (m.d 3 5) (by simp) with h1851 | h1851
                                    · linarith only [h1648, h1851, hlam]
                                    · linarith only [h1653, h1851, hlam]
                                · linarith only [h1650, h1848, hlam]
                              · linarith only [h1847, hlam, p1829_0]
                            · linarith only [h1846, h5, hlam]
                          · have p1829_0 := h1829c.1
                            have p1829_1 := h1829c.2.1
                            have p1829_2 := h1829c.2.2.1
                            have p1829_3 := h1829c.2.2.2
                            rcases p1829_3 (m.d 0 3) (by simp) with h1857 | h1857
                            · rcases p1829_3 (m.d 1 3) (by simp) with h1858 | h1858
                              · rcases p1829_3 (m.d 2 3) (by simp) with h1859 | h1859
                                · rcases p1829_3 (m.d 3 4) (by simp) with h1860 | h1860
                                  · linarith only [h1647, h1860, hlam]
                                  · rcases p1829_3 (m.d 3 5) (by simp) with h1862 | h1862
                                    · linarith only [h1862, hlam, p1829_0]
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
                                        rcases p1864_3 (m.d 0 5) (by simp) with h1866 | h1866
                                        · rcases p1864_3 (m.d 1 5) (by simp) with h1867 | h1867
                                          · linarith only [h1867, hlam, p1864_0]
                                          · rcases p1864_3 (m.d 2 5) (by simp) with h1869 | h1869
                                            · linarith only [h1869, h4, hlam]
                                            · linarith only [h1586, h1869, hlam]
                                        · linarith only [h1866, hlam, p1864_0]
                                      · have p1864_0 := h1864c.1
                                        have p1864_1 := h1864c.2.1
                                        have p1864_2 := h1864c.2.2.1
                                        have p1864_3 := h1864c.2.2.2
                                        linarith only [h0, h2, h5, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1771_1, p1864_1]
                                      · have p1864_0 := h1864c.1
                                        have p1864_1 := h1864c.2.1
                                        have p1864_2 := h1864c.2.2.1
                                        have p1864_3 := h1864c.2.2.2
                                        rcases p1864_3 (m.d 0 5) (by simp) with h1874 | h1874
                                        · rcases p1864_3 (m.d 1 5) (by simp) with h1875 | h1875
                                          · linarith only [h0, h1586, h1875, h4, hc01, hlam, hphi, u0ehi4]
                                          · linarith only [h1648, h1875, hlam]
                                        · linarith only [h1874, h6, hlam]
                                      · have p1864_0 := h1864c.1
                                        have p1864_1 := h1864c.2.1
                                        have p1864_2 := h1864c.2.2.1
                                        have p1864_3 := h1864c.2.2.2
                                        rcases p1864_3 (m.d 0 5) (by simp) with h1879 | h1879
                                        · rcases p1864_3 (m.d 1 5) (by simp) with h1880 | h1880
                                          · linarith only [h0, h1464, h1649, h1650, h1653, h1880, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1864_1]
                                          · linarith only [h1649, h1880, hlam]
                                        · linarith only [h1879, h7, hlam]
                                      · have p1864_0 := h1864c.1
                                        have p1864_1 := h1864c.2.1
                                        have p1864_2 := h1864c.2.2.1
                                        have p1864_3 := h1864c.2.2.2
                                        linarith only [h0, h1464, h1649, h1650, h2, hc01, hlam, hphi, p1864_1, u0ehi4]
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
                                        rcases p1864_3 (m.d 0 5) (by simp) with h1887 | h1887
                                        · rcases p1864_3 (m.d 1 5) (by simp) with h1888 | h1888
                                          · rcases p1864_3 (m.d 2 5) (by simp) with h1889 | h1889
                                            · rcases p1864_3 (m.d 3 5) (by simp) with h1890 | h1890
                                              · linarith only [h1648, h1890, hlam]
                                              · rcases p1864_3 (m.d 4 5) (by simp) with h1892 | h1892
                                                · linarith only [h1649, h1892, hlam]
                                                · linarith only [h1653, h1892, hlam]
                                            · linarith only [h1651, h1889, hlam]
                                          · linarith only [h1648, h1888, hlam]
                                        · linarith only [h1887, h6, hlam]
                                      · have p1864_0 := h1864c.1
                                        have p1864_1 := h1864c.2.1
                                        have p1864_2 := h1864c.2.2.1
                                        have p1864_3 := h1864c.2.2.2
                                        linarith only [h0, h1464, h1649, h1650, h1653, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1864_1]
                                      · have p1864_0 := h1864c.1
                                        have p1864_1 := h1864c.2.1
                                        have p1864_2 := h1864c.2.2.1
                                        have p1864_3 := h1864c.2.2.2
                                        linarith only [h4, hlam, p1864_1]
                                      · have p1864_0 := h1864c.1
                                        have p1864_1 := h1864c.2.1
                                        have p1864_2 := h1864c.2.2.1
                                        have p1864_3 := h1864c.2.2.2
                                        linarith only [h0, h1649, h1650, h1652, h1653, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1864_1]
                                      · have p1864_0 := h1864c.1
                                        have p1864_1 := h1864c.2.1
                                        have p1864_2 := h1864c.2.2.1
                                        have p1864_3 := h1864c.2.2.2
                                        linarith only [hlam, p1864_0]
                                      · have p1864_0 := h1864c.1
                                        have p1864_1 := h1864c.2.1
                                        have p1864_2 := h1864c.2.2.1
                                        have p1864_3 := h1864c.2.2.2
                                        rcases p1864_3 (m.d 0 5) (by simp) with h1902 | h1902
                                        · rcases p1864_3 (m.d 1 5) (by simp) with h1903 | h1903
                                          · linarith only [h1586, h1903, hlam]
                                          · linarith only [h1648, h1903, hlam]
                                        · linarith only [h1902, h6, hlam]
                                      · have p1864_0 := h1864c.1
                                        have p1864_1 := h1864c.2.1
                                        have p1864_2 := h1864c.2.2.1
                                        have p1864_3 := h1864c.2.2.2
                                        linarith only [h0, h1650, h1652, h1653, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1864_1]
                                      · have p1864_0 := h1864c.1
                                        have p1864_1 := h1864c.2.1
                                        have p1864_2 := h1864c.2.2.1
                                        have p1864_3 := h1864c.2.2.2
                                        linarith only [h6, hlam, p1864_0]
                                      · have p1864_0 := h1864c.1
                                        have p1864_1 := h1864c.2.1
                                        have p1864_2 := h1864c.2.2.1
                                        have p1864_3 := h1864c.2.2.2
                                        linarith only [h1648, hlam, p1864_0]
                                      · have p1864_0 := h1864c.1
                                        have p1864_1 := h1864c.2.1
                                        have p1864_2 := h1864c.2.2.1
                                        have p1864_3 := h1864c.2.2.2
                                        linarith only [h1651, hlam, p1864_0]
                                      · have p1864_0 := h1864c.1
                                        have p1864_1 := h1864c.2.1
                                        have p1864_2 := h1864c.2.2.1
                                        have p1864_3 := h1864c.2.2.2
                                        linarith only [hlam, p1864_0]
                                      · have p1864_0 := h1864c.1
                                        have p1864_1 := h1864c.2.1
                                        have p1864_2 := h1864c.2.2.1
                                        have p1864_3 := h1864c.2.2.2
                                        linarith only [h1653, hlam, p1864_1]
                                      · have p1864_0 := h1864c.1
                                        have p1864_1 := h1864c.2.1
                                        have p1864_2 := h1864c.2.2.1
                                        have p1864_3 := h1864c.2.2.2
                                        linarith only [h7, hlam, p1864_0]
                                      · have p1864_0 := h1864c.1
                                        have p1864_1 := h1864c.2.1
                                        have p1864_2 := h1864c.2.2.1
                                        have p1864_3 := h1864c.2.2.2
                                        linarith only [h1649, hlam, p1864_0]
                                      · have p1864_0 := h1864c.1
                                        have p1864_1 := h1864c.2.1
                                        have p1864_2 := h1864c.2.2.1
                                        have p1864_3 := h1864c.2.2.2
                                        linarith only [h1652, hlam, p1864_0]
                                      · have p1864_0 := h1864c.1
                                        have p1864_1 := h1864c.2.1
                                        have p1864_2 := h1864c.2.2.1
                                        have p1864_3 := h1864c.2.2.2
                                        linarith only [h0, h1464, h1649, h1650, h1653, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1864_1]
                                      · have p1864_0 := h1864c.1
                                        have p1864_1 := h1864c.2.1
                                        have p1864_2 := h1864c.2.2.1
                                        have p1864_3 := h1864c.2.2.2
                                        linarith only [hlam, p1864_0]
                                · linarith only [h1651, h1859, hlam]
                              · linarith only [h1858, hlam, p1829_0]
                            · linarith only [h1857, h6, hlam]
                          · have p1829_0 := h1829c.1
                            have p1829_1 := h1829c.2.1
                            have p1829_2 := h1829c.2.2.1
                            have p1829_3 := h1829c.2.2.2
                            linarith only [h2, hlam, p1829_0]
                          · have p1829_0 := h1829c.1
                            have p1829_1 := h1829c.2.1
                            have p1829_2 := h1829c.2.2.1
                            have p1829_3 := h1829c.2.2.2
                            linarith only [h0, h1647, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1829_1]
                          · have p1829_0 := h1829c.1
                            have p1829_1 := h1829c.2.1
                            have p1829_2 := h1829c.2.2.1
                            have p1829_3 := h1829c.2.2.2
                            linarith only [hlam, p1829_0]
                          · have p1829_0 := h1829c.1
                            have p1829_1 := h1829c.2.1
                            have p1829_2 := h1829c.2.2.1
                            have p1829_3 := h1829c.2.2.2
                            rcases p1829_3 (m.d 0 3) (by simp) with h1924 | h1924
                            · rcases p1829_3 (m.d 1 3) (by simp) with h1925 | h1925
                              · linarith only [h1925, h8, hlam]
                              · linarith only [h1647, h1925, hlam]
                            · linarith only [h1924, h5, hlam]
                          · have p1829_0 := h1829c.1
                            have p1829_1 := h1829c.2.1
                            have p1829_2 := h1829c.2.2.1
                            have p1829_3 := h1829c.2.2.2
                            rcases p1829_3 (m.d 0 3) (by simp) with h1929 | h1929
                            · rcases p1829_3 (m.d 1 3) (by simp) with h1930 | h1930
                              · linarith only [h1930, h8, hlam]
                              · linarith only [h1648, h1930, hlam]
                            · linarith only [h1929, h6, hlam]
                          · have p1829_0 := h1829c.1
                            have p1829_1 := h1829c.2.1
                            have p1829_2 := h1829c.2.2.1
                            have p1829_3 := h1829c.2.2.2
                            linarith only [h5, hlam, p1829_0]
                          · have p1829_0 := h1829c.1
                            have p1829_1 := h1829c.2.1
                            have p1829_2 := h1829c.2.2.1
                            have p1829_3 := h1829c.2.2.2
                            linarith only [h1647, hlam, p1829_0]
                          · have p1829_0 := h1829c.1
                            have p1829_1 := h1829c.2.1
                            have p1829_2 := h1829c.2.2.1
                            have p1829_3 := h1829c.2.2.2
                            linarith only [h1650, hlam, p1829_0]
                          · have p1829_0 := h1829c.1
                            have p1829_1 := h1829c.2.1
                            have p1829_2 := h1829c.2.2.1
                            have p1829_3 := h1829c.2.2.2
                            linarith only [hlam, p1829_0]
                          · have p1829_0 := h1829c.1
                            have p1829_1 := h1829c.2.1
                            have p1829_2 := h1829c.2.2.1
                            have p1829_3 := h1829c.2.2.2
                            linarith only [h1653, hlam, p1829_1]
                          · have p1829_0 := h1829c.1
                            have p1829_1 := h1829c.2.1
                            have p1829_2 := h1829c.2.2.1
                            have p1829_3 := h1829c.2.2.2
                            linarith only [h6, hlam, p1829_0]
                          · have p1829_0 := h1829c.1
                            have p1829_1 := h1829c.2.1
                            have p1829_2 := h1829c.2.2.1
                            have p1829_3 := h1829c.2.2.2
                            linarith only [h1648, hlam, p1829_0]
                          · have p1829_0 := h1829c.1
                            have p1829_1 := h1829c.2.1
                            have p1829_2 := h1829c.2.2.1
                            have p1829_3 := h1829c.2.2.2
                            linarith only [h1651, hlam, p1829_0]
                          · have p1829_0 := h1829c.1
                            have p1829_1 := h1829c.2.1
                            have p1829_2 := h1829c.2.2.1
                            have p1829_3 := h1829c.2.2.2
                            linarith only [h0, h1648, h2, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1829_1]
                          · have p1829_0 := h1829c.1
                            have p1829_1 := h1829c.2.1
                            have p1829_2 := h1829c.2.2.1
                            have p1829_3 := h1829c.2.2.2
                            linarith only [hlam, p1829_0]
                        · linarith only [h1828, hlam, p1771_0]
                      · linarith only [h1464, h1827, hlam]
                    · linarith only [h1826, h8, hlam]
                · linarith only [h0, h1823, hlam]
              · have p1771_0 := h1771c.1
                have p1771_1 := h1771c.2.1
                have p1771_2 := h1771c.2.2.1
                have p1771_3 := h1771c.2.2.2
                linarith only [h1651, hlam, p1771_1]
              · have p1771_0 := h1771c.1
                have p1771_1 := h1771c.2.1
                have p1771_2 := h1771c.2.2.1
                have p1771_3 := h1771c.2.2.2
                linarith only [h1652, hlam, p1771_0]
              · have p1771_0 := h1771c.1
                have p1771_1 := h1771c.2.1
                have p1771_2 := h1771c.2.2.1
                have p1771_3 := h1771c.2.2.2
                linarith only [hlam, p1771_0]
          · linarith only [h0, h1464, h1647, h1649, h1652, h2, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · linarith only [h1648, h1651, h8, hlam]
      · linarith only [h1647, h1650, h8, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h1954 | h1954
      · rcases m.htr 2 3 5 (by decide) (by decide) with h1955 | h1955
        · rcases m.htr 2 4 5 (by decide) (by decide) with h1956 | h1956
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1957 | h1957
            · linarith only [h1, h1647, h1649, h1957, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · rcases h2bigk with h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c | h1959c
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [hlam, p1959_0]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [h1464, h1649, h1954, h1956, h2, hlam, p1959_2]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [h0, h1464, h1649, h1954, h1956, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1959_1]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [h0, h1464, h1649, h1956, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1959_1]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                rcases p1959_3 (m.d 0 2) (by simp) with h1964 | h1964
                · rcases p1959_3 (m.d 1 2) (by simp) with h1965 | h1965
                  · linarith only [h0, h1965, hlam]
                  · rcases p1959_3 (m.d 2 3) (by simp) with h1967 | h1967
                    · linarith only [h1967, h2, hlam]
                    · linarith only [h1955, h1967, hlam]
                · linarith only [h1964, hlam, p1959_0]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [h0, hlam, p1959_0]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [hlam, p1959_0]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [h8, hlam, p1959_0]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [h1464, hlam, p1959_0]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [h1586, hlam, p1959_0]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [h2, hlam, p1959_0]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                rcases p1959_3 (m.d 0 2) (by simp) with h1977 | h1977
                · rcases p1959_3 (m.d 1 2) (by simp) with h1978 | h1978
                  · linarith only [h1978, hlam, p1959_0]
                  · rcases p1959_3 (m.d 2 3) (by simp) with h1980 | h1980
                    · rcases p1959_3 (m.d 2 4) (by simp) with h1981 | h1981
                      · linarith only [h1954, h1981, hlam]
                      · linarith only [h1464, h1981, hlam]
                    · linarith only [h1980, hlam, p1959_0]
                · linarith only [h0, h1977, hlam]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [hlam, p1959_0]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [h1464, h1649, h1956, hc12, hc23, hlam, hphi, p1959_1]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [h0, h1586, h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1959_1]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [h3, hlam, p1959_0]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                rcases p1959_3 (m.d 0 2) (by simp) with h1990 | h1990
                · rcases p1959_3 (m.d 1 2) (by simp) with h1991 | h1991
                  · linarith only [h1991, hlam, p1959_0]
                  · rcases p1959_3 (m.d 2 3) (by simp) with h1993 | h1993
                    · rcases p1959_3 (m.d 2 4) (by simp) with h1994 | h1994
                      · rcases p1959_3 (m.d 2 5) (by simp) with h1995 | h1995
                        · linarith only [h1956, h1995, hlam]
                        · linarith only [h1586, h1995, hlam]
                      · linarith only [h1994, hlam, p1959_0]
                    · linarith only [h1993, h8, hlam]
                · linarith only [h0, h1990, hlam]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [h1954, hlam, p1959_1]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [hlam, p1959_0]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [h1464, h1649, h1956, hc12, hc24, hlam, hphi, p1959_1]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [h4, hlam, p1959_0]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                rcases p1959_3 (m.d 0 2) (by simp) with h2005 | h2005
                · rcases p1959_3 (m.d 1 2) (by simp) with h2006 | h2006
                  · linarith only [h2006, hlam, p1959_0]
                  · rcases p1959_3 (m.d 2 3) (by simp) with h2008 | h2008
                    · rcases p1959_3 (m.d 2 4) (by simp) with h2009 | h2009
                      · rcases p1959_3 (m.d 2 5) (by simp) with h2010 | h2010
                        · rcases h3bigk with h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c | h2011c
                          · have p2011_0 := h2011c.1
                            have p2011_1 := h2011c.2.1
                            have p2011_2 := h2011c.2.2.1
                            have p2011_3 := h2011c.2.2.2
                            linarith only [hlam, p2011_0]
                          · have p2011_0 := h2011c.1
                            have p2011_1 := h2011c.2.1
                            have p2011_2 := h2011c.2.2.1
                            have p2011_3 := h2011c.2.2.2
                            rcases p2011_3 (m.d 0 3) (by simp) with h2013 | h2013
                            · rcases p2011_3 (m.d 1 3) (by simp) with h2014 | h2014
                              · linarith only [h1, h2014, hlam]
                              · rcases p2011_3 (m.d 2 3) (by simp) with h2016 | h2016
                                · linarith only [h2, h2016, hlam]
                                · linarith only [h2016, h8, hlam]
                            · linarith only [h1, h2013, hlam]
                          · have p2011_0 := h2011c.1
                            have p2011_1 := h2011c.2.1
                            have p2011_2 := h2011c.2.2.1
                            have p2011_3 := h2011c.2.2.2
                            linarith only [h0, h1955, h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1959_1, p2011_1]
                          · have p2011_0 := h2011c.1
                            have p2011_1 := h2011c.2.1
                            have p2011_2 := h2011c.2.2.1
                            have p2011_3 := h2011c.2.2.2
                            rcases p2011_3 (m.d 0 3) (by simp) with h2021 | h2021
                            · rcases p2011_3 (m.d 1 3) (by simp) with h2022 | h2022
                              · linarith only [h1, h2022, hlam]
                              · linarith only [h1647, h2022, hlam]
                            · linarith only [h2021, hlam, p2011_0]
                          · have p2011_0 := h2011c.1
                            have p2011_1 := h2011c.2.1
                            have p2011_2 := h2011c.2.2.1
                            have p2011_3 := h2011c.2.2.2
                            rcases p2011_3 (m.d 0 3) (by simp) with h2026 | h2026
                            · rcases p2011_3 (m.d 1 3) (by simp) with h2027 | h2027
                              · linarith only [h1, h2027, hlam]
                              · linarith only [h1648, h2027, hlam]
                            · linarith only [h2026, hlam, p2011_0]
                          · have p2011_0 := h2011c.1
                            have p2011_1 := h2011c.2.1
                            have p2011_2 := h2011c.2.2.1
                            have p2011_3 := h2011c.2.2.2
                            linarith only [h1, hlam, p2011_0]
                          · have p2011_0 := h2011c.1
                            have p2011_1 := h2011c.2.1
                            have p2011_2 := h2011c.2.2.1
                            have p2011_3 := h2011c.2.2.2
                            linarith only [hlam, p2011_0]
                          · have p2011_0 := h2011c.1
                            have p2011_1 := h2011c.2.1
                            have p2011_2 := h2011c.2.2.1
                            have p2011_3 := h2011c.2.2.2
                            linarith only [h8, hlam, p2011_1]
                          · have p2011_0 := h2011c.1
                            have p2011_1 := h2011c.2.1
                            have p2011_2 := h2011c.2.2.1
                            have p2011_3 := h2011c.2.2.2
                            rcases p2011_3 (m.d 0 3) (by simp) with h2034 | h2034
                            · rcases p2011_3 (m.d 1 3) (by simp) with h2035 | h2035
                              · rcases p2011_3 (m.d 2 3) (by simp) with h2036 | h2036
                                · rcases p2011_3 (m.d 3 4) (by simp) with h2037 | h2037
                                  · linarith only [h2037, hlam, p2011_0]
                                  · rcases p2011_3 (m.d 3 5) (by simp) with h2039 | h2039
                                    · linarith only [h1648, h2039, hlam]
                                    · linarith only [h1957, h2039, hlam]
                                · linarith only [h1954, h2036, hlam]
                              · linarith only [h2035, hlam, p2011_0]
                            · linarith only [h2034, h5, hlam]
                          · have p2011_0 := h2011c.1
                            have p2011_1 := h2011c.2.1
                            have p2011_2 := h2011c.2.2.1
                            have p2011_3 := h2011c.2.2.2
                            rcases p2011_3 (m.d 0 3) (by simp) with h2045 | h2045
                            · rcases p2011_3 (m.d 1 3) (by simp) with h2046 | h2046
                              · rcases p2011_3 (m.d 2 3) (by simp) with h2047 | h2047
                                · rcases p2011_3 (m.d 3 4) (by simp) with h2048 | h2048
                                  · linarith only [h1647, h2048, hlam]
                                  · rcases p2011_3 (m.d 3 5) (by simp) with h2050 | h2050
                                    · linarith only [h2050, hlam, p2011_0]
                                    · rcases h5bigk with h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c
                                      · have p2052_0 := h2052c.1
                                        have p2052_1 := h2052c.2.1
                                        have p2052_2 := h2052c.2.2.1
                                        have p2052_3 := h2052c.2.2.2
                                        linarith only [hlam, p2052_0]
                                      · have p2052_0 := h2052c.1
                                        have p2052_1 := h2052c.2.1
                                        have p2052_2 := h2052c.2.2.1
                                        have p2052_3 := h2052c.2.2.2
                                        rcases p2052_3 (m.d 0 5) (by simp) with h2054 | h2054
                                        · rcases p2052_3 (m.d 1 5) (by simp) with h2055 | h2055
                                          · linarith only [h2055, hlam, p2052_0]
                                          · rcases p2052_3 (m.d 2 5) (by simp) with h2057 | h2057
                                            · linarith only [h2057, h4, hlam]
                                            · linarith only [h1586, h2057, hlam]
                                        · linarith only [h2054, hlam, p2052_0]
                                      · have p2052_0 := h2052c.1
                                        have p2052_1 := h2052c.2.1
                                        have p2052_2 := h2052c.2.2.1
                                        have p2052_3 := h2052c.2.2.2
                                        linarith only [hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1959_1, p2052_1]
                                      · have p2052_0 := h2052c.1
                                        have p2052_1 := h2052c.2.1
                                        have p2052_2 := h2052c.2.2.1
                                        have p2052_3 := h2052c.2.2.2
                                        rcases p2052_3 (m.d 0 5) (by simp) with h2062 | h2062
                                        · rcases p2052_3 (m.d 1 5) (by simp) with h2063 | h2063
                                          · linarith only [h0, h1586, h2063, h4, hc01, hlam, hphi, u0ehi4]
                                          · linarith only [h1648, h2063, hlam]
                                        · linarith only [h2062, h6, hlam]
                                      · have p2052_0 := h2052c.1
                                        have p2052_1 := h2052c.2.1
                                        have p2052_2 := h2052c.2.2.1
                                        have p2052_3 := h2052c.2.2.2
                                        rcases p2052_3 (m.d 0 5) (by simp) with h2067 | h2067
                                        · rcases p2052_3 (m.d 1 5) (by simp) with h2068 | h2068
                                          · linarith only [h1649, h2068, hlam, p2052_1]
                                          · rcases p2052_3 (m.d 2 5) (by simp) with h2070 | h2070
                                            · linarith only [h2070, h4, hlam]
                                            · linarith only [h1956, h2070, hlam]
                                        · linarith only [h2067, h7, hlam]
                                      · have p2052_0 := h2052c.1
                                        have p2052_1 := h2052c.2.1
                                        have p2052_2 := h2052c.2.2.1
                                        have p2052_3 := h2052c.2.2.2
                                        linarith only [h1649, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p2052_1, u0ehi4]
                                      · have p2052_0 := h2052c.1
                                        have p2052_1 := h2052c.2.1
                                        have p2052_2 := h2052c.2.2.1
                                        have p2052_3 := h2052c.2.2.2
                                        linarith only [hlam, p2052_0]
                                      · have p2052_0 := h2052c.1
                                        have p2052_1 := h2052c.2.1
                                        have p2052_2 := h2052c.2.2.1
                                        have p2052_3 := h2052c.2.2.2
                                        linarith only [h1586, hlam, p2052_0]
                                      · have p2052_0 := h2052c.1
                                        have p2052_1 := h2052c.2.1
                                        have p2052_2 := h2052c.2.2.1
                                        have p2052_3 := h2052c.2.2.2
                                        linarith only [h0, h1649, h1954, h1956, h1957, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2052_1]
                                      · have p2052_0 := h2052c.1
                                        have p2052_1 := h2052c.2.1
                                        have p2052_2 := h2052c.2.2.1
                                        have p2052_3 := h2052c.2.2.2
                                        linarith only [h1649, hlam, p2052_1]
                                      · have p2052_0 := h2052c.1
                                        have p2052_1 := h2052c.2.1
                                        have p2052_2 := h2052c.2.2.1
                                        have p2052_3 := h2052c.2.2.2
                                        linarith only [h4, hlam, p2052_1]
                                      · have p2052_0 := h2052c.1
                                        have p2052_1 := h2052c.2.1
                                        have p2052_2 := h2052c.2.2.1
                                        have p2052_3 := h2052c.2.2.2
                                        rcases p2052_3 (m.d 0 5) (by simp) with h2080 | h2080
                                        · rcases p2052_3 (m.d 1 5) (by simp) with h2081 | h2081
                                          · linarith only [h1586, h2081, hlam]
                                          · rcases p2052_3 (m.d 2 5) (by simp) with h2083 | h2083
                                            · rcases p2052_3 (m.d 3 5) (by simp) with h2084 | h2084
                                              · linarith only [h1955, h2084, hlam]
                                              · rcases p2052_3 (m.d 4 5) (by simp) with h2086 | h2086
                                                · linarith only [h1956, h2086, hlam]
                                                · linarith only [h1649, h2086, hlam]
                                            · linarith only [h1586, h2083, hlam]
                                        · linarith only [h0, h1954, h1956, h2, h2080, hc01, hlam, hphi, p2052_1, u0ehi4]
                                      · have p2052_0 := h2052c.1
                                        have p2052_1 := h2052c.2.1
                                        have p2052_2 := h2052c.2.2.1
                                        have p2052_3 := h2052c.2.2.2
                                        linarith only [hlam, p2052_0]
                                      · have p2052_0 := h2052c.1
                                        have p2052_1 := h2052c.2.1
                                        have p2052_2 := h2052c.2.2.1
                                        have p2052_3 := h2052c.2.2.2
                                        rcases p2052_3 (m.d 0 5) (by simp) with h2092 | h2092
                                        · rcases p2052_3 (m.d 1 5) (by simp) with h2093 | h2093
                                          · linarith only [h1586, h2093, hlam]
                                          · linarith only [h1648, h2093, hlam]
                                        · linarith only [h2092, h6, hlam]
                                      · have p2052_0 := h2052c.1
                                        have p2052_1 := h2052c.2.1
                                        have p2052_2 := h2052c.2.2.1
                                        have p2052_3 := h2052c.2.2.2
                                        linarith only [h0, h1649, h1954, h1956, h2, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2052_1]
                                      · have p2052_0 := h2052c.1
                                        have p2052_1 := h2052c.2.1
                                        have p2052_2 := h2052c.2.2.1
                                        have p2052_3 := h2052c.2.2.2
                                        linarith only [h6, hlam, p2052_0]
                                      · have p2052_0 := h2052c.1
                                        have p2052_1 := h2052c.2.1
                                        have p2052_2 := h2052c.2.2.1
                                        have p2052_3 := h2052c.2.2.2
                                        linarith only [h1648, hlam, p2052_0]
                                      · have p2052_0 := h2052c.1
                                        have p2052_1 := h2052c.2.1
                                        have p2052_2 := h2052c.2.2.1
                                        have p2052_3 := h2052c.2.2.2
                                        linarith only [h1955, hlam, p2052_0]
                                      · have p2052_0 := h2052c.1
                                        have p2052_1 := h2052c.2.1
                                        have p2052_2 := h2052c.2.2.1
                                        have p2052_3 := h2052c.2.2.2
                                        linarith only [hlam, p2052_0]
                                      · have p2052_0 := h2052c.1
                                        have p2052_1 := h2052c.2.1
                                        have p2052_2 := h2052c.2.2.1
                                        have p2052_3 := h2052c.2.2.2
                                        linarith only [h1957, hlam, p2052_1]
                                      · have p2052_0 := h2052c.1
                                        have p2052_1 := h2052c.2.1
                                        have p2052_2 := h2052c.2.2.1
                                        have p2052_3 := h2052c.2.2.2
                                        linarith only [h7, hlam, p2052_0]
                                      · have p2052_0 := h2052c.1
                                        have p2052_1 := h2052c.2.1
                                        have p2052_2 := h2052c.2.2.1
                                        have p2052_3 := h2052c.2.2.2
                                        linarith only [h0, h1464, h1649, h1954, h1956, h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2052_1]
                                      · have p2052_0 := h2052c.1
                                        have p2052_1 := h2052c.2.1
                                        have p2052_2 := h2052c.2.2.1
                                        have p2052_3 := h2052c.2.2.2
                                        linarith only [h1956, hlam, p2052_0]
                                      · have p2052_0 := h2052c.1
                                        have p2052_1 := h2052c.2.1
                                        have p2052_2 := h2052c.2.2.1
                                        have p2052_3 := h2052c.2.2.2
                                        linarith only [h0, h1954, h1956, h1957, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2052_1]
                                      · have p2052_0 := h2052c.1
                                        have p2052_1 := h2052c.2.1
                                        have p2052_2 := h2052c.2.2.1
                                        have p2052_3 := h2052c.2.2.2
                                        linarith only [hlam, p2052_0]
                                · linarith only [h1955, h2047, hlam]
                              · linarith only [h2046, hlam, p2011_0]
                            · linarith only [h2045, h6, hlam]
                          · have p2011_0 := h2011c.1
                            have p2011_1 := h2011c.2.1
                            have p2011_2 := h2011c.2.2.1
                            have p2011_3 := h2011c.2.2.2
                            linarith only [h2, hlam, p2011_0]
                          · have p2011_0 := h2011c.1
                            have p2011_1 := h2011c.2.1
                            have p2011_2 := h2011c.2.2.1
                            have p2011_3 := h2011c.2.2.2
                            linarith only [h0, h1647, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2011_1]
                          · have p2011_0 := h2011c.1
                            have p2011_1 := h2011c.2.1
                            have p2011_2 := h2011c.2.2.1
                            have p2011_3 := h2011c.2.2.2
                            linarith only [hlam, p2011_0]
                          · have p2011_0 := h2011c.1
                            have p2011_1 := h2011c.2.1
                            have p2011_2 := h2011c.2.2.1
                            have p2011_3 := h2011c.2.2.2
                            rcases p2011_3 (m.d 0 3) (by simp) with h2114 | h2114
                            · rcases p2011_3 (m.d 1 3) (by simp) with h2115 | h2115
                              · linarith only [h2115, h8, hlam]
                              · linarith only [h1647, h2115, hlam]
                            · linarith only [h2114, h5, hlam]
                          · have p2011_0 := h2011c.1
                            have p2011_1 := h2011c.2.1
                            have p2011_2 := h2011c.2.2.1
                            have p2011_3 := h2011c.2.2.2
                            rcases p2011_3 (m.d 0 3) (by simp) with h2119 | h2119
                            · rcases p2011_3 (m.d 1 3) (by simp) with h2120 | h2120
                              · linarith only [h2120, h8, hlam]
                              · linarith only [h1648, h2120, hlam]
                            · linarith only [h2119, h6, hlam]
                          · have p2011_0 := h2011c.1
                            have p2011_1 := h2011c.2.1
                            have p2011_2 := h2011c.2.2.1
                            have p2011_3 := h2011c.2.2.2
                            linarith only [h5, hlam, p2011_0]
                          · have p2011_0 := h2011c.1
                            have p2011_1 := h2011c.2.1
                            have p2011_2 := h2011c.2.2.1
                            have p2011_3 := h2011c.2.2.2
                            linarith only [h1647, hlam, p2011_0]
                          · have p2011_0 := h2011c.1
                            have p2011_1 := h2011c.2.1
                            have p2011_2 := h2011c.2.2.1
                            have p2011_3 := h2011c.2.2.2
                            linarith only [h1954, hlam, p2011_0]
                          · have p2011_0 := h2011c.1
                            have p2011_1 := h2011c.2.1
                            have p2011_2 := h2011c.2.2.1
                            have p2011_3 := h2011c.2.2.2
                            linarith only [hlam, p2011_0]
                          · have p2011_0 := h2011c.1
                            have p2011_1 := h2011c.2.1
                            have p2011_2 := h2011c.2.2.1
                            have p2011_3 := h2011c.2.2.2
                            linarith only [h1957, hlam, p2011_1]
                          · have p2011_0 := h2011c.1
                            have p2011_1 := h2011c.2.1
                            have p2011_2 := h2011c.2.2.1
                            have p2011_3 := h2011c.2.2.2
                            linarith only [h6, hlam, p2011_0]
                          · have p2011_0 := h2011c.1
                            have p2011_1 := h2011c.2.1
                            have p2011_2 := h2011c.2.2.1
                            have p2011_3 := h2011c.2.2.2
                            linarith only [h1648, hlam, p2011_0]
                          · have p2011_0 := h2011c.1
                            have p2011_1 := h2011c.2.1
                            have p2011_2 := h2011c.2.2.1
                            have p2011_3 := h2011c.2.2.2
                            linarith only [h1955, hlam, p2011_0]
                          · have p2011_0 := h2011c.1
                            have p2011_1 := h2011c.2.1
                            have p2011_2 := h2011c.2.2.1
                            have p2011_3 := h2011c.2.2.2
                            linarith only [h1, h1648, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2011_1]
                          · have p2011_0 := h2011c.1
                            have p2011_1 := h2011c.2.1
                            have p2011_2 := h2011c.2.2.1
                            have p2011_3 := h2011c.2.2.2
                            linarith only [hlam, p2011_0]
                        · linarith only [h2010, hlam, p1959_0]
                      · linarith only [h1464, h2009, hlam]
                    · linarith only [h2008, h8, hlam]
                · linarith only [h0, h2005, hlam]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [h1955, hlam, p1959_1]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [h1956, hlam, p1959_0]
              · have p1959_0 := h1959c.1
                have p1959_1 := h1959c.2.1
                have p1959_2 := h1959c.2.2.1
                have p1959_3 := h1959c.2.2.2
                linarith only [hlam, p1959_0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2141 | h2141
            · linarith only [h0, h1464, h1956, h2, h2141, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases h2bigk with h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c | h2143c
              · have p2143_0 := h2143c.1
                have p2143_1 := h2143c.2.1
                have p2143_2 := h2143c.2.2.1
                have p2143_3 := h2143c.2.2.2
                linarith only [hlam, p2143_0]
              · have p2143_0 := h2143c.1
                have p2143_1 := h2143c.2.1
                have p2143_2 := h2143c.2.2.1
                have p2143_3 := h2143c.2.2.2
                linarith only [h1464, h1956, h2, h5, h7, hlam, p2143_2]
              · have p2143_0 := h2143c.1
                have p2143_1 := h2143c.2.1
                have p2143_2 := h2143c.2.2.1
                have p2143_3 := h2143c.2.2.2
                rcases p2143_3 (m.d 0 2) (by simp) with h2146 | h2146
                · rcases p2143_3 (m.d 1 2) (by simp) with h2147 | h2147
                  · linarith only [h0, h2147, hlam]
                  · rcases p2143_3 (m.d 2 3) (by simp) with h2149 | h2149
                    · linarith only [h2149, hlam, p2143_0]
                    · rcases p2143_3 (m.d 2 4) (by simp) with h2151 | h2151
                      · linarith only [h2151, h3, hlam]
                      · rcases p2143_3 (m.d 2 5) (by simp) with h2153 | h2153
                        · linarith only [h2153, h4, hlam]
                        · rcases h3bigk with h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c | h2155c
                          · have p2155_0 := h2155c.1
                            have p2155_1 := h2155c.2.1
                            have p2155_2 := h2155c.2.2.1
                            have p2155_3 := h2155c.2.2.2
                            linarith only [hlam, p2155_0]
                          · have p2155_0 := h2155c.1
                            have p2155_1 := h2155c.2.1
                            have p2155_2 := h2155c.2.2.1
                            have p2155_3 := h2155c.2.2.2
                            rcases p2155_3 (m.d 0 3) (by simp) with h2157 | h2157
                            · rcases p2155_3 (m.d 1 3) (by simp) with h2158 | h2158
                              · linarith only [h1, h2158, hlam]
                              · rcases p2155_3 (m.d 2 3) (by simp) with h2160 | h2160
                                · linarith only [h2, h2160, hlam]
                                · linarith only [h2160, h8, hlam]
                            · linarith only [h1, h2157, hlam]
                          · have p2155_0 := h2155c.1
                            have p2155_1 := h2155c.2.1
                            have p2155_2 := h2155c.2.2.1
                            have p2155_3 := h2155c.2.2.2
                            rcases p2155_3 (m.d 0 3) (by simp) with h2164 | h2164
                            · rcases p2155_3 (m.d 1 3) (by simp) with h2165 | h2165
                              · linarith only [h1, h2165, hlam]
                              · rcases p2155_3 (m.d 2 3) (by simp) with h2167 | h2167
                                · linarith only [h2, h2167, hlam]
                                · rcases p2155_3 (m.d 3 4) (by simp) with h2169 | h2169
                                  · linarith only [h2169, h5, hlam]
                                  · rcases p2155_3 (m.d 3 5) (by simp) with h2171 | h2171
                                    · linarith only [h2171, h6, hlam]
                                    · rcases h5bigk with h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c
                                      · have p2173_0 := h2173c.1
                                        have p2173_1 := h2173c.2.1
                                        have p2173_2 := h2173c.2.2.1
                                        have p2173_3 := h2173c.2.2.2
                                        linarith only [hlam, p2173_0]
                                      · have p2173_0 := h2173c.1
                                        have p2173_1 := h2173c.2.1
                                        have p2173_2 := h2173c.2.2.1
                                        have p2173_3 := h2173c.2.2.2
                                        rcases p2173_3 (m.d 0 5) (by simp) with h2175 | h2175
                                        · rcases p2173_3 (m.d 1 5) (by simp) with h2176 | h2176
                                          · linarith only [h2176, hlam, p2173_0]
                                          · rcases p2173_3 (m.d 2 5) (by simp) with h2178 | h2178
                                            · linarith only [h2178, h4, hlam]
                                            · linarith only [h1586, h2178, hlam]
                                        · linarith only [h2175, hlam, p2173_0]
                                      · have p2173_0 := h2173c.1
                                        have p2173_1 := h2173c.2.1
                                        have p2173_2 := h2173c.2.2.1
                                        have p2173_3 := h2173c.2.2.2
                                        rcases p2173_3 (m.d 0 5) (by simp) with h2182 | h2182
                                        · rcases p2173_3 (m.d 1 5) (by simp) with h2183 | h2183
                                          · linarith only [h1586, h2183, hlam, p2173_1]
                                          · rcases p2173_3 (m.d 2 5) (by simp) with h2185 | h2185
                                            · linarith only [h2185, h4, hlam]
                                            · rcases p2173_3 (m.d 3 5) (by simp) with h2187 | h2187
                                              · linarith only [h2187, h6, hlam]
                                              · rcases p2173_3 (m.d 4 5) (by simp) with h2189 | h2189
                                                · linarith only [h2189, h7, hlam]
                                                · linarith only [h1956, h2189, hlam]
                                        · linarith only [h2182, h4, hlam]
                                      · have p2173_0 := h2173c.1
                                        have p2173_1 := h2173c.2.1
                                        have p2173_2 := h2173c.2.2.1
                                        have p2173_3 := h2173c.2.2.2
                                        rcases p2173_3 (m.d 0 5) (by simp) with h2193 | h2193
                                        · rcases p2173_3 (m.d 1 5) (by simp) with h2194 | h2194
                                          · linarith only [h1586, h1955, h2194, hc02, hlam, hphi, p2143_1, u0ehi4]
                                          · linarith only [h1648, h2194, hlam]
                                        · linarith only [h2193, h6, hlam]
                                      · have p2173_0 := h2173c.1
                                        have p2173_1 := h2173c.2.1
                                        have p2173_2 := h2173c.2.2.1
                                        have p2173_3 := h2173c.2.2.2
                                        linarith only [h1464, h1956, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2173_1]
                                      · have p2173_0 := h2173c.1
                                        have p2173_1 := h2173c.2.1
                                        have p2173_2 := h2173c.2.2.1
                                        have p2173_3 := h2173c.2.2.2
                                        linarith only [h0, h1586, h1955, h2, hc01, hc05, hlam, hphi, ht0b, ht5b, p2155_1, p2173_1]
                                      · have p2173_0 := h2173c.1
                                        have p2173_1 := h2173c.2.1
                                        have p2173_2 := h2173c.2.2.1
                                        have p2173_3 := h2173c.2.2.2
                                        linarith only [hlam, p2173_0]
                                      · have p2173_0 := h2173c.1
                                        have p2173_1 := h2173c.2.1
                                        have p2173_2 := h2173c.2.2.1
                                        have p2173_3 := h2173c.2.2.2
                                        linarith only [h1586, hlam, p2173_0]
                                      · have p2173_0 := h2173c.1
                                        have p2173_1 := h2173c.2.1
                                        have p2173_2 := h2173c.2.2.1
                                        have p2173_3 := h2173c.2.2.2
                                        linarith only [h0, h1586, h1955, h2, hc01, hc35, hlam, hphi, ht0b, ht5b, p2155_1, p2173_1]
                                      · have p2173_0 := h2173c.1
                                        have p2173_1 := h2173c.2.1
                                        have p2173_2 := h2173c.2.2.1
                                        have p2173_3 := h2173c.2.2.2
                                        linarith only [h1649, hlam, p2173_1]
                                      · have p2173_0 := h2173c.1
                                        have p2173_1 := h2173c.2.1
                                        have p2173_2 := h2173c.2.2.1
                                        have p2173_3 := h2173c.2.2.2
                                        linarith only [h4, hlam, p2173_1]
                                      · have p2173_0 := h2173c.1
                                        have p2173_1 := h2173c.2.1
                                        have p2173_2 := h2173c.2.2.1
                                        have p2173_3 := h2173c.2.2.2
                                        linarith only [h0, h1955, h2, hc01, hc15, hlam, hphi, ht0b, ht5b, p2155_1, p2173_1]
                                      · have p2173_0 := h2173c.1
                                        have p2173_1 := h2173c.2.1
                                        have p2173_2 := h2173c.2.2.1
                                        have p2173_3 := h2173c.2.2.2
                                        linarith only [hlam, p2173_0]
                                      · have p2173_0 := h2173c.1
                                        have p2173_1 := h2173c.2.1
                                        have p2173_2 := h2173c.2.2.1
                                        have p2173_3 := h2173c.2.2.2
                                        linarith only [h0, h1955, h2, hc01, hc35, hlam, hphi, ht0b, ht5b, p2155_1, p2173_1]
                                      · have p2173_0 := h2173c.1
                                        have p2173_1 := h2173c.2.1
                                        have p2173_2 := h2173c.2.2.1
                                        have p2173_3 := h2173c.2.2.2
                                        linarith only [h1956, hlam, p2173_1]
                                      · have p2173_0 := h2173c.1
                                        have p2173_1 := h2173c.2.1
                                        have p2173_2 := h2173c.2.2.1
                                        have p2173_3 := h2173c.2.2.2
                                        linarith only [h6, hlam, p2173_0]
                                      · have p2173_0 := h2173c.1
                                        have p2173_1 := h2173c.2.1
                                        have p2173_2 := h2173c.2.2.1
                                        have p2173_3 := h2173c.2.2.2
                                        linarith only [h1648, hlam, p2173_0]
                                      · have p2173_0 := h2173c.1
                                        have p2173_1 := h2173c.2.1
                                        have p2173_2 := h2173c.2.2.1
                                        have p2173_3 := h2173c.2.2.2
                                        linarith only [h1955, hlam, p2173_0]
                                      · have p2173_0 := h2173c.1
                                        have p2173_1 := h2173c.2.1
                                        have p2173_2 := h2173c.2.2.1
                                        have p2173_3 := h2173c.2.2.2
                                        linarith only [hlam, p2173_0]
                                      · have p2173_0 := h2173c.1
                                        have p2173_1 := h2173c.2.1
                                        have p2173_2 := h2173c.2.2.1
                                        have p2173_3 := h2173c.2.2.2
                                        linarith only [h2141, hlam, p2173_1]
                                      · have p2173_0 := h2173c.1
                                        have p2173_1 := h2173c.2.1
                                        have p2173_2 := h2173c.2.2.1
                                        have p2173_3 := h2173c.2.2.2
                                        linarith only [h7, hlam, p2173_0]
                                      · have p2173_0 := h2173c.1
                                        have p2173_1 := h2173c.2.1
                                        have p2173_2 := h2173c.2.2.1
                                        have p2173_3 := h2173c.2.2.2
                                        rcases p2173_3 (m.d 0 5) (by simp) with h2215 | h2215
                                        · rcases p2173_3 (m.d 1 5) (by simp) with h2216 | h2216
                                          · linarith only [h1649, h2216, hlam]
                                          · rcases p2173_3 (m.d 2 5) (by simp) with h2218 | h2218
                                            · linarith only [h1956, h2218, hlam]
                                            · linarith only [h1586, h2218, hlam]
                                        · linarith only [h0, h2, h2215, h5, h7, hc01, hlam, hphi, p2173_1, u0ehi4]
                                      · have p2173_0 := h2173c.1
                                        have p2173_1 := h2173c.2.1
                                        have p2173_2 := h2173c.2.2.1
                                        have p2173_3 := h2173c.2.2.2
                                        linarith only [h0, h1464, h1956, h2, h5, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2173_1]
                                      · have p2173_0 := h2173c.1
                                        have p2173_1 := h2173c.2.1
                                        have p2173_2 := h2173c.2.2.1
                                        have p2173_3 := h2173c.2.2.2
                                        rcases p2173_3 (m.d 0 5) (by simp) with h2223 | h2223
                                        · rcases p2173_3 (m.d 1 5) (by simp) with h2224 | h2224
                                          · linarith only [h1649, h2224, hlam]
                                          · linarith only [h1648, h2224, hlam]
                                        · linarith only [h2223, h6, hlam]
                                      · have p2173_0 := h2173c.1
                                        have p2173_1 := h2173c.2.1
                                        have p2173_2 := h2173c.2.2.1
                                        have p2173_3 := h2173c.2.2.2
                                        linarith only [hlam, p2173_0]
                            · linarith only [h2, h2164, hlam]
                          · have p2155_0 := h2155c.1
                            have p2155_1 := h2155c.2.1
                            have p2155_2 := h2155c.2.2.1
                            have p2155_3 := h2155c.2.2.2
                            rcases p2155_3 (m.d 0 3) (by simp) with h2230 | h2230
                            · rcases p2155_3 (m.d 1 3) (by simp) with h2231 | h2231
                              · linarith only [h1, h2231, hlam]
                              · linarith only [h1647, h2231, hlam]
                            · linarith only [h2230, hlam, p2155_0]
                          · have p2155_0 := h2155c.1
                            have p2155_1 := h2155c.2.1
                            have p2155_2 := h2155c.2.2.1
                            have p2155_3 := h2155c.2.2.2
                            rcases p2155_3 (m.d 0 3) (by simp) with h2235 | h2235
                            · rcases p2155_3 (m.d 1 3) (by simp) with h2236 | h2236
                              · linarith only [h1, h2236, hlam]
                              · linarith only [h1648, h2236, hlam]
                            · linarith only [h2235, hlam, p2155_0]
                          · have p2155_0 := h2155c.1
                            have p2155_1 := h2155c.2.1
                            have p2155_2 := h2155c.2.2.1
                            have p2155_3 := h2155c.2.2.2
                            linarith only [h1, hlam, p2155_0]
                          · have p2155_0 := h2155c.1
                            have p2155_1 := h2155c.2.1
                            have p2155_2 := h2155c.2.2.1
                            have p2155_3 := h2155c.2.2.2
                            linarith only [hlam, p2155_0]
                          · have p2155_0 := h2155c.1
                            have p2155_1 := h2155c.2.1
                            have p2155_2 := h2155c.2.2.1
                            have p2155_3 := h2155c.2.2.2
                            linarith only [h8, hlam, p2155_1]
                          · have p2155_0 := h2155c.1
                            have p2155_1 := h2155c.2.1
                            have p2155_2 := h2155c.2.2.1
                            have p2155_3 := h2155c.2.2.2
                            linarith only [h0, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2143_1, p2155_1]
                          · have p2155_0 := h2155c.1
                            have p2155_1 := h2155c.2.1
                            have p2155_2 := h2155c.2.2.1
                            have p2155_3 := h2155c.2.2.2
                            linarith only [h0, h8, hc01, hc35, hlam, hphi, ht0b, ht5b, p2143_1, p2155_1]
                          · have p2155_0 := h2155c.1
                            have p2155_1 := h2155c.2.1
                            have p2155_2 := h2155c.2.2.1
                            have p2155_3 := h2155c.2.2.2
                            linarith only [h2, hlam, p2155_0]
                          · have p2155_0 := h2155c.1
                            have p2155_1 := h2155c.2.1
                            have p2155_2 := h2155c.2.2.1
                            have p2155_3 := h2155c.2.2.2
                            linarith only [h0, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2143_1, p2155_1]
                          · have p2155_0 := h2155c.1
                            have p2155_1 := h2155c.2.1
                            have p2155_2 := h2155c.2.2.1
                            have p2155_3 := h2155c.2.2.2
                            linarith only [hlam, p2155_0]
                          · have p2155_0 := h2155c.1
                            have p2155_1 := h2155c.2.1
                            have p2155_2 := h2155c.2.2.1
                            have p2155_3 := h2155c.2.2.2
                            linarith only [h0, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2143_1, p2155_1]
                          · have p2155_0 := h2155c.1
                            have p2155_1 := h2155c.2.1
                            have p2155_2 := h2155c.2.2.1
                            have p2155_3 := h2155c.2.2.2
                            linarith only [h0, hc01, hc35, hlam, hphi, ht0b, ht5b, p2143_1, p2155_1]
                          · have p2155_0 := h2155c.1
                            have p2155_1 := h2155c.2.1
                            have p2155_2 := h2155c.2.2.1
                            have p2155_3 := h2155c.2.2.2
                            linarith only [h5, hlam, p2155_0]
                          · have p2155_0 := h2155c.1
                            have p2155_1 := h2155c.2.1
                            have p2155_2 := h2155c.2.2.1
                            have p2155_3 := h2155c.2.2.2
                            linarith only [h1647, hlam, p2155_0]
                          · have p2155_0 := h2155c.1
                            have p2155_1 := h2155c.2.1
                            have p2155_2 := h2155c.2.2.1
                            have p2155_3 := h2155c.2.2.2
                            linarith only [h1954, hlam, p2155_0]
                          · have p2155_0 := h2155c.1
                            have p2155_1 := h2155c.2.1
                            have p2155_2 := h2155c.2.2.1
                            have p2155_3 := h2155c.2.2.2
                            linarith only [hlam, p2155_0]
                          · have p2155_0 := h2155c.1
                            have p2155_1 := h2155c.2.1
                            have p2155_2 := h2155c.2.2.1
                            have p2155_3 := h2155c.2.2.2
                            linarith only [h2141, hlam, p2155_1]
                          · have p2155_0 := h2155c.1
                            have p2155_1 := h2155c.2.1
                            have p2155_2 := h2155c.2.2.1
                            have p2155_3 := h2155c.2.2.2
                            linarith only [h6, hlam, p2155_0]
                          · have p2155_0 := h2155c.1
                            have p2155_1 := h2155c.2.1
                            have p2155_2 := h2155c.2.2.1
                            have p2155_3 := h2155c.2.2.2
                            linarith only [h1648, hlam, p2155_0]
                          · have p2155_0 := h2155c.1
                            have p2155_1 := h2155c.2.1
                            have p2155_2 := h2155c.2.2.1
                            have p2155_3 := h2155c.2.2.2
                            linarith only [h1955, hlam, p2155_0]
                          · have p2155_0 := h2155c.1
                            have p2155_1 := h2155c.2.1
                            have p2155_2 := h2155c.2.2.1
                            have p2155_3 := h2155c.2.2.2
                            linarith only [h1, h1648, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2155_1]
                          · have p2155_0 := h2155c.1
                            have p2155_1 := h2155c.2.1
                            have p2155_2 := h2155c.2.2.1
                            have p2155_3 := h2155c.2.2.2
                            linarith only [hlam, p2155_0]
                · linarith only [h2146, hlam, p2143_0]
              · have p2143_0 := h2143c.1
                have p2143_1 := h2143c.2.1
                have p2143_2 := h2143c.2.2.1
                have p2143_3 := h2143c.2.2.2
                rcases p2143_3 (m.d 0 2) (by simp) with h2261 | h2261
                · rcases p2143_3 (m.d 1 2) (by simp) with h2262 | h2262
                  · linarith only [h0, h2262, hlam]
                  · rcases p2143_3 (m.d 2 3) (by simp) with h2264 | h2264
                    · linarith only [h2, h2264, hlam]
                    · linarith only [h1954, h2264, hlam]
                · linarith only [h2261, hlam, p2143_0]
              · have p2143_0 := h2143c.1
                have p2143_1 := h2143c.2.1
                have p2143_2 := h2143c.2.2.1
                have p2143_3 := h2143c.2.2.2
                rcases p2143_3 (m.d 0 2) (by simp) with h2268 | h2268
                · rcases p2143_3 (m.d 1 2) (by simp) with h2269 | h2269
                  · linarith only [h0, h2269, hlam]
                  · rcases p2143_3 (m.d 2 3) (by simp) with h2271 | h2271
                    · linarith only [h2, h2271, hlam]
                    · linarith only [h1955, h2271, hlam]
                · linarith only [h2268, hlam, p2143_0]
              · have p2143_0 := h2143c.1
                have p2143_1 := h2143c.2.1
                have p2143_2 := h2143c.2.2.1
                have p2143_3 := h2143c.2.2.2
                linarith only [h0, hlam, p2143_0]
              · have p2143_0 := h2143c.1
                have p2143_1 := h2143c.2.1
                have p2143_2 := h2143c.2.2.1
                have p2143_3 := h2143c.2.2.2
                linarith only [hlam, p2143_0]
              · have p2143_0 := h2143c.1
                have p2143_1 := h2143c.2.1
                have p2143_2 := h2143c.2.2.1
                have p2143_3 := h2143c.2.2.2
                linarith only [h8, hlam, p2143_0]
              · have p2143_0 := h2143c.1
                have p2143_1 := h2143c.2.1
                have p2143_2 := h2143c.2.2.1
                have p2143_3 := h2143c.2.2.2
                linarith only [h1464, hlam, p2143_0]
              · have p2143_0 := h2143c.1
                have p2143_1 := h2143c.2.1
                have p2143_2 := h2143c.2.2.1
                have p2143_3 := h2143c.2.2.2
                linarith only [h1586, hlam, p2143_0]
              · have p2143_0 := h2143c.1
                have p2143_1 := h2143c.2.1
                have p2143_2 := h2143c.2.2.1
                have p2143_3 := h2143c.2.2.2
                linarith only [h2, hlam, p2143_0]
              · have p2143_0 := h2143c.1
                have p2143_1 := h2143c.2.1
                have p2143_2 := h2143c.2.2.1
                have p2143_3 := h2143c.2.2.2
                rcases p2143_3 (m.d 0 2) (by simp) with h2281 | h2281
                · rcases p2143_3 (m.d 1 2) (by simp) with h2282 | h2282
                  · linarith only [h2282, hlam, p2143_0]
                  · rcases p2143_3 (m.d 2 3) (by simp) with h2284 | h2284
                    · rcases p2143_3 (m.d 2 4) (by simp) with h2285 | h2285
                      · linarith only [h1954, h2285, hlam]
                      · linarith only [h1464, h2285, hlam]
                    · linarith only [h2284, hlam, p2143_0]
                · linarith only [h0, h2281, hlam]
              · have p2143_0 := h2143c.1
                have p2143_1 := h2143c.2.1
                have p2143_2 := h2143c.2.2.1
                have p2143_3 := h2143c.2.2.2
                linarith only [hlam, p2143_0]
              · have p2143_0 := h2143c.1
                have p2143_1 := h2143c.2.1
                have p2143_2 := h2143c.2.2.1
                have p2143_3 := h2143c.2.2.2
                linarith only [h0, h1464, h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2143_1]
              · have p2143_0 := h2143c.1
                have p2143_1 := h2143c.2.1
                have p2143_2 := h2143c.2.2.1
                have p2143_3 := h2143c.2.2.2
                linarith only [h0, h1586, h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2143_1]
              · have p2143_0 := h2143c.1
                have p2143_1 := h2143c.2.1
                have p2143_2 := h2143c.2.2.1
                have p2143_3 := h2143c.2.2.2
                linarith only [h3, hlam, p2143_0]
              · have p2143_0 := h2143c.1
                have p2143_1 := h2143c.2.1
                have p2143_2 := h2143c.2.2.1
                have p2143_3 := h2143c.2.2.2
                linarith only [h1956, h5, h7, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2143_1]
              · have p2143_0 := h2143c.1
                have p2143_1 := h2143c.2.1
                have p2143_2 := h2143c.2.2.1
                have p2143_3 := h2143c.2.2.2
                linarith only [h1954, hlam, p2143_1]
              · have p2143_0 := h2143c.1
                have p2143_1 := h2143c.2.1
                have p2143_2 := h2143c.2.2.1
                have p2143_3 := h2143c.2.2.2
                linarith only [hlam, p2143_0]
              · have p2143_0 := h2143c.1
                have p2143_1 := h2143c.2.1
                have p2143_2 := h2143c.2.2.1
                have p2143_3 := h2143c.2.2.2
                linarith only [h1956, hlam, p2143_1]
              · have p2143_0 := h2143c.1
                have p2143_1 := h2143c.2.1
                have p2143_2 := h2143c.2.2.1
                have p2143_3 := h2143c.2.2.2
                linarith only [h4, hlam, p2143_0]
              · have p2143_0 := h2143c.1
                have p2143_1 := h2143c.2.1
                have p2143_2 := h2143c.2.2.1
                have p2143_3 := h2143c.2.2.2
                rcases p2143_3 (m.d 0 2) (by simp) with h2299 | h2299
                · rcases p2143_3 (m.d 1 2) (by simp) with h2300 | h2300
                  · linarith only [h2300, hlam, p2143_0]
                  · rcases p2143_3 (m.d 2 3) (by simp) with h2302 | h2302
                    · rcases p2143_3 (m.d 2 4) (by simp) with h2303 | h2303
                      · linarith only [h1956, h2303, hlam]
                      · linarith only [h1464, h2303, hlam]
                    · linarith only [h2302, h8, hlam]
                · linarith only [h0, h2299, hlam]
              · have p2143_0 := h2143c.1
                have p2143_1 := h2143c.2.1
                have p2143_2 := h2143c.2.2.1
                have p2143_3 := h2143c.2.2.2
                linarith only [h1955, hlam, p2143_1]
              · have p2143_0 := h2143c.1
                have p2143_1 := h2143c.2.1
                have p2143_2 := h2143c.2.2.1
                have p2143_3 := h2143c.2.2.2
                linarith only [h1464, hc12, hc25, hlam, hphi, p2143_1]
              · have p2143_0 := h2143c.1
                have p2143_1 := h2143c.2.1
                have p2143_2 := h2143c.2.2.1
                have p2143_3 := h2143c.2.2.2
                linarith only [hlam, p2143_0]
        · linarith only [h1648, h1955, h8, hlam]
      · linarith only [h1647, h1954, h8, hlam]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h2313 | h2313
    · linarith only [h1647, h1648, h2313, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2315 | h2315
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2316 | h2316
        · linarith only [h0, h1647, h1648, h2, h2316, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2318 | h2318
          · linarith only [h0, h2, h2313, h2315, h2316, h2318, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2320 | h2320
            · linarith only [h0, h1647, h2, h2316, h2318, h2320, h6, h8, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · rcases h2bigk with h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c | h2322c
              · have p2322_0 := h2322c.1
                have p2322_1 := h2322c.2.1
                have p2322_2 := h2322c.2.2.1
                have p2322_3 := h2322c.2.2.2
                linarith only [hlam, p2322_0]
              · have p2322_0 := h2322c.1
                have p2322_1 := h2322c.2.1
                have p2322_2 := h2322c.2.2.1
                have p2322_3 := h2322c.2.2.2
                linarith only [h1464, h2, h2315, h2316, h2320, h5, h7, hlam, p2322_2]
              · have p2322_0 := h2322c.1
                have p2322_1 := h2322c.2.1
                have p2322_2 := h2322c.2.2.1
                have p2322_3 := h2322c.2.2.2
                rcases p2322_3 (m.d 0 2) (by simp) with h2325 | h2325
                · rcases p2322_3 (m.d 1 2) (by simp) with h2326 | h2326
                  · linarith only [h0, h2326, hlam]
                  · rcases p2322_3 (m.d 2 3) (by simp) with h2328 | h2328
                    · linarith only [h2328, hlam, p2322_0]
                    · rcases p2322_3 (m.d 2 4) (by simp) with h2330 | h2330
                      · linarith only [h2330, h3, hlam]
                      · rcases p2322_3 (m.d 2 5) (by simp) with h2332 | h2332
                        · linarith only [h2332, h4, hlam]
                        · linarith only [h2316, h2332, hlam]
                · linarith only [h2325, hlam, p2322_0]
              · have p2322_0 := h2322c.1
                have p2322_1 := h2322c.2.1
                have p2322_2 := h2322c.2.2.1
                have p2322_3 := h2322c.2.2.2
                rcases p2322_3 (m.d 0 2) (by simp) with h2336 | h2336
                · rcases p2322_3 (m.d 1 2) (by simp) with h2337 | h2337
                  · linarith only [h0, h2337, hlam]
                  · rcases p2322_3 (m.d 2 3) (by simp) with h2339 | h2339
                    · linarith only [h2, h2339, hlam]
                    · linarith only [h2315, h2339, hlam]
                · linarith only [h2336, hlam, p2322_0]
              · have p2322_0 := h2322c.1
                have p2322_1 := h2322c.2.1
                have p2322_2 := h2322c.2.2.1
                have p2322_3 := h2322c.2.2.2
                rcases p2322_3 (m.d 0 2) (by simp) with h2343 | h2343
                · rcases p2322_3 (m.d 1 2) (by simp) with h2344 | h2344
                  · linarith only [h0, h2344, hlam]
                  · rcases p2322_3 (m.d 2 3) (by simp) with h2346 | h2346
                    · linarith only [h2, h2346, hlam]
                    · rcases p2322_3 (m.d 2 4) (by simp) with h2348 | h2348
                      · linarith only [h2348, h3, hlam]
                      · rcases p2322_3 (m.d 2 5) (by simp) with h2350 | h2350
                        · linarith only [h2350, hlam, p2322_0]
                        · rcases h3bigk with h2352c | h2352c | h2352c | h2352c | h2352c | h2352c | h2352c | h2352c | h2352c | h2352c | h2352c | h2352c | h2352c | h2352c | h2352c | h2352c | h2352c | h2352c | h2352c | h2352c | h2352c | h2352c | h2352c | h2352c | h2352c
                          · have p2352_0 := h2352c.1
                            have p2352_1 := h2352c.2.1
                            have p2352_2 := h2352c.2.2.1
                            have p2352_3 := h2352c.2.2.2
                            linarith only [hlam, p2352_0]
                          · have p2352_0 := h2352c.1
                            have p2352_1 := h2352c.2.1
                            have p2352_2 := h2352c.2.2.1
                            have p2352_3 := h2352c.2.2.2
                            rcases p2352_3 (m.d 0 3) (by simp) with h2354 | h2354
                            · rcases p2352_3 (m.d 1 3) (by simp) with h2355 | h2355
                              · linarith only [h1, h2355, hlam]
                              · rcases p2352_3 (m.d 2 3) (by simp) with h2357 | h2357
                                · linarith only [h2, h2357, hlam]
                                · linarith only [h2357, h8, hlam]
                            · linarith only [h1, h2354, hlam]
                          · have p2352_0 := h2352c.1
                            have p2352_1 := h2352c.2.1
                            have p2352_2 := h2352c.2.2.1
                            have p2352_3 := h2352c.2.2.2
                            rcases p2352_3 (m.d 0 3) (by simp) with h2361 | h2361
                            · rcases p2352_3 (m.d 1 3) (by simp) with h2362 | h2362
                              · linarith only [h1, h2362, hlam]
                              · rcases p2352_3 (m.d 2 3) (by simp) with h2364 | h2364
                                · linarith only [h2, h2364, hlam]
                                · rcases p2352_3 (m.d 3 4) (by simp) with h2366 | h2366
                                  · linarith only [h2366, h5, hlam]
                                  · rcases p2352_3 (m.d 3 5) (by simp) with h2368 | h2368
                                    · linarith only [h2368, h6, hlam]
                                    · linarith only [h2316, h2368, hlam]
                            · linarith only [h2, h2361, hlam]
                          · have p2352_0 := h2352c.1
                            have p2352_1 := h2352c.2.1
                            have p2352_2 := h2352c.2.2.1
                            have p2352_3 := h2352c.2.2.2
                            linarith only [h1647, h2316, h2320, h5, h7, h8, hlam, p2352_2]
                          · have p2352_0 := h2352c.1
                            have p2352_1 := h2352c.2.1
                            have p2352_2 := h2352c.2.2.1
                            have p2352_3 := h2352c.2.2.2
                            linarith only [h0, h1464, h2, h2315, h2316, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2352_1]
                          · have p2352_0 := h2352c.1
                            have p2352_1 := h2352c.2.1
                            have p2352_2 := h2352c.2.2.1
                            have p2352_3 := h2352c.2.2.2
                            linarith only [h1, hlam, p2352_0]
                          · have p2352_0 := h2352c.1
                            have p2352_1 := h2352c.2.1
                            have p2352_2 := h2352c.2.2.1
                            have p2352_3 := h2352c.2.2.2
                            linarith only [hlam, p2352_0]
                          · have p2352_0 := h2352c.1
                            have p2352_1 := h2352c.2.1
                            have p2352_2 := h2352c.2.2.1
                            have p2352_3 := h2352c.2.2.2
                            linarith only [h8, hlam, p2352_1]
                          · have p2352_0 := h2352c.1
                            have p2352_1 := h2352c.2.1
                            have p2352_2 := h2352c.2.2.1
                            have p2352_3 := h2352c.2.2.2
                            linarith only [h2316, h2320, h8, hc34, hc45, hlam, hphi, p2352_1]
                          · have p2352_0 := h2352c.1
                            have p2352_1 := h2352c.2.1
                            have p2352_2 := h2352c.2.2.1
                            have p2352_3 := h2352c.2.2.2
                            linarith only [h1648, hlam, p2352_0]
                          · have p2352_0 := h2352c.1
                            have p2352_1 := h2352c.2.1
                            have p2352_2 := h2352c.2.2.1
                            have p2352_3 := h2352c.2.2.2
                            linarith only [h2, hlam, p2352_0]
                          · have p2352_0 := h2352c.1
                            have p2352_1 := h2352c.2.1
                            have p2352_2 := h2352c.2.2.1
                            have p2352_3 := h2352c.2.2.2
                            linarith only [h2316, hc13, hc35, hlam, hphi, p2352_1]
                          · have p2352_0 := h2352c.1
                            have p2352_1 := h2352c.2.1
                            have p2352_2 := h2352c.2.2.1
                            have p2352_3 := h2352c.2.2.2
                            linarith only [hlam, p2352_0]
                          · have p2352_0 := h2352c.1
                            have p2352_1 := h2352c.2.1
                            have p2352_2 := h2352c.2.2.1
                            have p2352_3 := h2352c.2.2.2
                            linarith only [h0, h2, h2316, h2320, h5, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2352_1]
                          · have p2352_0 := h2352c.1
                            have p2352_1 := h2352c.2.1
                            have p2352_2 := h2352c.2.2.1
                            have p2352_3 := h2352c.2.2.2
                            linarith only [h2316, hlam, p2352_0]
                          · have p2352_0 := h2352c.1
                            have p2352_1 := h2352c.2.1
                            have p2352_2 := h2352c.2.2.1
                            have p2352_3 := h2352c.2.2.2
                            linarith only [h5, hlam, p2352_0]
                          · have p2352_0 := h2352c.1
                            have p2352_1 := h2352c.2.1
                            have p2352_2 := h2352c.2.2.1
                            have p2352_3 := h2352c.2.2.2
                            linarith only [h1647, hlam, p2352_0]
                          · have p2352_0 := h2352c.1
                            have p2352_1 := h2352c.2.1
                            have p2352_2 := h2352c.2.2.1
                            have p2352_3 := h2352c.2.2.2
                            linarith only [h2315, hlam, p2352_0]
                          · have p2352_0 := h2352c.1
                            have p2352_1 := h2352c.2.1
                            have p2352_2 := h2352c.2.2.1
                            have p2352_3 := h2352c.2.2.2
                            linarith only [hlam, p2352_0]
                          · have p2352_0 := h2352c.1
                            have p2352_1 := h2352c.2.1
                            have p2352_2 := h2352c.2.2.1
                            have p2352_3 := h2352c.2.2.2
                            linarith only [h2320, hlam, p2352_1]
                          · have p2352_0 := h2352c.1
                            have p2352_1 := h2352c.2.1
                            have p2352_2 := h2352c.2.2.1
                            have p2352_3 := h2352c.2.2.2
                            linarith only [h6, hlam, p2352_0]
                          · have p2352_0 := h2352c.1
                            have p2352_1 := h2352c.2.1
                            have p2352_2 := h2352c.2.2.1
                            have p2352_3 := h2352c.2.2.2
                            linarith only [h0, h1647, h2, h2320, h5, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2352_1]
                          · have p2352_0 := h2352c.1
                            have p2352_1 := h2352c.2.1
                            have p2352_2 := h2352c.2.2.1
                            have p2352_3 := h2352c.2.2.2
                            linarith only [h0, h2, h2320, h5, h7, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2352_1]
                          · have p2352_0 := h2352c.1
                            have p2352_1 := h2352c.2.1
                            have p2352_2 := h2352c.2.2.1
                            have p2352_3 := h2352c.2.2.2
                            rcases p2352_3 (m.d 0 3) (by simp) with h2392 | h2392
                            · rcases p2352_3 (m.d 1 3) (by simp) with h2393 | h2393
                              · linarith only [h1648, h2393, hlam]
                              · linarith only [h1647, h2393, hlam]
                            · linarith only [h2392, h5, hlam]
                          · have p2352_0 := h2352c.1
                            have p2352_1 := h2352c.2.1
                            have p2352_2 := h2352c.2.2.1
                            have p2352_3 := h2352c.2.2.2
                            linarith only [hlam, p2352_0]
                · linarith only [h2343, hlam, p2322_0]
              · have p2322_0 := h2322c.1
                have p2322_1 := h2322c.2.1
                have p2322_2 := h2322c.2.2.1
                have p2322_3 := h2322c.2.2.2
                linarith only [h0, hlam, p2322_0]
              · have p2322_0 := h2322c.1
                have p2322_1 := h2322c.2.1
                have p2322_2 := h2322c.2.2.1
                have p2322_3 := h2322c.2.2.2
                linarith only [hlam, p2322_0]
              · have p2322_0 := h2322c.1
                have p2322_1 := h2322c.2.1
                have p2322_2 := h2322c.2.2.1
                have p2322_3 := h2322c.2.2.2
                linarith only [h8, hlam, p2322_0]
              · have p2322_0 := h2322c.1
                have p2322_1 := h2322c.2.1
                have p2322_2 := h2322c.2.2.1
                have p2322_3 := h2322c.2.2.2
                linarith only [h1464, hlam, p2322_0]
              · have p2322_0 := h2322c.1
                have p2322_1 := h2322c.2.1
                have p2322_2 := h2322c.2.2.1
                have p2322_3 := h2322c.2.2.2
                linarith only [h1586, hlam, p2322_0]
              · have p2322_0 := h2322c.1
                have p2322_1 := h2322c.2.1
                have p2322_2 := h2322c.2.2.1
                have p2322_3 := h2322c.2.2.2
                linarith only [h2, hlam, p2322_0]
              · have p2322_0 := h2322c.1
                have p2322_1 := h2322c.2.1
                have p2322_2 := h2322c.2.2.1
                have p2322_3 := h2322c.2.2.2
                linarith only [h0, h2, h2316, h2320, h5, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2322_1]
              · have p2322_0 := h2322c.1
                have p2322_1 := h2322c.2.1
                have p2322_2 := h2322c.2.2.1
                have p2322_3 := h2322c.2.2.2
                linarith only [hlam, p2322_0]
              · have p2322_0 := h2322c.1
                have p2322_1 := h2322c.2.1
                have p2322_2 := h2322c.2.2.1
                have p2322_3 := h2322c.2.2.2
                linarith only [h1464, hc12, hc23, hlam, hphi, p2322_1]
              · have p2322_0 := h2322c.1
                have p2322_1 := h2322c.2.1
                have p2322_2 := h2322c.2.2.1
                have p2322_3 := h2322c.2.2.2
                linarith only [h2316, hlam, p2322_0]
              · have p2322_0 := h2322c.1
                have p2322_1 := h2322c.2.1
                have p2322_2 := h2322c.2.2.1
                have p2322_3 := h2322c.2.2.2
                linarith only [h3, hlam, p2322_0]
              · have p2322_0 := h2322c.1
                have p2322_1 := h2322c.2.1
                have p2322_2 := h2322c.2.2.1
                have p2322_3 := h2322c.2.2.2
                linarith only [h0, h2, h2315, h2316, h2320, h5, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2322_1]
              · have p2322_0 := h2322c.1
                have p2322_1 := h2322c.2.1
                have p2322_2 := h2322c.2.2.1
                have p2322_3 := h2322c.2.2.2
                linarith only [h2315, hlam, p2322_1]
              · have p2322_0 := h2322c.1
                have p2322_1 := h2322c.2.1
                have p2322_2 := h2322c.2.2.1
                have p2322_3 := h2322c.2.2.2
                linarith only [hlam, p2322_0]
              · have p2322_0 := h2322c.1
                have p2322_1 := h2322c.2.1
                have p2322_2 := h2322c.2.2.1
                have p2322_3 := h2322c.2.2.2
                linarith only [h2318, hlam, p2322_1]
              · have p2322_0 := h2322c.1
                have p2322_1 := h2322c.2.1
                have p2322_2 := h2322c.2.2.1
                have p2322_3 := h2322c.2.2.2
                linarith only [h4, hlam, p2322_0]
              · have p2322_0 := h2322c.1
                have p2322_1 := h2322c.2.1
                have p2322_2 := h2322c.2.2.1
                have p2322_3 := h2322c.2.2.2
                rcases p2322_3 (m.d 0 2) (by simp) with h2415 | h2415
                · rcases p2322_3 (m.d 1 2) (by simp) with h2416 | h2416
                  · linarith only [h2416, hlam, p2322_0]
                  · rcases p2322_3 (m.d 2 3) (by simp) with h2418 | h2418
                    · linarith only [h2316, h2418, hlam]
                    · linarith only [h2418, h8, hlam]
                · linarith only [h0, h2415, hlam]
              · have p2322_0 := h2322c.1
                have p2322_1 := h2322c.2.1
                have p2322_2 := h2322c.2.2.1
                have p2322_3 := h2322c.2.2.2
                linarith only [h0, h2, h2316, h2320, h5, h7, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2322_1]
              · have p2322_0 := h2322c.1
                have p2322_1 := h2322c.2.1
                have p2322_2 := h2322c.2.2.1
                have p2322_3 := h2322c.2.2.2
                linarith only [h0, h1464, h2, h2316, h2320, h5, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2322_1]
              · have p2322_0 := h2322c.1
                have p2322_1 := h2322c.2.1
                have p2322_2 := h2322c.2.2.1
                have p2322_3 := h2322c.2.2.2
                linarith only [hlam, p2322_0]
      · linarith only [h1, h1647, h2315, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]

end R2N4
