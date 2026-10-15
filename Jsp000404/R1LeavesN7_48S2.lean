import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_48S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5810000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h692 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h921 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1036 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1117 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1118 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1119 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1120 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1121 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1122 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h1641 | h1641
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1642 | h1642
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1643 | h1643
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1644 | h1644
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1645 | h1645
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1646 | h1646
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1647 | h1647
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1648 | h1648
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1649 | h1649
                  · linarith only [h1118, h1122, h1649, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1651 | h1651
                    · linarith only [h1118, h1122, h1647, h1651, hlam]
                    · rcases h0bigk with h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c | h1653c
                      · have p1653_0 := h1653c.1
                        have p1653_1 := h1653c.2.1
                        have p1653_2 := h1653c.2.2.1
                        have p1653_3 := h1653c.2.2.2
                        linarith only [hlam, p1653_0]
                      · have p1653_0 := h1653c.1
                        have p1653_1 := h1653c.2.1
                        have p1653_2 := h1653c.2.2.1
                        have p1653_3 := h1653c.2.2.2
                        linarith only [h0, hlam, p1653_1]
                      · have p1653_0 := h1653c.1
                        have p1653_1 := h1653c.2.1
                        have p1653_2 := h1653c.2.2.1
                        have p1653_3 := h1653c.2.2.2
                        linarith only [h692, hlam, p1653_0]
                      · have p1653_0 := h1653c.1
                        have p1653_1 := h1653c.2.1
                        have p1653_2 := h1653c.2.2.1
                        have p1653_3 := h1653c.2.2.2
                        linarith only [h921, hlam, p1653_1]
                      · have p1653_0 := h1653c.1
                        have p1653_1 := h1653c.2.1
                        have p1653_2 := h1653c.2.2.1
                        have p1653_3 := h1653c.2.2.2
                        linarith only [h1036, hlam, p1653_1]
                      · have p1653_0 := h1653c.1
                        have p1653_1 := h1653c.2.1
                        have p1653_2 := h1653c.2.2.1
                        have p1653_3 := h1653c.2.2.2
                        rcases p1653_3 (m.d 0 1) (by simp) with h1659 | h1659
                        · linarith only [h0, h1659, hlam]
                        · rcases p1653_3 (m.d 0 2) (by simp) with h1661 | h1661
                          · rcases p1653_3 (m.d 0 3) (by simp) with h1662 | h1662
                            · linarith only [h1117, h1662, hlam]
                            · linarith only [h1662, h692, hlam]
                          · linarith only [h0, h1661, hlam]
                      · have p1653_0 := h1653c.1
                        have p1653_1 := h1653c.2.1
                        have p1653_2 := h1653c.2.2.1
                        have p1653_3 := h1653c.2.2.2
                        linarith only [hlam, p1653_0]
                      · have p1653_0 := h1653c.1
                        have p1653_1 := h1653c.2.1
                        have p1653_2 := h1653c.2.2.1
                        have p1653_3 := h1653c.2.2.2
                        linarith only [h1117, h1648, hc02, hlam, hphi, ht0b, ht5b, p1653_1, u5ehi3]
                      · have p1653_0 := h1653c.1
                        have p1653_1 := h1653c.2.1
                        have p1653_2 := h1653c.2.2.1
                        have p1653_3 := h1653c.2.2.2
                        rcases p1653_3 (m.d 0 1) (by simp) with h1668 | h1668
                        · linarith only [h0, h1668, hlam]
                        · rcases p1653_3 (m.d 0 2) (by simp) with h1670 | h1670
                          · rcases p1653_3 (m.d 0 3) (by simp) with h1671 | h1671
                            · linarith only [h1117, h1671, hlam]
                            · linarith only [h1120, h1671, hlam]
                          · linarith only [h1118, h1670, hlam]
                      · have p1653_0 := h1653c.1
                        have p1653_1 := h1653c.2.1
                        have p1653_2 := h1653c.2.2.1
                        have p1653_3 := h1653c.2.2.2
                        rcases p1653_3 (m.d 0 1) (by simp) with h1675 | h1675
                        · linarith only [h0, h1675, hlam]
                        · rcases p1653_3 (m.d 0 2) (by simp) with h1677 | h1677
                          · rcases p1653_3 (m.d 0 3) (by simp) with h1678 | h1678
                            · linarith only [h1117, h1678, hlam]
                            · linarith only [h1121, h1678, hlam]
                          · linarith only [h1119, h1677, hlam]
                      · have p1653_0 := h1653c.1
                        have p1653_1 := h1653c.2.1
                        have p1653_2 := h1653c.2.2.1
                        have p1653_3 := h1653c.2.2.2
                        rcases p1653_3 (m.d 0 1) (by simp) with h1682 | h1682
                        · linarith only [h1682, h692, hlam]
                        · rcases p1653_3 (m.d 0 2) (by simp) with h1684 | h1684
                          · rcases p1653_3 (m.d 0 3) (by simp) with h1685 | h1685
                            · rcases p1653_3 (m.d 0 4) (by simp) with h1686 | h1686
                              · linarith only [h1120, h1686, hlam]
                              · linarith only [h1686, h921, hlam]
                            · linarith only [h1685, h692, hlam]
                          · linarith only [h0, h1684, hlam]
                      · have p1653_0 := h1653c.1
                        have p1653_1 := h1653c.2.1
                        have p1653_2 := h1653c.2.2.1
                        have p1653_3 := h1653c.2.2.2
                        linarith only [h1117, hlam, p1653_1]
                      · have p1653_0 := h1653c.1
                        have p1653_1 := h1653c.2.1
                        have p1653_2 := h1653c.2.2.1
                        have p1653_3 := h1653c.2.2.2
                        linarith only [hlam, p1653_0]
                      · have p1653_0 := h1653c.1
                        have p1653_1 := h1653c.2.1
                        have p1653_2 := h1653c.2.2.1
                        have p1653_3 := h1653c.2.2.2
                        rcases p1653_3 (m.d 0 1) (by simp) with h1693 | h1693
                        · linarith only [h1693, h692, hlam]
                        · rcases p1653_3 (m.d 0 2) (by simp) with h1695 | h1695
                          · rcases p1653_3 (m.d 0 3) (by simp) with h1696 | h1696
                            · rcases p1653_3 (m.d 0 4) (by simp) with h1697 | h1697
                              · linarith only [h1120, h1697, hlam]
                              · rcases p1653_3 (m.d 0 5) (by simp) with h1699 | h1699
                                · linarith only [h1121, h1699, hlam]
                                · linarith only [h1122, h1699, hlam]
                            · linarith only [h1120, h1696, hlam]
                          · linarith only [h1118, h1695, hlam]
                      · have p1653_0 := h1653c.1
                        have p1653_1 := h1653c.2.1
                        have p1653_2 := h1653c.2.2.1
                        have p1653_3 := h1653c.2.2.2
                        rcases p1653_3 (m.d 0 1) (by simp) with h1704 | h1704
                        · linarith only [h1704, h692, hlam]
                        · rcases p1653_3 (m.d 0 2) (by simp) with h1706 | h1706
                          · rcases p1653_3 (m.d 0 3) (by simp) with h1707 | h1707
                            · rcases p1653_3 (m.d 0 4) (by simp) with h1708 | h1708
                              · linarith only [h1120, h1708, hlam]
                              · rcases p1653_3 (m.d 0 5) (by simp) with h1710 | h1710
                                · linarith only [h1121, h1710, hlam]
                                · rcases h3bigk with h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c
                                  · have p1712_0 := h1712c.1
                                    have p1712_1 := h1712c.2.1
                                    have p1712_2 := h1712c.2.2.1
                                    have p1712_3 := h1712c.2.2.2
                                    linarith only [hlam, p1712_0]
                                  · have p1712_0 := h1712c.1
                                    have p1712_1 := h1712c.2.1
                                    have p1712_2 := h1712c.2.2.1
                                    have p1712_3 := h1712c.2.2.2
                                    linarith only [h692, hlam, p1712_1]
                                  · have p1712_0 := h1712c.1
                                    have p1712_1 := h1712c.2.1
                                    have p1712_2 := h1712c.2.2.1
                                    have p1712_3 := h1712c.2.2.2
                                    linarith only [h1641, h1648, h692, hc12, hlam, hphi, ht01, ht0b, ht5b, p1712_1, u5ehi3]
                                  · have p1712_0 := h1712c.1
                                    have p1712_1 := h1712c.2.1
                                    have p1712_2 := h1712c.2.2.1
                                    have p1712_3 := h1712c.2.2.2
                                    rcases p1712_3 (m.d 0 3) (by simp) with h1716 | h1716
                                    · rcases p1712_3 (m.d 1 3) (by simp) with h1717 | h1717
                                      · rcases p1712_3 (m.d 2 3) (by simp) with h1718 | h1718
                                        · linarith only [h1117, h1718, hlam]
                                        · linarith only [h1647, h1718, hlam]
                                      · linarith only [h1644, h1717, hlam]
                                    · linarith only [h1716, hlam, p1712_0]
                                  · have p1712_0 := h1712c.1
                                    have p1712_1 := h1712c.2.1
                                    have p1712_2 := h1712c.2.2.1
                                    have p1712_3 := h1712c.2.2.2
                                    rcases p1712_3 (m.d 0 3) (by simp) with h1723 | h1723
                                    · rcases p1712_3 (m.d 1 3) (by simp) with h1724 | h1724
                                      · rcases p1712_3 (m.d 2 3) (by simp) with h1725 | h1725
                                        · linarith only [h1117, h1725, hlam]
                                        · linarith only [h1648, h1725, hlam]
                                      · linarith only [h1645, h1724, hlam]
                                    · linarith only [h1723, hlam, p1712_0]
                                  · have p1712_0 := h1712c.1
                                    have p1712_1 := h1712c.2.1
                                    have p1712_2 := h1712c.2.2.1
                                    have p1712_3 := h1712c.2.2.2
                                    linarith only [h1118, h1122, h1641, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1653_1, p1712_1, u2ehi3]
                                  · have p1712_0 := h1712c.1
                                    have p1712_1 := h1712c.2.1
                                    have p1712_2 := h1712c.2.2.1
                                    have p1712_3 := h1712c.2.2.2
                                    linarith only [hlam, p1712_0]
                                  · have p1712_0 := h1712c.1
                                    have p1712_1 := h1712c.2.1
                                    have p1712_2 := h1712c.2.2.1
                                    have p1712_3 := h1712c.2.2.2
                                    linarith only [h1641, h1648, hc12, hlam, hphi, ht01, ht0b, ht5b, p1712_1, u5ehi3]
                                  · have p1712_0 := h1712c.1
                                    have p1712_1 := h1712c.2.1
                                    have p1712_2 := h1712c.2.2.1
                                    have p1712_3 := h1712c.2.2.2
                                    rcases p1712_3 (m.d 0 3) (by simp) with h1733 | h1733
                                    · linarith only [h1733, h692, hlam]
                                    · linarith only [h1120, h1733, hlam]
                                  · have p1712_0 := h1712c.1
                                    have p1712_1 := h1712c.2.1
                                    have p1712_2 := h1712c.2.2.1
                                    have p1712_3 := h1712c.2.2.2
                                    rcases p1712_3 (m.d 0 3) (by simp) with h1736 | h1736
                                    · linarith only [h1736, h692, hlam]
                                    · linarith only [h1121, h1736, hlam]
                                  · have p1712_0 := h1712c.1
                                    have p1712_1 := h1712c.2.1
                                    have p1712_2 := h1712c.2.2.1
                                    have p1712_3 := h1712c.2.2.2
                                    linarith only [h1117, hlam, p1712_0]
                                  · have p1712_0 := h1712c.1
                                    have p1712_1 := h1712c.2.1
                                    have p1712_2 := h1712c.2.2.1
                                    have p1712_3 := h1712c.2.2.2
                                    linarith only [h1641, hlam, p1712_0]
                                  · have p1712_0 := h1712c.1
                                    have p1712_1 := h1712c.2.1
                                    have p1712_2 := h1712c.2.2.1
                                    have p1712_3 := h1712c.2.2.2
                                    linarith only [hlam, p1712_0]
                                  · have p1712_0 := h1712c.1
                                    have p1712_1 := h1712c.2.1
                                    have p1712_2 := h1712c.2.2.1
                                    have p1712_3 := h1712c.2.2.2
                                    rcases p1712_3 (m.d 0 3) (by simp) with h1742 | h1742
                                    · rcases p1712_3 (m.d 1 3) (by simp) with h1743 | h1743
                                      · rcases p1712_3 (m.d 2 3) (by simp) with h1744 | h1744
                                        · rcases p1712_3 (m.d 3 4) (by simp) with h1745 | h1745
                                          · linarith only [h1745, hlam, p1712_0]
                                          · rcases p1712_3 (m.d 3 5) (by simp) with h1747 | h1747
                                            · linarith only [h1648, h1747, hlam]
                                            · linarith only [h1651, h1747, hlam]
                                        · linarith only [h1744, hlam, p1712_0]
                                      · linarith only [h1644, h1743, hlam]
                                    · linarith only [h1120, h1742, hlam]
                                  · have p1712_0 := h1712c.1
                                    have p1712_1 := h1712c.2.1
                                    have p1712_2 := h1712c.2.2.1
                                    have p1712_3 := h1712c.2.2.2
                                    linarith only [h0, h1117, hc12, hlam, hphi, ht01, ht0b, ht5b, p1712_1, u5ehi3]
                                  · have p1712_0 := h1712c.1
                                    have p1712_1 := h1712c.2.1
                                    have p1712_2 := h1712c.2.2.1
                                    have p1712_3 := h1712c.2.2.2
                                    linarith only [h1120, hlam, p1712_0]
                                  · have p1712_0 := h1712c.1
                                    have p1712_1 := h1712c.2.1
                                    have p1712_2 := h1712c.2.2.1
                                    have p1712_3 := h1712c.2.2.2
                                    linarith only [h1644, hlam, p1712_0]
                                  · have p1712_0 := h1712c.1
                                    have p1712_1 := h1712c.2.1
                                    have p1712_2 := h1712c.2.2.1
                                    have p1712_3 := h1712c.2.2.2
                                    linarith only [h1647, hlam, p1712_0]
                                  · have p1712_0 := h1712c.1
                                    have p1712_1 := h1712c.2.1
                                    have p1712_2 := h1712c.2.2.1
                                    have p1712_3 := h1712c.2.2.2
                                    linarith only [hlam, p1712_0]
                                  · have p1712_0 := h1712c.1
                                    have p1712_1 := h1712c.2.1
                                    have p1712_2 := h1712c.2.2.1
                                    have p1712_3 := h1712c.2.2.2
                                    linarith only [h1651, hlam, p1712_1]
                                  · have p1712_0 := h1712c.1
                                    have p1712_1 := h1712c.2.1
                                    have p1712_2 := h1712c.2.2.1
                                    have p1712_3 := h1712c.2.2.2
                                    linarith only [h1121, hlam, p1712_0]
                                  · have p1712_0 := h1712c.1
                                    have p1712_1 := h1712c.2.1
                                    have p1712_2 := h1712c.2.2.1
                                    have p1712_3 := h1712c.2.2.2
                                    linarith only [h1645, hlam, p1712_0]
                                  · have p1712_0 := h1712c.1
                                    have p1712_1 := h1712c.2.1
                                    have p1712_2 := h1712c.2.2.1
                                    have p1712_3 := h1712c.2.2.2
                                    linarith only [h1648, hlam, p1712_0]
                                  · have p1712_0 := h1712c.1
                                    have p1712_1 := h1712c.2.1
                                    have p1712_2 := h1712c.2.2.1
                                    have p1712_3 := h1712c.2.2.2
                                    linarith only [h1121, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1653_1, p1712_1]
                                  · have p1712_0 := h1712c.1
                                    have p1712_1 := h1712c.2.1
                                    have p1712_2 := h1712c.2.2.1
                                    have p1712_3 := h1712c.2.2.2
                                    linarith only [hlam, p1712_0]
                            · linarith only [h1121, h1707, hlam]
                          · linarith only [h1119, h1706, hlam]
                      · have p1653_0 := h1653c.1
                        have p1653_1 := h1653c.2.1
                        have p1653_2 := h1653c.2.2.1
                        have p1653_3 := h1653c.2.2.2
                        linarith only [h1122, h1641, h1644, h1646, hc01, hc12, hlam, hphi, p1653_1]
                      · have p1653_0 := h1653c.1
                        have p1653_1 := h1653c.2.1
                        have p1653_2 := h1653c.2.2.1
                        have p1653_3 := h1653c.2.2.2
                        linarith only [h1118, hlam, p1653_0]
                      · have p1653_0 := h1653c.1
                        have p1653_1 := h1653c.2.1
                        have p1653_2 := h1653c.2.2.1
                        have p1653_3 := h1653c.2.2.2
                        linarith only [h1120, hlam, p1653_0]
                      · have p1653_0 := h1653c.1
                        have p1653_1 := h1653c.2.1
                        have p1653_2 := h1653c.2.2.1
                        have p1653_3 := h1653c.2.2.2
                        linarith only [hlam, p1653_0]
                      · have p1653_0 := h1653c.1
                        have p1653_1 := h1653c.2.1
                        have p1653_2 := h1653c.2.2.1
                        have p1653_3 := h1653c.2.2.2
                        linarith only [h1122, hlam, p1653_0]
                      · have p1653_0 := h1653c.1
                        have p1653_1 := h1653c.2.1
                        have p1653_2 := h1653c.2.2.1
                        have p1653_3 := h1653c.2.2.2
                        linarith only [h1122, h1641, h1644, h1646, hc01, hc12, hlam, hphi, p1653_1]
                      · have p1653_0 := h1653c.1
                        have p1653_1 := h1653c.2.1
                        have p1653_2 := h1653c.2.2.1
                        have p1653_3 := h1653c.2.2.2
                        linarith only [h1119, hlam, p1653_1]
                      · have p1653_0 := h1653c.1
                        have p1653_1 := h1653c.2.1
                        have p1653_2 := h1653c.2.2.1
                        have p1653_3 := h1653c.2.2.2
                        linarith only [h1121, hlam, p1653_0]
                      · have p1653_0 := h1653c.1
                        have p1653_1 := h1653c.2.1
                        have p1653_2 := h1653c.2.2.1
                        have p1653_3 := h1653c.2.2.2
                        linarith only [h1122, h1641, h1644, h1646, h921, hc01, hc12, hlam, hphi, p1653_1]
                      · have p1653_0 := h1653c.1
                        have p1653_1 := h1653c.2.1
                        have p1653_2 := h1653c.2.2.1
                        have p1653_3 := h1653c.2.2.2
                        linarith only [hlam, p1653_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1776 | h1776
                  · linarith only [h1121, h1122, h1648, h1776, hc24, hlam, hphi, u2ehi2]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1778 | h1778
                    · linarith only [h1121, h1122, h1647, h1648, h1778, hc34, hlam, hphi, ht23, u2ehi3]
                    · rcases h0bigk with h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c | h1780c
                      · have p1780_0 := h1780c.1
                        have p1780_1 := h1780c.2.1
                        have p1780_2 := h1780c.2.2.1
                        have p1780_3 := h1780c.2.2.2
                        linarith only [hlam, p1780_0]
                      · have p1780_0 := h1780c.1
                        have p1780_1 := h1780c.2.1
                        have p1780_2 := h1780c.2.2.1
                        have p1780_3 := h1780c.2.2.2
                        linarith only [h0, hlam, p1780_1]
                      · have p1780_0 := h1780c.1
                        have p1780_1 := h1780c.2.1
                        have p1780_2 := h1780c.2.2.1
                        have p1780_3 := h1780c.2.2.2
                        linarith only [h692, hlam, p1780_0]
                      · have p1780_0 := h1780c.1
                        have p1780_1 := h1780c.2.1
                        have p1780_2 := h1780c.2.2.1
                        have p1780_3 := h1780c.2.2.2
                        linarith only [h921, hlam, p1780_1]
                      · have p1780_0 := h1780c.1
                        have p1780_1 := h1780c.2.1
                        have p1780_2 := h1780c.2.2.1
                        have p1780_3 := h1780c.2.2.2
                        linarith only [h1036, hlam, p1780_1]
                      · have p1780_0 := h1780c.1
                        have p1780_1 := h1780c.2.1
                        have p1780_2 := h1780c.2.2.1
                        have p1780_3 := h1780c.2.2.2
                        rcases p1780_3 (m.d 0 1) (by simp) with h1786 | h1786
                        · linarith only [h0, h1786, hlam]
                        · rcases p1780_3 (m.d 0 2) (by simp) with h1788 | h1788
                          · rcases p1780_3 (m.d 0 3) (by simp) with h1789 | h1789
                            · linarith only [h1117, h1789, hlam]
                            · linarith only [h1789, h692, hlam]
                          · linarith only [h0, h1788, hlam]
                      · have p1780_0 := h1780c.1
                        have p1780_1 := h1780c.2.1
                        have p1780_2 := h1780c.2.2.1
                        have p1780_3 := h1780c.2.2.2
                        linarith only [hlam, p1780_0]
                      · have p1780_0 := h1780c.1
                        have p1780_1 := h1780c.2.1
                        have p1780_2 := h1780c.2.2.1
                        have p1780_3 := h1780c.2.2.2
                        linarith only [h0, h1121, h1647, h1648, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1780_1, u2ehi3]
                      · have p1780_0 := h1780c.1
                        have p1780_1 := h1780c.2.1
                        have p1780_2 := h1780c.2.2.1
                        have p1780_3 := h1780c.2.2.2
                        rcases p1780_3 (m.d 0 1) (by simp) with h1795 | h1795
                        · linarith only [h0, h1795, hlam]
                        · rcases p1780_3 (m.d 0 2) (by simp) with h1797 | h1797
                          · rcases p1780_3 (m.d 0 3) (by simp) with h1798 | h1798
                            · linarith only [h1117, h1798, hlam]
                            · linarith only [h1120, h1798, hlam]
                          · linarith only [h1118, h1797, hlam]
                      · have p1780_0 := h1780c.1
                        have p1780_1 := h1780c.2.1
                        have p1780_2 := h1780c.2.2.1
                        have p1780_3 := h1780c.2.2.2
                        linarith only [h0, h1121, h1647, h1648, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1780_1, u2ehi3]
                      · have p1780_0 := h1780c.1
                        have p1780_1 := h1780c.2.1
                        have p1780_2 := h1780c.2.2.1
                        have p1780_3 := h1780c.2.2.2
                        rcases p1780_3 (m.d 0 1) (by simp) with h1803 | h1803
                        · linarith only [h1803, h692, hlam]
                        · rcases p1780_3 (m.d 0 2) (by simp) with h1805 | h1805
                          · rcases p1780_3 (m.d 0 3) (by simp) with h1806 | h1806
                            · rcases p1780_3 (m.d 0 4) (by simp) with h1807 | h1807
                              · linarith only [h1120, h1807, hlam]
                              · linarith only [h1807, h921, hlam]
                            · linarith only [h1806, h692, hlam]
                          · linarith only [h0, h1805, hlam]
                      · have p1780_0 := h1780c.1
                        have p1780_1 := h1780c.2.1
                        have p1780_2 := h1780c.2.2.1
                        have p1780_3 := h1780c.2.2.2
                        linarith only [h1117, hlam, p1780_1]
                      · have p1780_0 := h1780c.1
                        have p1780_1 := h1780c.2.1
                        have p1780_2 := h1780c.2.2.1
                        have p1780_3 := h1780c.2.2.2
                        linarith only [hlam, p1780_0]
                      · have p1780_0 := h1780c.1
                        have p1780_1 := h1780c.2.1
                        have p1780_2 := h1780c.2.2.1
                        have p1780_3 := h1780c.2.2.2
                        rcases p1780_3 (m.d 0 1) (by simp) with h1814 | h1814
                        · linarith only [h1814, h692, hlam]
                        · rcases p1780_3 (m.d 0 2) (by simp) with h1816 | h1816
                          · rcases p1780_3 (m.d 0 3) (by simp) with h1817 | h1817
                            · rcases p1780_3 (m.d 0 4) (by simp) with h1818 | h1818
                              · linarith only [h1120, h1818, hlam]
                              · rcases p1780_3 (m.d 0 5) (by simp) with h1820 | h1820
                                · linarith only [h1121, h1820, hlam]
                                · linarith only [h1122, h1820, hlam]
                            · linarith only [h1120, h1817, hlam]
                          · linarith only [h1118, h1816, hlam]
                      · have p1780_0 := h1780c.1
                        have p1780_1 := h1780c.2.1
                        have p1780_2 := h1780c.2.2.1
                        have p1780_3 := h1780c.2.2.2
                        linarith only [h1121, h1647, h1648, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1780_1, u2ehi3]
                      · have p1780_0 := h1780c.1
                        have p1780_1 := h1780c.2.1
                        have p1780_2 := h1780c.2.2.1
                        have p1780_3 := h1780c.2.2.2
                        linarith only [h1122, h1641, h1644, h1646, hc01, hc12, hlam, hphi, p1780_1]
                      · have p1780_0 := h1780c.1
                        have p1780_1 := h1780c.2.1
                        have p1780_2 := h1780c.2.2.1
                        have p1780_3 := h1780c.2.2.2
                        linarith only [h1118, hlam, p1780_0]
                      · have p1780_0 := h1780c.1
                        have p1780_1 := h1780c.2.1
                        have p1780_2 := h1780c.2.2.1
                        have p1780_3 := h1780c.2.2.2
                        linarith only [h1120, hlam, p1780_0]
                      · have p1780_0 := h1780c.1
                        have p1780_1 := h1780c.2.1
                        have p1780_2 := h1780c.2.2.1
                        have p1780_3 := h1780c.2.2.2
                        linarith only [hlam, p1780_0]
                      · have p1780_0 := h1780c.1
                        have p1780_1 := h1780c.2.1
                        have p1780_2 := h1780c.2.2.1
                        have p1780_3 := h1780c.2.2.2
                        linarith only [h1122, hlam, p1780_0]
                      · have p1780_0 := h1780c.1
                        have p1780_1 := h1780c.2.1
                        have p1780_2 := h1780c.2.2.1
                        have p1780_3 := h1780c.2.2.2
                        linarith only [h1122, h1641, h1644, h1646, hc01, hc12, hlam, hphi, p1780_1]
                      · have p1780_0 := h1780c.1
                        have p1780_1 := h1780c.2.1
                        have p1780_2 := h1780c.2.2.1
                        have p1780_3 := h1780c.2.2.2
                        linarith only [h1119, hlam, p1780_1]
                      · have p1780_0 := h1780c.1
                        have p1780_1 := h1780c.2.1
                        have p1780_2 := h1780c.2.2.1
                        have p1780_3 := h1780c.2.2.2
                        linarith only [h1121, hlam, p1780_0]
                      · have p1780_0 := h1780c.1
                        have p1780_1 := h1780c.2.1
                        have p1780_2 := h1780c.2.2.1
                        have p1780_3 := h1780c.2.2.2
                        linarith only [h1122, h1641, h1644, h1646, h921, hc01, hc12, hlam, hphi, p1780_1]
                      · have p1780_0 := h1780c.1
                        have p1780_1 := h1780c.2.1
                        have p1780_2 := h1780c.2.2.1
                        have p1780_3 := h1780c.2.2.2
                        linarith only [hlam, p1780_0]
              · linarith only [h1120, h1122, h1641, h1644, h1646, h1647, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1837 | h1837
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1838 | h1838
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1839 | h1839
                  · linarith only [h1646, h1839, h921, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1841 | h1841
                    · linarith only [h1118, h1646, h1837, h1841, h921, hc23, hlam, hphi, u2ehi3]
                    · rcases h0bigk with h1843c | h1843c | h1843c | h1843c | h1843c | h1843c | h1843c | h1843c | h1843c | h1843c | h1843c | h1843c | h1843c | h1843c | h1843c | h1843c | h1843c | h1843c | h1843c | h1843c | h1843c | h1843c | h1843c | h1843c | h1843c
                      · have p1843_0 := h1843c.1
                        have p1843_1 := h1843c.2.1
                        have p1843_2 := h1843c.2.2.1
                        have p1843_3 := h1843c.2.2.2
                        linarith only [hlam, p1843_0]
                      · have p1843_0 := h1843c.1
                        have p1843_1 := h1843c.2.1
                        have p1843_2 := h1843c.2.2.1
                        have p1843_3 := h1843c.2.2.2
                        linarith only [h0, hlam, p1843_1]
                      · have p1843_0 := h1843c.1
                        have p1843_1 := h1843c.2.1
                        have p1843_2 := h1843c.2.2.1
                        have p1843_3 := h1843c.2.2.2
                        linarith only [h692, hlam, p1843_0]
                      · have p1843_0 := h1843c.1
                        have p1843_1 := h1843c.2.1
                        have p1843_2 := h1843c.2.2.1
                        have p1843_3 := h1843c.2.2.2
                        linarith only [h921, hlam, p1843_1]
                      · have p1843_0 := h1843c.1
                        have p1843_1 := h1843c.2.1
                        have p1843_2 := h1843c.2.2.1
                        have p1843_3 := h1843c.2.2.2
                        linarith only [h1036, hlam, p1843_1]
                      · have p1843_0 := h1843c.1
                        have p1843_1 := h1843c.2.1
                        have p1843_2 := h1843c.2.2.1
                        have p1843_3 := h1843c.2.2.2
                        rcases p1843_3 (m.d 0 1) (by simp) with h1849 | h1849
                        · linarith only [h0, h1849, hlam]
                        · rcases p1843_3 (m.d 0 2) (by simp) with h1851 | h1851
                          · rcases p1843_3 (m.d 0 3) (by simp) with h1852 | h1852
                            · linarith only [h1117, h1852, hlam]
                            · linarith only [h1852, h692, hlam]
                          · linarith only [h0, h1851, hlam]
                      · have p1843_0 := h1843c.1
                        have p1843_1 := h1843c.2.1
                        have p1843_2 := h1843c.2.2.1
                        have p1843_3 := h1843c.2.2.2
                        linarith only [hlam, p1843_0]
                      · have p1843_0 := h1843c.1
                        have p1843_1 := h1843c.2.1
                        have p1843_2 := h1843c.2.2.1
                        have p1843_3 := h1843c.2.2.2
                        linarith only [h0, h1121, hc12, hlam, hphi, ht01, ht0b, ht5b, p1843_1, u5ehi3]
                      · have p1843_0 := h1843c.1
                        have p1843_1 := h1843c.2.1
                        have p1843_2 := h1843c.2.2.1
                        have p1843_3 := h1843c.2.2.2
                        rcases p1843_3 (m.d 0 1) (by simp) with h1858 | h1858
                        · linarith only [h0, h1858, hlam]
                        · rcases p1843_3 (m.d 0 2) (by simp) with h1860 | h1860
                          · rcases p1843_3 (m.d 0 3) (by simp) with h1861 | h1861
                            · linarith only [h1117, h1861, hlam]
                            · linarith only [h1120, h1861, hlam]
                          · linarith only [h1118, h1860, hlam]
                      · have p1843_0 := h1843c.1
                        have p1843_1 := h1843c.2.1
                        have p1843_2 := h1843c.2.2.1
                        have p1843_3 := h1843c.2.2.2
                        rcases p1843_3 (m.d 0 1) (by simp) with h1865 | h1865
                        · linarith only [h0, h1865, hlam]
                        · rcases p1843_3 (m.d 0 2) (by simp) with h1867 | h1867
                          · rcases p1843_3 (m.d 0 3) (by simp) with h1868 | h1868
                            · linarith only [h1117, h1868, hlam]
                            · linarith only [h1121, h1868, hlam]
                          · linarith only [h1119, h1867, hlam]
                      · have p1843_0 := h1843c.1
                        have p1843_1 := h1843c.2.1
                        have p1843_2 := h1843c.2.2.1
                        have p1843_3 := h1843c.2.2.2
                        rcases p1843_3 (m.d 0 1) (by simp) with h1872 | h1872
                        · linarith only [h1872, h692, hlam]
                        · rcases p1843_3 (m.d 0 2) (by simp) with h1874 | h1874
                          · rcases p1843_3 (m.d 0 3) (by simp) with h1875 | h1875
                            · rcases p1843_3 (m.d 0 4) (by simp) with h1876 | h1876
                              · linarith only [h1120, h1876, hlam]
                              · linarith only [h1876, h921, hlam]
                            · linarith only [h1875, h692, hlam]
                          · linarith only [h0, h1874, hlam]
                      · have p1843_0 := h1843c.1
                        have p1843_1 := h1843c.2.1
                        have p1843_2 := h1843c.2.2.1
                        have p1843_3 := h1843c.2.2.2
                        linarith only [h1117, hlam, p1843_1]
                      · have p1843_0 := h1843c.1
                        have p1843_1 := h1843c.2.1
                        have p1843_2 := h1843c.2.2.1
                        have p1843_3 := h1843c.2.2.2
                        linarith only [hlam, p1843_0]
                      · have p1843_0 := h1843c.1
                        have p1843_1 := h1843c.2.1
                        have p1843_2 := h1843c.2.2.1
                        have p1843_3 := h1843c.2.2.2
                        rcases p1843_3 (m.d 0 1) (by simp) with h1883 | h1883
                        · linarith only [h1883, h692, hlam]
                        · rcases p1843_3 (m.d 0 2) (by simp) with h1885 | h1885
                          · rcases p1843_3 (m.d 0 3) (by simp) with h1886 | h1886
                            · rcases p1843_3 (m.d 0 4) (by simp) with h1887 | h1887
                              · linarith only [h1120, h1887, hlam]
                              · rcases p1843_3 (m.d 0 5) (by simp) with h1889 | h1889
                                · linarith only [h1121, h1889, hlam]
                                · linarith only [h1122, h1889, hlam]
                            · linarith only [h1120, h1886, hlam]
                          · linarith only [h1118, h1885, hlam]
                      · have p1843_0 := h1843c.1
                        have p1843_1 := h1843c.2.1
                        have p1843_2 := h1843c.2.2.1
                        have p1843_3 := h1843c.2.2.2
                        rcases p1843_3 (m.d 0 1) (by simp) with h1894 | h1894
                        · linarith only [h1894, h692, hlam]
                        · rcases p1843_3 (m.d 0 2) (by simp) with h1896 | h1896
                          · rcases p1843_3 (m.d 0 3) (by simp) with h1897 | h1897
                            · rcases p1843_3 (m.d 0 4) (by simp) with h1898 | h1898
                              · linarith only [h1120, h1898, hlam]
                              · rcases p1843_3 (m.d 0 5) (by simp) with h1900 | h1900
                                · linarith only [h1121, h1900, hlam]
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
                                    linarith only [h692, hlam, p1902_1]
                                  · have p1902_0 := h1902c.1
                                    have p1902_1 := h1902c.2.1
                                    have p1902_2 := h1902c.2.2.1
                                    have p1902_3 := h1902c.2.2.2
                                    linarith only [h1641, h1838, h692, hc12, hlam, hphi, ht01, ht0b, ht5b, p1902_1, u5ehi3]
                                  · have p1902_0 := h1902c.1
                                    have p1902_1 := h1902c.2.1
                                    have p1902_2 := h1902c.2.2.1
                                    have p1902_3 := h1902c.2.2.2
                                    rcases p1902_3 (m.d 0 3) (by simp) with h1906 | h1906
                                    · rcases p1902_3 (m.d 1 3) (by simp) with h1907 | h1907
                                      · rcases p1902_3 (m.d 2 3) (by simp) with h1908 | h1908
                                        · linarith only [h1117, h1908, hlam]
                                        · linarith only [h1837, h1908, hlam]
                                      · linarith only [h1644, h1907, hlam]
                                    · linarith only [h1906, hlam, p1902_0]
                                  · have p1902_0 := h1902c.1
                                    have p1902_1 := h1902c.2.1
                                    have p1902_2 := h1902c.2.2.1
                                    have p1902_3 := h1902c.2.2.2
                                    rcases p1902_3 (m.d 0 3) (by simp) with h1913 | h1913
                                    · rcases p1902_3 (m.d 1 3) (by simp) with h1914 | h1914
                                      · rcases p1902_3 (m.d 2 3) (by simp) with h1915 | h1915
                                        · linarith only [h1117, h1915, hlam]
                                        · linarith only [h1838, h1915, hlam]
                                      · linarith only [h1645, h1914, hlam]
                                    · linarith only [h1913, hlam, p1902_0]
                                  · have p1902_0 := h1902c.1
                                    have p1902_1 := h1902c.2.1
                                    have p1902_2 := h1902c.2.2.1
                                    have p1902_3 := h1902c.2.2.2
                                    linarith only [h1118, h1122, h1641, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1843_1, p1902_1, u2ehi3]
                                  · have p1902_0 := h1902c.1
                                    have p1902_1 := h1902c.2.1
                                    have p1902_2 := h1902c.2.2.1
                                    have p1902_3 := h1902c.2.2.2
                                    linarith only [hlam, p1902_0]
                                  · have p1902_0 := h1902c.1
                                    have p1902_1 := h1902c.2.1
                                    have p1902_2 := h1902c.2.2.1
                                    have p1902_3 := h1902c.2.2.2
                                    linarith only [h1641, h1838, hc12, hlam, hphi, ht01, ht0b, ht5b, p1902_1, u5ehi3]
                                  · have p1902_0 := h1902c.1
                                    have p1902_1 := h1902c.2.1
                                    have p1902_2 := h1902c.2.2.1
                                    have p1902_3 := h1902c.2.2.2
                                    rcases p1902_3 (m.d 0 3) (by simp) with h1923 | h1923
                                    · linarith only [h1923, h692, hlam]
                                    · linarith only [h1120, h1923, hlam]
                                  · have p1902_0 := h1902c.1
                                    have p1902_1 := h1902c.2.1
                                    have p1902_2 := h1902c.2.2.1
                                    have p1902_3 := h1902c.2.2.2
                                    rcases p1902_3 (m.d 0 3) (by simp) with h1926 | h1926
                                    · linarith only [h1926, h692, hlam]
                                    · linarith only [h1121, h1926, hlam]
                                  · have p1902_0 := h1902c.1
                                    have p1902_1 := h1902c.2.1
                                    have p1902_2 := h1902c.2.2.1
                                    have p1902_3 := h1902c.2.2.2
                                    linarith only [h1117, hlam, p1902_0]
                                  · have p1902_0 := h1902c.1
                                    have p1902_1 := h1902c.2.1
                                    have p1902_2 := h1902c.2.2.1
                                    have p1902_3 := h1902c.2.2.2
                                    linarith only [h1641, hlam, p1902_0]
                                  · have p1902_0 := h1902c.1
                                    have p1902_1 := h1902c.2.1
                                    have p1902_2 := h1902c.2.2.1
                                    have p1902_3 := h1902c.2.2.2
                                    linarith only [hlam, p1902_0]
                                  · have p1902_0 := h1902c.1
                                    have p1902_1 := h1902c.2.1
                                    have p1902_2 := h1902c.2.2.1
                                    have p1902_3 := h1902c.2.2.2
                                    rcases p1902_3 (m.d 0 3) (by simp) with h1932 | h1932
                                    · rcases p1902_3 (m.d 1 3) (by simp) with h1933 | h1933
                                      · rcases p1902_3 (m.d 2 3) (by simp) with h1934 | h1934
                                        · rcases p1902_3 (m.d 3 4) (by simp) with h1935 | h1935
                                          · linarith only [h1935, hlam, p1902_0]
                                          · rcases p1902_3 (m.d 3 5) (by simp) with h1937 | h1937
                                            · linarith only [h1838, h1937, hlam]
                                            · linarith only [h1841, h1937, hlam]
                                        · linarith only [h1934, hlam, p1902_0]
                                      · linarith only [h1644, h1933, hlam]
                                    · linarith only [h1120, h1932, hlam]
                                  · have p1902_0 := h1902c.1
                                    have p1902_1 := h1902c.2.1
                                    have p1902_2 := h1902c.2.2.1
                                    have p1902_3 := h1902c.2.2.2
                                    linarith only [h1117, hc02, hlam, hphi, ht0b, ht5b, p1902_1, u5ehi3]
                                  · have p1902_0 := h1902c.1
                                    have p1902_1 := h1902c.2.1
                                    have p1902_2 := h1902c.2.2.1
                                    have p1902_3 := h1902c.2.2.2
                                    linarith only [h1120, hlam, p1902_0]
                                  · have p1902_0 := h1902c.1
                                    have p1902_1 := h1902c.2.1
                                    have p1902_2 := h1902c.2.2.1
                                    have p1902_3 := h1902c.2.2.2
                                    linarith only [h1644, hlam, p1902_0]
                                  · have p1902_0 := h1902c.1
                                    have p1902_1 := h1902c.2.1
                                    have p1902_2 := h1902c.2.2.1
                                    have p1902_3 := h1902c.2.2.2
                                    linarith only [h1837, hlam, p1902_0]
                                  · have p1902_0 := h1902c.1
                                    have p1902_1 := h1902c.2.1
                                    have p1902_2 := h1902c.2.2.1
                                    have p1902_3 := h1902c.2.2.2
                                    linarith only [hlam, p1902_0]
                                  · have p1902_0 := h1902c.1
                                    have p1902_1 := h1902c.2.1
                                    have p1902_2 := h1902c.2.2.1
                                    have p1902_3 := h1902c.2.2.2
                                    linarith only [h1841, hlam, p1902_1]
                                  · have p1902_0 := h1902c.1
                                    have p1902_1 := h1902c.2.1
                                    have p1902_2 := h1902c.2.2.1
                                    have p1902_3 := h1902c.2.2.2
                                    linarith only [h1121, hlam, p1902_0]
                                  · have p1902_0 := h1902c.1
                                    have p1902_1 := h1902c.2.1
                                    have p1902_2 := h1902c.2.2.1
                                    have p1902_3 := h1902c.2.2.2
                                    linarith only [h1645, hlam, p1902_0]
                                  · have p1902_0 := h1902c.1
                                    have p1902_1 := h1902c.2.1
                                    have p1902_2 := h1902c.2.2.1
                                    have p1902_3 := h1902c.2.2.2
                                    linarith only [h1838, hlam, p1902_0]
                                  · have p1902_0 := h1902c.1
                                    have p1902_1 := h1902c.2.1
                                    have p1902_2 := h1902c.2.2.1
                                    have p1902_3 := h1902c.2.2.2
                                    linarith only [h1121, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1843_1, p1902_1]
                                  · have p1902_0 := h1902c.1
                                    have p1902_1 := h1902c.2.1
                                    have p1902_2 := h1902c.2.2.1
                                    have p1902_3 := h1902c.2.2.2
                                    linarith only [hlam, p1902_0]
                            · linarith only [h1121, h1897, hlam]
                          · linarith only [h1119, h1896, hlam]
                      · have p1843_0 := h1843c.1
                        have p1843_1 := h1843c.2.1
                        have p1843_2 := h1843c.2.2.1
                        have p1843_3 := h1843c.2.2.2
                        linarith only [h1646, h921, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1843_1]
                      · have p1843_0 := h1843c.1
                        have p1843_1 := h1843c.2.1
                        have p1843_2 := h1843c.2.2.1
                        have p1843_3 := h1843c.2.2.2
                        linarith only [h1118, hlam, p1843_0]
                      · have p1843_0 := h1843c.1
                        have p1843_1 := h1843c.2.1
                        have p1843_2 := h1843c.2.2.1
                        have p1843_3 := h1843c.2.2.2
                        linarith only [h1120, hlam, p1843_0]
                      · have p1843_0 := h1843c.1
                        have p1843_1 := h1843c.2.1
                        have p1843_2 := h1843c.2.2.1
                        have p1843_3 := h1843c.2.2.2
                        linarith only [hlam, p1843_0]
                      · have p1843_0 := h1843c.1
                        have p1843_1 := h1843c.2.1
                        have p1843_2 := h1843c.2.2.1
                        have p1843_3 := h1843c.2.2.2
                        linarith only [h1122, hlam, p1843_0]
                      · have p1843_0 := h1843c.1
                        have p1843_1 := h1843c.2.1
                        have p1843_2 := h1843c.2.2.1
                        have p1843_3 := h1843c.2.2.2
                        rcases p1843_3 (m.d 0 1) (by simp) with h1961 | h1961
                        · linarith only [h1036, h1961, hlam]
                        · rcases p1843_3 (m.d 0 2) (by simp) with h1963 | h1963
                          · rcases p1843_3 (m.d 0 3) (by simp) with h1964 | h1964
                            · rcases p1843_3 (m.d 0 4) (by simp) with h1965 | h1965
                              · linarith only [h1122, h1965, hlam]
                              · linarith only [h1965, h921, hlam]
                            · linarith only [h1964, h692, hlam]
                          · linarith only [h0, h1963, hlam]
                      · have p1843_0 := h1843c.1
                        have p1843_1 := h1843c.2.1
                        have p1843_2 := h1843c.2.2.1
                        have p1843_3 := h1843c.2.2.2
                        linarith only [h1119, hlam, p1843_1]
                      · have p1843_0 := h1843c.1
                        have p1843_1 := h1843c.2.1
                        have p1843_2 := h1843c.2.2.1
                        have p1843_3 := h1843c.2.2.2
                        linarith only [h1121, hlam, p1843_0]
                      · have p1843_0 := h1843c.1
                        have p1843_1 := h1843c.2.1
                        have p1843_2 := h1843c.2.2.1
                        have p1843_3 := h1843c.2.2.2
                        linarith only [h1036, h1118, h1646, hc45, hlam, hphi, ht23, ht34, p1843_1, u2ehi3]
                      · have p1843_0 := h1843c.1
                        have p1843_1 := h1843c.2.1
                        have p1843_2 := h1843c.2.2.1
                        have p1843_3 := h1843c.2.2.2
                        linarith only [hlam, p1843_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1974 | h1974
                  · linarith only [h1036, h1121, h1641, h1646, h1837, h1838, h1974, h692, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1976 | h1976
                    · linarith only [h1121, h1641, h1646, h1837, h1838, h1976, h692, h921, hc01, hc12, hc34, hlam, hphi, ht23, u2ehi3]
                    · rcases h0bigk with h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c
                      · have p1978_0 := h1978c.1
                        have p1978_1 := h1978c.2.1
                        have p1978_2 := h1978c.2.2.1
                        have p1978_3 := h1978c.2.2.2
                        linarith only [hlam, p1978_0]
                      · have p1978_0 := h1978c.1
                        have p1978_1 := h1978c.2.1
                        have p1978_2 := h1978c.2.2.1
                        have p1978_3 := h1978c.2.2.2
                        linarith only [h0, hlam, p1978_1]
                      · have p1978_0 := h1978c.1
                        have p1978_1 := h1978c.2.1
                        have p1978_2 := h1978c.2.2.1
                        have p1978_3 := h1978c.2.2.2
                        linarith only [h692, hlam, p1978_0]
                      · have p1978_0 := h1978c.1
                        have p1978_1 := h1978c.2.1
                        have p1978_2 := h1978c.2.2.1
                        have p1978_3 := h1978c.2.2.2
                        linarith only [h921, hlam, p1978_1]
                      · have p1978_0 := h1978c.1
                        have p1978_1 := h1978c.2.1
                        have p1978_2 := h1978c.2.2.1
                        have p1978_3 := h1978c.2.2.2
                        linarith only [h1036, hlam, p1978_1]
                      · have p1978_0 := h1978c.1
                        have p1978_1 := h1978c.2.1
                        have p1978_2 := h1978c.2.2.1
                        have p1978_3 := h1978c.2.2.2
                        rcases p1978_3 (m.d 0 1) (by simp) with h1984 | h1984
                        · linarith only [h0, h1984, hlam]
                        · rcases p1978_3 (m.d 0 2) (by simp) with h1986 | h1986
                          · rcases p1978_3 (m.d 0 3) (by simp) with h1987 | h1987
                            · linarith only [h1117, h1987, hlam]
                            · linarith only [h1987, h692, hlam]
                          · linarith only [h0, h1986, hlam]
                      · have p1978_0 := h1978c.1
                        have p1978_1 := h1978c.2.1
                        have p1978_2 := h1978c.2.2.1
                        have p1978_3 := h1978c.2.2.2
                        linarith only [hlam, p1978_0]
                      · have p1978_0 := h1978c.1
                        have p1978_1 := h1978c.2.1
                        have p1978_2 := h1978c.2.2.1
                        have p1978_3 := h1978c.2.2.2
                        linarith only [h0, h1121, h1837, h1838, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1978_1, u2ehi3]
                      · have p1978_0 := h1978c.1
                        have p1978_1 := h1978c.2.1
                        have p1978_2 := h1978c.2.2.1
                        have p1978_3 := h1978c.2.2.2
                        rcases p1978_3 (m.d 0 1) (by simp) with h1993 | h1993
                        · linarith only [h0, h1993, hlam]
                        · rcases p1978_3 (m.d 0 2) (by simp) with h1995 | h1995
                          · rcases p1978_3 (m.d 0 3) (by simp) with h1996 | h1996
                            · linarith only [h1117, h1996, hlam]
                            · linarith only [h1120, h1996, hlam]
                          · linarith only [h1118, h1995, hlam]
                      · have p1978_0 := h1978c.1
                        have p1978_1 := h1978c.2.1
                        have p1978_2 := h1978c.2.2.1
                        have p1978_3 := h1978c.2.2.2
                        linarith only [h0, h1121, h1837, h1838, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1978_1, u2ehi3]
                      · have p1978_0 := h1978c.1
                        have p1978_1 := h1978c.2.1
                        have p1978_2 := h1978c.2.2.1
                        have p1978_3 := h1978c.2.2.2
                        rcases p1978_3 (m.d 0 1) (by simp) with h2001 | h2001
                        · linarith only [h2001, h692, hlam]
                        · rcases p1978_3 (m.d 0 2) (by simp) with h2003 | h2003
                          · rcases p1978_3 (m.d 0 3) (by simp) with h2004 | h2004
                            · rcases p1978_3 (m.d 0 4) (by simp) with h2005 | h2005
                              · linarith only [h1120, h2005, hlam]
                              · linarith only [h2005, h921, hlam]
                            · linarith only [h2004, h692, hlam]
                          · linarith only [h0, h2003, hlam]
                      · have p1978_0 := h1978c.1
                        have p1978_1 := h1978c.2.1
                        have p1978_2 := h1978c.2.2.1
                        have p1978_3 := h1978c.2.2.2
                        linarith only [h1117, hlam, p1978_1]
                      · have p1978_0 := h1978c.1
                        have p1978_1 := h1978c.2.1
                        have p1978_2 := h1978c.2.2.1
                        have p1978_3 := h1978c.2.2.2
                        linarith only [hlam, p1978_0]
                      · have p1978_0 := h1978c.1
                        have p1978_1 := h1978c.2.1
                        have p1978_2 := h1978c.2.2.1
                        have p1978_3 := h1978c.2.2.2
                        rcases p1978_3 (m.d 0 1) (by simp) with h2012 | h2012
                        · linarith only [h2012, h692, hlam]
                        · rcases p1978_3 (m.d 0 2) (by simp) with h2014 | h2014
                          · rcases p1978_3 (m.d 0 3) (by simp) with h2015 | h2015
                            · rcases p1978_3 (m.d 0 4) (by simp) with h2016 | h2016
                              · linarith only [h1120, h2016, hlam]
                              · rcases p1978_3 (m.d 0 5) (by simp) with h2018 | h2018
                                · linarith only [h1121, h2018, hlam]
                                · linarith only [h1122, h2018, hlam]
                            · linarith only [h1120, h2015, hlam]
                          · linarith only [h1118, h2014, hlam]
                      · have p1978_0 := h1978c.1
                        have p1978_1 := h1978c.2.1
                        have p1978_2 := h1978c.2.2.1
                        have p1978_3 := h1978c.2.2.2
                        linarith only [h1121, h1837, h1838, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1978_1, u2ehi3]
                      · have p1978_0 := h1978c.1
                        have p1978_1 := h1978c.2.1
                        have p1978_2 := h1978c.2.2.1
                        have p1978_3 := h1978c.2.2.2
                        linarith only [h1646, h921, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1978_1]
                      · have p1978_0 := h1978c.1
                        have p1978_1 := h1978c.2.1
                        have p1978_2 := h1978c.2.2.1
                        have p1978_3 := h1978c.2.2.2
                        linarith only [h1118, hlam, p1978_0]
                      · have p1978_0 := h1978c.1
                        have p1978_1 := h1978c.2.1
                        have p1978_2 := h1978c.2.2.1
                        have p1978_3 := h1978c.2.2.2
                        linarith only [h1120, hlam, p1978_0]
                      · have p1978_0 := h1978c.1
                        have p1978_1 := h1978c.2.1
                        have p1978_2 := h1978c.2.2.1
                        have p1978_3 := h1978c.2.2.2
                        linarith only [hlam, p1978_0]
                      · have p1978_0 := h1978c.1
                        have p1978_1 := h1978c.2.1
                        have p1978_2 := h1978c.2.2.1
                        have p1978_3 := h1978c.2.2.2
                        linarith only [h1122, hlam, p1978_0]
                      · have p1978_0 := h1978c.1
                        have p1978_1 := h1978c.2.1
                        have p1978_2 := h1978c.2.2.1
                        have p1978_3 := h1978c.2.2.2
                        rcases p1978_3 (m.d 0 1) (by simp) with h2029 | h2029
                        · linarith only [h1036, h2029, hlam]
                        · rcases p1978_3 (m.d 0 2) (by simp) with h2031 | h2031
                          · rcases p1978_3 (m.d 0 3) (by simp) with h2032 | h2032
                            · rcases p1978_3 (m.d 0 4) (by simp) with h2033 | h2033
                              · linarith only [h1122, h2033, hlam]
                              · linarith only [h2033, h921, hlam]
                            · linarith only [h2032, h692, hlam]
                          · linarith only [h0, h2031, hlam]
                      · have p1978_0 := h1978c.1
                        have p1978_1 := h1978c.2.1
                        have p1978_2 := h1978c.2.2.1
                        have p1978_3 := h1978c.2.2.2
                        linarith only [h1119, hlam, p1978_1]
                      · have p1978_0 := h1978c.1
                        have p1978_1 := h1978c.2.1
                        have p1978_2 := h1978c.2.2.1
                        have p1978_3 := h1978c.2.2.2
                        linarith only [h1121, hlam, p1978_0]
                      · have p1978_0 := h1978c.1
                        have p1978_1 := h1978c.2.1
                        have p1978_2 := h1978c.2.2.1
                        have p1978_3 := h1978c.2.2.2
                        linarith only [h1118, h1122, hc45, hlam, hphi, ht23, ht34, p1978_1, u2ehi3]
                      · have p1978_0 := h1978c.1
                        have p1978_1 := h1978c.2.1
                        have p1978_2 := h1978c.2.2.1
                        have p1978_3 := h1978c.2.2.2
                        linarith only [hlam, p1978_0]
              · linarith only [h1120, h1646, h1837, h921, hc45, hlam, hphi, ht23, ht34, u2ehi2]
          · linarith only [h0, h1117, h1121, h1645, h692, hc01, hc12, hlam, hphi]
        · linarith only [h1120, h1121, h1122, h1644, h692, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
      · linarith only [h0, h1117, h1643, hc25, hlam, hphi, u2ehi2]
    · linarith only [h0, h1119, h1642, hc24, hlam, hphi, u2ehi4]
  · linarith only [h0, h1119, h1641, hc23, hlam, hphi, u2ehi4]

set_option maxHeartbeats 5810000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h692 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h921 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1036 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1117 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1118 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1119 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1120 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1121 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h1122 | h1122
  · exact r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h692 h921 h1036 h1117 h1118 h1119 h1120 h1121 h1122
  · exact r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h692 h921 h1036 h1117 h1118 h1119 h1120 h1121 h1122

set_option maxHeartbeats 5810000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h692 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h921 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1036 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1117 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1118 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1119 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1120 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1121 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h2048 | h2048
  · linarith only [h1120, h1121, h2048, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h2050 | h2050
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2051 | h2051
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2052 | h2052
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2053 | h2053
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2054 | h2054
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2055 | h2055
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2056 | h2056
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2057 | h2057
                  · linarith only [h1117, h1118, h1120, h1121, h2057, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2059 | h2059
                    · linarith only [h1118, h2048, h2059, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2061 | h2061
                      · linarith only [h1117, h1118, h2048, h2056, h2061, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · rcases h0bigk with h2063c | h2063c | h2063c | h2063c | h2063c | h2063c | h2063c | h2063c | h2063c | h2063c | h2063c | h2063c | h2063c | h2063c | h2063c | h2063c | h2063c | h2063c | h2063c | h2063c | h2063c | h2063c | h2063c | h2063c | h2063c
                        · have p2063_0 := h2063c.1
                          have p2063_1 := h2063c.2.1
                          have p2063_2 := h2063c.2.2.1
                          have p2063_3 := h2063c.2.2.2
                          linarith only [hlam, p2063_0]
                        · have p2063_0 := h2063c.1
                          have p2063_1 := h2063c.2.1
                          have p2063_2 := h2063c.2.2.1
                          have p2063_3 := h2063c.2.2.2
                          linarith only [h0, hlam, p2063_1]
                        · have p2063_0 := h2063c.1
                          have p2063_1 := h2063c.2.1
                          have p2063_2 := h2063c.2.2.1
                          have p2063_3 := h2063c.2.2.2
                          linarith only [h692, hlam, p2063_0]
                        · have p2063_0 := h2063c.1
                          have p2063_1 := h2063c.2.1
                          have p2063_2 := h2063c.2.2.1
                          have p2063_3 := h2063c.2.2.2
                          linarith only [h921, hlam, p2063_1]
                        · have p2063_0 := h2063c.1
                          have p2063_1 := h2063c.2.1
                          have p2063_2 := h2063c.2.2.1
                          have p2063_3 := h2063c.2.2.2
                          linarith only [h1036, hlam, p2063_1]
                        · have p2063_0 := h2063c.1
                          have p2063_1 := h2063c.2.1
                          have p2063_2 := h2063c.2.2.1
                          have p2063_3 := h2063c.2.2.2
                          rcases p2063_3 (m.d 0 1) (by simp) with h2069 | h2069
                          · linarith only [h0, h2069, hlam]
                          · rcases p2063_3 (m.d 0 2) (by simp) with h2071 | h2071
                            · rcases p2063_3 (m.d 0 3) (by simp) with h2072 | h2072
                              · linarith only [h1117, h2072, hlam]
                              · linarith only [h2072, h692, hlam]
                            · linarith only [h0, h2071, hlam]
                        · have p2063_0 := h2063c.1
                          have p2063_1 := h2063c.2.1
                          have p2063_2 := h2063c.2.2.1
                          have p2063_3 := h2063c.2.2.2
                          linarith only [hlam, p2063_0]
                        · have p2063_0 := h2063c.1
                          have p2063_1 := h2063c.2.1
                          have p2063_2 := h2063c.2.2.1
                          have p2063_3 := h2063c.2.2.2
                          rcases p2063_3 (m.d 0 1) (by simp) with h2077 | h2077
                          · linarith only [h0, h2077, hlam]
                          · rcases p2063_3 (m.d 0 2) (by simp) with h2079 | h2079
                            · rcases p2063_3 (m.d 0 3) (by simp) with h2080 | h2080
                              · linarith only [h1117, h2080, hlam]
                              · rcases p2063_3 (m.d 0 4) (by simp) with h2082 | h2082
                                · linarith only [h1118, h2082, hlam]
                                · rcases p2063_3 (m.d 0 5) (by simp) with h2084 | h2084
                                  · linarith only [h1119, h2084, hlam]
                                  · linarith only [h1121, h2084, hlam]
                            · linarith only [h1117, h2079, hlam]
                        · have p2063_0 := h2063c.1
                          have p2063_1 := h2063c.2.1
                          have p2063_2 := h2063c.2.2.1
                          have p2063_3 := h2063c.2.2.2
                          rcases p2063_3 (m.d 0 1) (by simp) with h2088 | h2088
                          · linarith only [h0, h2088, hlam]
                          · rcases p2063_3 (m.d 0 2) (by simp) with h2090 | h2090
                            · rcases p2063_3 (m.d 0 3) (by simp) with h2091 | h2091
                              · linarith only [h1117, h2091, hlam]
                              · linarith only [h1120, h2091, hlam]
                            · linarith only [h1118, h2090, hlam]
                        · have p2063_0 := h2063c.1
                          have p2063_1 := h2063c.2.1
                          have p2063_2 := h2063c.2.2.1
                          have p2063_3 := h2063c.2.2.2
                          rcases p2063_3 (m.d 0 1) (by simp) with h2095 | h2095
                          · linarith only [h0, h2095, hlam]
                          · rcases p2063_3 (m.d 0 2) (by simp) with h2097 | h2097
                            · rcases p2063_3 (m.d 0 3) (by simp) with h2098 | h2098
                              · linarith only [h1117, h2098, hlam]
                              · rcases p2063_3 (m.d 0 4) (by simp) with h2100 | h2100
                                · linarith only [h1118, h2100, hlam]
                                · rcases p2063_3 (m.d 0 5) (by simp) with h2102 | h2102
                                  · linarith only [h1119, h2102, hlam]
                                  · rcases h3bigk with h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c | h2104c
                                    · have p2104_0 := h2104c.1
                                      have p2104_1 := h2104c.2.1
                                      have p2104_2 := h2104c.2.2.1
                                      have p2104_3 := h2104c.2.2.2
                                      linarith only [hlam, p2104_0]
                                    · have p2104_0 := h2104c.1
                                      have p2104_1 := h2104c.2.1
                                      have p2104_2 := h2104c.2.2.1
                                      have p2104_3 := h2104c.2.2.2
                                      linarith only [h692, hlam, p2104_1]
                                    · have p2104_0 := h2104c.1
                                      have p2104_1 := h2104c.2.1
                                      have p2104_2 := h2104c.2.2.1
                                      have p2104_3 := h2104c.2.2.2
                                      linarith only [h1121, h2050, h2053, h2055, h2061, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2104_1]
                                    · have p2104_0 := h2104c.1
                                      have p2104_1 := h2104c.2.1
                                      have p2104_2 := h2104c.2.2.1
                                      have p2104_3 := h2104c.2.2.2
                                      linarith only [h1121, h2050, h2053, h2055, h2061, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2104_1]
                                    · have p2104_0 := h2104c.1
                                      have p2104_1 := h2104c.2.1
                                      have p2104_2 := h2104c.2.2.1
                                      have p2104_3 := h2104c.2.2.2
                                      linarith only [h1121, hlam, p2104_0]
                                    · have p2104_0 := h2104c.1
                                      have p2104_1 := h2104c.2.1
                                      have p2104_2 := h2104c.2.2.1
                                      have p2104_3 := h2104c.2.2.2
                                      rcases p2104_3 (m.d 0 3) (by simp) with h2110 | h2110
                                      · linarith only [h2110, h692, hlam]
                                      · rcases p2104_3 (m.d 1 3) (by simp) with h2112 | h2112
                                        · rcases p2104_3 (m.d 2 3) (by simp) with h2113 | h2113
                                          · linarith only [h2050, h2113, hlam]
                                          · rcases p2104_3 (m.d 3 4) (by simp) with h2115 | h2115
                                            · linarith only [h2053, h2115, hlam]
                                            · rcases p2104_3 (m.d 3 5) (by simp) with h2117 | h2117
                                              · linarith only [h2054, h2117, hlam]
                                              · linarith only [h1121, h2117, hlam]
                                        · linarith only [h2112, h692, hlam]
                                    · have p2104_0 := h2104c.1
                                      have p2104_1 := h2104c.2.1
                                      have p2104_2 := h2104c.2.2.1
                                      have p2104_3 := h2104c.2.2.2
                                      linarith only [hlam, p2104_0]
                                    · have p2104_0 := h2104c.1
                                      have p2104_1 := h2104c.2.1
                                      have p2104_2 := h2104c.2.2.1
                                      have p2104_3 := h2104c.2.2.2
                                      rcases p2104_3 (m.d 0 3) (by simp) with h2122 | h2122
                                      · linarith only [h2122, h692, hlam]
                                      · linarith only [h1117, h2122, hlam]
                                    · have p2104_0 := h2104c.1
                                      have p2104_1 := h2104c.2.1
                                      have p2104_2 := h2104c.2.2.1
                                      have p2104_3 := h2104c.2.2.2
                                      linarith only [h1120, h1121, h2053, h2055, h2061, hlam, p2104_2]
                                    · have p2104_0 := h2104c.1
                                      have p2104_1 := h2104c.2.1
                                      have p2104_2 := h2104c.2.2.1
                                      have p2104_3 := h2104c.2.2.2
                                      linarith only [h1120, h1121, h2050, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2104_1]
                                    · have p2104_0 := h2104c.1
                                      have p2104_1 := h2104c.2.1
                                      have p2104_2 := h2104c.2.2.1
                                      have p2104_3 := h2104c.2.2.2
                                      linarith only [h1117, hlam, p2104_0]
                                    · have p2104_0 := h2104c.1
                                      have p2104_1 := h2104c.2.1
                                      have p2104_2 := h2104c.2.2.1
                                      have p2104_3 := h2104c.2.2.2
                                      linarith only [h2050, hlam, p2104_0]
                                    · have p2104_0 := h2104c.1
                                      have p2104_1 := h2104c.2.1
                                      have p2104_2 := h2104c.2.2.1
                                      have p2104_3 := h2104c.2.2.2
                                      linarith only [hlam, p2104_0]
                                    · have p2104_0 := h2104c.1
                                      have p2104_1 := h2104c.2.1
                                      have p2104_2 := h2104c.2.2.1
                                      have p2104_3 := h2104c.2.2.2
                                      linarith only [h0, h1119, h2057, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2063_1, p2104_1]
                                    · have p2104_0 := h2104c.1
                                      have p2104_1 := h2104c.2.1
                                      have p2104_2 := h2104c.2.2.1
                                      have p2104_3 := h2104c.2.2.2
                                      linarith only [h2057, hlam, p2104_0]
                                    · have p2104_0 := h2104c.1
                                      have p2104_1 := h2104c.2.1
                                      have p2104_2 := h2104c.2.2.1
                                      have p2104_3 := h2104c.2.2.2
                                      linarith only [h1120, hlam, p2104_0]
                                    · have p2104_0 := h2104c.1
                                      have p2104_1 := h2104c.2.1
                                      have p2104_2 := h2104c.2.2.1
                                      have p2104_3 := h2104c.2.2.2
                                      linarith only [h2053, hlam, p2104_0]
                                    · have p2104_0 := h2104c.1
                                      have p2104_1 := h2104c.2.1
                                      have p2104_2 := h2104c.2.2.1
                                      have p2104_3 := h2104c.2.2.2
                                      linarith only [h2056, hlam, p2104_0]
                                    · have p2104_0 := h2104c.1
                                      have p2104_1 := h2104c.2.1
                                      have p2104_2 := h2104c.2.2.1
                                      have p2104_3 := h2104c.2.2.2
                                      linarith only [hlam, p2104_0]
                                    · have p2104_0 := h2104c.1
                                      have p2104_1 := h2104c.2.1
                                      have p2104_2 := h2104c.2.2.1
                                      have p2104_3 := h2104c.2.2.2
                                      linarith only [h2061, hlam, p2104_1]
                                    · have p2104_0 := h2104c.1
                                      have p2104_1 := h2104c.2.1
                                      have p2104_2 := h2104c.2.2.1
                                      have p2104_3 := h2104c.2.2.2
                                      linarith only [h1117, hc35, hlam, hphi, ht23, p2104_1, u2ehi2]
                                    · have p2104_0 := h2104c.1
                                      have p2104_1 := h2104c.2.1
                                      have p2104_2 := h2104c.2.2.1
                                      have p2104_3 := h2104c.2.2.2
                                      linarith only [h2054, hlam, p2104_0]
                                    · have p2104_0 := h2104c.1
                                      have p2104_1 := h2104c.2.1
                                      have p2104_2 := h2104c.2.2.1
                                      have p2104_3 := h2104c.2.2.2
                                      linarith only [h2050, h2054, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2104_1, u2ehi2]
                                    · have p2104_0 := h2104c.1
                                      have p2104_1 := h2104c.2.1
                                      have p2104_2 := h2104c.2.2.1
                                      have p2104_3 := h2104c.2.2.2
                                      rcases p2104_3 (m.d 0 3) (by simp) with h2140 | h2140
                                      · linarith only [h1121, h2140, hlam]
                                      · linarith only [h1120, h2140, hlam]
                                    · have p2104_0 := h2104c.1
                                      have p2104_1 := h2104c.2.1
                                      have p2104_2 := h2104c.2.2.1
                                      have p2104_3 := h2104c.2.2.2
                                      linarith only [hlam, p2104_0]
                            · linarith only [h1119, h2097, hlam]
                        · have p2063_0 := h2063c.1
                          have p2063_1 := h2063c.2.1
                          have p2063_2 := h2063c.2.2.1
                          have p2063_3 := h2063c.2.2.2
                          linarith only [h1121, h2050, h2053, h2055, h2061, hc01, hc12, hlam, hphi, p2063_1]
                        · have p2063_0 := h2063c.1
                          have p2063_1 := h2063c.2.1
                          have p2063_2 := h2063c.2.2.1
                          have p2063_3 := h2063c.2.2.2
                          linarith only [h1117, hlam, p2063_1]
                        · have p2063_0 := h2063c.1
                          have p2063_1 := h2063c.2.1
                          have p2063_2 := h2063c.2.2.1
                          have p2063_3 := h2063c.2.2.2
                          linarith only [hlam, p2063_0]
                        · have p2063_0 := h2063c.1
                          have p2063_1 := h2063c.2.1
                          have p2063_2 := h2063c.2.2.1
                          have p2063_3 := h2063c.2.2.2
                          linarith only [h1121, h2050, h2053, h2055, h2061, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2063_1]
                        · have p2063_0 := h2063c.1
                          have p2063_1 := h2063c.2.1
                          have p2063_2 := h2063c.2.2.1
                          have p2063_3 := h2063c.2.2.2
                          linarith only [h1121, hlam, p2063_1]
                        · have p2063_0 := h2063c.1
                          have p2063_1 := h2063c.2.1
                          have p2063_2 := h2063c.2.2.1
                          have p2063_3 := h2063c.2.2.2
                          linarith only [h1120, h1121, h2050, h2053, h2055, h2061, hc01, hc12, hlam, hphi, p2063_1]
                        · have p2063_0 := h2063c.1
                          have p2063_1 := h2063c.2.1
                          have p2063_2 := h2063c.2.2.1
                          have p2063_3 := h2063c.2.2.2
                          linarith only [h1118, hlam, p2063_0]
                        · have p2063_0 := h2063c.1
                          have p2063_1 := h2063c.2.1
                          have p2063_2 := h2063c.2.2.1
                          have p2063_3 := h2063c.2.2.2
                          linarith only [h1120, hlam, p2063_0]
                        · have p2063_0 := h2063c.1
                          have p2063_1 := h2063c.2.1
                          have p2063_2 := h2063c.2.2.1
                          have p2063_3 := h2063c.2.2.2
                          linarith only [hlam, p2063_0]
                        · have p2063_0 := h2063c.1
                          have p2063_1 := h2063c.2.1
                          have p2063_2 := h2063c.2.2.1
                          have p2063_3 := h2063c.2.2.2
                          linarith only [h2048, hlam, p2063_0]
                        · have p2063_0 := h2063c.1
                          have p2063_1 := h2063c.2.1
                          have p2063_2 := h2063c.2.2.1
                          have p2063_3 := h2063c.2.2.2
                          linarith only [h1121, h2050, h2053, h2055, h2061, hc01, hc12, hlam, hphi, p2063_1]
                        · have p2063_0 := h2063c.1
                          have p2063_1 := h2063c.2.1
                          have p2063_2 := h2063c.2.2.1
                          have p2063_3 := h2063c.2.2.2
                          linarith only [h1119, hlam, p2063_1]
                        · have p2063_0 := h2063c.1
                          have p2063_1 := h2063c.2.1
                          have p2063_2 := h2063c.2.2.1
                          have p2063_3 := h2063c.2.2.2
                          linarith only [h1121, h2050, h2053, h2055, h2061, h692, hc01, hc12, hlam, hphi, p2063_1]
                        · have p2063_0 := h2063c.1
                          have p2063_1 := h2063c.2.1
                          have p2063_2 := h2063c.2.2.1
                          have p2063_3 := h2063c.2.2.2
                          linarith only [h1118, h1121, h2050, h2053, h2055, h2061, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2063_1, u2ehi3]
                        · have p2063_0 := h2063c.1
                          have p2063_1 := h2063c.2.1
                          have p2063_2 := h2063c.2.2.1
                          have p2063_3 := h2063c.2.2.2
                          linarith only [hlam, p2063_0]
                · linarith only [h1120, h1121, h2056, hc35, hlam, hphi, ht23, u2ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2161 | h2161
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2162 | h2162
                  · linarith only [h1117, h1121, h2162, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2164 | h2164
                    · linarith only [h1118, h1120, h1121, h2050, h2054, h2055, h2164, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2166 | h2166
                      · linarith only [h1117, h1121, h2050, h2054, h2055, h2161, h2166, h921, hc01, hc12, hlam, hphi]
                      · rcases h0bigk with h2168c | h2168c | h2168c | h2168c | h2168c | h2168c | h2168c | h2168c | h2168c | h2168c | h2168c | h2168c | h2168c | h2168c | h2168c | h2168c | h2168c | h2168c | h2168c | h2168c | h2168c | h2168c | h2168c | h2168c | h2168c
                        · have p2168_0 := h2168c.1
                          have p2168_1 := h2168c.2.1
                          have p2168_2 := h2168c.2.2.1
                          have p2168_3 := h2168c.2.2.2
                          linarith only [hlam, p2168_0]
                        · have p2168_0 := h2168c.1
                          have p2168_1 := h2168c.2.1
                          have p2168_2 := h2168c.2.2.1
                          have p2168_3 := h2168c.2.2.2
                          linarith only [h0, hlam, p2168_1]
                        · have p2168_0 := h2168c.1
                          have p2168_1 := h2168c.2.1
                          have p2168_2 := h2168c.2.2.1
                          have p2168_3 := h2168c.2.2.2
                          linarith only [h692, hlam, p2168_0]
                        · have p2168_0 := h2168c.1
                          have p2168_1 := h2168c.2.1
                          have p2168_2 := h2168c.2.2.1
                          have p2168_3 := h2168c.2.2.2
                          linarith only [h921, hlam, p2168_1]
                        · have p2168_0 := h2168c.1
                          have p2168_1 := h2168c.2.1
                          have p2168_2 := h2168c.2.2.1
                          have p2168_3 := h2168c.2.2.2
                          linarith only [h1036, hlam, p2168_1]
                        · have p2168_0 := h2168c.1
                          have p2168_1 := h2168c.2.1
                          have p2168_2 := h2168c.2.2.1
                          have p2168_3 := h2168c.2.2.2
                          rcases p2168_3 (m.d 0 1) (by simp) with h2174 | h2174
                          · linarith only [h0, h2174, hlam]
                          · rcases p2168_3 (m.d 0 2) (by simp) with h2176 | h2176
                            · rcases p2168_3 (m.d 0 3) (by simp) with h2177 | h2177
                              · linarith only [h1117, h2177, hlam]
                              · linarith only [h2177, h692, hlam]
                            · linarith only [h0, h2176, hlam]
                        · have p2168_0 := h2168c.1
                          have p2168_1 := h2168c.2.1
                          have p2168_2 := h2168c.2.2.1
                          have p2168_3 := h2168c.2.2.2
                          linarith only [hlam, p2168_0]
                        · have p2168_0 := h2168c.1
                          have p2168_1 := h2168c.2.1
                          have p2168_2 := h2168c.2.2.1
                          have p2168_3 := h2168c.2.2.2
                          rcases p2168_3 (m.d 0 1) (by simp) with h2182 | h2182
                          · linarith only [h0, h2182, hlam]
                          · rcases p2168_3 (m.d 0 2) (by simp) with h2184 | h2184
                            · rcases p2168_3 (m.d 0 3) (by simp) with h2185 | h2185
                              · linarith only [h1117, h2185, hlam]
                              · rcases p2168_3 (m.d 0 4) (by simp) with h2187 | h2187
                                · linarith only [h1118, h2187, hlam]
                                · rcases p2168_3 (m.d 0 5) (by simp) with h2189 | h2189
                                  · linarith only [h1119, h2189, hlam]
                                  · linarith only [h1121, h2189, hlam]
                            · linarith only [h1117, h2184, hlam]
                        · have p2168_0 := h2168c.1
                          have p2168_1 := h2168c.2.1
                          have p2168_2 := h2168c.2.2.1
                          have p2168_3 := h2168c.2.2.2
                          rcases p2168_3 (m.d 0 1) (by simp) with h2193 | h2193
                          · linarith only [h0, h2193, hlam]
                          · rcases p2168_3 (m.d 0 2) (by simp) with h2195 | h2195
                            · rcases p2168_3 (m.d 0 3) (by simp) with h2196 | h2196
                              · linarith only [h1117, h2196, hlam]
                              · linarith only [h1120, h2196, hlam]
                            · linarith only [h1118, h2195, hlam]
                        · have p2168_0 := h2168c.1
                          have p2168_1 := h2168c.2.1
                          have p2168_2 := h2168c.2.2.1
                          have p2168_3 := h2168c.2.2.2
                          rcases p2168_3 (m.d 0 1) (by simp) with h2200 | h2200
                          · linarith only [h0, h2200, hlam]
                          · rcases p2168_3 (m.d 0 2) (by simp) with h2202 | h2202
                            · rcases p2168_3 (m.d 0 3) (by simp) with h2203 | h2203
                              · linarith only [h1117, h2203, hlam]
                              · rcases p2168_3 (m.d 0 4) (by simp) with h2205 | h2205
                                · linarith only [h1118, h2205, hlam]
                                · rcases p2168_3 (m.d 0 5) (by simp) with h2207 | h2207
                                  · linarith only [h1119, h2207, hlam]
                                  · rcases h3bigk with h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c | h2209c
                                    · have p2209_0 := h2209c.1
                                      have p2209_1 := h2209c.2.1
                                      have p2209_2 := h2209c.2.2.1
                                      have p2209_3 := h2209c.2.2.2
                                      linarith only [hlam, p2209_0]
                                    · have p2209_0 := h2209c.1
                                      have p2209_1 := h2209c.2.1
                                      have p2209_2 := h2209c.2.2.1
                                      have p2209_3 := h2209c.2.2.2
                                      linarith only [h692, hlam, p2209_1]
                                    · have p2209_0 := h2209c.1
                                      have p2209_1 := h2209c.2.1
                                      have p2209_2 := h2209c.2.2.1
                                      have p2209_3 := h2209c.2.2.2
                                      linarith only [h0, h1121, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2168_1, p2209_1]
                                    · have p2209_0 := h2209c.1
                                      have p2209_1 := h2209c.2.1
                                      have p2209_2 := h2209c.2.2.1
                                      have p2209_3 := h2209c.2.2.2
                                      linarith only [h0, h1121, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2168_1, p2209_1]
                                    · have p2209_0 := h2209c.1
                                      have p2209_1 := h2209c.2.1
                                      have p2209_2 := h2209c.2.2.1
                                      have p2209_3 := h2209c.2.2.2
                                      linarith only [h1121, hlam, p2209_0]
                                    · have p2209_0 := h2209c.1
                                      have p2209_1 := h2209c.2.1
                                      have p2209_2 := h2209c.2.2.1
                                      have p2209_3 := h2209c.2.2.2
                                      rcases p2209_3 (m.d 0 3) (by simp) with h2215 | h2215
                                      · linarith only [h2215, h692, hlam]
                                      · rcases p2209_3 (m.d 1 3) (by simp) with h2217 | h2217
                                        · rcases p2209_3 (m.d 2 3) (by simp) with h2218 | h2218
                                          · linarith only [h2050, h2218, hlam]
                                          · rcases p2209_3 (m.d 3 4) (by simp) with h2220 | h2220
                                            · linarith only [h2053, h2220, hlam]
                                            · rcases p2209_3 (m.d 3 5) (by simp) with h2222 | h2222
                                              · linarith only [h2054, h2222, hlam]
                                              · linarith only [h1121, h2222, hlam]
                                        · linarith only [h2217, h692, hlam]
                                    · have p2209_0 := h2209c.1
                                      have p2209_1 := h2209c.2.1
                                      have p2209_2 := h2209c.2.2.1
                                      have p2209_3 := h2209c.2.2.2
                                      linarith only [hlam, p2209_0]
                                    · have p2209_0 := h2209c.1
                                      have p2209_1 := h2209c.2.1
                                      have p2209_2 := h2209c.2.2.1
                                      have p2209_3 := h2209c.2.2.2
                                      rcases p2209_3 (m.d 0 3) (by simp) with h2227 | h2227
                                      · linarith only [h2227, h692, hlam]
                                      · linarith only [h1117, h2227, hlam]
                                    · have p2209_0 := h2209c.1
                                      have p2209_1 := h2209c.2.1
                                      have p2209_2 := h2209c.2.2.1
                                      have p2209_3 := h2209c.2.2.2
                                      linarith only [h1120, h1121, h2054, hlam, p2209_2]
                                    · have p2209_0 := h2209c.1
                                      have p2209_1 := h2209c.2.1
                                      have p2209_2 := h2209c.2.2.1
                                      have p2209_3 := h2209c.2.2.2
                                      linarith only [h1120, h1121, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2209_1]
                                    · have p2209_0 := h2209c.1
                                      have p2209_1 := h2209c.2.1
                                      have p2209_2 := h2209c.2.2.1
                                      have p2209_3 := h2209c.2.2.2
                                      linarith only [h1117, hlam, p2209_0]
                                    · have p2209_0 := h2209c.1
                                      have p2209_1 := h2209c.2.1
                                      have p2209_2 := h2209c.2.2.1
                                      have p2209_3 := h2209c.2.2.2
                                      linarith only [h2050, hlam, p2209_0]
                                    · have p2209_0 := h2209c.1
                                      have p2209_1 := h2209c.2.1
                                      have p2209_2 := h2209c.2.2.1
                                      have p2209_3 := h2209c.2.2.2
                                      linarith only [hlam, p2209_0]
                                    · have p2209_0 := h2209c.1
                                      have p2209_1 := h2209c.2.1
                                      have p2209_2 := h2209c.2.2.1
                                      have p2209_3 := h2209c.2.2.2
                                      linarith only [h0, h1117, h1121, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2168_1, p2209_1]
                                    · have p2209_0 := h2209c.1
                                      have p2209_1 := h2209c.2.1
                                      have p2209_2 := h2209c.2.2.1
                                      have p2209_3 := h2209c.2.2.2
                                      linarith only [h2162, hlam, p2209_0]
                                    · have p2209_0 := h2209c.1
                                      have p2209_1 := h2209c.2.1
                                      have p2209_2 := h2209c.2.2.1
                                      have p2209_3 := h2209c.2.2.2
                                      linarith only [h1120, hlam, p2209_0]
                                    · have p2209_0 := h2209c.1
                                      have p2209_1 := h2209c.2.1
                                      have p2209_2 := h2209c.2.2.1
                                      have p2209_3 := h2209c.2.2.2
                                      linarith only [h2053, hlam, p2209_0]
                                    · have p2209_0 := h2209c.1
                                      have p2209_1 := h2209c.2.1
                                      have p2209_2 := h2209c.2.2.1
                                      have p2209_3 := h2209c.2.2.2
                                      linarith only [h2161, hlam, p2209_0]
                                    · have p2209_0 := h2209c.1
                                      have p2209_1 := h2209c.2.1
                                      have p2209_2 := h2209c.2.2.1
                                      have p2209_3 := h2209c.2.2.2
                                      linarith only [hlam, p2209_0]
                                    · have p2209_0 := h2209c.1
                                      have p2209_1 := h2209c.2.1
                                      have p2209_2 := h2209c.2.2.1
                                      have p2209_3 := h2209c.2.2.2
                                      linarith only [h2166, hlam, p2209_1]
                                    · have p2209_0 := h2209c.1
                                      have p2209_1 := h2209c.2.1
                                      have p2209_2 := h2209c.2.2.1
                                      have p2209_3 := h2209c.2.2.2
                                      linarith only [h1117, hc35, hlam, hphi, ht23, p2209_1, u2ehi2]
                                    · have p2209_0 := h2209c.1
                                      have p2209_1 := h2209c.2.1
                                      have p2209_2 := h2209c.2.2.1
                                      have p2209_3 := h2209c.2.2.2
                                      linarith only [h2054, hlam, p2209_0]
                                    · have p2209_0 := h2209c.1
                                      have p2209_1 := h2209c.2.1
                                      have p2209_2 := h2209c.2.2.1
                                      have p2209_3 := h2209c.2.2.2
                                      linarith only [h2050, h2054, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2209_1, u2ehi2]
                                    · have p2209_0 := h2209c.1
                                      have p2209_1 := h2209c.2.1
                                      have p2209_2 := h2209c.2.2.1
                                      have p2209_3 := h2209c.2.2.2
                                      rcases p2209_3 (m.d 0 3) (by simp) with h2245 | h2245
                                      · linarith only [h1121, h2245, hlam]
                                      · linarith only [h1120, h2245, hlam]
                                    · have p2209_0 := h2209c.1
                                      have p2209_1 := h2209c.2.1
                                      have p2209_2 := h2209c.2.2.1
                                      have p2209_3 := h2209c.2.2.2
                                      linarith only [hlam, p2209_0]
                            · linarith only [h1119, h2202, hlam]
                        · have p2168_0 := h2168c.1
                          have p2168_1 := h2168c.2.1
                          have p2168_2 := h2168c.2.2.1
                          have p2168_3 := h2168c.2.2.2
                          linarith only [h1121, h2050, h2054, hc01, hc12, hlam, hphi, p2168_1]
                        · have p2168_0 := h2168c.1
                          have p2168_1 := h2168c.2.1
                          have p2168_2 := h2168c.2.2.1
                          have p2168_3 := h2168c.2.2.2
                          linarith only [h1117, hlam, p2168_1]
                        · have p2168_0 := h2168c.1
                          have p2168_1 := h2168c.2.1
                          have p2168_2 := h2168c.2.2.1
                          have p2168_3 := h2168c.2.2.2
                          linarith only [hlam, p2168_0]
                        · have p2168_0 := h2168c.1
                          have p2168_1 := h2168c.2.1
                          have p2168_2 := h2168c.2.2.1
                          have p2168_3 := h2168c.2.2.2
                          linarith only [h1036, h1118, h1121, h2055, hc45, hlam, hphi, ht23, ht34, p2168_1, u2ehi3]
                        · have p2168_0 := h2168c.1
                          have p2168_1 := h2168c.2.1
                          have p2168_2 := h2168c.2.2.1
                          have p2168_3 := h2168c.2.2.2
                          linarith only [h1121, hlam, p2168_1]
                        · have p2168_0 := h2168c.1
                          have p2168_1 := h2168c.2.1
                          have p2168_2 := h2168c.2.2.1
                          have p2168_3 := h2168c.2.2.2
                          linarith only [h1120, h1121, h2050, h2054, hc01, hc12, hlam, hphi, p2168_1]
                        · have p2168_0 := h2168c.1
                          have p2168_1 := h2168c.2.1
                          have p2168_2 := h2168c.2.2.1
                          have p2168_3 := h2168c.2.2.2
                          linarith only [h1118, hlam, p2168_0]
                        · have p2168_0 := h2168c.1
                          have p2168_1 := h2168c.2.1
                          have p2168_2 := h2168c.2.2.1
                          have p2168_3 := h2168c.2.2.2
                          linarith only [h1120, hlam, p2168_0]
                        · have p2168_0 := h2168c.1
                          have p2168_1 := h2168c.2.1
                          have p2168_2 := h2168c.2.2.1
                          have p2168_3 := h2168c.2.2.2
                          linarith only [hlam, p2168_0]
                        · have p2168_0 := h2168c.1
                          have p2168_1 := h2168c.2.1
                          have p2168_2 := h2168c.2.2.1
                          have p2168_3 := h2168c.2.2.2
                          linarith only [h2048, hlam, p2168_0]
                        · have p2168_0 := h2168c.1
                          have p2168_1 := h2168c.2.1
                          have p2168_2 := h2168c.2.2.1
                          have p2168_3 := h2168c.2.2.2
                          linarith only [h1121, h2050, h2054, hc01, hc12, hlam, hphi, p2168_1]
                        · have p2168_0 := h2168c.1
                          have p2168_1 := h2168c.2.1
                          have p2168_2 := h2168c.2.2.1
                          have p2168_3 := h2168c.2.2.2
                          linarith only [h1119, hlam, p2168_1]
                        · have p2168_0 := h2168c.1
                          have p2168_1 := h2168c.2.1
                          have p2168_2 := h2168c.2.2.1
                          have p2168_3 := h2168c.2.2.2
                          linarith only [h1117, h1121, h2050, h2054, h2161, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2168_1, u2ehi3]
                        · have p2168_0 := h2168c.1
                          have p2168_1 := h2168c.2.1
                          have p2168_2 := h2168c.2.2.1
                          have p2168_3 := h2168c.2.2.2
                          linarith only [h1121, h2050, h2054, h921, hc01, hc12, hlam, hphi, p2168_1]
                        · have p2168_0 := h2168c.1
                          have p2168_1 := h2168c.2.1
                          have p2168_2 := h2168c.2.2.1
                          have p2168_3 := h2168c.2.2.2
                          linarith only [hlam, p2168_0]
                · linarith only [h1120, h1121, h2050, h2054, h2161, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2266 | h2266
              · linarith only [h1118, h2048, h2053, h2054, h2266, hc35, hlam, hphi, ht23, u2ehi3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2268 | h2268
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2269 | h2269
                  · linarith only [h2054, h2269, h692, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2271 | h2271
                    · linarith only [h1118, h1120, h2266, h2271, h692, h921, hc01, hc13, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2273 | h2273
                      · linarith only [h1117, h1118, h2054, h2266, h2268, h2273, h692, h921, hc35, hlam, hphi, ht23, u2ehi3]
                      · rcases h0bigk with h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c | h2275c
                        · have p2275_0 := h2275c.1
                          have p2275_1 := h2275c.2.1
                          have p2275_2 := h2275c.2.2.1
                          have p2275_3 := h2275c.2.2.2
                          linarith only [hlam, p2275_0]
                        · have p2275_0 := h2275c.1
                          have p2275_1 := h2275c.2.1
                          have p2275_2 := h2275c.2.2.1
                          have p2275_3 := h2275c.2.2.2
                          linarith only [h0, hlam, p2275_1]
                        · have p2275_0 := h2275c.1
                          have p2275_1 := h2275c.2.1
                          have p2275_2 := h2275c.2.2.1
                          have p2275_3 := h2275c.2.2.2
                          linarith only [h692, hlam, p2275_0]
                        · have p2275_0 := h2275c.1
                          have p2275_1 := h2275c.2.1
                          have p2275_2 := h2275c.2.2.1
                          have p2275_3 := h2275c.2.2.2
                          linarith only [h921, hlam, p2275_1]
                        · have p2275_0 := h2275c.1
                          have p2275_1 := h2275c.2.1
                          have p2275_2 := h2275c.2.2.1
                          have p2275_3 := h2275c.2.2.2
                          linarith only [h1036, hlam, p2275_1]
                        · have p2275_0 := h2275c.1
                          have p2275_1 := h2275c.2.1
                          have p2275_2 := h2275c.2.2.1
                          have p2275_3 := h2275c.2.2.2
                          rcases p2275_3 (m.d 0 1) (by simp) with h2281 | h2281
                          · linarith only [h0, h2281, hlam]
                          · rcases p2275_3 (m.d 0 2) (by simp) with h2283 | h2283
                            · rcases p2275_3 (m.d 0 3) (by simp) with h2284 | h2284
                              · linarith only [h1117, h2284, hlam]
                              · linarith only [h2284, h692, hlam]
                            · linarith only [h0, h2283, hlam]
                        · have p2275_0 := h2275c.1
                          have p2275_1 := h2275c.2.1
                          have p2275_2 := h2275c.2.2.1
                          have p2275_3 := h2275c.2.2.2
                          linarith only [hlam, p2275_0]
                        · have p2275_0 := h2275c.1
                          have p2275_1 := h2275c.2.1
                          have p2275_2 := h2275c.2.2.1
                          have p2275_3 := h2275c.2.2.2
                          rcases p2275_3 (m.d 0 1) (by simp) with h2289 | h2289
                          · linarith only [h0, h2289, hlam]
                          · rcases p2275_3 (m.d 0 2) (by simp) with h2291 | h2291
                            · rcases p2275_3 (m.d 0 3) (by simp) with h2292 | h2292
                              · linarith only [h1117, h2292, hlam]
                              · rcases p2275_3 (m.d 0 4) (by simp) with h2294 | h2294
                                · linarith only [h1118, h2294, hlam]
                                · rcases p2275_3 (m.d 0 5) (by simp) with h2296 | h2296
                                  · linarith only [h1119, h2296, hlam]
                                  · linarith only [h1121, h2296, hlam]
                            · linarith only [h1117, h2291, hlam]
                        · have p2275_0 := h2275c.1
                          have p2275_1 := h2275c.2.1
                          have p2275_2 := h2275c.2.2.1
                          have p2275_3 := h2275c.2.2.2
                          rcases p2275_3 (m.d 0 1) (by simp) with h2300 | h2300
                          · linarith only [h0, h2300, hlam]
                          · rcases p2275_3 (m.d 0 2) (by simp) with h2302 | h2302
                            · rcases p2275_3 (m.d 0 3) (by simp) with h2303 | h2303
                              · linarith only [h1117, h2303, hlam]
                              · linarith only [h1120, h2303, hlam]
                            · linarith only [h1118, h2302, hlam]
                        · have p2275_0 := h2275c.1
                          have p2275_1 := h2275c.2.1
                          have p2275_2 := h2275c.2.2.1
                          have p2275_3 := h2275c.2.2.2
                          rcases p2275_3 (m.d 0 1) (by simp) with h2307 | h2307
                          · linarith only [h0, h2307, hlam]
                          · rcases p2275_3 (m.d 0 2) (by simp) with h2309 | h2309
                            · rcases p2275_3 (m.d 0 3) (by simp) with h2310 | h2310
                              · linarith only [h1117, h2310, hlam]
                              · rcases p2275_3 (m.d 0 4) (by simp) with h2312 | h2312
                                · linarith only [h1118, h2312, hlam]
                                · rcases p2275_3 (m.d 0 5) (by simp) with h2314 | h2314
                                  · linarith only [h1119, h2314, hlam]
                                  · rcases h3bigk with h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c | h2316c
                                    · have p2316_0 := h2316c.1
                                      have p2316_1 := h2316c.2.1
                                      have p2316_2 := h2316c.2.2.1
                                      have p2316_3 := h2316c.2.2.2
                                      linarith only [hlam, p2316_0]
                                    · have p2316_0 := h2316c.1
                                      have p2316_1 := h2316c.2.1
                                      have p2316_2 := h2316c.2.2.1
                                      have p2316_3 := h2316c.2.2.2
                                      linarith only [h692, hlam, p2316_1]
                                    · have p2316_0 := h2316c.1
                                      have p2316_1 := h2316c.2.1
                                      have p2316_2 := h2316c.2.2.1
                                      have p2316_3 := h2316c.2.2.2
                                      linarith only [h0, h1121, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2275_1, p2316_1]
                                    · have p2316_0 := h2316c.1
                                      have p2316_1 := h2316c.2.1
                                      have p2316_2 := h2316c.2.2.1
                                      have p2316_3 := h2316c.2.2.2
                                      linarith only [h0, h1121, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2275_1, p2316_1]
                                    · have p2316_0 := h2316c.1
                                      have p2316_1 := h2316c.2.1
                                      have p2316_2 := h2316c.2.2.1
                                      have p2316_3 := h2316c.2.2.2
                                      linarith only [h1121, hlam, p2316_0]
                                    · have p2316_0 := h2316c.1
                                      have p2316_1 := h2316c.2.1
                                      have p2316_2 := h2316c.2.2.1
                                      have p2316_3 := h2316c.2.2.2
                                      linarith only [h2054, hc03, hc35, hlam, hphi, p2316_1]
                                    · have p2316_0 := h2316c.1
                                      have p2316_1 := h2316c.2.1
                                      have p2316_2 := h2316c.2.2.1
                                      have p2316_3 := h2316c.2.2.2
                                      linarith only [hlam, p2316_0]
                                    · have p2316_0 := h2316c.1
                                      have p2316_1 := h2316c.2.1
                                      have p2316_2 := h2316c.2.2.1
                                      have p2316_3 := h2316c.2.2.2
                                      linarith only [h2054, h2273, hc45, hlam, hphi, ht23, ht34, p2316_1, u2ehi2]
                                    · have p2316_0 := h2316c.1
                                      have p2316_1 := h2316c.2.1
                                      have p2316_2 := h2316c.2.2.1
                                      have p2316_3 := h2316c.2.2.2
                                      linarith only [h2054, h2273, hc34, hc45, hlam, hphi, p2316_1]
                                    · have p2316_0 := h2316c.1
                                      have p2316_1 := h2316c.2.1
                                      have p2316_2 := h2316c.2.2.1
                                      have p2316_3 := h2316c.2.2.2
                                      linarith only [h2054, hlam, p2316_0]
                                    · have p2316_0 := h2316c.1
                                      have p2316_1 := h2316c.2.1
                                      have p2316_2 := h2316c.2.2.1
                                      have p2316_3 := h2316c.2.2.2
                                      linarith only [h1117, hlam, p2316_0]
                                    · have p2316_0 := h2316c.1
                                      have p2316_1 := h2316c.2.1
                                      have p2316_2 := h2316c.2.2.1
                                      have p2316_3 := h2316c.2.2.2
                                      linarith only [h2050, hlam, p2316_0]
                                    · have p2316_0 := h2316c.1
                                      have p2316_1 := h2316c.2.1
                                      have p2316_2 := h2316c.2.2.1
                                      have p2316_3 := h2316c.2.2.2
                                      linarith only [hlam, p2316_0]
                                    · have p2316_0 := h2316c.1
                                      have p2316_1 := h2316c.2.1
                                      have p2316_2 := h2316c.2.2.1
                                      have p2316_3 := h2316c.2.2.2
                                      linarith only [h1117, h2054, h2273, h692, hc34, hc45, hlam, hphi, p2316_1]
                                    · have p2316_0 := h2316c.1
                                      have p2316_1 := h2316c.2.1
                                      have p2316_2 := h2316c.2.2.1
                                      have p2316_3 := h2316c.2.2.2
                                      linarith only [h2269, hlam, p2316_0]
                                    · have p2316_0 := h2316c.1
                                      have p2316_1 := h2316c.2.1
                                      have p2316_2 := h2316c.2.2.1
                                      have p2316_3 := h2316c.2.2.2
                                      linarith only [h1120, hlam, p2316_0]
                                    · have p2316_0 := h2316c.1
                                      have p2316_1 := h2316c.2.1
                                      have p2316_2 := h2316c.2.2.1
                                      have p2316_3 := h2316c.2.2.2
                                      linarith only [h2053, hlam, p2316_0]
                                    · have p2316_0 := h2316c.1
                                      have p2316_1 := h2316c.2.1
                                      have p2316_2 := h2316c.2.2.1
                                      have p2316_3 := h2316c.2.2.2
                                      linarith only [h2268, hlam, p2316_0]
                                    · have p2316_0 := h2316c.1
                                      have p2316_1 := h2316c.2.1
                                      have p2316_2 := h2316c.2.2.1
                                      have p2316_3 := h2316c.2.2.2
                                      linarith only [hlam, p2316_0]
                                    · have p2316_0 := h2316c.1
                                      have p2316_1 := h2316c.2.1
                                      have p2316_2 := h2316c.2.2.1
                                      have p2316_3 := h2316c.2.2.2
                                      linarith only [h2273, hlam, p2316_1]
                                    · have p2316_0 := h2316c.1
                                      have p2316_1 := h2316c.2.1
                                      have p2316_2 := h2316c.2.2.1
                                      have p2316_3 := h2316c.2.2.2
                                      linarith only [h1117, h2273, hc45, hlam, hphi, ht23, ht34, p2316_1, u2ehi2]
                                    · have p2316_0 := h2316c.1
                                      have p2316_1 := h2316c.2.1
                                      have p2316_2 := h2316c.2.2.1
                                      have p2316_3 := h2316c.2.2.2
                                      linarith only [h2273, h692, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2316_1]
                                    · have p2316_0 := h2316c.1
                                      have p2316_1 := h2316c.2.1
                                      have p2316_2 := h2316c.2.2.1
                                      have p2316_3 := h2316c.2.2.2
                                      linarith only [h2268, h2273, hc45, hlam, hphi, ht23, ht34, p2316_1, u2ehi3]
                                    · have p2316_0 := h2316c.1
                                      have p2316_1 := h2316c.2.1
                                      have p2316_2 := h2316c.2.2.1
                                      have p2316_3 := h2316c.2.2.2
                                      rcases p2316_3 (m.d 0 3) (by simp) with h2340 | h2340
                                      · linarith only [h1121, h2340, hlam]
                                      · linarith only [h1120, h2340, hlam]
                                    · have p2316_0 := h2316c.1
                                      have p2316_1 := h2316c.2.1
                                      have p2316_2 := h2316c.2.2.1
                                      have p2316_3 := h2316c.2.2.2
                                      linarith only [hlam, p2316_0]
                            · linarith only [h1119, h2309, hlam]
                        · have p2275_0 := h2275c.1
                          have p2275_1 := h2275c.2.1
                          have p2275_2 := h2275c.2.2.1
                          have p2275_3 := h2275c.2.2.2
                          linarith only [h1121, h2273, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2275_1]
                        · have p2275_0 := h2275c.1
                          have p2275_1 := h2275c.2.1
                          have p2275_2 := h2275c.2.2.1
                          have p2275_3 := h2275c.2.2.2
                          linarith only [h1117, hlam, p2275_1]
                        · have p2275_0 := h2275c.1
                          have p2275_1 := h2275c.2.1
                          have p2275_2 := h2275c.2.2.1
                          have p2275_3 := h2275c.2.2.2
                          linarith only [hlam, p2275_0]
                        · have p2275_0 := h2275c.1
                          have p2275_1 := h2275c.2.1
                          have p2275_2 := h2275c.2.2.1
                          have p2275_3 := h2275c.2.2.2
                          linarith only [h1036, h1118, h1121, h2054, h2273, hc45, hlam, hphi, ht23, ht34, p2275_1, u2ehi3]
                        · have p2275_0 := h2275c.1
                          have p2275_1 := h2275c.2.1
                          have p2275_2 := h2275c.2.2.1
                          have p2275_3 := h2275c.2.2.2
                          linarith only [h1121, hlam, p2275_1]
                        · have p2275_0 := h2275c.1
                          have p2275_1 := h2275c.2.1
                          have p2275_2 := h2275c.2.2.1
                          have p2275_3 := h2275c.2.2.2
                          linarith only [h1120, h1121, h2273, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2275_1]
                        · have p2275_0 := h2275c.1
                          have p2275_1 := h2275c.2.1
                          have p2275_2 := h2275c.2.2.1
                          have p2275_3 := h2275c.2.2.2
                          linarith only [h1118, hlam, p2275_0]
                        · have p2275_0 := h2275c.1
                          have p2275_1 := h2275c.2.1
                          have p2275_2 := h2275c.2.2.1
                          have p2275_3 := h2275c.2.2.2
                          linarith only [h1120, hlam, p2275_0]
                        · have p2275_0 := h2275c.1
                          have p2275_1 := h2275c.2.1
                          have p2275_2 := h2275c.2.2.1
                          have p2275_3 := h2275c.2.2.2
                          linarith only [hlam, p2275_0]
                        · have p2275_0 := h2275c.1
                          have p2275_1 := h2275c.2.1
                          have p2275_2 := h2275c.2.2.1
                          have p2275_3 := h2275c.2.2.2
                          linarith only [h2048, hlam, p2275_0]
                        · have p2275_0 := h2275c.1
                          have p2275_1 := h2275c.2.1
                          have p2275_2 := h2275c.2.2.1
                          have p2275_3 := h2275c.2.2.2
                          rcases p2275_3 (m.d 0 1) (by simp) with h2355 | h2355
                          · linarith only [h1036, h2355, hlam]
                          · rcases p2275_3 (m.d 0 2) (by simp) with h2357 | h2357
                            · rcases p2275_3 (m.d 0 3) (by simp) with h2358 | h2358
                              · linarith only [h1121, h2358, hlam]
                              · linarith only [h2358, h692, hlam]
                            · linarith only [h0, h2357, hlam]
                        · have p2275_0 := h2275c.1
                          have p2275_1 := h2275c.2.1
                          have p2275_2 := h2275c.2.2.1
                          have p2275_3 := h2275c.2.2.2
                          linarith only [h1119, hlam, p2275_1]
                        · have p2275_0 := h2275c.1
                          have p2275_1 := h2275c.2.1
                          have p2275_2 := h2275c.2.2.1
                          have p2275_3 := h2275c.2.2.2
                          linarith only [h1036, h1117, h2054, h2268, h2273, hc45, hlam, hphi, ht23, ht34, p2275_1, u2ehi3]
                        · have p2275_0 := h2275c.1
                          have p2275_1 := h2275c.2.1
                          have p2275_2 := h2275c.2.2.1
                          have p2275_3 := h2275c.2.2.2
                          linarith only [h1036, h1118, h2054, h2273, hc45, hlam, hphi, ht23, ht34, p2275_1, u2ehi3]
                        · have p2275_0 := h2275c.1
                          have p2275_1 := h2275c.2.1
                          have p2275_2 := h2275c.2.2.1
                          have p2275_3 := h2275c.2.2.2
                          linarith only [hlam, p2275_0]
                · linarith only [h1120, h2054, h2268, h692, hc35, hlam, hphi, ht23, u2ehi2]
          · linarith only [h1120, h1121, h2053, hc13, hc35, hlam, hphi]
        · linarith only [h0, h1117, h2052, hc25, hlam, hphi, u2ehi2]
      · linarith only [h0, h1117, h2051, hc24, hlam, hphi, u2ehi2]
    · linarith only [h0, h1119, h2050, hc23, hlam, hphi, u2ehi4]

set_option maxHeartbeats 5810000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h692 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h921 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1036 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1117 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1118 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1119 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1120 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h1121 | h1121
  · exact r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h692 h921 h1036 h1117 h1118 h1119 h1120 h1121
  · exact r1l7_10_12_13_25_L_I_L_R_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h692 h921 h1036 h1117 h1118 h1119 h1120 h1121

end R2N4
