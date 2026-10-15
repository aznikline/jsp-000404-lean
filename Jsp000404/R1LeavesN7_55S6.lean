import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_55S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4278000 in
set_option maxHeartbeats 4278000 in
theorem r1l7_11_12_25_L_I_L_0_M_IR_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emin := hb1.2.1
  have h2elo := hb2.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1629 | h1629
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1630 | h1630
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1631 | h1631
      · linarith only [h0, h1631, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1633 | h1633
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1634 | h1634
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1635 | h1635
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1636 | h1636
              · linarith only [h0, h1629, h1636, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1638 | h1638
                · linarith only [h0, h1630, h1638, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1640 | h1640
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1641 | h1641
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1642 | h1642
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1643 | h1643
                        · linarith only [h1629, h1631, h1642, h1643, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1645 | h1645
                          · linarith only [h1630, h1631, h1636, h1642, h1643, h1645, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1647 | h1647
                            · linarith only [h1630, h1631, h1638, h1642, h1647, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1649 | h1649
                              · linarith only [h1640, h1643, h1649, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1651 | h1651
                                · linarith only [h1630, h1631, h1640, h1643, h1645, h1651, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1653 | h1653
                                  · linarith only [h1630, h1631, h1641, h1647, h1653, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1655 | h1655
                                    · linarith only [h1630, h1631, h1643, h1647, h1655, hc13, hc34, hlam, hphi]
                                    · rcases h1bigk with h1657c | h1657c | h1657c | h1657c | h1657c | h1657c | h1657c | h1657c | h1657c | h1657c | h1657c | h1657c | h1657c | h1657c | h1657c | h1657c | h1657c | h1657c | h1657c | h1657c | h1657c | h1657c | h1657c | h1657c | h1657c
                                      · have p1657_0 := h1657c.1
                                        have p1657_1 := h1657c.2.1
                                        have p1657_2 := h1657c.2.2.1
                                        have p1657_3 := h1657c.2.2.2
                                        linarith only [hlam, p1657_0]
                                      · have p1657_0 := h1657c.1
                                        have p1657_1 := h1657c.2.1
                                        have p1657_2 := h1657c.2.2.1
                                        have p1657_3 := h1657c.2.2.2
                                        linarith only [h0, hlam, p1657_0]
                                      · have p1657_0 := h1657c.1
                                        have p1657_1 := h1657c.2.1
                                        have p1657_2 := h1657c.2.2.1
                                        have p1657_3 := h1657c.2.2.2
                                        linarith only [h1631, h1640, h1642, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1657_1, u2elo1]
                                      · have p1657_0 := h1657c.1
                                        have p1657_1 := h1657c.2.1
                                        have p1657_2 := h1657c.2.2.1
                                        have p1657_3 := h1657c.2.2.2
                                        linarith only [h1631, h1642, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1657_1, u2elo1]
                                      · have p1657_0 := h1657c.1
                                        have p1657_1 := h1657c.2.1
                                        have p1657_2 := h1657c.2.2.1
                                        have p1657_3 := h1657c.2.2.2
                                        linarith only [h1631, hlam, p1657_0]
                                      · have p1657_0 := h1657c.1
                                        have p1657_1 := h1657c.2.1
                                        have p1657_2 := h1657c.2.2.1
                                        have p1657_3 := h1657c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht12, p1657_1, u2elo1]
                                      · have p1657_0 := h1657c.1
                                        have p1657_1 := h1657c.2.1
                                        have p1657_2 := h1657c.2.2.1
                                        have p1657_3 := h1657c.2.2.2
                                        linarith only [hlam, p1657_0]
                                      · have p1657_0 := h1657c.1
                                        have p1657_1 := h1657c.2.1
                                        have p1657_2 := h1657c.2.2.1
                                        have p1657_3 := h1657c.2.2.2
                                        rcases p1657_3 (m.d 0 1) (by simp) with h1665 | h1665
                                        · linarith only [h0, h1665, hlam]
                                        · linarith only [h1629, h1665, hlam]
                                      · have p1657_0 := h1657c.1
                                        have p1657_1 := h1657c.2.1
                                        have p1657_2 := h1657c.2.2.1
                                        have p1657_3 := h1657c.2.2.2
                                        rcases p1657_3 (m.d 0 1) (by simp) with h1668 | h1668
                                        · linarith only [h0, h1668, hlam]
                                        · linarith only [h1630, h1668, hlam]
                                      · have p1657_0 := h1657c.1
                                        have p1657_1 := h1657c.2.1
                                        have p1657_2 := h1657c.2.2.1
                                        have p1657_3 := h1657c.2.2.2
                                        linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p1657_1, u2elo1, u5ehi1]
                                      · have p1657_0 := h1657c.1
                                        have p1657_1 := h1657c.2.1
                                        have p1657_2 := h1657c.2.2.1
                                        have p1657_3 := h1657c.2.2.2
                                        linarith only [h1629, hlam, p1657_0]
                                      · have p1657_0 := h1657c.1
                                        have p1657_1 := h1657c.2.1
                                        have p1657_2 := h1657c.2.2.1
                                        have p1657_3 := h1657c.2.2.2
                                        linarith only [h1640, hlam, p1657_0]
                                      · have p1657_0 := h1657c.1
                                        have p1657_1 := h1657c.2.1
                                        have p1657_2 := h1657c.2.2.1
                                        have p1657_3 := h1657c.2.2.2
                                        linarith only [hlam, p1657_0]
                                      · have p1657_0 := h1657c.1
                                        have p1657_1 := h1657c.2.1
                                        have p1657_2 := h1657c.2.2.1
                                        have p1657_3 := h1657c.2.2.2
                                        linarith only [h1643, hlam, p1657_0]
                                      · have p1657_0 := h1657c.1
                                        have p1657_1 := h1657c.2.1
                                        have p1657_2 := h1657c.2.2.1
                                        have p1657_3 := h1657c.2.2.2
                                        linarith only [h1645, hlam, p1657_1]
                                      · have p1657_0 := h1657c.1
                                        have p1657_1 := h1657c.2.1
                                        have p1657_2 := h1657c.2.2.1
                                        have p1657_3 := h1657c.2.2.2
                                        linarith only [h1630, hlam, p1657_0]
                                      · have p1657_0 := h1657c.1
                                        have p1657_1 := h1657c.2.1
                                        have p1657_2 := h1657c.2.2.1
                                        have p1657_3 := h1657c.2.2.2
                                        linarith only [h1641, hlam, p1657_0]
                                      · have p1657_0 := h1657c.1
                                        have p1657_1 := h1657c.2.1
                                        have p1657_2 := h1657c.2.2.1
                                        have p1657_3 := h1657c.2.2.2
                                        linarith only [h0, h1630, h1640, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1657_1, u2elo1]
                                      · have p1657_0 := h1657c.1
                                        have p1657_1 := h1657c.2.1
                                        have p1657_2 := h1657c.2.2.1
                                        have p1657_3 := h1657c.2.2.2
                                        linarith only [hlam, p1657_0]
                                      · have p1657_0 := h1657c.1
                                        have p1657_1 := h1657c.2.1
                                        have p1657_2 := h1657c.2.2.1
                                        have p1657_3 := h1657c.2.2.2
                                        linarith only [h1647, hlam, p1657_1]
                                      · have p1657_0 := h1657c.1
                                        have p1657_1 := h1657c.2.1
                                        have p1657_2 := h1657c.2.2.1
                                        have p1657_3 := h1657c.2.2.2
                                        linarith only [h1630, h1645, h1655, hc14, hc45, hlam, hphi, p1657_1]
                                      · have p1657_0 := h1657c.1
                                        have p1657_1 := h1657c.2.1
                                        have p1657_2 := h1657c.2.2.1
                                        have p1657_3 := h1657c.2.2.2
                                        linarith only [h1642, hlam, p1657_0]
                                      · have p1657_0 := h1657c.1
                                        have p1657_1 := h1657c.2.1
                                        have p1657_2 := h1657c.2.2.1
                                        have p1657_3 := h1657c.2.2.2
                                        rcases p1657_3 (m.d 0 1) (by simp) with h1684 | h1684
                                        · linarith only [h1631, h1684, hlam]
                                        · linarith only [h1629, h1684, hlam]
                                      · have p1657_0 := h1657c.1
                                        have p1657_1 := h1657c.2.1
                                        have p1657_2 := h1657c.2.2.1
                                        have p1657_3 := h1657c.2.2.2
                                        rcases p1657_3 (m.d 0 1) (by simp) with h1687 | h1687
                                        · linarith only [h1631, h1687, hlam]
                                        · linarith only [h1630, h1687, hlam]
                                      · have p1657_0 := h1657c.1
                                        have p1657_1 := h1657c.2.1
                                        have p1657_2 := h1657c.2.2.1
                                        have p1657_3 := h1657c.2.2.2
                                        linarith only [hlam, p1657_0]
                      · linarith only [h1635, h1642, hc12, hlam, hphi, u2elo0]
                    · linarith only [h0, h1635, h1641, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
                  · linarith only [h0, h1635, h1640, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1694 | h1694
              · linarith only [h0, h1629, h1635, h1694, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1696 | h1696
                · linarith only [h0, h1630, h1635, h1696, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1698 | h1698
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1699 | h1699
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1700 | h1700
                      · linarith only [h0, h1629, h1635, h1698, h1700, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h1629, h1698, h1700, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · linarith only [h0, h1629, h1698, h1699, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1629, h1698, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
          · linarith only [h0, h1630, h1634, hlam]
        · linarith only [h0, h1629, h1633, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1707 | h1707
      · linarith only [h0, h1707, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1709 | h1709
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1710 | h1710
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1711 | h1711
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1712 | h1712
              · linarith only [h0, h1629, h1712, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1714 | h1714
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1715 | h1715
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1716 | h1716
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1717 | h1717
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1718 | h1718
                        · linarith only [h1629, h1630, h1716, h1718, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1720 | h1720
                          · linarith only [h1629, h1630, h1712, h1716, h1720, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1722 | h1722
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1723 | h1723
                              · linarith only [h1629, h1707, h1715, h1718, h1722, h1723, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1725 | h1725
                                · linarith only [h1629, h1707, h1715, h1720, h1725, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1727 | h1727
                                  · linarith only [h1710, h1727, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1729 | h1729
                                    · rcases h1bigk with h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c | h1730c
                                      · have p1730_0 := h1730c.1
                                        have p1730_1 := h1730c.2.1
                                        have p1730_2 := h1730c.2.2.1
                                        have p1730_3 := h1730c.2.2.2
                                        linarith only [hlam, p1730_0]
                                      · have p1730_0 := h1730c.1
                                        have p1730_1 := h1730c.2.1
                                        have p1730_2 := h1730c.2.2.1
                                        have p1730_3 := h1730c.2.2.2
                                        linarith only [h0, hlam, p1730_0]
                                      · have p1730_0 := h1730c.1
                                        have p1730_1 := h1730c.2.1
                                        have p1730_2 := h1730c.2.2.1
                                        have p1730_3 := h1730c.2.2.2
                                        linarith only [h1707, h1716, h1722, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1730_1, u2elo1]
                                      · have p1730_0 := h1730c.1
                                        have p1730_1 := h1730c.2.1
                                        have p1730_2 := h1730c.2.2.1
                                        have p1730_3 := h1730c.2.2.2
                                        linarith only [h1630, hlam, p1730_0]
                                      · have p1730_0 := h1730c.1
                                        have p1730_1 := h1730c.2.1
                                        have p1730_2 := h1730c.2.2.1
                                        have p1730_3 := h1730c.2.2.2
                                        linarith only [h1707, hlam, p1730_0]
                                      · have p1730_0 := h1730c.1
                                        have p1730_1 := h1730c.2.1
                                        have p1730_2 := h1730c.2.2.1
                                        have p1730_3 := h1730c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht12, p1730_1, u2elo1]
                                      · have p1730_0 := h1730c.1
                                        have p1730_1 := h1730c.2.1
                                        have p1730_2 := h1730c.2.2.1
                                        have p1730_3 := h1730c.2.2.2
                                        linarith only [hlam, p1730_0]
                                      · have p1730_0 := h1730c.1
                                        have p1730_1 := h1730c.2.1
                                        have p1730_2 := h1730c.2.2.1
                                        have p1730_3 := h1730c.2.2.2
                                        rcases p1730_3 (m.d 0 1) (by simp) with h1738 | h1738
                                        · linarith only [h0, h1738, hlam]
                                        · linarith only [h1629, h1738, hlam]
                                      · have p1730_0 := h1730c.1
                                        have p1730_1 := h1730c.2.1
                                        have p1730_2 := h1730c.2.2.1
                                        have p1730_3 := h1730c.2.2.2
                                        linarith only [h1722, hlam, hphi, ht01, ht0b, ht12, ht5b, p1730_1, u2elo1, u5ehi1]
                                      · have p1730_0 := h1730c.1
                                        have p1730_1 := h1730c.2.1
                                        have p1730_2 := h1730c.2.2.1
                                        have p1730_3 := h1730c.2.2.2
                                        linarith only [h1629, h1707, h1715, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1730_1, u2elo1]
                                      · have p1730_0 := h1730c.1
                                        have p1730_1 := h1730c.2.1
                                        have p1730_2 := h1730c.2.2.1
                                        have p1730_3 := h1730c.2.2.2
                                        linarith only [h1629, hlam, p1730_0]
                                      · have p1730_0 := h1730c.1
                                        have p1730_1 := h1730c.2.1
                                        have p1730_2 := h1730c.2.2.1
                                        have p1730_3 := h1730c.2.2.2
                                        linarith only [h1715, hlam, p1730_0]
                                      · have p1730_0 := h1730c.1
                                        have p1730_1 := h1730c.2.1
                                        have p1730_2 := h1730c.2.2.1
                                        have p1730_3 := h1730c.2.2.2
                                        linarith only [hlam, p1730_0]
                                      · have p1730_0 := h1730c.1
                                        have p1730_1 := h1730c.2.1
                                        have p1730_2 := h1730c.2.2.1
                                        have p1730_3 := h1730c.2.2.2
                                        linarith only [h1718, hlam, p1730_0]
                                      · have p1730_0 := h1730c.1
                                        have p1730_1 := h1730c.2.1
                                        have p1730_2 := h1730c.2.2.1
                                        have p1730_3 := h1730c.2.2.2
                                        linarith only [h1720, hlam, p1730_1]
                                      · have p1730_0 := h1730c.1
                                        have p1730_1 := h1730c.2.1
                                        have p1730_2 := h1730c.2.2.1
                                        have p1730_3 := h1730c.2.2.2
                                        linarith only [h1629, h1715, h1718, hc23, hc34, hlam, hphi, p1730_1]
                                      · have p1730_0 := h1730c.1
                                        have p1730_1 := h1730c.2.1
                                        have p1730_2 := h1730c.2.2.1
                                        have p1730_3 := h1730c.2.2.2
                                        linarith only [h1716, hlam, p1730_0]
                                      · have p1730_0 := h1730c.1
                                        have p1730_1 := h1730c.2.1
                                        have p1730_2 := h1730c.2.2.1
                                        have p1730_3 := h1730c.2.2.2
                                        rcases p1730_3 (m.d 0 1) (by simp) with h1750 | h1750
                                        · linarith only [h1630, h1750, hlam]
                                        · linarith only [h1629, h1750, hlam]
                                      · have p1730_0 := h1730c.1
                                        have p1730_1 := h1730c.2.1
                                        have p1730_2 := h1730c.2.2.1
                                        have p1730_3 := h1730c.2.2.2
                                        linarith only [hlam, p1730_0]
                                      · have p1730_0 := h1730c.1
                                        have p1730_1 := h1730c.2.1
                                        have p1730_2 := h1730c.2.2.1
                                        have p1730_3 := h1730c.2.2.2
                                        linarith only [h1629, h1707, h1715, h1716, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1730_1, u2elo1]
                                      · have p1730_0 := h1730c.1
                                        have p1730_1 := h1730c.2.1
                                        have p1730_2 := h1730c.2.2.1
                                        have p1730_3 := h1730c.2.2.2
                                        linarith only [h1629, h1715, h1720, hc23, hc35, hlam, hphi, p1730_1]
                                      · have p1730_0 := h1730c.1
                                        have p1730_1 := h1730c.2.1
                                        have p1730_2 := h1730c.2.2.1
                                        have p1730_3 := h1730c.2.2.2
                                        linarith only [h1717, hlam, p1730_0]
                                      · have p1730_0 := h1730c.1
                                        have p1730_1 := h1730c.2.1
                                        have p1730_2 := h1730c.2.2.1
                                        have p1730_3 := h1730c.2.2.2
                                        rcases p1730_3 (m.d 0 1) (by simp) with h1757 | h1757
                                        · linarith only [h1707, h1757, hlam]
                                        · linarith only [h1629, h1757, hlam]
                                      · have p1730_0 := h1730c.1
                                        have p1730_1 := h1730c.2.1
                                        have p1730_2 := h1730c.2.2.1
                                        have p1730_3 := h1730c.2.2.2
                                        linarith only [h1722, hlam, p1730_0]
                                      · have p1730_0 := h1730c.1
                                        have p1730_1 := h1730c.2.1
                                        have p1730_2 := h1730c.2.2.1
                                        have p1730_3 := h1730c.2.2.2
                                        linarith only [hlam, p1730_0]
                                    · linarith only [h1630, h1714, h1715, h1716, h1718, h1729, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · linarith only [h1630, h1714, h1722, hlam]
                      · linarith only [h1630, h1714, h1716, h1717, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                    · linarith only [h0, h1629, h1715, h1716, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1715, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1767 | h1767
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1768 | h1768
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1769 | h1769
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1770 | h1770
                        · linarith only [h1629, h1630, h1768, h1770, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1772 | h1772
                          · linarith only [h1629, h1630, h1768, h1772, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1774 | h1774
                            · linarith only [h1629, h1630, h1714, h1767, h1768, h1774, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · linarith only [h1629, h1630, h1767, h1774, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h1711, h1769, hc12, hlam, hphi, u2elo0]
                    · linarith only [h0, h1710, h1768, hlam]
                  · linarith only [h0, h1711, h1767, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1780 | h1780
              · linarith only [h0, h1629, h1780, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1782 | h1782
                · linarith only [h1710, h1711, h1782, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1784 | h1784
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1785 | h1785
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1786 | h1786
                      · linarith only [h1630, h1710, h1711, h1786, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h1629, h1784, h1786, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · linarith only [h0, h1629, h1710, h1784, h1785, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h1629, h1784, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1791 | h1791
            · linarith only [h1710, h1791, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1793 | h1793
              · linarith only [h0, h1629, h1793, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1795 | h1795
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1796 | h1796
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1797 | h1797
                    · linarith only [h0, h1710, h1797, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1629, h1796, h1797, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1796, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1801 | h1801
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1802 | h1802
                    · linarith only [h0, h1710, h1802, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1629, h1801, h1802, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1629, h1801, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
        · linarith only [h0, h1629, h1709, hlam]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1807 | h1807
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1808 | h1808
      · linarith only [h0, h1808, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1810 | h1810
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1811 | h1811
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1812 | h1812
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1813 | h1813
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1814 | h1814
                · linarith only [h0, h1807, h1814, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1816 | h1816
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1817 | h1817
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1818 | h1818
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1819 | h1819
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1820 | h1820
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1821 | h1821
                            · linarith only [h1807, h1808, h1814, h1816, h1820, h1821, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1823 | h1823
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1824 | h1824
                                · linarith only [h1810, h1824, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                                · linarith only [h1629, h1813, h1816, h1823, h1824, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · linarith only [h1807, h1808, h1816, h1819, h1820, h1823, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · linarith only [h1629, h1813, h1820, hlam]
                        · linarith only [h1629, h1807, h1808, h1813, h1819, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · linarith only [h1629, h1816, h1818, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h1629, h1807, h1816, h1817, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1812, h1816, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1833 | h1833
                · linarith only [h0, h1807, h1833, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1835 | h1835
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1836 | h1836
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1837 | h1837
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1838 | h1838
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1839 | h1839
                          · linarith only [h1629, h1813, h1835, h1839, hc01, hlam, hphi, ht12, u2elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1841 | h1841
                            · linarith only [h0, h1807, h1833, h1841, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1843 | h1843
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1844 | h1844
                                · linarith only [h1629, h1807, h1836, h1839, h1843, h1844, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1846 | h1846
                                  · linarith only [h1629, h1807, h1836, h1839, h1841, h1846, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1848 | h1848
                                    · linarith only [h1629, h1807, h1836, h1839, h1841, h1843, h1848, hlam]
                                    · linarith only [h1629, h1807, h1836, h1839, h1843, h1848, hc34, hc45, hlam, hphi]
                              · linarith only [h1838, h1839, h1843, hc23, hc35, hlam, hphi]
                        · linarith only [h1629, h1807, h1838, hlam]
                      · linarith only [h0, h1812, h1837, hlam]
                    · linarith only [h0, h1812, h1836, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
                  · linarith only [h0, h1812, h1835, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1856 | h1856
              · linarith only [h1810, h1812, h1856, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1858 | h1858
                · linarith only [h0, h1807, h1858, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1860 | h1860
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1861 | h1861
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1862 | h1862
                      · linarith only [h1629, h1810, h1812, h1862, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h1807, h1861, h1862, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                    · linarith only [h1629, h1807, h1860, h1861, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1807, h1860, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
          · linarith only [h0, h1807, h1811, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1868 | h1868
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1869 | h1869
            · linarith only [h1810, h1869, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1871 | h1871
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1872 | h1872
                · linarith only [h0, h1807, h1872, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1874 | h1874
                  · linarith only [h0, h1810, h1874, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h1807, h1874, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1877 | h1877
                · linarith only [h0, h1807, h1869, h1877, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1879 | h1879
                  · linarith only [h0, h1810, h1879, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h1807, h1879, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
          · linarith only [h0, h1807, h1868, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1883 | h1883
      · linarith only [h0, h1883, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1885 | h1885
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1886 | h1886
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1887 | h1887
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1888 | h1888
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1889 | h1889
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1890 | h1890
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1891 | h1891
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1892 | h1892
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1893 | h1893
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1894 | h1894
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1895 | h1895
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1896 | h1896
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1897 | h1897
                                · linarith only [h1885, h1897, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                                · linarith only [h1629, h1888, h1890, h1896, h1897, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1900 | h1900
                                · linarith only [h1890, h1893, h1896, h1900, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1902 | h1902
                                  · linarith only [h0, h1886, h1902, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1904 | h1904
                                    · linarith only [h1890, h1893, h1896, h1902, h1904, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                                    · linarith only [h1807, h1889, h1890, h1893, h1896, h1904, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · linarith only [h1807, h1889, h1895, hlam]
                          · linarith only [h1629, h1888, h1894, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1909 | h1909
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1910 | h1910
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1911 | h1911
                              · linarith only [h1629, h1888, h1893, h1911, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1913 | h1913
                                · linarith only [h1886, h1911, h1913, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                                · linarith only [h1629, h1888, h1893, h1913, hc23, hc34, hlam, hphi]
                            · linarith only [h1807, h1889, h1910, hlam]
                          · linarith only [h1629, h1888, h1909, hlam]
                      · linarith only [h0, h1886, h1889, h1892, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                    · linarith only [h0, h1886, h1891, hlam]
                  · linarith only [h0, h1887, h1890, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1921 | h1921
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1922 | h1922
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1923 | h1923
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1924 | h1924
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1925 | h1925
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1926 | h1926
                            · linarith only [h1807, h1889, h1922, h1926, hc01, hlam, hphi, ht12, u2elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1928 | h1928
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1929 | h1929
                                · linarith only [h0, h1885, h1929, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                                · linarith only [h0, h1885, h1888, h1928, h1929, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1932 | h1932
                                · linarith only [h0, h1885, h1932, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1934 | h1934
                                  · linarith only [h1807, h1926, h1934, hc01, hlam, hphi, ht12, u2elo3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1936 | h1936
                                    · linarith only [h1807, h1921, h1924, h1926, h1936, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                    · rcases h1bigk with h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c
                                      · have p1938_0 := h1938c.1
                                        have p1938_1 := h1938c.2.1
                                        have p1938_2 := h1938c.2.2.1
                                        have p1938_3 := h1938c.2.2.2
                                        linarith only [hlam, p1938_0]
                                      · have p1938_0 := h1938c.1
                                        have p1938_1 := h1938c.2.1
                                        have p1938_2 := h1938c.2.2.1
                                        have p1938_3 := h1938c.2.2.2
                                        linarith only [h0, hlam, p1938_0]
                                      · have p1938_0 := h1938c.1
                                        have p1938_1 := h1938c.2.1
                                        have p1938_2 := h1938c.2.2.1
                                        have p1938_3 := h1938c.2.2.2
                                        linarith only [h1629, hlam, p1938_0]
                                      · have p1938_0 := h1938c.1
                                        have p1938_1 := h1938c.2.1
                                        have p1938_2 := h1938c.2.2.1
                                        have p1938_3 := h1938c.2.2.2
                                        linarith only [h1807, hlam, p1938_0]
                                      · have p1938_0 := h1938c.1
                                        have p1938_1 := h1938c.2.1
                                        have p1938_2 := h1938c.2.2.1
                                        have p1938_3 := h1938c.2.2.2
                                        linarith only [h1883, hlam, p1938_0]
                                      · have p1938_0 := h1938c.1
                                        have p1938_1 := h1938c.2.1
                                        have p1938_2 := h1938c.2.2.1
                                        have p1938_3 := h1938c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht12, p1938_1, u2elo1]
                                      · have p1938_0 := h1938c.1
                                        have p1938_1 := h1938c.2.1
                                        have p1938_2 := h1938c.2.2.1
                                        have p1938_3 := h1938c.2.2.2
                                        linarith only [hlam, p1938_0]
                                      · have p1938_0 := h1938c.1
                                        have p1938_1 := h1938c.2.1
                                        have p1938_2 := h1938c.2.2.1
                                        have p1938_3 := h1938c.2.2.2
                                        linarith only [h1925, hlam, hphi, ht01, ht0b, ht12, ht5b, p1938_1, u2elo1, u5ehi1]
                                      · have p1938_0 := h1938c.1
                                        have p1938_1 := h1938c.2.1
                                        have p1938_2 := h1938c.2.2.1
                                        have p1938_3 := h1938c.2.2.2
                                        linarith only [h1807, hc01, hlam, hphi, ht12, p1938_1, u2elo1]
                                      · have p1938_0 := h1938c.1
                                        have p1938_1 := h1938c.2.1
                                        have p1938_2 := h1938c.2.2.1
                                        have p1938_3 := h1938c.2.2.2
                                        linarith only [h1883, hc01, hlam, hphi, ht12, p1938_1, u2elo1]
                                      · have p1938_0 := h1938c.1
                                        have p1938_1 := h1938c.2.1
                                        have p1938_2 := h1938c.2.2.1
                                        have p1938_3 := h1938c.2.2.2
                                        linarith only [h1921, hc01, hlam, hphi, ht12, p1938_1, u2elo1]
                                      · have p1938_0 := h1938c.1
                                        have p1938_1 := h1938c.2.1
                                        have p1938_2 := h1938c.2.2.1
                                        have p1938_3 := h1938c.2.2.2
                                        linarith only [h1921, hlam, p1938_0]
                                      · have p1938_0 := h1938c.1
                                        have p1938_1 := h1938c.2.1
                                        have p1938_2 := h1938c.2.2.1
                                        have p1938_3 := h1938c.2.2.2
                                        linarith only [hlam, p1938_0]
                                      · have p1938_0 := h1938c.1
                                        have p1938_1 := h1938c.2.1
                                        have p1938_2 := h1938c.2.2.1
                                        have p1938_3 := h1938c.2.2.2
                                        linarith only [h1807, h1921, hc01, hlam, hphi, ht12, p1938_1, u2elo1]
                                      · have p1938_0 := h1938c.1
                                        have p1938_1 := h1938c.2.1
                                        have p1938_2 := h1938c.2.2.1
                                        have p1938_3 := h1938c.2.2.2
                                        linarith only [h1883, h1921, hc01, hlam, hphi, ht12, p1938_1, u2elo1]
                                      · have p1938_0 := h1938c.1
                                        have p1938_1 := h1938c.2.1
                                        have p1938_2 := h1938c.2.2.1
                                        have p1938_3 := h1938c.2.2.2
                                        linarith only [h0, h1885, h1888, h1926, h1928, h1936, hc01, hc23, hc45, hlam, hphi, ht12, ht34, p1938_1, u2elo1]
                                      · have p1938_0 := h1938c.1
                                        have p1938_1 := h1938c.2.1
                                        have p1938_2 := h1938c.2.2.1
                                        have p1938_3 := h1938c.2.2.2
                                        linarith only [h1922, hlam, p1938_0]
                                      · have p1938_0 := h1938c.1
                                        have p1938_1 := h1938c.2.1
                                        have p1938_2 := h1938c.2.2.1
                                        have p1938_3 := h1938c.2.2.2
                                        linarith only [h1924, hlam, p1938_1]
                                      · have p1938_0 := h1938c.1
                                        have p1938_1 := h1938c.2.1
                                        have p1938_2 := h1938c.2.2.1
                                        have p1938_3 := h1938c.2.2.2
                                        linarith only [hlam, p1938_0]
                                      · have p1938_0 := h1938c.1
                                        have p1938_1 := h1938c.2.1
                                        have p1938_2 := h1938c.2.2.1
                                        have p1938_3 := h1938c.2.2.2
                                        linarith only [h1926, hlam, p1938_1]
                                      · have p1938_0 := h1938c.1
                                        have p1938_1 := h1938c.2.1
                                        have p1938_2 := h1938c.2.2.1
                                        have p1938_3 := h1938c.2.2.2
                                        linarith only [h1923, hc01, hlam, hphi, ht12, p1938_1, u2elo1]
                                      · have p1938_0 := h1938c.1
                                        have p1938_1 := h1938c.2.1
                                        have p1938_2 := h1938c.2.2.1
                                        have p1938_3 := h1938c.2.2.2
                                        linarith only [h1923, hlam, p1938_0]
                                      · have p1938_0 := h1938c.1
                                        have p1938_1 := h1938c.2.1
                                        have p1938_2 := h1938c.2.2.1
                                        have p1938_3 := h1938c.2.2.2
                                        linarith only [h1925, hlam, p1938_0]
                                      · have p1938_0 := h1938c.1
                                        have p1938_1 := h1938c.2.1
                                        have p1938_2 := h1938c.2.2.1
                                        have p1938_3 := h1938c.2.2.2
                                        linarith only [h1807, h1921, h1925, hc01, hlam, hphi, ht12, p1938_1, u2elo1]
                                      · have p1938_0 := h1938c.1
                                        have p1938_1 := h1938c.2.1
                                        have p1938_2 := h1938c.2.2.1
                                        have p1938_3 := h1938c.2.2.2
                                        linarith only [hlam, p1938_0]
                          · linarith only [h0, h1629, h1885, h1888, h1925, hc01, hlam, hphi, ht12, u2elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1965 | h1965
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1966 | h1966
                            · linarith only [h1807, h1889, h1922, h1966, hc01, hlam, hphi, ht12, u2elo1]
                            · linarith only [h1924, h1965, h1966, hlam]
                          · linarith only [h1629, h1888, h1965, hlam]
                      · linarith only [h0, h1923, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h1887, h1922, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
                  · linarith only [h0, h1885, h1888, h1921, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1973 | h1973
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1974 | h1974
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1975 | h1975
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1976 | h1976
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1977 | h1977
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1978 | h1978
                          · linarith only [h1629, h1888, h1974, h1978, hc01, hlam, hphi, ht12, u2elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1980 | h1980
                            · linarith only [h1977, h1978, h1980, hlam]
                            · linarith only [h1807, h1886, h1973, h1980, hc01, hlam, hphi, ht12, u2elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1983 | h1983
                          · linarith only [h1629, h1888, h1977, h1983, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1985 | h1985
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1986 | h1986
                              · linarith only [h1629, h1977, h1986, hc01, hlam, hphi, ht12, u2elo2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1988 | h1988
                                · linarith only [h0, h1629, h1886, h1983, h1986, h1988, hc01, hlam, hphi, ht12, u2elo1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1990 | h1990
                                  · linarith only [h0, h1886, h1990, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1992 | h1992
                                    · rcases h1bigk with h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c
                                      · have p1993_0 := h1993c.1
                                        have p1993_1 := h1993c.2.1
                                        have p1993_2 := h1993c.2.2.1
                                        have p1993_3 := h1993c.2.2.2
                                        linarith only [hlam, p1993_0]
                                      · have p1993_0 := h1993c.1
                                        have p1993_1 := h1993c.2.1
                                        have p1993_2 := h1993c.2.2.1
                                        have p1993_3 := h1993c.2.2.2
                                        linarith only [h0, hlam, p1993_0]
                                      · have p1993_0 := h1993c.1
                                        have p1993_1 := h1993c.2.1
                                        have p1993_2 := h1993c.2.2.1
                                        have p1993_3 := h1993c.2.2.2
                                        linarith only [h1629, hlam, p1993_0]
                                      · have p1993_0 := h1993c.1
                                        have p1993_1 := h1993c.2.1
                                        have p1993_2 := h1993c.2.2.1
                                        have p1993_3 := h1993c.2.2.2
                                        linarith only [h1807, hlam, p1993_0]
                                      · have p1993_0 := h1993c.1
                                        have p1993_1 := h1993c.2.1
                                        have p1993_2 := h1993c.2.2.1
                                        have p1993_3 := h1993c.2.2.2
                                        linarith only [h1883, hlam, p1993_0]
                                      · have p1993_0 := h1993c.1
                                        have p1993_1 := h1993c.2.1
                                        have p1993_2 := h1993c.2.2.1
                                        have p1993_3 := h1993c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht12, p1993_1, u2elo1]
                                      · have p1993_0 := h1993c.1
                                        have p1993_1 := h1993c.2.1
                                        have p1993_2 := h1993c.2.2.1
                                        have p1993_3 := h1993c.2.2.2
                                        linarith only [hlam, p1993_0]
                                      · have p1993_0 := h1993c.1
                                        have p1993_1 := h1993c.2.1
                                        have p1993_2 := h1993c.2.2.1
                                        have p1993_3 := h1993c.2.2.2
                                        linarith only [h1629, hc01, hlam, hphi, ht12, p1993_1, u2elo1]
                                      · have p1993_0 := h1993c.1
                                        have p1993_1 := h1993c.2.1
                                        have p1993_2 := h1993c.2.2.1
                                        have p1993_3 := h1993c.2.2.2
                                        linarith only [h1883, h1985, hlam, hphi, ht01, ht0b, ht12, ht5b, p1993_1, u2elo1, u5ehi0]
                                      · have p1993_0 := h1993c.1
                                        have p1993_1 := h1993c.2.1
                                        have p1993_2 := h1993c.2.2.1
                                        have p1993_3 := h1993c.2.2.2
                                        linarith only [h1883, hc01, hlam, hphi, ht12, p1993_1, u2elo1]
                                      · have p1993_0 := h1993c.1
                                        have p1993_1 := h1993c.2.1
                                        have p1993_2 := h1993c.2.2.1
                                        have p1993_3 := h1993c.2.2.2
                                        linarith only [h0, h1886, h1973, h1983, h1986, h1990, h1992, hc01, hc23, hc34, hlam, hphi, ht12, p1993_1, u2elo1]
                                      · have p1993_0 := h1993c.1
                                        have p1993_1 := h1993c.2.1
                                        have p1993_2 := h1993c.2.2.1
                                        have p1993_3 := h1993c.2.2.2
                                        linarith only [h1974, hlam, p1993_0]
                                      · have p1993_0 := h1993c.1
                                        have p1993_1 := h1993c.2.1
                                        have p1993_2 := h1993c.2.2.1
                                        have p1993_3 := h1993c.2.2.2
                                        linarith only [hlam, p1993_0]
                                      · have p1993_0 := h1993c.1
                                        have p1993_1 := h1993c.2.1
                                        have p1993_2 := h1993c.2.2.1
                                        have p1993_3 := h1993c.2.2.2
                                        linarith only [h1977, hlam, p1993_0]
                                      · have p1993_0 := h1993c.1
                                        have p1993_1 := h1993c.2.1
                                        have p1993_2 := h1993c.2.2.1
                                        have p1993_3 := h1993c.2.2.2
                                        linarith only [h1983, hlam, p1993_1]
                                      · have p1993_0 := h1993c.1
                                        have p1993_1 := h1993c.2.1
                                        have p1993_2 := h1993c.2.2.1
                                        have p1993_3 := h1993c.2.2.2
                                        linarith only [h1975, hc01, hlam, hphi, ht12, p1993_1, u2elo1]
                                      · have p1993_0 := h1993c.1
                                        have p1993_1 := h1993c.2.1
                                        have p1993_2 := h1993c.2.2.1
                                        have p1993_3 := h1993c.2.2.2
                                        linarith only [h1975, hlam, p1993_0]
                                      · have p1993_0 := h1993c.1
                                        have p1993_1 := h1993c.2.1
                                        have p1993_2 := h1993c.2.2.1
                                        have p1993_3 := h1993c.2.2.2
                                        linarith only [h1629, h1975, hc01, hlam, hphi, ht12, p1993_1, u2elo1]
                                      · have p1993_0 := h1993c.1
                                        have p1993_1 := h1993c.2.1
                                        have p1993_2 := h1993c.2.2.1
                                        have p1993_3 := h1993c.2.2.2
                                        linarith only [hlam, p1993_0]
                                      · have p1993_0 := h1993c.1
                                        have p1993_1 := h1993c.2.1
                                        have p1993_2 := h1993c.2.2.1
                                        have p1993_3 := h1993c.2.2.2
                                        linarith only [h1629, h1975, h1983, hc01, hlam, hphi, ht12, p1993_1, u2elo1]
                                      · have p1993_0 := h1993c.1
                                        have p1993_1 := h1993c.2.1
                                        have p1993_2 := h1993c.2.2.1
                                        have p1993_3 := h1993c.2.2.2
                                        linarith only [h1976, hc01, hlam, hphi, ht12, p1993_1, u2elo1]
                                      · have p1993_0 := h1993c.1
                                        have p1993_1 := h1993c.2.1
                                        have p1993_2 := h1993c.2.2.1
                                        have p1993_3 := h1993c.2.2.2
                                        linarith only [h1976, hlam, p1993_0]
                                      · have p1993_0 := h1993c.1
                                        have p1993_1 := h1993c.2.1
                                        have p1993_2 := h1993c.2.2.1
                                        have p1993_3 := h1993c.2.2.2
                                        linarith only [h1629, h1976, hc01, hlam, hphi, ht12, p1993_1, u2elo1]
                                      · have p1993_0 := h1993c.1
                                        have p1993_1 := h1993c.2.1
                                        have p1993_2 := h1993c.2.2.1
                                        have p1993_3 := h1993c.2.2.2
                                        linarith only [h1985, hlam, p1993_0]
                                      · have p1993_0 := h1993c.1
                                        have p1993_1 := h1993c.2.1
                                        have p1993_2 := h1993c.2.2.1
                                        have p1993_3 := h1993c.2.2.2
                                        linarith only [hlam, p1993_0]
                                    · linarith only [h0, h1629, h1886, h1973, h1977, h1992, hc01, hlam, hphi, ht12, u2elo1]
                            · linarith only [h0, h1807, h1886, h1973, h1985, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h1886, h1973, h1976, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                    · linarith only [h0, h1886, h1973, h1975, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
                  · linarith only [h0, h1886, h1973, h1974, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2024 | h2024
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2025 | h2025
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2026 | h2026
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h2027 | h2027
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2028 | h2028
                          · linarith only [h1629, h1888, h2024, h2028, hc01, hlam, hphi, ht12, u2elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2030 | h2030
                            · linarith only [h1807, h1973, h2025, h2030, hc01, hlam, hphi, ht12, u2elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2032 | h2032
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2033 | h2033
                                · linarith only [h1629, h2028, h2033, hc01, hlam, hphi, ht12, u2elo2]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2035 | h2035
                                  · linarith only [h1886, h2035, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2037 | h2037
                                    · linarith only [h0, h1807, h1887, h2030, h2032, h2033, h2037, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                    · rcases h1bigk with h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c
                                      · have p2039_0 := h2039c.1
                                        have p2039_1 := h2039c.2.1
                                        have p2039_2 := h2039c.2.2.1
                                        have p2039_3 := h2039c.2.2.2
                                        linarith only [hlam, p2039_0]
                                      · have p2039_0 := h2039c.1
                                        have p2039_1 := h2039c.2.1
                                        have p2039_2 := h2039c.2.2.1
                                        have p2039_3 := h2039c.2.2.2
                                        linarith only [h0, hlam, p2039_0]
                                      · have p2039_0 := h2039c.1
                                        have p2039_1 := h2039c.2.1
                                        have p2039_2 := h2039c.2.2.1
                                        have p2039_3 := h2039c.2.2.2
                                        linarith only [h1629, hlam, p2039_0]
                                      · have p2039_0 := h2039c.1
                                        have p2039_1 := h2039c.2.1
                                        have p2039_2 := h2039c.2.2.1
                                        have p2039_3 := h2039c.2.2.2
                                        linarith only [h1807, hlam, p2039_0]
                                      · have p2039_0 := h2039c.1
                                        have p2039_1 := h2039c.2.1
                                        have p2039_2 := h2039c.2.2.1
                                        have p2039_3 := h2039c.2.2.2
                                        linarith only [h1883, hlam, p2039_0]
                                      · have p2039_0 := h2039c.1
                                        have p2039_1 := h2039c.2.1
                                        have p2039_2 := h2039c.2.2.1
                                        have p2039_3 := h2039c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht12, p2039_1, u2elo1]
                                      · have p2039_0 := h2039c.1
                                        have p2039_1 := h2039c.2.1
                                        have p2039_2 := h2039c.2.2.1
                                        have p2039_3 := h2039c.2.2.2
                                        linarith only [hlam, p2039_0]
                                      · have p2039_0 := h2039c.1
                                        have p2039_1 := h2039c.2.1
                                        have p2039_2 := h2039c.2.2.1
                                        have p2039_3 := h2039c.2.2.2
                                        linarith only [h1807, h2027, hc01, hlam, hphi, ht12, p2039_1, u2elo1]
                                      · have p2039_0 := h2039c.1
                                        have p2039_1 := h2039c.2.1
                                        have p2039_2 := h2039c.2.2.1
                                        have p2039_3 := h2039c.2.2.2
                                        linarith only [h1807, hc01, hlam, hphi, ht12, p2039_1, u2elo1]
                                      · have p2039_0 := h2039c.1
                                        have p2039_1 := h2039c.2.1
                                        have p2039_2 := h2039c.2.2.1
                                        have p2039_3 := h2039c.2.2.2
                                        linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p2039_1, u2elo1, u5ehi1]
                                      · have p2039_0 := h2039c.1
                                        have p2039_1 := h2039c.2.1
                                        have p2039_2 := h2039c.2.2.1
                                        have p2039_3 := h2039c.2.2.2
                                        linarith only [h2028, hc01, hc35, hlam, hphi, ht12, ht23, p2039_1]
                                      · have p2039_0 := h2039c.1
                                        have p2039_1 := h2039c.2.1
                                        have p2039_2 := h2039c.2.2.1
                                        have p2039_3 := h2039c.2.2.2
                                        linarith only [h2024, hlam, p2039_0]
                                      · have p2039_0 := h2039c.1
                                        have p2039_1 := h2039c.2.1
                                        have p2039_2 := h2039c.2.2.1
                                        have p2039_3 := h2039c.2.2.2
                                        linarith only [hlam, p2039_0]
                                      · have p2039_0 := h2039c.1
                                        have p2039_1 := h2039c.2.1
                                        have p2039_2 := h2039c.2.2.1
                                        have p2039_3 := h2039c.2.2.2
                                        linarith only [h0, h1807, h1887, h2028, h2032, h2033, h2037, hc01, hc34, hc45, hlam, hphi, ht12, p2039_1, u2elo1]
                                      · have p2039_0 := h2039c.1
                                        have p2039_1 := h2039c.2.1
                                        have p2039_2 := h2039c.2.2.1
                                        have p2039_3 := h2039c.2.2.2
                                        linarith only [h2028, hlam, p2039_1]
                                      · have p2039_0 := h2039c.1
                                        have p2039_1 := h2039c.2.1
                                        have p2039_2 := h2039c.2.2.1
                                        have p2039_3 := h2039c.2.2.2
                                        linarith only [h2025, hc01, hlam, hphi, ht12, p2039_1, u2elo1]
                                      · have p2039_0 := h2039c.1
                                        have p2039_1 := h2039c.2.1
                                        have p2039_2 := h2039c.2.2.1
                                        have p2039_3 := h2039c.2.2.2
                                        linarith only [h2025, hlam, p2039_0]
                                      · have p2039_0 := h2039c.1
                                        have p2039_1 := h2039c.2.1
                                        have p2039_2 := h2039c.2.2.1
                                        have p2039_3 := h2039c.2.2.2
                                        linarith only [h2027, hlam, p2039_1]
                                      · have p2039_0 := h2039c.1
                                        have p2039_1 := h2039c.2.1
                                        have p2039_2 := h2039c.2.2.1
                                        have p2039_3 := h2039c.2.2.2
                                        linarith only [hlam, p2039_0]
                                      · have p2039_0 := h2039c.1
                                        have p2039_1 := h2039c.2.1
                                        have p2039_2 := h2039c.2.2.1
                                        have p2039_3 := h2039c.2.2.2
                                        linarith only [h2030, hlam, p2039_1]
                                      · have p2039_0 := h2039c.1
                                        have p2039_1 := h2039c.2.1
                                        have p2039_2 := h2039c.2.2.1
                                        have p2039_3 := h2039c.2.2.2
                                        linarith only [h2026, hc01, hlam, hphi, ht12, p2039_1, u2elo1]
                                      · have p2039_0 := h2039c.1
                                        have p2039_1 := h2039c.2.1
                                        have p2039_2 := h2039c.2.2.1
                                        have p2039_3 := h2039c.2.2.2
                                        linarith only [h2026, hlam, p2039_0]
                                      · have p2039_0 := h2039c.1
                                        have p2039_1 := h2039c.2.1
                                        have p2039_2 := h2039c.2.2.1
                                        have p2039_3 := h2039c.2.2.2
                                        linarith only [h1629, h2026, hc01, hlam, hphi, ht12, p2039_1, u2elo1]
                                      · have p2039_0 := h2039c.1
                                        have p2039_1 := h2039c.2.1
                                        have p2039_2 := h2039c.2.2.1
                                        have p2039_3 := h2039c.2.2.2
                                        linarith only [h1807, h2026, hc01, hlam, hphi, ht12, p2039_1, u2elo1]
                                      · have p2039_0 := h2039c.1
                                        have p2039_1 := h2039c.2.1
                                        have p2039_2 := h2039c.2.2.1
                                        have p2039_3 := h2039c.2.2.2
                                        linarith only [hlam, p2039_0]
                              · linarith only [h2027, h2028, h2032, hc23, hc35, hlam, hphi]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h2066 | h2066
                          · linarith only [h1629, h1888, h2027, h2066, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h2068 | h2068
                            · linarith only [h1807, h1973, h2025, h2068, hc01, hlam, hphi, ht12, u2elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h2070 | h2070
                              · linarith only [h1629, h2027, h2070, hc01, hlam, hphi, ht12, u2elo2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h2072 | h2072
                                · linarith only [h1629, h2066, h2072, hc01, hlam, hphi, ht12, u2elo2]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h2074 | h2074
                                  · linarith only [h0, h1807, h1886, h2068, h2074, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2076 | h2076
                                    · linarith only [h1629, h2027, h2068, h2076, hc01, hc34, hlam, hphi, ht12, ht23]
                                    · linarith only [h1629, h2027, h2076, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h1887, h2026, hlam]
                    · linarith only [h0, h1887, h2025, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
                  · linarith only [h0, h1887, h2024, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2082 | h2082
              · linarith only [h1885, h1887, h2082, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2084 | h2084
                · linarith only [h1886, h1887, h2084, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2086 | h2086
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2087 | h2087
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2088 | h2088
                      · linarith only [h1887, h2088, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h2088, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h1629, h2086, h2087, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1885, h1887, h2086, hc01, hlam, hphi, ht12, u2elo4]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2093 | h2093
            · linarith only [h1886, h2093, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2095 | h2095
              · linarith only [h1885, h1886, h2095, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2097 | h2097
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2098 | h2098
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2099 | h2099
                    · linarith only [h1886, h2099, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h2099, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h2098, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2103 | h2103
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2104 | h2104
                    · linarith only [h1886, h2104, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h2104, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h2103, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h2108 | h2108
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2109 | h2109
            · linarith only [h1885, h2109, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2111 | h2111
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2112 | h2112
                · linarith only [h1885, h2108, h2112, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2114 | h2114
                  · linarith only [h1885, h2114, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h2114, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2117 | h2117
                · linarith only [h2108, h2109, h2117, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2119 | h2119
                  · linarith only [h1885, h2119, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h2119, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h2122 | h2122
            · linarith only [h2108, h2122, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2124 | h2124
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2125 | h2125
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2126 | h2126
                  · linarith only [h1885, h2126, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h2126, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2129 | h2129
                  · linarith only [h0, h1885, h2129, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h2129, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2132 | h2132
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2133 | h2133
                  · linarith only [h0, h1885, h2133, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h2133, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2136 | h2136
                  · linarith only [h0, h1885, h2136, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h2136, hc01, hlam, hphi, ht12, u2elo2]

set_option maxHeartbeats 4278000 in
set_option maxHeartbeats 4278000 in
theorem r1l7_11_12_25_L_I_L_0_M_IR (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emin := hb1.2.1
  have h2elo := hb2.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_12_25_L_I_L_0_M_IR_x0 m hb1 hb2 hb5 h0
  · exact r1l7_11_12_25_L_I_L_0_M_IR_x1 m hb1 hb2 hb5 h0

end R2N4
