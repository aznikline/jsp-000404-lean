import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6082000 in
set_option maxHeartbeats 6082000 in
theorem r1l7_20_12_H_I_L_0_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1647 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  rcases m.htr 0 1 4 (by decide) (by decide) with h1648 | h1648
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1649 | h1649
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1650 | h1650
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1651 | h1651
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1652 | h1652
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1653 | h1653
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1654 | h1654
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1655 | h1655
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1656 | h1656
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1657 | h1657
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1658 | h1658
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1659 | h1659
                        · linarith only [h0, h1647, h1659, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · linarith only [h0, h1647, h1654, h1656, h1659, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h1658, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h1657, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1656, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1665 | h1665
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1666 | h1666
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1667 | h1667
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1668 | h1668
                        · linarith only [h0, h1647, h1668, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · linarith only [h0, h1647, h1654, h1665, h1668, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h1667, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h1666, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1665, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1674 | h1674
                · linarith only [h1653, h1654, h1674, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1676 | h1676
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1677 | h1677
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1678 | h1678
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1679 | h1679
                        · linarith only [h1647, h1653, h1654, h1679, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1681 | h1681
                          · linarith only [h0, h1649, h1676, h1679, h1681, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · linarith only [h1653, h1654, h1681, hc23, hc35, hlam, hphi]
                      · linarith only [h0, h1678, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h1677, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1649, h1653, h1654, h1676, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1687 | h1687
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1688 | h1688
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1689 | h1689
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1690 | h1690
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1691 | h1691
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1692 | h1692
                        · linarith only [h0, h1647, h1692, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · linarith only [h0, h1648, h1653, h1687, h1689, h1692, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h1691, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h1690, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1689, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h1653, h1687, h1688, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1699 | h1699
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1700 | h1700
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1701 | h1701
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1702 | h1702
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1703 | h1703
                        · linarith only [h0, h1647, h1687, h1703, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1705 | h1705
                          · linarith only [h0, h1647, h1653, h1700, h1705, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1707 | h1707
                            · linarith only [h0, h1648, h1701, h1707, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · linarith only [h0, h1648, h1699, h1707, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h0, h1702, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h1701, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1647, h1700, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1713 | h1713
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1714 | h1714
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1715 | h1715
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1716 | h1716
                        · linarith only [h1647, h1687, h1716, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1718 | h1718
                          · linarith only [h1647, h1653, h1713, h1718, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1720 | h1720
                            · linarith only [h0, h1648, h1699, h1714, h1720, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1722 | h1722
                              · rcases h0bigk with h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c | h1723c
                                · have p1723_0 := h1723c.1
                                  have p1723_1 := h1723c.2.1
                                  have p1723_2 := h1723c.2.2.1
                                  have p1723_3 := h1723c.2.2.2
                                  linarith only [hlam, p1723_0]
                                · have p1723_0 := h1723c.1
                                  have p1723_1 := h1723c.2.1
                                  have p1723_2 := h1723c.2.2.1
                                  have p1723_3 := h1723c.2.2.2
                                  linarith only [h0, hlam, p1723_0]
                                · have p1723_0 := h1723c.1
                                  have p1723_1 := h1723c.2.1
                                  have p1723_2 := h1723c.2.2.1
                                  have p1723_3 := h1723c.2.2.2
                                  linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1723_1, u2elo1]
                                · have p1723_0 := h1723c.1
                                  have p1723_1 := h1723c.2.1
                                  have p1723_2 := h1723c.2.2.1
                                  have p1723_3 := h1723c.2.2.2
                                  linarith only [h0, h1647, h1653, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1723_1, u2elo1]
                                · have p1723_0 := h1723c.1
                                  have p1723_1 := h1723c.2.1
                                  have p1723_2 := h1723c.2.2.1
                                  have p1723_3 := h1723c.2.2.2
                                  linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1723_1, u2elo1]
                                · have p1723_0 := h1723c.1
                                  have p1723_1 := h1723c.2.1
                                  have p1723_2 := h1723c.2.2.1
                                  have p1723_3 := h1723c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht12, p1723_1, u2elo1]
                                · have p1723_0 := h1723c.1
                                  have p1723_1 := h1723c.2.1
                                  have p1723_2 := h1723c.2.2.1
                                  have p1723_3 := h1723c.2.2.2
                                  linarith only [hlam, p1723_0]
                                · have p1723_0 := h1723c.1
                                  have p1723_1 := h1723c.2.1
                                  have p1723_2 := h1723c.2.2.1
                                  have p1723_3 := h1723c.2.2.2
                                  linarith only [h0, h1647, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1723_1, u2elo1]
                                · have p1723_0 := h1723c.1
                                  have p1723_1 := h1723c.2.1
                                  have p1723_2 := h1723c.2.2.1
                                  have p1723_3 := h1723c.2.2.2
                                  linarith only [h0, h1648, h1714, h1718, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1723_1, u2elo1]
                                · have p1723_0 := h1723c.1
                                  have p1723_1 := h1723c.2.1
                                  have p1723_2 := h1723c.2.2.1
                                  have p1723_3 := h1723c.2.2.2
                                  linarith only [h0, h1649, h1715, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1723_1, u2elo1]
                                · have p1723_0 := h1723c.1
                                  have p1723_1 := h1723c.2.1
                                  have p1723_2 := h1723c.2.2.1
                                  have p1723_3 := h1723c.2.2.2
                                  linarith only [h1647, hlam, p1723_1]
                                · have p1723_0 := h1723c.1
                                  have p1723_1 := h1723c.2.1
                                  have p1723_2 := h1723c.2.2.1
                                  have p1723_3 := h1723c.2.2.2
                                  linarith only [h1650, hlam, p1723_0]
                                · have p1723_0 := h1723c.1
                                  have p1723_1 := h1723c.2.1
                                  have p1723_2 := h1723c.2.2.1
                                  have p1723_3 := h1723c.2.2.2
                                  linarith only [hlam, p1723_0]
                                · have p1723_0 := h1723c.1
                                  have p1723_1 := h1723c.2.1
                                  have p1723_2 := h1723c.2.2.1
                                  have p1723_3 := h1723c.2.2.2
                                  linarith only [h1653, hlam, p1723_0]
                                · have p1723_0 := h1723c.1
                                  have p1723_1 := h1723c.2.1
                                  have p1723_2 := h1723c.2.2.1
                                  have p1723_3 := h1723c.2.2.2
                                  linarith only [h1687, hlam, p1723_1]
                                · have p1723_0 := h1723c.1
                                  have p1723_1 := h1723c.2.1
                                  have p1723_2 := h1723c.2.2.1
                                  have p1723_3 := h1723c.2.2.2
                                  linarith only [h1648, hlam, p1723_1]
                                · have p1723_0 := h1723c.1
                                  have p1723_1 := h1723c.2.1
                                  have p1723_2 := h1723c.2.2.1
                                  have p1723_3 := h1723c.2.2.2
                                  linarith only [h1651, hlam, p1723_0]
                                · have p1723_0 := h1723c.1
                                  have p1723_1 := h1723c.2.1
                                  have p1723_2 := h1723c.2.2.1
                                  have p1723_3 := h1723c.2.2.2
                                  linarith only [h1647, h1699, h1722, hc13, hc34, hlam, hphi, p1723_1]
                                · have p1723_0 := h1723c.1
                                  have p1723_1 := h1723c.2.1
                                  have p1723_2 := h1723c.2.2.1
                                  have p1723_3 := h1723c.2.2.2
                                  linarith only [hlam, p1723_0]
                                · have p1723_0 := h1723c.1
                                  have p1723_1 := h1723c.2.1
                                  have p1723_2 := h1723c.2.2.1
                                  have p1723_3 := h1723c.2.2.2
                                  linarith only [h1699, hlam, p1723_1]
                                · have p1723_0 := h1723c.1
                                  have p1723_1 := h1723c.2.1
                                  have p1723_2 := h1723c.2.2.1
                                  have p1723_3 := h1723c.2.2.2
                                  linarith only [h1649, hlam, p1723_1]
                                · have p1723_0 := h1723c.1
                                  have p1723_1 := h1723c.2.1
                                  have p1723_2 := h1723c.2.2.1
                                  have p1723_3 := h1723c.2.2.2
                                  linarith only [h1652, hlam, p1723_0]
                                · have p1723_0 := h1723c.1
                                  have p1723_1 := h1723c.2.1
                                  have p1723_2 := h1723c.2.2.1
                                  have p1723_3 := h1723c.2.2.2
                                  linarith only [h0, h1647, h1649, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1723_1, u2elo1]
                                · have p1723_0 := h1723c.1
                                  have p1723_1 := h1723c.2.1
                                  have p1723_2 := h1723c.2.2.1
                                  have p1723_3 := h1723c.2.2.2
                                  linarith only [h0, h1649, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1723_1, u2elo1]
                                · have p1723_0 := h1723c.1
                                  have p1723_1 := h1723c.2.1
                                  have p1723_2 := h1723c.2.2.1
                                  have p1723_3 := h1723c.2.2.2
                                  linarith only [hlam, p1723_0]
                              · rcases h0bigk with h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c
                                · have p1749_0 := h1749c.1
                                  have p1749_1 := h1749c.2.1
                                  have p1749_2 := h1749c.2.2.1
                                  have p1749_3 := h1749c.2.2.2
                                  linarith only [hlam, p1749_0]
                                · have p1749_0 := h1749c.1
                                  have p1749_1 := h1749c.2.1
                                  have p1749_2 := h1749c.2.2.1
                                  have p1749_3 := h1749c.2.2.2
                                  linarith only [h0, hlam, p1749_0]
                                · have p1749_0 := h1749c.1
                                  have p1749_1 := h1749c.2.1
                                  have p1749_2 := h1749c.2.2.1
                                  have p1749_3 := h1749c.2.2.2
                                  linarith only [h0, h1647, h1713, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1749_1, u2elo1]
                                · have p1749_0 := h1749c.1
                                  have p1749_1 := h1749c.2.1
                                  have p1749_2 := h1749c.2.2.1
                                  have p1749_3 := h1749c.2.2.2
                                  linarith only [h0, h1648, h1714, h1718, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1749_1, u2elo1]
                                · have p1749_0 := h1749c.1
                                  have p1749_1 := h1749c.2.1
                                  have p1749_2 := h1749c.2.2.1
                                  have p1749_3 := h1749c.2.2.2
                                  linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1749_1, u2elo1]
                                · have p1749_0 := h1749c.1
                                  have p1749_1 := h1749c.2.1
                                  have p1749_2 := h1749c.2.2.1
                                  have p1749_3 := h1749c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht12, p1749_1, u2elo1]
                                · have p1749_0 := h1749c.1
                                  have p1749_1 := h1749c.2.1
                                  have p1749_2 := h1749c.2.2.1
                                  have p1749_3 := h1749c.2.2.2
                                  linarith only [hlam, p1749_0]
                                · have p1749_0 := h1749c.1
                                  have p1749_1 := h1749c.2.1
                                  have p1749_2 := h1749c.2.2.1
                                  have p1749_3 := h1749c.2.2.2
                                  linarith only [h0, h1647, h1713, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1749_1, u2elo1]
                                · have p1749_0 := h1749c.1
                                  have p1749_1 := h1749c.2.1
                                  have p1749_2 := h1749c.2.2.1
                                  have p1749_3 := h1749c.2.2.2
                                  linarith only [h0, h1648, h1714, h1718, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1749_1, u2elo1]
                                · have p1749_0 := h1749c.1
                                  have p1749_1 := h1749c.2.1
                                  have p1749_2 := h1749c.2.2.1
                                  have p1749_3 := h1749c.2.2.2
                                  linarith only [h0, h1649, h1715, h1718, h1720, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1749_1, u2elo1]
                                · have p1749_0 := h1749c.1
                                  have p1749_1 := h1749c.2.1
                                  have p1749_2 := h1749c.2.2.1
                                  have p1749_3 := h1749c.2.2.2
                                  linarith only [h1647, hlam, p1749_1]
                                · have p1749_0 := h1749c.1
                                  have p1749_1 := h1749c.2.1
                                  have p1749_2 := h1749c.2.2.1
                                  have p1749_3 := h1749c.2.2.2
                                  linarith only [h1650, hlam, p1749_0]
                                · have p1749_0 := h1749c.1
                                  have p1749_1 := h1749c.2.1
                                  have p1749_2 := h1749c.2.2.1
                                  have p1749_3 := h1749c.2.2.2
                                  linarith only [hlam, p1749_0]
                                · have p1749_0 := h1749c.1
                                  have p1749_1 := h1749c.2.1
                                  have p1749_2 := h1749c.2.2.1
                                  have p1749_3 := h1749c.2.2.2
                                  linarith only [h1653, hlam, p1749_0]
                                · have p1749_0 := h1749c.1
                                  have p1749_1 := h1749c.2.1
                                  have p1749_2 := h1749c.2.2.1
                                  have p1749_3 := h1749c.2.2.2
                                  linarith only [h1687, hlam, p1749_1]
                                · have p1749_0 := h1749c.1
                                  have p1749_1 := h1749c.2.1
                                  have p1749_2 := h1749c.2.2.1
                                  have p1749_3 := h1749c.2.2.2
                                  linarith only [h1648, hlam, p1749_1]
                                · have p1749_0 := h1749c.1
                                  have p1749_1 := h1749c.2.1
                                  have p1749_2 := h1749c.2.2.1
                                  have p1749_3 := h1749c.2.2.2
                                  linarith only [h1651, hlam, p1749_0]
                                · have p1749_0 := h1749c.1
                                  have p1749_1 := h1749c.2.1
                                  have p1749_2 := h1749c.2.2.1
                                  have p1749_3 := h1749c.2.2.2
                                  linarith only [h0, h1647, h1648, h1713, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1749_1, u2elo1]
                                · have p1749_0 := h1749c.1
                                  have p1749_1 := h1749c.2.1
                                  have p1749_2 := h1749c.2.2.1
                                  have p1749_3 := h1749c.2.2.2
                                  linarith only [hlam, p1749_0]
                                · have p1749_0 := h1749c.1
                                  have p1749_1 := h1749c.2.1
                                  have p1749_2 := h1749c.2.2.1
                                  have p1749_3 := h1749c.2.2.2
                                  linarith only [h1699, hlam, p1749_1]
                                · have p1749_0 := h1749c.1
                                  have p1749_1 := h1749c.2.1
                                  have p1749_2 := h1749c.2.2.1
                                  have p1749_3 := h1749c.2.2.2
                                  linarith only [h1649, hlam, p1749_1]
                                · have p1749_0 := h1749c.1
                                  have p1749_1 := h1749c.2.1
                                  have p1749_2 := h1749c.2.2.1
                                  have p1749_3 := h1749c.2.2.2
                                  linarith only [h1652, hlam, p1749_0]
                                · have p1749_0 := h1749c.1
                                  have p1749_1 := h1749c.2.1
                                  have p1749_2 := h1749c.2.2.1
                                  have p1749_3 := h1749c.2.2.2
                                  linarith only [h0, h1647, h1649, h1713, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1749_1, u2elo1]
                                · have p1749_0 := h1749c.1
                                  have p1749_1 := h1749c.2.1
                                  have p1749_2 := h1749c.2.2.1
                                  have p1749_3 := h1749c.2.2.2
                                  linarith only [h0, h1649, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1749_1, u2elo1]
                                · have p1749_0 := h1749c.1
                                  have p1749_1 := h1749c.2.1
                                  have p1749_2 := h1749c.2.2.1
                                  have p1749_3 := h1749c.2.2.2
                                  linarith only [hlam, p1749_0]
                      · linarith only [h0, h1715, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h1647, h1713, h1714, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1647, h1713, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
          · linarith only [h0, h1649, h1652, hlam]
        · linarith only [h0, h1648, h1651, hlam]
      · linarith only [h0, h1647, h1650, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1781 | h1781
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1782 | h1782
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1783 | h1783
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1784 | h1784
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1785 | h1785
              · linarith only [h1647, h1649, h1785, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1787 | h1787
                · linarith only [h1647, h1649, h1784, h1787, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1789 | h1789
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1790 | h1790
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1791 | h1791
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1792 | h1792
                        · linarith only [h1647, h1649, h1785, h1791, h1792, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1794 | h1794
                          · linarith only [h1647, h1649, h1789, h1791, h1794, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · linarith only [h1647, h1649, h1784, h1791, h1794, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h1783, h1791, hlam]
                    · linarith only [h0, h1647, h1790, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1647, h1789, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1800 | h1800
              · linarith only [h1648, h1649, h1784, h1800, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1802 | h1802
                · linarith only [h1648, h1649, h1802, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1804 | h1804
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1805 | h1805
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1806 | h1806
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1807 | h1807
                        · linarith only [h1647, h1649, h1800, h1807, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1809 | h1809
                          · linarith only [h1647, h1649, h1784, h1804, h1806, h1809, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1811 | h1811
                            · linarith only [h1648, h1649, h1805, h1806, h1811, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1813 | h1813
                              · rcases h0bigk with h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c
                                · have p1814_0 := h1814c.1
                                  have p1814_1 := h1814c.2.1
                                  have p1814_2 := h1814c.2.2.1
                                  have p1814_3 := h1814c.2.2.2
                                  linarith only [hlam, p1814_0]
                                · have p1814_0 := h1814c.1
                                  have p1814_1 := h1814c.2.1
                                  have p1814_2 := h1814c.2.2.1
                                  have p1814_3 := h1814c.2.2.2
                                  linarith only [h0, hlam, p1814_0]
                                · have p1814_0 := h1814c.1
                                  have p1814_1 := h1814c.2.1
                                  have p1814_2 := h1814c.2.2.1
                                  have p1814_3 := h1814c.2.2.2
                                  linarith only [h1649, h1806, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1814_1, u2elo1]
                                · have p1814_0 := h1814c.1
                                  have p1814_1 := h1814c.2.1
                                  have p1814_2 := h1814c.2.2.1
                                  have p1814_3 := h1814c.2.2.2
                                  linarith only [h1647, h1649, h1784, h1806, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1814_1, u2elo1]
                                · have p1814_0 := h1814c.1
                                  have p1814_1 := h1814c.2.1
                                  have p1814_2 := h1814c.2.2.1
                                  have p1814_3 := h1814c.2.2.2
                                  linarith only [h1649, hlam, p1814_0]
                                · have p1814_0 := h1814c.1
                                  have p1814_1 := h1814c.2.1
                                  have p1814_2 := h1814c.2.2.1
                                  have p1814_3 := h1814c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht12, p1814_1, u2elo1]
                                · have p1814_0 := h1814c.1
                                  have p1814_1 := h1814c.2.1
                                  have p1814_2 := h1814c.2.2.1
                                  have p1814_3 := h1814c.2.2.2
                                  linarith only [hlam, p1814_0]
                                · have p1814_0 := h1814c.1
                                  have p1814_1 := h1814c.2.1
                                  have p1814_2 := h1814c.2.2.1
                                  have p1814_3 := h1814c.2.2.2
                                  linarith only [h0, h1647, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1814_1, u2elo1]
                                · have p1814_0 := h1814c.1
                                  have p1814_1 := h1814c.2.1
                                  have p1814_2 := h1814c.2.2.1
                                  have p1814_3 := h1814c.2.2.2
                                  linarith only [h0, h1648, h1805, h1809, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1814_1, u2elo1]
                                · have p1814_0 := h1814c.1
                                  have p1814_1 := h1814c.2.1
                                  have p1814_2 := h1814c.2.2.1
                                  have p1814_3 := h1814c.2.2.2
                                  linarith only [h0, h1648, h1649, h1805, h1809, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1814_1, u2elo1]
                                · have p1814_0 := h1814c.1
                                  have p1814_1 := h1814c.2.1
                                  have p1814_2 := h1814c.2.2.1
                                  have p1814_3 := h1814c.2.2.2
                                  linarith only [h1647, hlam, p1814_1]
                                · have p1814_0 := h1814c.1
                                  have p1814_1 := h1814c.2.1
                                  have p1814_2 := h1814c.2.2.1
                                  have p1814_3 := h1814c.2.2.2
                                  linarith only [h1781, hlam, p1814_0]
                                · have p1814_0 := h1814c.1
                                  have p1814_1 := h1814c.2.1
                                  have p1814_2 := h1814c.2.2.1
                                  have p1814_3 := h1814c.2.2.2
                                  linarith only [hlam, p1814_0]
                                · have p1814_0 := h1814c.1
                                  have p1814_1 := h1814c.2.1
                                  have p1814_2 := h1814c.2.2.1
                                  have p1814_3 := h1814c.2.2.2
                                  linarith only [h1784, hlam, p1814_0]
                                · have p1814_0 := h1814c.1
                                  have p1814_1 := h1814c.2.1
                                  have p1814_2 := h1814c.2.2.1
                                  have p1814_3 := h1814c.2.2.2
                                  linarith only [h1800, hlam, p1814_1]
                                · have p1814_0 := h1814c.1
                                  have p1814_1 := h1814c.2.1
                                  have p1814_2 := h1814c.2.2.1
                                  have p1814_3 := h1814c.2.2.2
                                  linarith only [h1648, hlam, p1814_1]
                                · have p1814_0 := h1814c.1
                                  have p1814_1 := h1814c.2.1
                                  have p1814_2 := h1814c.2.2.1
                                  have p1814_3 := h1814c.2.2.2
                                  linarith only [h1782, hlam, p1814_0]
                                · have p1814_0 := h1814c.1
                                  have p1814_1 := h1814c.2.1
                                  have p1814_2 := h1814c.2.2.1
                                  have p1814_3 := h1814c.2.2.2
                                  linarith only [h1647, h1802, h1813, hc13, hc34, hlam, hphi, p1814_1]
                                · have p1814_0 := h1814c.1
                                  have p1814_1 := h1814c.2.1
                                  have p1814_2 := h1814c.2.2.1
                                  have p1814_3 := h1814c.2.2.2
                                  linarith only [hlam, p1814_0]
                                · have p1814_0 := h1814c.1
                                  have p1814_1 := h1814c.2.1
                                  have p1814_2 := h1814c.2.2.1
                                  have p1814_3 := h1814c.2.2.2
                                  linarith only [h1802, hlam, p1814_1]
                                · have p1814_0 := h1814c.1
                                  have p1814_1 := h1814c.2.1
                                  have p1814_2 := h1814c.2.2.1
                                  have p1814_3 := h1814c.2.2.2
                                  linarith only [h1648, h1805, h1809, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1814_1]
                                · have p1814_0 := h1814c.1
                                  have p1814_1 := h1814c.2.1
                                  have p1814_2 := h1814c.2.2.1
                                  have p1814_3 := h1814c.2.2.2
                                  linarith only [h1783, hlam, p1814_0]
                                · have p1814_0 := h1814c.1
                                  have p1814_1 := h1814c.2.1
                                  have p1814_2 := h1814c.2.2.1
                                  have p1814_3 := h1814c.2.2.2
                                  linarith only [h1647, h1649, h1806, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1814_1, u2elo1]
                                · have p1814_0 := h1814c.1
                                  have p1814_1 := h1814c.2.1
                                  have p1814_2 := h1814c.2.2.1
                                  have p1814_3 := h1814c.2.2.2
                                  linarith only [h1802, h1813, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1814_1]
                                · have p1814_0 := h1814c.1
                                  have p1814_1 := h1814c.2.1
                                  have p1814_2 := h1814c.2.2.1
                                  have p1814_3 := h1814c.2.2.2
                                  linarith only [hlam, p1814_0]
                              · rcases h0bigk with h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c | h1840c
                                · have p1840_0 := h1840c.1
                                  have p1840_1 := h1840c.2.1
                                  have p1840_2 := h1840c.2.2.1
                                  have p1840_3 := h1840c.2.2.2
                                  linarith only [hlam, p1840_0]
                                · have p1840_0 := h1840c.1
                                  have p1840_1 := h1840c.2.1
                                  have p1840_2 := h1840c.2.2.1
                                  have p1840_3 := h1840c.2.2.2
                                  linarith only [h0, hlam, p1840_0]
                                · have p1840_0 := h1840c.1
                                  have p1840_1 := h1840c.2.1
                                  have p1840_2 := h1840c.2.2.1
                                  have p1840_3 := h1840c.2.2.2
                                  linarith only [h1647, h1649, h1804, h1806, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1840_1, u2elo1]
                                · have p1840_0 := h1840c.1
                                  have p1840_1 := h1840c.2.1
                                  have p1840_2 := h1840c.2.2.1
                                  have p1840_3 := h1840c.2.2.2
                                  linarith only [h1649, h1806, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1840_1, u2elo1]
                                · have p1840_0 := h1840c.1
                                  have p1840_1 := h1840c.2.1
                                  have p1840_2 := h1840c.2.2.1
                                  have p1840_3 := h1840c.2.2.2
                                  linarith only [h1649, hlam, p1840_0]
                                · have p1840_0 := h1840c.1
                                  have p1840_1 := h1840c.2.1
                                  have p1840_2 := h1840c.2.2.1
                                  have p1840_3 := h1840c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht12, p1840_1, u2elo1]
                                · have p1840_0 := h1840c.1
                                  have p1840_1 := h1840c.2.1
                                  have p1840_2 := h1840c.2.2.1
                                  have p1840_3 := h1840c.2.2.2
                                  linarith only [hlam, p1840_0]
                                · have p1840_0 := h1840c.1
                                  have p1840_1 := h1840c.2.1
                                  have p1840_2 := h1840c.2.2.1
                                  have p1840_3 := h1840c.2.2.2
                                  linarith only [h0, h1647, h1804, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1840_1, u2elo1]
                                · have p1840_0 := h1840c.1
                                  have p1840_1 := h1840c.2.1
                                  have p1840_2 := h1840c.2.2.1
                                  have p1840_3 := h1840c.2.2.2
                                  linarith only [h0, h1648, h1805, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1840_1, u2elo1]
                                · have p1840_0 := h1840c.1
                                  have p1840_1 := h1840c.2.1
                                  have p1840_2 := h1840c.2.2.1
                                  have p1840_3 := h1840c.2.2.2
                                  linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1840_1, u2elo1]
                                · have p1840_0 := h1840c.1
                                  have p1840_1 := h1840c.2.1
                                  have p1840_2 := h1840c.2.2.1
                                  have p1840_3 := h1840c.2.2.2
                                  linarith only [h1647, hlam, p1840_1]
                                · have p1840_0 := h1840c.1
                                  have p1840_1 := h1840c.2.1
                                  have p1840_2 := h1840c.2.2.1
                                  have p1840_3 := h1840c.2.2.2
                                  linarith only [h1781, hlam, p1840_0]
                                · have p1840_0 := h1840c.1
                                  have p1840_1 := h1840c.2.1
                                  have p1840_2 := h1840c.2.2.1
                                  have p1840_3 := h1840c.2.2.2
                                  linarith only [hlam, p1840_0]
                                · have p1840_0 := h1840c.1
                                  have p1840_1 := h1840c.2.1
                                  have p1840_2 := h1840c.2.2.1
                                  have p1840_3 := h1840c.2.2.2
                                  linarith only [h1784, hlam, p1840_0]
                                · have p1840_0 := h1840c.1
                                  have p1840_1 := h1840c.2.1
                                  have p1840_2 := h1840c.2.2.1
                                  have p1840_3 := h1840c.2.2.2
                                  linarith only [h1800, hlam, p1840_1]
                                · have p1840_0 := h1840c.1
                                  have p1840_1 := h1840c.2.1
                                  have p1840_2 := h1840c.2.2.1
                                  have p1840_3 := h1840c.2.2.2
                                  linarith only [h1648, hlam, p1840_1]
                                · have p1840_0 := h1840c.1
                                  have p1840_1 := h1840c.2.1
                                  have p1840_2 := h1840c.2.2.1
                                  have p1840_3 := h1840c.2.2.2
                                  linarith only [h1782, hlam, p1840_0]
                                · have p1840_0 := h1840c.1
                                  have p1840_1 := h1840c.2.1
                                  have p1840_2 := h1840c.2.2.1
                                  have p1840_3 := h1840c.2.2.2
                                  linarith only [h0, h1647, h1648, h1804, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1840_1, u2elo1]
                                · have p1840_0 := h1840c.1
                                  have p1840_1 := h1840c.2.1
                                  have p1840_2 := h1840c.2.2.1
                                  have p1840_3 := h1840c.2.2.2
                                  linarith only [hlam, p1840_0]
                                · have p1840_0 := h1840c.1
                                  have p1840_1 := h1840c.2.1
                                  have p1840_2 := h1840c.2.2.1
                                  have p1840_3 := h1840c.2.2.2
                                  linarith only [h1802, hlam, p1840_1]
                                · have p1840_0 := h1840c.1
                                  have p1840_1 := h1840c.2.1
                                  have p1840_2 := h1840c.2.2.1
                                  have p1840_3 := h1840c.2.2.2
                                  linarith only [h1647, h1804, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1840_1]
                                · have p1840_0 := h1840c.1
                                  have p1840_1 := h1840c.2.1
                                  have p1840_2 := h1840c.2.2.1
                                  have p1840_3 := h1840c.2.2.2
                                  linarith only [h1783, hlam, p1840_0]
                                · have p1840_0 := h1840c.1
                                  have p1840_1 := h1840c.2.1
                                  have p1840_2 := h1840c.2.2.1
                                  have p1840_3 := h1840c.2.2.2
                                  linarith only [h1647, h1649, h1804, h1806, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1840_1, u2elo1]
                                · have p1840_0 := h1840c.1
                                  have p1840_1 := h1840c.2.1
                                  have p1840_2 := h1840c.2.2.1
                                  have p1840_3 := h1840c.2.2.2
                                  linarith only [h1649, h1806, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1840_1, u2elo1]
                                · have p1840_0 := h1840c.1
                                  have p1840_1 := h1840c.2.1
                                  have p1840_2 := h1840c.2.2.1
                                  have p1840_3 := h1840c.2.2.2
                                  linarith only [hlam, p1840_0]
                      · linarith only [h0, h1783, h1806, hlam]
                    · linarith only [h0, h1647, h1804, h1805, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1647, h1804, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1869 | h1869
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1870 | h1870
              · linarith only [h1647, h1649, h1870, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1872 | h1872
                · linarith only [h0, h1647, h1783, h1869, h1872, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1874 | h1874
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1875 | h1875
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1876 | h1876
                      · linarith only [h0, h1783, h1876, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h1647, h1874, h1876, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · linarith only [h0, h1647, h1874, h1875, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1874, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1881 | h1881
              · linarith only [h0, h1648, h1783, h1869, h1881, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1883 | h1883
                · linarith only [h0, h1648, h1783, h1883, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1885 | h1885
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1886 | h1886
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1887 | h1887
                      · linarith only [h0, h1647, h1783, h1885, h1887, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h1647, h1885, h1887, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · linarith only [h0, h1647, h1885, h1886, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1647, h1885, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
        · linarith only [h0, h1648, h1782, hlam]
      · linarith only [h0, h1647, h1781, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1894 | h1894
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1895 | h1895
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1896 | h1896
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1897 | h1897
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1898 | h1898
            · linarith only [h1647, h1648, h1898, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1900 | h1900
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1901 | h1901
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1902 | h1902
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1903 | h1903
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1904 | h1904
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1905 | h1905
                        · linarith only [h0, h1647, h1905, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · linarith only [h1647, h1648, h1900, h1902, h1903, h1905, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h1648, h1903, h1904, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h1896, h1903, hlam]
                  · linarith only [h0, h1902, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h1647, h1648, h1900, h1901, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1912 | h1912
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1913 | h1913
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1914 | h1914
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1915 | h1915
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1916 | h1916
                        · linarith only [h1647, h1648, h1900, h1914, h1916, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1918 | h1918
                          · linarith only [h1647, h1648, h1913, h1914, h1918, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1920 | h1920
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1921 | h1921
                              · rcases h0bigk with h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [hlam, p1922_0]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h0, hlam, p1922_0]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h1647, h1648, h1913, h1914, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1922_1, u2elo1]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h1648, hlam, p1922_0]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h1648, h1914, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1922_1, u2elo1]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht12, p1922_1, u2elo1]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [hlam, p1922_0]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h0, h1647, h1913, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1922_1, u2elo1]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h0, h1647, h1648, h1913, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1922_1, u2elo1]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h0, h1894, h1915, h1920, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1922_1, u2elo1]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h1647, hlam, p1922_1]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h1895, hlam, p1922_0]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [hlam, p1922_0]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h1898, hlam, p1922_0]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h1900, hlam, p1922_1]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h1647, h1913, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1922_1]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h1896, hlam, p1922_0]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h1647, h1648, h1913, h1914, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1922_1, u2elo1]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [hlam, p1922_0]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h1647, h1648, h1900, h1913, h1914, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1922_1, u2elo1]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h1894, hlam, p1922_1]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h1897, hlam, p1922_0]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h0, h1647, h1894, h1913, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1922_1, u2elo1]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h1912, hlam, p1922_0]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [hlam, p1922_0]
                              · linarith only [h0, h1647, h1897, h1898, h1913, h1920, h1921, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1949 | h1949
                              · rcases h0bigk with h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c | h1950c
                                · have p1950_0 := h1950c.1
                                  have p1950_1 := h1950c.2.1
                                  have p1950_2 := h1950c.2.2.1
                                  have p1950_3 := h1950c.2.2.2
                                  linarith only [hlam, p1950_0]
                                · have p1950_0 := h1950c.1
                                  have p1950_1 := h1950c.2.1
                                  have p1950_2 := h1950c.2.2.1
                                  have p1950_3 := h1950c.2.2.2
                                  linarith only [h0, hlam, p1950_0]
                                · have p1950_0 := h1950c.1
                                  have p1950_1 := h1950c.2.1
                                  have p1950_2 := h1950c.2.2.1
                                  have p1950_3 := h1950c.2.2.2
                                  linarith only [h1647, h1648, h1913, h1914, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1950_1, u2elo1]
                                · have p1950_0 := h1950c.1
                                  have p1950_1 := h1950c.2.1
                                  have p1950_2 := h1950c.2.2.1
                                  have p1950_3 := h1950c.2.2.2
                                  linarith only [h1648, hlam, p1950_0]
                                · have p1950_0 := h1950c.1
                                  have p1950_1 := h1950c.2.1
                                  have p1950_2 := h1950c.2.2.1
                                  have p1950_3 := h1950c.2.2.2
                                  linarith only [h1648, h1914, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1950_1, u2elo1]
                                · have p1950_0 := h1950c.1
                                  have p1950_1 := h1950c.2.1
                                  have p1950_2 := h1950c.2.2.1
                                  have p1950_3 := h1950c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht12, p1950_1, u2elo1]
                                · have p1950_0 := h1950c.1
                                  have p1950_1 := h1950c.2.1
                                  have p1950_2 := h1950c.2.2.1
                                  have p1950_3 := h1950c.2.2.2
                                  linarith only [hlam, p1950_0]
                                · have p1950_0 := h1950c.1
                                  have p1950_1 := h1950c.2.1
                                  have p1950_2 := h1950c.2.2.1
                                  have p1950_3 := h1950c.2.2.2
                                  linarith only [h0, h1647, h1913, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1950_1, u2elo1]
                                · have p1950_0 := h1950c.1
                                  have p1950_1 := h1950c.2.1
                                  have p1950_2 := h1950c.2.2.1
                                  have p1950_3 := h1950c.2.2.2
                                  linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1950_1, u2elo1]
                                · have p1950_0 := h1950c.1
                                  have p1950_1 := h1950c.2.1
                                  have p1950_2 := h1950c.2.2.1
                                  have p1950_3 := h1950c.2.2.2
                                  linarith only [h0, h1894, h1915, h1918, h1920, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1950_1, u2elo1]
                                · have p1950_0 := h1950c.1
                                  have p1950_1 := h1950c.2.1
                                  have p1950_2 := h1950c.2.2.1
                                  have p1950_3 := h1950c.2.2.2
                                  linarith only [h1647, hlam, p1950_1]
                                · have p1950_0 := h1950c.1
                                  have p1950_1 := h1950c.2.1
                                  have p1950_2 := h1950c.2.2.1
                                  have p1950_3 := h1950c.2.2.2
                                  linarith only [h1895, hlam, p1950_0]
                                · have p1950_0 := h1950c.1
                                  have p1950_1 := h1950c.2.1
                                  have p1950_2 := h1950c.2.2.1
                                  have p1950_3 := h1950c.2.2.2
                                  linarith only [hlam, p1950_0]
                                · have p1950_0 := h1950c.1
                                  have p1950_1 := h1950c.2.1
                                  have p1950_2 := h1950c.2.2.1
                                  have p1950_3 := h1950c.2.2.2
                                  linarith only [h1898, hlam, p1950_0]
                                · have p1950_0 := h1950c.1
                                  have p1950_1 := h1950c.2.1
                                  have p1950_2 := h1950c.2.2.1
                                  have p1950_3 := h1950c.2.2.2
                                  linarith only [h1900, hlam, p1950_1]
                                · have p1950_0 := h1950c.1
                                  have p1950_1 := h1950c.2.1
                                  have p1950_2 := h1950c.2.2.1
                                  have p1950_3 := h1950c.2.2.2
                                  linarith only [h1894, h1915, h1918, h1920, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1950_1]
                                · have p1950_0 := h1950c.1
                                  have p1950_1 := h1950c.2.1
                                  have p1950_2 := h1950c.2.2.1
                                  have p1950_3 := h1950c.2.2.2
                                  linarith only [h1896, hlam, p1950_0]
                                · have p1950_0 := h1950c.1
                                  have p1950_1 := h1950c.2.1
                                  have p1950_2 := h1950c.2.2.1
                                  have p1950_3 := h1950c.2.2.2
                                  linarith only [h1647, h1648, h1913, h1914, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1950_1, u2elo1]
                                · have p1950_0 := h1950c.1
                                  have p1950_1 := h1950c.2.1
                                  have p1950_2 := h1950c.2.2.1
                                  have p1950_3 := h1950c.2.2.2
                                  linarith only [hlam, p1950_0]
                                · have p1950_0 := h1950c.1
                                  have p1950_1 := h1950c.2.1
                                  have p1950_2 := h1950c.2.2.1
                                  have p1950_3 := h1950c.2.2.2
                                  linarith only [h1648, h1894, h1914, h1915, h1918, h1920, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1950_1, u2elo1]
                                · have p1950_0 := h1950c.1
                                  have p1950_1 := h1950c.2.1
                                  have p1950_2 := h1950c.2.2.1
                                  have p1950_3 := h1950c.2.2.2
                                  linarith only [h1894, hlam, p1950_1]
                                · have p1950_0 := h1950c.1
                                  have p1950_1 := h1950c.2.1
                                  have p1950_2 := h1950c.2.2.1
                                  have p1950_3 := h1950c.2.2.2
                                  linarith only [h1897, hlam, p1950_0]
                                · have p1950_0 := h1950c.1
                                  have p1950_1 := h1950c.2.1
                                  have p1950_2 := h1950c.2.2.1
                                  have p1950_3 := h1950c.2.2.2
                                  linarith only [h0, h1647, h1894, h1913, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1950_1, u2elo1]
                                · have p1950_0 := h1950c.1
                                  have p1950_1 := h1950c.2.1
                                  have p1950_2 := h1950c.2.2.1
                                  have p1950_3 := h1950c.2.2.2
                                  linarith only [h1912, hlam, p1950_0]
                                · have p1950_0 := h1950c.1
                                  have p1950_1 := h1950c.2.1
                                  have p1950_2 := h1950c.2.2.1
                                  have p1950_3 := h1950c.2.2.2
                                  linarith only [hlam, p1950_0]
                              · linarith only [h1898, h1912, h1949, hlam]
                      · linarith only [h1648, h1914, h1915, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h1914, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1913, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h1648, h1894, h1912, hlam]
          · linarith only [h0, h1894, h1897, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1982 | h1982
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1983 | h1983
            · linarith only [h0, h1647, h1896, h1983, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1985 | h1985
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1986 | h1986
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1987 | h1987
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1988 | h1988
                    · linarith only [h0, h1647, h1896, h1985, h1988, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · linarith only [h0, h1647, h1987, h1988, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1987, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h0, h1647, h1896, h1985, h1986, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1993 | h1993
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1994 | h1994
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1995 | h1995
                    · linarith only [h0, h1647, h1896, h1994, h1995, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1647, h1994, h1995, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1647, h1994, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                · linarith only [h1648, h1894, h1993, hlam]
          · linarith only [h0, h1894, h1982, hlam]
      · linarith only [h0, h1647, h1895, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2002 | h2002
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2003 | h2003
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2004 | h2004
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2005 | h2005
            · linarith only [h1647, h1648, h2005, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2007 | h2007
              · linarith only [h1647, h1894, h2007, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2009 | h2009
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2010 | h2010
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2011 | h2011
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2012 | h2012
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2013 | h2013
                        · linarith only [h1647, h1894, h2007, h2013, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2015 | h2015
                          · linarith only [h1647, h1648, h2005, h2009, h2010, h2011, h2015, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2017 | h2017
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2018 | h2018
                              · rcases h0bigk with h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c | h2019c
                                · have p2019_0 := h2019c.1
                                  have p2019_1 := h2019c.2.1
                                  have p2019_2 := h2019c.2.2.1
                                  have p2019_3 := h2019c.2.2.2
                                  linarith only [hlam, p2019_0]
                                · have p2019_0 := h2019c.1
                                  have p2019_1 := h2019c.2.1
                                  have p2019_2 := h2019c.2.2.1
                                  have p2019_3 := h2019c.2.2.2
                                  linarith only [h0, hlam, p2019_0]
                                · have p2019_0 := h2019c.1
                                  have p2019_1 := h2019c.2.1
                                  have p2019_2 := h2019c.2.2.1
                                  have p2019_3 := h2019c.2.2.2
                                  linarith only [h1648, h2011, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2019_1, u2elo1]
                                · have p2019_0 := h2019c.1
                                  have p2019_1 := h2019c.2.1
                                  have p2019_2 := h2019c.2.2.1
                                  have p2019_3 := h2019c.2.2.2
                                  linarith only [h1648, hlam, p2019_0]
                                · have p2019_0 := h2019c.1
                                  have p2019_1 := h2019c.2.1
                                  have p2019_2 := h2019c.2.2.1
                                  have p2019_3 := h2019c.2.2.2
                                  linarith only [h1894, hlam, p2019_0]
                                · have p2019_0 := h2019c.1
                                  have p2019_1 := h2019c.2.1
                                  have p2019_2 := h2019c.2.2.1
                                  have p2019_3 := h2019c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, p2019_1, u2elo0]
                                · have p2019_0 := h2019c.1
                                  have p2019_1 := h2019c.2.1
                                  have p2019_2 := h2019c.2.2.1
                                  have p2019_3 := h2019c.2.2.2
                                  linarith only [hlam, p2019_0]
                                · have p2019_0 := h2019c.1
                                  have p2019_1 := h2019c.2.1
                                  have p2019_2 := h2019c.2.2.1
                                  have p2019_3 := h2019c.2.2.2
                                  linarith only [h0, h1647, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2019_1, u2elo1]
                                · have p2019_0 := h2019c.1
                                  have p2019_1 := h2019c.2.1
                                  have p2019_2 := h2019c.2.2.1
                                  have p2019_3 := h2019c.2.2.2
                                  linarith only [h0, h1647, h1894, h2009, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2019_1, u2elo1]
                                · have p2019_0 := h2019c.1
                                  have p2019_1 := h2019c.2.1
                                  have p2019_2 := h2019c.2.2.1
                                  have p2019_3 := h2019c.2.2.2
                                  linarith only [h0, h1647, h1894, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2019_1, u2elo1]
                                · have p2019_0 := h2019c.1
                                  have p2019_1 := h2019c.2.1
                                  have p2019_2 := h2019c.2.2.1
                                  have p2019_3 := h2019c.2.2.2
                                  linarith only [h1647, hlam, p2019_1]
                                · have p2019_0 := h2019c.1
                                  have p2019_1 := h2019c.2.1
                                  have p2019_2 := h2019c.2.2.1
                                  have p2019_3 := h2019c.2.2.2
                                  linarith only [h2002, hlam, p2019_0]
                                · have p2019_0 := h2019c.1
                                  have p2019_1 := h2019c.2.1
                                  have p2019_2 := h2019c.2.2.1
                                  have p2019_3 := h2019c.2.2.2
                                  linarith only [hlam, p2019_0]
                                · have p2019_0 := h2019c.1
                                  have p2019_1 := h2019c.2.1
                                  have p2019_2 := h2019c.2.2.1
                                  have p2019_3 := h2019c.2.2.2
                                  linarith only [h2005, hlam, p2019_0]
                                · have p2019_0 := h2019c.1
                                  have p2019_1 := h2019c.2.1
                                  have p2019_2 := h2019c.2.2.1
                                  have p2019_3 := h2019c.2.2.2
                                  linarith only [h2007, hlam, p2019_1]
                                · have p2019_0 := h2019c.1
                                  have p2019_1 := h2019c.2.1
                                  have p2019_2 := h2019c.2.2.1
                                  have p2019_3 := h2019c.2.2.2
                                  linarith only [h1647, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2019_1]
                                · have p2019_0 := h2019c.1
                                  have p2019_1 := h2019c.2.1
                                  have p2019_2 := h2019c.2.2.1
                                  have p2019_3 := h2019c.2.2.2
                                  linarith only [h2003, hlam, p2019_0]
                                · have p2019_0 := h2019c.1
                                  have p2019_1 := h2019c.2.1
                                  have p2019_2 := h2019c.2.2.1
                                  have p2019_3 := h2019c.2.2.2
                                  linarith only [h1647, h1648, h2011, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2019_1, u2elo1]
                                · have p2019_0 := h2019c.1
                                  have p2019_1 := h2019c.2.1
                                  have p2019_2 := h2019c.2.2.1
                                  have p2019_3 := h2019c.2.2.2
                                  linarith only [hlam, p2019_0]
                                · have p2019_0 := h2019c.1
                                  have p2019_1 := h2019c.2.1
                                  have p2019_2 := h2019c.2.2.1
                                  have p2019_3 := h2019c.2.2.2
                                  linarith only [h1647, h1648, h1894, h2011, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2019_1, u2elo1]
                                · have p2019_0 := h2019c.1
                                  have p2019_1 := h2019c.2.1
                                  have p2019_2 := h2019c.2.2.1
                                  have p2019_3 := h2019c.2.2.2
                                  linarith only [h1647, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2019_1]
                                · have p2019_0 := h2019c.1
                                  have p2019_1 := h2019c.2.1
                                  have p2019_2 := h2019c.2.2.1
                                  have p2019_3 := h2019c.2.2.2
                                  linarith only [h2004, hlam, p2019_0]
                                · have p2019_0 := h2019c.1
                                  have p2019_1 := h2019c.2.1
                                  have p2019_2 := h2019c.2.2.1
                                  have p2019_3 := h2019c.2.2.2
                                  linarith only [h1647, h1894, h2013, hc13, hc35, hlam, hphi, p2019_1]
                                · have p2019_0 := h2019c.1
                                  have p2019_1 := h2019c.2.1
                                  have p2019_2 := h2019c.2.2.1
                                  have p2019_3 := h2019c.2.2.2
                                  linarith only [h2009, hlam, p2019_0]
                                · have p2019_0 := h2019c.1
                                  have p2019_1 := h2019c.2.1
                                  have p2019_2 := h2019c.2.2.1
                                  have p2019_3 := h2019c.2.2.2
                                  linarith only [hlam, p2019_0]
                              · linarith only [h1647, h1648, h2005, h2010, h2017, h2018, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2046 | h2046
                              · rcases h0bigk with h2047c | h2047c | h2047c | h2047c | h2047c | h2047c | h2047c | h2047c | h2047c | h2047c | h2047c | h2047c | h2047c | h2047c | h2047c | h2047c | h2047c | h2047c | h2047c | h2047c | h2047c | h2047c | h2047c | h2047c | h2047c
                                · have p2047_0 := h2047c.1
                                  have p2047_1 := h2047c.2.1
                                  have p2047_2 := h2047c.2.2.1
                                  have p2047_3 := h2047c.2.2.2
                                  linarith only [hlam, p2047_0]
                                · have p2047_0 := h2047c.1
                                  have p2047_1 := h2047c.2.1
                                  have p2047_2 := h2047c.2.2.1
                                  have p2047_3 := h2047c.2.2.2
                                  linarith only [h0, hlam, p2047_0]
                                · have p2047_0 := h2047c.1
                                  have p2047_1 := h2047c.2.1
                                  have p2047_2 := h2047c.2.2.1
                                  have p2047_3 := h2047c.2.2.2
                                  linarith only [h0, h1647, h2010, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2047_1, u2elo1]
                                · have p2047_0 := h2047c.1
                                  have p2047_1 := h2047c.2.1
                                  have p2047_2 := h2047c.2.2.1
                                  have p2047_3 := h2047c.2.2.2
                                  linarith only [h1648, hlam, p2047_0]
                                · have p2047_0 := h2047c.1
                                  have p2047_1 := h2047c.2.1
                                  have p2047_2 := h2047c.2.2.1
                                  have p2047_3 := h2047c.2.2.2
                                  linarith only [h1894, hlam, p2047_0]
                                · have p2047_0 := h2047c.1
                                  have p2047_1 := h2047c.2.1
                                  have p2047_2 := h2047c.2.2.1
                                  have p2047_3 := h2047c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht12, p2047_1, u2elo1]
                                · have p2047_0 := h2047c.1
                                  have p2047_1 := h2047c.2.1
                                  have p2047_2 := h2047c.2.2.1
                                  have p2047_3 := h2047c.2.2.2
                                  linarith only [hlam, p2047_0]
                                · have p2047_0 := h2047c.1
                                  have p2047_1 := h2047c.2.1
                                  have p2047_2 := h2047c.2.2.1
                                  have p2047_3 := h2047c.2.2.2
                                  linarith only [h0, h1647, h2010, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2047_1, u2elo1]
                                · have p2047_0 := h2047c.1
                                  have p2047_1 := h2047c.2.1
                                  have p2047_2 := h2047c.2.2.1
                                  have p2047_3 := h2047c.2.2.2
                                  linarith only [h0, h2009, h2015, h2017, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2047_1, u2elo1]
                                · have p2047_0 := h2047c.1
                                  have p2047_1 := h2047c.2.1
                                  have p2047_2 := h2047c.2.2.1
                                  have p2047_3 := h2047c.2.2.2
                                  linarith only [h0, h1647, h1894, h2010, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2047_1, u2elo1]
                                · have p2047_0 := h2047c.1
                                  have p2047_1 := h2047c.2.1
                                  have p2047_2 := h2047c.2.2.1
                                  have p2047_3 := h2047c.2.2.2
                                  linarith only [h1647, hlam, p2047_1]
                                · have p2047_0 := h2047c.1
                                  have p2047_1 := h2047c.2.1
                                  have p2047_2 := h2047c.2.2.1
                                  have p2047_3 := h2047c.2.2.2
                                  linarith only [h2002, hlam, p2047_0]
                                · have p2047_0 := h2047c.1
                                  have p2047_1 := h2047c.2.1
                                  have p2047_2 := h2047c.2.2.1
                                  have p2047_3 := h2047c.2.2.2
                                  linarith only [hlam, p2047_0]
                                · have p2047_0 := h2047c.1
                                  have p2047_1 := h2047c.2.1
                                  have p2047_2 := h2047c.2.2.1
                                  have p2047_3 := h2047c.2.2.2
                                  linarith only [h2005, hlam, p2047_0]
                                · have p2047_0 := h2047c.1
                                  have p2047_1 := h2047c.2.1
                                  have p2047_2 := h2047c.2.2.1
                                  have p2047_3 := h2047c.2.2.2
                                  linarith only [h2007, hlam, p2047_1]
                                · have p2047_0 := h2047c.1
                                  have p2047_1 := h2047c.2.1
                                  have p2047_2 := h2047c.2.2.1
                                  have p2047_3 := h2047c.2.2.2
                                  linarith only [h1647, h2010, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2047_1]
                                · have p2047_0 := h2047c.1
                                  have p2047_1 := h2047c.2.1
                                  have p2047_2 := h2047c.2.2.1
                                  have p2047_3 := h2047c.2.2.2
                                  linarith only [h2003, hlam, p2047_0]
                                · have p2047_0 := h2047c.1
                                  have p2047_1 := h2047c.2.1
                                  have p2047_2 := h2047c.2.2.1
                                  have p2047_3 := h2047c.2.2.2
                                  linarith only [h1647, h1648, h2010, h2011, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2047_1, u2elo1]
                                · have p2047_0 := h2047c.1
                                  have p2047_1 := h2047c.2.1
                                  have p2047_2 := h2047c.2.2.1
                                  have p2047_3 := h2047c.2.2.2
                                  linarith only [hlam, p2047_0]
                                · have p2047_0 := h2047c.1
                                  have p2047_1 := h2047c.2.1
                                  have p2047_2 := h2047c.2.2.1
                                  have p2047_3 := h2047c.2.2.2
                                  linarith only [h1647, h1648, h1894, h2010, h2011, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2047_1, u2elo1]
                                · have p2047_0 := h2047c.1
                                  have p2047_1 := h2047c.2.1
                                  have p2047_2 := h2047c.2.2.1
                                  have p2047_3 := h2047c.2.2.2
                                  linarith only [h1647, h2010, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2047_1]
                                · have p2047_0 := h2047c.1
                                  have p2047_1 := h2047c.2.1
                                  have p2047_2 := h2047c.2.2.1
                                  have p2047_3 := h2047c.2.2.2
                                  linarith only [h2004, hlam, p2047_0]
                                · have p2047_0 := h2047c.1
                                  have p2047_1 := h2047c.2.1
                                  have p2047_2 := h2047c.2.2.1
                                  have p2047_3 := h2047c.2.2.2
                                  linarith only [h1647, h1894, h2010, h2012, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2047_1, u2elo1]
                                · have p2047_0 := h2047c.1
                                  have p2047_1 := h2047c.2.1
                                  have p2047_2 := h2047c.2.2.1
                                  have p2047_3 := h2047c.2.2.2
                                  linarith only [h2009, hlam, p2047_0]
                                · have p2047_0 := h2047c.1
                                  have p2047_1 := h2047c.2.1
                                  have p2047_2 := h2047c.2.2.1
                                  have p2047_3 := h2047c.2.2.2
                                  linarith only [hlam, p2047_0]
                              · linarith only [h2005, h2009, h2046, hlam]
                      · linarith only [h0, h2004, h2012, hlam]
                    · linarith only [h0, h1647, h2010, h2011, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h2010, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2077 | h2077
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2078 | h2078
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2079 | h2079
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2080 | h2080
                        · linarith only [h1647, h1648, h2078, h2080, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2082 | h2082
                          · linarith only [h1647, h1648, h2005, h2077, h2078, h2082, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2084 | h2084
                            · linarith only [h1648, h2009, h2084, hc01, hlam, hphi, ht12, u2elo3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2086 | h2086
                              · linarith only [h1647, h1648, h2009, h2077, h2086, hc23, hc34, hlam, hphi]
                              · rcases h0bigk with h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c | h2088c
                                · have p2088_0 := h2088c.1
                                  have p2088_1 := h2088c.2.1
                                  have p2088_2 := h2088c.2.2.1
                                  have p2088_3 := h2088c.2.2.2
                                  linarith only [hlam, p2088_0]
                                · have p2088_0 := h2088c.1
                                  have p2088_1 := h2088c.2.1
                                  have p2088_2 := h2088c.2.2.1
                                  have p2088_3 := h2088c.2.2.2
                                  linarith only [h0, hlam, p2088_0]
                                · have p2088_0 := h2088c.1
                                  have p2088_1 := h2088c.2.1
                                  have p2088_2 := h2088c.2.2.1
                                  have p2088_3 := h2088c.2.2.2
                                  linarith only [h1647, h1648, h2077, h2078, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2088_1]
                                · have p2088_0 := h2088c.1
                                  have p2088_1 := h2088c.2.1
                                  have p2088_2 := h2088c.2.2.1
                                  have p2088_3 := h2088c.2.2.2
                                  linarith only [h1648, hlam, p2088_0]
                                · have p2088_0 := h2088c.1
                                  have p2088_1 := h2088c.2.1
                                  have p2088_2 := h2088c.2.2.1
                                  have p2088_3 := h2088c.2.2.2
                                  linarith only [h1894, hlam, p2088_0]
                                · have p2088_0 := h2088c.1
                                  have p2088_1 := h2088c.2.1
                                  have p2088_2 := h2088c.2.2.1
                                  have p2088_3 := h2088c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, p2088_1, u2elo0]
                                · have p2088_0 := h2088c.1
                                  have p2088_1 := h2088c.2.1
                                  have p2088_2 := h2088c.2.2.1
                                  have p2088_3 := h2088c.2.2.2
                                  linarith only [hlam, p2088_0]
                                · have p2088_0 := h2088c.1
                                  have p2088_1 := h2088c.2.1
                                  have p2088_2 := h2088c.2.2.1
                                  have p2088_3 := h2088c.2.2.2
                                  linarith only [h0, h1647, h2077, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2088_1, u2elo1]
                                · have p2088_0 := h2088c.1
                                  have p2088_1 := h2088c.2.1
                                  have p2088_2 := h2088c.2.2.1
                                  have p2088_3 := h2088c.2.2.2
                                  linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2088_1, u2elo1]
                                · have p2088_0 := h2088c.1
                                  have p2088_1 := h2088c.2.1
                                  have p2088_2 := h2088c.2.2.1
                                  have p2088_3 := h2088c.2.2.2
                                  linarith only [h0, h1647, h1648, h2009, h2077, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2088_1, u2elo1]
                                · have p2088_0 := h2088c.1
                                  have p2088_1 := h2088c.2.1
                                  have p2088_2 := h2088c.2.2.1
                                  have p2088_3 := h2088c.2.2.2
                                  linarith only [h1647, hlam, p2088_1]
                                · have p2088_0 := h2088c.1
                                  have p2088_1 := h2088c.2.1
                                  have p2088_2 := h2088c.2.2.1
                                  have p2088_3 := h2088c.2.2.2
                                  linarith only [h2002, hlam, p2088_0]
                                · have p2088_0 := h2088c.1
                                  have p2088_1 := h2088c.2.1
                                  have p2088_2 := h2088c.2.2.1
                                  have p2088_3 := h2088c.2.2.2
                                  linarith only [hlam, p2088_0]
                                · have p2088_0 := h2088c.1
                                  have p2088_1 := h2088c.2.1
                                  have p2088_2 := h2088c.2.2.1
                                  have p2088_3 := h2088c.2.2.2
                                  linarith only [h2005, hlam, p2088_0]
                                · have p2088_0 := h2088c.1
                                  have p2088_1 := h2088c.2.1
                                  have p2088_2 := h2088c.2.2.1
                                  have p2088_3 := h2088c.2.2.2
                                  linarith only [h2007, hlam, p2088_1]
                                · have p2088_0 := h2088c.1
                                  have p2088_1 := h2088c.2.1
                                  have p2088_2 := h2088c.2.2.1
                                  have p2088_3 := h2088c.2.2.2
                                  linarith only [h1647, h2077, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2088_1]
                                · have p2088_0 := h2088c.1
                                  have p2088_1 := h2088c.2.1
                                  have p2088_2 := h2088c.2.2.1
                                  have p2088_3 := h2088c.2.2.2
                                  linarith only [h2003, hlam, p2088_0]
                                · have p2088_0 := h2088c.1
                                  have p2088_1 := h2088c.2.1
                                  have p2088_2 := h2088c.2.2.1
                                  have p2088_3 := h2088c.2.2.2
                                  linarith only [h1647, h2005, h2077, h2086, hc23, hc45, hlam, hphi, ht34, p2088_1]
                                · have p2088_0 := h2088c.1
                                  have p2088_1 := h2088c.2.1
                                  have p2088_2 := h2088c.2.2.1
                                  have p2088_3 := h2088c.2.2.2
                                  linarith only [hlam, p2088_0]
                                · have p2088_0 := h2088c.1
                                  have p2088_1 := h2088c.2.1
                                  have p2088_2 := h2088c.2.2.1
                                  have p2088_3 := h2088c.2.2.2
                                  linarith only [h2009, hlam, p2088_1]
                                · have p2088_0 := h2088c.1
                                  have p2088_1 := h2088c.2.1
                                  have p2088_2 := h2088c.2.2.1
                                  have p2088_3 := h2088c.2.2.2
                                  linarith only [h0, h1647, h2004, h2077, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2088_1, u2elo1]
                                · have p2088_0 := h2088c.1
                                  have p2088_1 := h2088c.2.1
                                  have p2088_2 := h2088c.2.2.1
                                  have p2088_3 := h2088c.2.2.2
                                  linarith only [h2004, hlam, p2088_0]
                                · have p2088_0 := h2088c.1
                                  have p2088_1 := h2088c.2.1
                                  have p2088_2 := h2088c.2.2.1
                                  have p2088_3 := h2088c.2.2.2
                                  linarith only [h0, h1647, h2004, h2077, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2088_1, u2elo1]
                                · have p2088_0 := h2088c.1
                                  have p2088_1 := h2088c.2.1
                                  have p2088_2 := h2088c.2.2.1
                                  have p2088_3 := h2088c.2.2.2
                                  linarith only [h0, h2004, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2088_1, u2elo1]
                                · have p2088_0 := h2088c.1
                                  have p2088_1 := h2088c.2.1
                                  have p2088_2 := h2088c.2.2.1
                                  have p2088_3 := h2088c.2.2.2
                                  linarith only [hlam, p2088_0]
                      · linarith only [h0, h2004, h2079, hlam]
                    · linarith only [h0, h1647, h2077, h2078, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h2077, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2117 | h2117
            · linarith only [h1647, h1648, h2117, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2119 | h2119
              · linarith only [h1647, h1648, h2003, h2004, h2119, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2121 | h2121
                · linarith only [h2003, h2004, h2121, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2123 | h2123
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2124 | h2124
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h2125 | h2125
                      · linarith only [h1648, h2003, h2004, h2125, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h1647, h2123, h2125, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · linarith only [h0, h1647, h2003, h2123, h2124, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h1647, h2123, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2130 | h2130
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2131 | h2131
            · linarith only [h0, h1647, h2003, h2131, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2133 | h2133
              · linarith only [h1647, h1894, h2133, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2135 | h2135
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2136 | h2136
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2137 | h2137
                    · linarith only [h1647, h1894, h2003, h2130, h2136, h2137, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1647, h2136, h2137, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h2136, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h2003, h2130, h2135, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2142 | h2142
            · linarith only [h0, h1647, h2003, h2142, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2144 | h2144
              · linarith only [h0, h1647, h2130, h2144, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2146 | h2146
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2147 | h2147
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2148 | h2148
                    · linarith only [h0, h2003, h2148, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1647, h2147, h2148, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h2147, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2152 | h2152
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2153 | h2153
                    · linarith only [h0, h1647, h2003, h2152, h2153, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1647, h2152, h2153, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1647, h2152, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
      · linarith only [h0, h1647, h2002, hlam]

set_option maxHeartbeats 6082000 in
set_option maxHeartbeats 6082000 in
theorem r1l7_20_12_H_I_L_0_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1647 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2158 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  rcases m.htr 0 1 5 (by decide) (by decide) with h2159 | h2159
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2160 | h2160
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2161 | h2161
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2162 | h2162
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2163 | h2163
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2164 | h2164
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2165 | h2165
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2166 | h2166
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2167 | h2167
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2168 | h2168
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2169 | h2169
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2170 | h2170
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2171 | h2171
                          · linarith only [h0, h2158, h2167, h2171, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · linarith only [h1647, h2158, h2165, h2166, h2170, h2171, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2174 | h2174
                          · linarith only [h1647, h2158, h2166, h2167, h2174, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · linarith only [h1647, h2158, h2165, h2166, h2174, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h1647, h2164, h2169, hlam]
                    · linarith only [h1647, h2166, h2168, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h1647, h2166, h2167, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h2158, h2166, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2181 | h2181
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2182 | h2182
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2183 | h2183
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2184 | h2184
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2185 | h2185
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2186 | h2186
                          · linarith only [h1647, h2158, h2165, h2181, h2182, h2186, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2188 | h2188
                            · linarith only [h1647, h2159, h2165, h2181, h2183, h2185, h2186, h2188, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · rcases h0bigk with h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c | h2190c
                              · have p2190_0 := h2190c.1
                                have p2190_1 := h2190c.2.1
                                have p2190_2 := h2190c.2.2.1
                                have p2190_3 := h2190c.2.2.2
                                linarith only [hlam, p2190_0]
                              · have p2190_0 := h2190c.1
                                have p2190_1 := h2190c.2.1
                                have p2190_2 := h2190c.2.2.1
                                have p2190_3 := h2190c.2.2.2
                                linarith only [h0, hlam, p2190_0]
                              · have p2190_0 := h2190c.1
                                have p2190_1 := h2190c.2.1
                                have p2190_2 := h2190c.2.2.1
                                have p2190_3 := h2190c.2.2.2
                                linarith only [h1647, hlam, p2190_0]
                              · have p2190_0 := h2190c.1
                                have p2190_1 := h2190c.2.1
                                have p2190_2 := h2190c.2.2.1
                                have p2190_3 := h2190c.2.2.2
                                linarith only [h1647, h2158, h2181, h2182, h2185, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2190_1, u2elo1]
                              · have p2190_0 := h2190c.1
                                have p2190_1 := h2190c.2.1
                                have p2190_2 := h2190c.2.2.1
                                have p2190_3 := h2190c.2.2.2
                                linarith only [h1647, h2181, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2190_1, u2elo1]
                              · have p2190_0 := h2190c.1
                                have p2190_1 := h2190c.2.1
                                have p2190_2 := h2190c.2.2.1
                                have p2190_3 := h2190c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht12, p2190_1, u2elo1]
                              · have p2190_0 := h2190c.1
                                have p2190_1 := h2190c.2.1
                                have p2190_2 := h2190c.2.2.1
                                have p2190_3 := h2190c.2.2.2
                                linarith only [hlam, p2190_0]
                              · have p2190_0 := h2190c.1
                                have p2190_1 := h2190c.2.1
                                have p2190_2 := h2190c.2.2.1
                                have p2190_3 := h2190c.2.2.2
                                linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2190_1, u2elo1]
                              · have p2190_0 := h2190c.1
                                have p2190_1 := h2190c.2.1
                                have p2190_2 := h2190c.2.2.1
                                have p2190_3 := h2190c.2.2.2
                                linarith only [h0, h2158, h2182, h2185, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2190_1, u2elo1]
                              · have p2190_0 := h2190c.1
                                have p2190_1 := h2190c.2.1
                                have p2190_2 := h2190c.2.2.1
                                have p2190_3 := h2190c.2.2.2
                                linarith only [h0, h2159, h2183, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p2190_1, u2elo1]
                              · have p2190_0 := h2190c.1
                                have p2190_1 := h2190c.2.1
                                have p2190_2 := h2190c.2.2.1
                                have p2190_3 := h2190c.2.2.2
                                linarith only [h2158, h2182, h2185, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p2190_1]
                              · have p2190_0 := h2190c.1
                                have p2190_1 := h2190c.2.1
                                have p2190_2 := h2190c.2.2.1
                                have p2190_3 := h2190c.2.2.2
                                linarith only [h2160, hlam, p2190_0]
                              · have p2190_0 := h2190c.1
                                have p2190_1 := h2190c.2.1
                                have p2190_2 := h2190c.2.2.1
                                have p2190_3 := h2190c.2.2.2
                                linarith only [hlam, p2190_0]
                              · have p2190_0 := h2190c.1
                                have p2190_1 := h2190c.2.1
                                have p2190_2 := h2190c.2.2.1
                                have p2190_3 := h2190c.2.2.2
                                linarith only [h1647, h2158, h2181, h2182, h2185, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2190_1, u2elo1]
                              · have p2190_0 := h2190c.1
                                have p2190_1 := h2190c.2.1
                                have p2190_2 := h2190c.2.2.1
                                have p2190_3 := h2190c.2.2.2
                                linarith only [h1647, h2159, h2181, h2183, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p2190_1, u2elo1]
                              · have p2190_0 := h2190c.1
                                have p2190_1 := h2190c.2.1
                                have p2190_2 := h2190c.2.2.1
                                have p2190_3 := h2190c.2.2.2
                                linarith only [h2158, hlam, p2190_1]
                              · have p2190_0 := h2190c.1
                                have p2190_1 := h2190c.2.1
                                have p2190_2 := h2190c.2.2.1
                                have p2190_3 := h2190c.2.2.2
                                linarith only [h2161, hlam, p2190_0]
                              · have p2190_0 := h2190c.1
                                have p2190_1 := h2190c.2.1
                                have p2190_2 := h2190c.2.2.1
                                have p2190_3 := h2190c.2.2.2
                                linarith only [h2163, hlam, p2190_1]
                              · have p2190_0 := h2190c.1
                                have p2190_1 := h2190c.2.1
                                have p2190_2 := h2190c.2.2.1
                                have p2190_3 := h2190c.2.2.2
                                linarith only [hlam, p2190_0]
                              · have p2190_0 := h2190c.1
                                have p2190_1 := h2190c.2.1
                                have p2190_2 := h2190c.2.2.1
                                have p2190_3 := h2190c.2.2.2
                                linarith only [h2165, hlam, p2190_1]
                              · have p2190_0 := h2190c.1
                                have p2190_1 := h2190c.2.1
                                have p2190_2 := h2190c.2.2.1
                                have p2190_3 := h2190c.2.2.2
                                linarith only [h2159, hlam, p2190_1]
                              · have p2190_0 := h2190c.1
                                have p2190_1 := h2190c.2.1
                                have p2190_2 := h2190c.2.2.1
                                have p2190_3 := h2190c.2.2.2
                                linarith only [h2162, hlam, p2190_0]
                              · have p2190_0 := h2190c.1
                                have p2190_1 := h2190c.2.1
                                have p2190_2 := h2190c.2.2.1
                                have p2190_3 := h2190c.2.2.2
                                linarith only [h2164, hlam, p2190_0]
                              · have p2190_0 := h2190c.1
                                have p2190_1 := h2190c.2.1
                                have p2190_2 := h2190c.2.2.1
                                have p2190_3 := h2190c.2.2.2
                                linarith only [h0, h2158, h2159, h2182, h2185, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2190_1, u2elo1]
                              · have p2190_0 := h2190c.1
                                have p2190_1 := h2190c.2.1
                                have p2190_2 := h2190c.2.2.1
                                have p2190_3 := h2190c.2.2.2
                                linarith only [hlam, p2190_0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2216 | h2216
                          · linarith only [h1647, h2158, h2165, h2181, h2182, h2216, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2218 | h2218
                            · linarith only [h2163, h2165, h2218, hlam]
                            · linarith only [h1647, h2159, h2181, h2184, h2185, h2218, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h1647, h2164, h2184, hlam]
                    · linarith only [h1647, h2181, h2183, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h1647, h2158, h2181, h2182, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                · linarith only [h0, h2158, h2181, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · linarith only [h1647, h2159, h2164, hlam]
          · linarith only [h1647, h2158, h2163, hlam]
        · linarith only [h1647, h2159, h2160, h2162, hlam]
      · linarith only [h1647, h2158, h2160, h2161, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2229 | h2229
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2230 | h2230
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2231 | h2231
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2232 | h2232
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2233 | h2233
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2234 | h2234
                · linarith only [h2160, h2229, h2234, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · linarith only [h0, h2158, h2234, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2237 | h2237
                · linarith only [h0, h2158, h2160, h2237, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · linarith only [h0, h2158, h2237, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · linarith only [h0, h2159, h2160, h2232, hlam]
          · linarith only [h0, h2158, h2160, h2231, hlam]
        · linarith only [h0, h2159, h2230, hlam]
      · linarith only [h0, h2158, h2229, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2244 | h2244
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2245 | h2245
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2246 | h2246
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2247 | h2247
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2248 | h2248
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2249 | h2249
              · linarith only [h2158, h2159, h2249, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2251 | h2251
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2252 | h2252
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2253 | h2253
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2254 | h2254
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2255 | h2255
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2256 | h2256
                          · linarith only [h2158, h2159, h2249, h2251, h2252, h2254, h2256, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2258 | h2258
                            · linarith only [h2158, h2159, h2249, h2252, h2255, h2258, hlam]
                            · rcases h0bigk with h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c | h2260c
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [hlam, p2260_0]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [h0, hlam, p2260_0]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [h1647, hlam, p2260_0]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [h2158, h2159, h2251, h2252, h2254, h2255, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2260_1]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [h2159, hlam, p2260_0]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht12, p2260_1, u2elo1]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [hlam, p2260_0]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [h0, h2158, h2159, h2248, h2252, h2255, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2260_1, u2elo1]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [h0, h2158, h2252, h2255, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2260_1, u2elo1]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [h0, h2158, h2159, h2252, h2255, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2260_1, u2elo1]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [h2158, h2252, h2255, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p2260_1]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [h2244, hlam, p2260_0]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [hlam, p2260_0]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [h1647, h2158, h2251, h2252, h2255, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2260_1, u2elo1]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [h1647, h2158, h2159, h2251, h2252, h2255, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2260_1, u2elo1]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [h2158, hlam, p2260_1]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [h2245, hlam, p2260_0]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [h2247, hlam, p2260_1]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [hlam, p2260_0]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [h2249, hlam, p2260_1]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [h2158, h2252, h2255, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p2260_1]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [h2246, hlam, p2260_0]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [h2248, hlam, p2260_0]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [h2158, h2159, h2251, h2252, h2254, h2255, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2260_1, u2elo1]
                              · have p2260_0 := h2260c.1
                                have p2260_1 := h2260c.2.1
                                have p2260_2 := h2260c.2.2.1
                                have p2260_3 := h2260c.2.2.2
                                linarith only [hlam, p2260_0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2286 | h2286
                          · linarith only [h2158, h2159, h2251, h2252, h2254, h2286, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2288 | h2288
                            · linarith only [h2158, h2159, h2247, h2249, h2288, hlam]
                            · rcases h0bigk with h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c | h2290c
                              · have p2290_0 := h2290c.1
                                have p2290_1 := h2290c.2.1
                                have p2290_2 := h2290c.2.2.1
                                have p2290_3 := h2290c.2.2.2
                                linarith only [hlam, p2290_0]
                              · have p2290_0 := h2290c.1
                                have p2290_1 := h2290c.2.1
                                have p2290_2 := h2290c.2.2.1
                                have p2290_3 := h2290c.2.2.2
                                linarith only [h0, hlam, p2290_0]
                              · have p2290_0 := h2290c.1
                                have p2290_1 := h2290c.2.1
                                have p2290_2 := h2290c.2.2.1
                                have p2290_3 := h2290c.2.2.2
                                linarith only [h1647, hlam, p2290_0]
                              · have p2290_0 := h2290c.1
                                have p2290_1 := h2290c.2.1
                                have p2290_2 := h2290c.2.2.1
                                have p2290_3 := h2290c.2.2.2
                                linarith only [h2247, h2255, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2290_1]
                              · have p2290_0 := h2290c.1
                                have p2290_1 := h2290c.2.1
                                have p2290_2 := h2290c.2.2.1
                                have p2290_3 := h2290c.2.2.2
                                linarith only [h2159, hlam, p2290_0]
                              · have p2290_0 := h2290c.1
                                have p2290_1 := h2290c.2.1
                                have p2290_2 := h2290c.2.2.1
                                have p2290_3 := h2290c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht12, p2290_1, u2elo1]
                              · have p2290_0 := h2290c.1
                                have p2290_1 := h2290c.2.1
                                have p2290_2 := h2290c.2.2.1
                                have p2290_3 := h2290c.2.2.2
                                linarith only [hlam, p2290_0]
                              · have p2290_0 := h2290c.1
                                have p2290_1 := h2290c.2.1
                                have p2290_2 := h2290c.2.2.1
                                have p2290_3 := h2290c.2.2.2
                                linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2290_1, u2elo1]
                              · have p2290_0 := h2290c.1
                                have p2290_1 := h2290c.2.1
                                have p2290_2 := h2290c.2.2.1
                                have p2290_3 := h2290c.2.2.2
                                linarith only [h0, h2247, h2255, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2290_1, u2elo1]
                              · have p2290_0 := h2290c.1
                                have p2290_1 := h2290c.2.1
                                have p2290_2 := h2290c.2.2.1
                                have p2290_3 := h2290c.2.2.2
                                linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2290_1, u2elo1]
                              · have p2290_0 := h2290c.1
                                have p2290_1 := h2290c.2.1
                                have p2290_2 := h2290c.2.2.1
                                have p2290_3 := h2290c.2.2.2
                                linarith only [h2158, h2252, h2255, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2290_1]
                              · have p2290_0 := h2290c.1
                                have p2290_1 := h2290c.2.1
                                have p2290_2 := h2290c.2.2.1
                                have p2290_3 := h2290c.2.2.2
                                linarith only [h2244, hlam, p2290_0]
                              · have p2290_0 := h2290c.1
                                have p2290_1 := h2290c.2.1
                                have p2290_2 := h2290c.2.2.1
                                have p2290_3 := h2290c.2.2.2
                                linarith only [hlam, p2290_0]
                              · have p2290_0 := h2290c.1
                                have p2290_1 := h2290c.2.1
                                have p2290_2 := h2290c.2.2.1
                                have p2290_3 := h2290c.2.2.2
                                linarith only [h1647, h2247, h2251, h2255, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2290_1, u2elo1]
                              · have p2290_0 := h2290c.1
                                have p2290_1 := h2290c.2.1
                                have p2290_2 := h2290c.2.2.1
                                have p2290_3 := h2290c.2.2.2
                                linarith only [h1647, h2158, h2159, h2251, h2252, h2255, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2290_1, u2elo1]
                              · have p2290_0 := h2290c.1
                                have p2290_1 := h2290c.2.1
                                have p2290_2 := h2290c.2.2.1
                                have p2290_3 := h2290c.2.2.2
                                linarith only [h2158, hlam, p2290_1]
                              · have p2290_0 := h2290c.1
                                have p2290_1 := h2290c.2.1
                                have p2290_2 := h2290c.2.2.1
                                have p2290_3 := h2290c.2.2.2
                                linarith only [h2245, hlam, p2290_0]
                              · have p2290_0 := h2290c.1
                                have p2290_1 := h2290c.2.1
                                have p2290_2 := h2290c.2.2.1
                                have p2290_3 := h2290c.2.2.2
                                linarith only [h2247, hlam, p2290_1]
                              · have p2290_0 := h2290c.1
                                have p2290_1 := h2290c.2.1
                                have p2290_2 := h2290c.2.2.1
                                have p2290_3 := h2290c.2.2.2
                                linarith only [hlam, p2290_0]
                              · have p2290_0 := h2290c.1
                                have p2290_1 := h2290c.2.1
                                have p2290_2 := h2290c.2.2.1
                                have p2290_3 := h2290c.2.2.2
                                linarith only [h2249, hlam, p2290_1]
                              · have p2290_0 := h2290c.1
                                have p2290_1 := h2290c.2.1
                                have p2290_2 := h2290c.2.2.1
                                have p2290_3 := h2290c.2.2.2
                                linarith only [h2158, h2252, h2255, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2290_1]
                              · have p2290_0 := h2290c.1
                                have p2290_1 := h2290c.2.1
                                have p2290_2 := h2290c.2.2.1
                                have p2290_3 := h2290c.2.2.2
                                linarith only [h2246, hlam, p2290_0]
                              · have p2290_0 := h2290c.1
                                have p2290_1 := h2290c.2.1
                                have p2290_2 := h2290c.2.2.1
                                have p2290_3 := h2290c.2.2.2
                                linarith only [h2248, hlam, p2290_0]
                              · have p2290_0 := h2290c.1
                                have p2290_1 := h2290c.2.1
                                have p2290_2 := h2290c.2.2.1
                                have p2290_3 := h2290c.2.2.2
                                linarith only [h2159, h2247, h2251, h2254, h2255, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2290_1, u2elo1]
                              · have p2290_0 := h2290c.1
                                have p2290_1 := h2290c.2.1
                                have p2290_2 := h2290c.2.2.1
                                have p2290_3 := h2290c.2.2.2
                                linarith only [hlam, p2290_0]
                      · linarith only [h1647, h2248, h2254, hlam]
                    · linarith only [h0, h2246, h2253, hlam]
                  · linarith only [h0, h2252, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h2158, h2251, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2320 | h2320
              · linarith only [h1647, h2158, h2248, h2320, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2322 | h2322
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2323 | h2323
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2324 | h2324
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2325 | h2325
                      · linarith only [h1647, h2158, h2248, h2322, h2323, h2325, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2327 | h2327
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2328 | h2328
                          · linarith only [h0, h2158, h2320, h2323, h2328, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2330 | h2330
                            · linarith only [h1647, h2158, h2248, h2320, h2323, h2327, h2330, hlam]
                            · linarith only [h1647, h2158, h2325, h2330, hc14, hc45, hlam, hphi]
                        · linarith only [h1647, h2247, h2325, h2327, hc23, hc35, hlam, hphi]
                    · linarith only [h0, h2246, h2324, hlam]
                  · linarith only [h0, h2158, h2323, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                · linarith only [h0, h2158, h2322, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
          · linarith only [h1647, h2158, h2247, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2338 | h2338
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2339 | h2339
            · linarith only [h2244, h2246, h2339, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2341 | h2341
              · linarith only [h1647, h2158, h2244, h2246, h2341, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2343 | h2343
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2344 | h2344
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2345 | h2345
                    · linarith only [h1647, h2158, h2244, h2246, h2344, h2345, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h2158, h2344, h2345, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                  · linarith only [h1647, h2343, h2344, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h2158, h2343, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
          · linarith only [h1647, h2158, h2338, hlam]
      · linarith only [h1647, h2158, h2244, h2245, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2352 | h2352
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2353 | h2353
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2354 | h2354
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2355 | h2355
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2356 | h2356
              · linarith only [h2158, h2159, h2356, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2358 | h2358
                · linarith only [h2244, h2358, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h2158, h2358, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · linarith only [h2244, h2353, h2355, hlam]
          · linarith only [h2158, h2159, h2244, h2353, h2354, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2363 | h2363
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2364 | h2364
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2365 | h2365
              · linarith only [h0, h2158, h2353, h2365, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2367 | h2367
                · linarith only [h0, h2158, h2244, h2367, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · linarith only [h0, h2158, h2367, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2370 | h2370
              · linarith only [h1647, h2158, h2364, h2370, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2372 | h2372
                · linarith only [h0, h2158, h2244, h2372, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · linarith only [h0, h2158, h2372, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
          · linarith only [h0, h2158, h2244, h2363, hlam]
      · linarith only [h0, h2158, h2352, hlam]

end R2N4
