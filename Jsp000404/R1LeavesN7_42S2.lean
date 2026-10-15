import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6588000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_LR_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1697 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1698 | h1698
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1699 | h1699
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1700 | h1700
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1701 | h1701
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1702 | h1702
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1703 | h1703
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1704 | h1704
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1705 | h1705
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1706 | h1706
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1707 | h1707
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1708 | h1708
                      · linarith only [h0, h1697, h1708, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                      · linarith only [h1707, h1708, hc34, hlam, hphi, ht45, u5elo3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1711 | h1711
                      · linarith only [h0, h1697, h1702, h1707, h1711, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1713 | h1713
                        · linarith only [h0, h1698, h1713, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1715 | h1715
                          · linarith only [h1704, h1707, h1715, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1717 | h1717
                            · linarith only [h0, h1697, h1702, h1703, h1704, h1707, h1711, h1713, h1717, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi6]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1719 | h1719
                              · linarith only [h1705, h1713, h1719, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1721 | h1721
                                · linarith only [h0, h1697, h1702, h1707, h1713, h1721, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                · linarith only [h1704, h1707, h1721, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h0, h1697, h1702, h1703, h1706, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                · linarith only [h0, h1697, h1702, h1703, h1705, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
              · linarith only [h0, h1697, h1702, h1703, h1704, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1727 | h1727
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1728 | h1728
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1729 | h1729
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1730 | h1730
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1731 | h1731
                      · linarith only [h0, h1697, h1731, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                      · linarith only [h1730, h1731, hc34, hlam, hphi, ht45, u5elo3]
                    · linarith only [h1702, h1703, h1730, hc13, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h0, h1729, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                · linarith only [h0, h1699, h1728, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
              · linarith only [h0, h1699, h1727, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1738 | h1738
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1739 | h1739
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1740 | h1740
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1741 | h1741
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1742 | h1742
                    · linarith only [h0, h1697, h1702, h1742, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1744 | h1744
                      · linarith only [h0, h1698, h1742, h1744, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1746 | h1746
                        · linarith only [h0, h1698, h1746, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1748 | h1748
                          · linarith only [h1702, h1738, h1739, h1742, h1746, h1748, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1750 | h1750
                            · linarith only [h0, h1698, h1738, h1739, h1742, h1746, h1750, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1752 | h1752
                              · linarith only [h1740, h1746, h1752, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1754 | h1754
                                · rcases h1bigk with h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c | h1755c
                                  · have p1755_0 := h1755c.1
                                    have p1755_1 := h1755c.2.1
                                    have p1755_2 := h1755c.2.2.1
                                    have p1755_3 := h1755c.2.2.2
                                    linarith only [hlam, p1755_0]
                                  · have p1755_0 := h1755c.1
                                    have p1755_1 := h1755c.2.1
                                    have p1755_2 := h1755c.2.2.1
                                    have p1755_3 := h1755c.2.2.2
                                    linarith only [h0, hlam, p1755_0]
                                  · have p1755_0 := h1755c.1
                                    have p1755_1 := h1755c.2.1
                                    have p1755_2 := h1755c.2.2.1
                                    have p1755_3 := h1755c.2.2.2
                                    rcases p1755_3 (m.d 0 1) (by simp) with h1758 | h1758
                                    · rcases p1755_3 (m.d 1 2) (by simp) with h1759 | h1759
                                      · rcases p1755_3 (m.d 1 3) (by simp) with h1760 | h1760
                                        · linarith only [h1760, hlam, p1755_0]
                                        · rcases p1755_3 (m.d 1 4) (by simp) with h1762 | h1762
                                          · linarith only [h1698, h1762, hlam]
                                          · linarith only [h1742, h1762, hlam]
                                      · linarith only [h1739, h1759, hlam]
                                    · linarith only [h1758, hlam, p1755_0]
                                  · have p1755_0 := h1755c.1
                                    have p1755_1 := h1755c.2.1
                                    have p1755_2 := h1755c.2.2.1
                                    have p1755_3 := h1755c.2.2.2
                                    rcases p1755_3 (m.d 0 1) (by simp) with h1767 | h1767
                                    · rcases p1755_3 (m.d 1 2) (by simp) with h1768 | h1768
                                      · rcases p1755_3 (m.d 1 3) (by simp) with h1769 | h1769
                                        · linarith only [h1697, h1769, hlam]
                                        · rcases p1755_3 (m.d 1 4) (by simp) with h1771 | h1771
                                          · linarith only [h1771, hlam, p1755_0]
                                          · rcases p1755_3 (m.d 1 5) (by simp) with h1773 | h1773
                                            · linarith only [h1699, h1773, hlam]
                                            · linarith only [h1746, h1773, hlam]
                                      · linarith only [h1740, h1768, hlam]
                                    · linarith only [h1767, hlam, p1755_0]
                                  · have p1755_0 := h1755c.1
                                    have p1755_1 := h1755c.2.1
                                    have p1755_2 := h1755c.2.2.1
                                    have p1755_3 := h1755c.2.2.2
                                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p1755_1, u5ehi6]
                                  · have p1755_0 := h1755c.1
                                    have p1755_1 := h1755c.2.1
                                    have p1755_2 := h1755c.2.2.1
                                    have p1755_3 := h1755c.2.2.2
                                    linarith only [h1698, h1738, h1742, h1746, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1755_1]
                                  · have p1755_0 := h1755c.1
                                    have p1755_1 := h1755c.2.1
                                    have p1755_2 := h1755c.2.2.1
                                    have p1755_3 := h1755c.2.2.2
                                    linarith only [hlam, p1755_0]
                                  · have p1755_0 := h1755c.1
                                    have p1755_1 := h1755c.2.1
                                    have p1755_2 := h1755c.2.2.1
                                    have p1755_3 := h1755c.2.2.2
                                    linarith only [h0, h1698, h1738, h1742, h1746, hlam, p1755_2]
                                  · have p1755_0 := h1755c.1
                                    have p1755_1 := h1755c.2.1
                                    have p1755_2 := h1755c.2.2.1
                                    have p1755_3 := h1755c.2.2.2
                                    linarith only [h0, h1698, h1738, h1746, hlam, p1755_2]
                                  · have p1755_0 := h1755c.1
                                    have p1755_1 := h1755c.2.1
                                    have p1755_2 := h1755c.2.2.1
                                    have p1755_3 := h1755c.2.2.2
                                    rcases p1755_3 (m.d 0 1) (by simp) with h1783 | h1783
                                    · linarith only [h0, h1783, hlam]
                                    · linarith only [h1699, h1783, hlam]
                                  · have p1755_0 := h1755c.1
                                    have p1755_1 := h1755c.2.1
                                    have p1755_2 := h1755c.2.2.1
                                    have p1755_3 := h1755c.2.2.2
                                    linarith only [h1697, hlam, p1755_0]
                                  · have p1755_0 := h1755c.1
                                    have p1755_1 := h1755c.2.1
                                    have p1755_2 := h1755c.2.2.1
                                    have p1755_3 := h1755c.2.2.2
                                    linarith only [h1739, hlam, p1755_0]
                                  · have p1755_0 := h1755c.1
                                    have p1755_1 := h1755c.2.1
                                    have p1755_2 := h1755c.2.2.1
                                    have p1755_3 := h1755c.2.2.2
                                    linarith only [hlam, p1755_0]
                                  · have p1755_0 := h1755c.1
                                    have p1755_1 := h1755c.2.1
                                    have p1755_2 := h1755c.2.2.1
                                    have p1755_3 := h1755c.2.2.2
                                    linarith only [h1742, hlam, p1755_0]
                                  · have p1755_0 := h1755c.1
                                    have p1755_1 := h1755c.2.1
                                    have p1755_2 := h1755c.2.2.1
                                    have p1755_3 := h1755c.2.2.2
                                    linarith only [h1744, hlam, p1755_1]
                                  · have p1755_0 := h1755c.1
                                    have p1755_1 := h1755c.2.1
                                    have p1755_2 := h1755c.2.2.1
                                    have p1755_3 := h1755c.2.2.2
                                    linarith only [h1698, hlam, p1755_0]
                                  · have p1755_0 := h1755c.1
                                    have p1755_1 := h1755c.2.1
                                    have p1755_2 := h1755c.2.2.1
                                    have p1755_3 := h1755c.2.2.2
                                    linarith only [h1740, hlam, p1755_0]
                                  · have p1755_0 := h1755c.1
                                    have p1755_1 := h1755c.2.1
                                    have p1755_2 := h1755c.2.2.1
                                    have p1755_3 := h1755c.2.2.2
                                    linarith only [h1698, h1738, h1739, h1746, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1755_1]
                                  · have p1755_0 := h1755c.1
                                    have p1755_1 := h1755c.2.1
                                    have p1755_2 := h1755c.2.2.1
                                    have p1755_3 := h1755c.2.2.2
                                    linarith only [hlam, p1755_0]
                                  · have p1755_0 := h1755c.1
                                    have p1755_1 := h1755c.2.1
                                    have p1755_2 := h1755c.2.2.1
                                    have p1755_3 := h1755c.2.2.2
                                    linarith only [h1746, hlam, p1755_1]
                                  · have p1755_0 := h1755c.1
                                    have p1755_1 := h1755c.2.1
                                    have p1755_2 := h1755c.2.2.1
                                    have p1755_3 := h1755c.2.2.2
                                    linarith only [h1699, hlam, p1755_0]
                                  · have p1755_0 := h1755c.1
                                    have p1755_1 := h1755c.2.1
                                    have p1755_2 := h1755c.2.2.1
                                    have p1755_3 := h1755c.2.2.2
                                    linarith only [h1741, hlam, p1755_0]
                                  · have p1755_0 := h1755c.1
                                    have p1755_1 := h1755c.2.1
                                    have p1755_2 := h1755c.2.2.1
                                    have p1755_3 := h1755c.2.2.2
                                    linarith only [h1739, hc23, hlam, hphi, ht34, ht45, p1755_1, u5elo1]
                                  · have p1755_0 := h1755c.1
                                    have p1755_1 := h1755c.2.1
                                    have p1755_2 := h1755c.2.2.1
                                    have p1755_3 := h1755c.2.2.2
                                    linarith only [h0, h1698, h1738, h1746, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1755_1]
                                  · have p1755_0 := h1755c.1
                                    have p1755_1 := h1755c.2.1
                                    have p1755_2 := h1755c.2.2.1
                                    have p1755_3 := h1755c.2.2.2
                                    linarith only [hlam, p1755_0]
                                · linarith only [h1702, h1738, h1754, hlam]
                  · linarith only [h0, h1698, h1738, h1741, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                · linarith only [h0, h1698, h1738, h1740, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
              · linarith only [h0, h1698, h1738, h1739, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1805 | h1805
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1806 | h1806
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1807 | h1807
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1808 | h1808
                    · linarith only [h1697, h1702, h1808, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1810 | h1810
                      · linarith only [h0, h1697, h1810, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1812 | h1812
                        · linarith only [h1698, h1738, h1812, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1814 | h1814
                          · linarith only [h1697, h1702, h1805, h1814, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1816 | h1816
                            · linarith only [h1700, h1738, h1810, h1814, h1816, hc13, hlam, hphi, ht34, ht45, u5elo4]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1818 | h1818
                              · linarith only [h1698, h1738, h1806, h1818, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1820 | h1820
                                · rcases h1bigk with h1821c | h1821c | h1821c | h1821c | h1821c | h1821c | h1821c | h1821c | h1821c | h1821c | h1821c | h1821c | h1821c | h1821c | h1821c | h1821c | h1821c | h1821c | h1821c | h1821c | h1821c | h1821c | h1821c | h1821c | h1821c
                                  · have p1821_0 := h1821c.1
                                    have p1821_1 := h1821c.2.1
                                    have p1821_2 := h1821c.2.2.1
                                    have p1821_3 := h1821c.2.2.2
                                    linarith only [hlam, p1821_0]
                                  · have p1821_0 := h1821c.1
                                    have p1821_1 := h1821c.2.1
                                    have p1821_2 := h1821c.2.2.1
                                    have p1821_3 := h1821c.2.2.2
                                    linarith only [h0, hlam, p1821_0]
                                  · have p1821_0 := h1821c.1
                                    have p1821_1 := h1821c.2.1
                                    have p1821_2 := h1821c.2.2.1
                                    have p1821_3 := h1821c.2.2.2
                                    rcases p1821_3 (m.d 0 1) (by simp) with h1824 | h1824
                                    · rcases p1821_3 (m.d 1 2) (by simp) with h1825 | h1825
                                      · rcases p1821_3 (m.d 1 3) (by simp) with h1826 | h1826
                                        · linarith only [h1826, hlam, p1821_0]
                                        · rcases p1821_3 (m.d 1 4) (by simp) with h1828 | h1828
                                          · linarith only [h1698, h1828, hlam]
                                          · linarith only [h1808, h1828, hlam]
                                      · linarith only [h1805, h1825, hlam]
                                    · linarith only [h1824, hlam, p1821_0]
                                  · have p1821_0 := h1821c.1
                                    have p1821_1 := h1821c.2.1
                                    have p1821_2 := h1821c.2.2.1
                                    have p1821_3 := h1821c.2.2.2
                                    rcases p1821_3 (m.d 0 1) (by simp) with h1833 | h1833
                                    · rcases p1821_3 (m.d 1 2) (by simp) with h1834 | h1834
                                      · rcases p1821_3 (m.d 1 3) (by simp) with h1835 | h1835
                                        · linarith only [h1697, h1835, hlam]
                                        · rcases p1821_3 (m.d 1 4) (by simp) with h1837 | h1837
                                          · linarith only [h1837, hlam, p1821_0]
                                          · rcases p1821_3 (m.d 1 5) (by simp) with h1839 | h1839
                                            · linarith only [h1699, h1839, hlam]
                                            · linarith only [h1812, h1839, hlam]
                                      · linarith only [h1806, h1834, hlam]
                                    · linarith only [h1833, hlam, p1821_0]
                                  · have p1821_0 := h1821c.1
                                    have p1821_1 := h1821c.2.1
                                    have p1821_2 := h1821c.2.2.1
                                    have p1821_3 := h1821c.2.2.2
                                    linarith only [h0, h1807, hc12, hlam, hphi, ht01, ht0b, ht5b, p1821_1, u5ehi7]
                                  · have p1821_0 := h1821c.1
                                    have p1821_1 := h1821c.2.1
                                    have p1821_2 := h1821c.2.2.1
                                    have p1821_3 := h1821c.2.2.2
                                    linarith only [h1699, h1807, hc12, hlam, hphi, ht01, ht0b, ht5b, p1821_1, u5ehi7]
                                  · have p1821_0 := h1821c.1
                                    have p1821_1 := h1821c.2.1
                                    have p1821_2 := h1821c.2.2.1
                                    have p1821_3 := h1821c.2.2.2
                                    linarith only [hlam, p1821_0]
                                  · have p1821_0 := h1821c.1
                                    have p1821_1 := h1821c.2.1
                                    have p1821_2 := h1821c.2.2.1
                                    have p1821_3 := h1821c.2.2.2
                                    rcases p1821_3 (m.d 0 1) (by simp) with h1847 | h1847
                                    · linarith only [h0, h1847, hlam]
                                    · linarith only [h1697, h1847, hlam]
                                  · have p1821_0 := h1821c.1
                                    have p1821_1 := h1821c.2.1
                                    have p1821_2 := h1821c.2.2.1
                                    have p1821_3 := h1821c.2.2.2
                                    rcases p1821_3 (m.d 0 1) (by simp) with h1850 | h1850
                                    · linarith only [h0, h1850, hlam]
                                    · linarith only [h1698, h1850, hlam]
                                  · have p1821_0 := h1821c.1
                                    have p1821_1 := h1821c.2.1
                                    have p1821_2 := h1821c.2.2.1
                                    have p1821_3 := h1821c.2.2.2
                                    rcases p1821_3 (m.d 0 1) (by simp) with h1853 | h1853
                                    · linarith only [h0, h1853, hlam]
                                    · linarith only [h1699, h1853, hlam]
                                  · have p1821_0 := h1821c.1
                                    have p1821_1 := h1821c.2.1
                                    have p1821_2 := h1821c.2.2.1
                                    have p1821_3 := h1821c.2.2.2
                                    linarith only [h1697, hlam, p1821_0]
                                  · have p1821_0 := h1821c.1
                                    have p1821_1 := h1821c.2.1
                                    have p1821_2 := h1821c.2.2.1
                                    have p1821_3 := h1821c.2.2.2
                                    linarith only [h1805, hlam, p1821_0]
                                  · have p1821_0 := h1821c.1
                                    have p1821_1 := h1821c.2.1
                                    have p1821_2 := h1821c.2.2.1
                                    have p1821_3 := h1821c.2.2.2
                                    linarith only [hlam, p1821_0]
                                  · have p1821_0 := h1821c.1
                                    have p1821_1 := h1821c.2.1
                                    have p1821_2 := h1821c.2.2.1
                                    have p1821_3 := h1821c.2.2.2
                                    linarith only [h1808, hlam, p1821_0]
                                  · have p1821_0 := h1821c.1
                                    have p1821_1 := h1821c.2.1
                                    have p1821_2 := h1821c.2.2.1
                                    have p1821_3 := h1821c.2.2.2
                                    linarith only [h1810, hlam, p1821_1]
                                  · have p1821_0 := h1821c.1
                                    have p1821_1 := h1821c.2.1
                                    have p1821_2 := h1821c.2.2.1
                                    have p1821_3 := h1821c.2.2.2
                                    linarith only [h1698, hlam, p1821_0]
                                  · have p1821_0 := h1821c.1
                                    have p1821_1 := h1821c.2.1
                                    have p1821_2 := h1821c.2.2.1
                                    have p1821_3 := h1821c.2.2.2
                                    linarith only [h1806, hlam, p1821_0]
                                  · have p1821_0 := h1821c.1
                                    have p1821_1 := h1821c.2.1
                                    have p1821_2 := h1821c.2.2.1
                                    have p1821_3 := h1821c.2.2.2
                                    linarith only [h1698, h1738, h1820, hc13, hlam, hphi, ht34, ht45, p1821_1, u5elo3]
                                  · have p1821_0 := h1821c.1
                                    have p1821_1 := h1821c.2.1
                                    have p1821_2 := h1821c.2.2.1
                                    have p1821_3 := h1821c.2.2.2
                                    linarith only [hlam, p1821_0]
                                  · have p1821_0 := h1821c.1
                                    have p1821_1 := h1821c.2.1
                                    have p1821_2 := h1821c.2.2.1
                                    have p1821_3 := h1821c.2.2.2
                                    linarith only [h1812, hlam, p1821_1]
                                  · have p1821_0 := h1821c.1
                                    have p1821_1 := h1821c.2.1
                                    have p1821_2 := h1821c.2.2.1
                                    have p1821_3 := h1821c.2.2.2
                                    linarith only [h1699, hlam, p1821_0]
                                  · have p1821_0 := h1821c.1
                                    have p1821_1 := h1821c.2.1
                                    have p1821_2 := h1821c.2.2.1
                                    have p1821_3 := h1821c.2.2.2
                                    linarith only [h1807, hlam, p1821_0]
                                  · have p1821_0 := h1821c.1
                                    have p1821_1 := h1821c.2.1
                                    have p1821_2 := h1821c.2.2.1
                                    have p1821_3 := h1821c.2.2.2
                                    linarith only [h1805, hc23, hlam, hphi, ht34, ht45, p1821_1, u5elo1]
                                  · have p1821_0 := h1821c.1
                                    have p1821_1 := h1821c.2.1
                                    have p1821_2 := h1821c.2.2.1
                                    have p1821_3 := h1821c.2.2.2
                                    linarith only [h1699, h1738, h1820, hc14, hlam, hphi, ht45, p1821_1, u5elo3]
                                  · have p1821_0 := h1821c.1
                                    have p1821_1 := h1821c.2.1
                                    have p1821_2 := h1821c.2.2.1
                                    have p1821_3 := h1821c.2.2.2
                                    linarith only [hlam, p1821_0]
                                · linarith only [h1697, h1702, h1805, h1820, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h0, h1699, h1807, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
                · linarith only [h0, h1699, h1806, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
              · linarith only [h0, h1699, h1805, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
        · linarith only [h0, h1699, h1701, hlam, hphi, u5ehi6, u5elo2]
      · linarith only [h0, h1698, h1700, hlam]
    · linarith only [h1698, h1699, hc14, hlam, hphi, ht45, u5elo1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1878 | h1878
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1879 | h1879
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1880 | h1880
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1881 | h1881
          · linarith only [h1697, h1698, h1881, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1883 | h1883
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1884 | h1884
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1885 | h1885
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1886 | h1886
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1887 | h1887
                    · linarith only [h1697, h1698, h1881, h1885, h1887, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1889 | h1889
                      · linarith only [h1697, h1698, h1887, h1889, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi8]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1891 | h1891
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1892 | h1892
                          · linarith only [h1698, h1878, h1886, h1887, h1892, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi7]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1894 | h1894
                            · linarith only [h1697, h1698, h1884, h1887, h1894, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi8]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1896 | h1896
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1897 | h1897
                                · rcases h1bigk with h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c | h1898c
                                  · have p1898_0 := h1898c.1
                                    have p1898_1 := h1898c.2.1
                                    have p1898_2 := h1898c.2.2.1
                                    have p1898_3 := h1898c.2.2.2
                                    linarith only [hlam, p1898_0]
                                  · have p1898_0 := h1898c.1
                                    have p1898_1 := h1898c.2.1
                                    have p1898_2 := h1898c.2.2.1
                                    have p1898_3 := h1898c.2.2.2
                                    linarith only [h0, hlam, p1898_0]
                                  · have p1898_0 := h1898c.1
                                    have p1898_1 := h1898c.2.1
                                    have p1898_2 := h1898c.2.2.1
                                    have p1898_3 := h1898c.2.2.2
                                    linarith only [h1698, h1887, hc13, hc34, hlam, hphi, p1898_1]
                                  · have p1898_0 := h1898c.1
                                    have p1898_1 := h1898c.2.1
                                    have p1898_2 := h1898c.2.2.1
                                    have p1898_3 := h1898c.2.2.2
                                    linarith only [h1698, hlam, p1898_0]
                                  · have p1898_0 := h1898c.1
                                    have p1898_1 := h1898c.2.1
                                    have p1898_2 := h1898c.2.2.1
                                    have p1898_3 := h1898c.2.2.2
                                    linarith only [h1698, h1886, h1887, h1896, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1898_1, u5ehi9]
                                  · have p1898_0 := h1898c.1
                                    have p1898_1 := h1898c.2.1
                                    have p1898_2 := h1898c.2.2.1
                                    have p1898_3 := h1898c.2.2.2
                                    linarith only [h1878, h1886, h1896, hc12, hlam, hphi, ht01, ht0b, ht5b, p1898_1, u5ehi9]
                                  · have p1898_0 := h1898c.1
                                    have p1898_1 := h1898c.2.1
                                    have p1898_2 := h1898c.2.2.1
                                    have p1898_3 := h1898c.2.2.2
                                    linarith only [hlam, p1898_0]
                                  · have p1898_0 := h1898c.1
                                    have p1898_1 := h1898c.2.1
                                    have p1898_2 := h1898c.2.2.1
                                    have p1898_3 := h1898c.2.2.2
                                    rcases p1898_3 (m.d 0 1) (by simp) with h1906 | h1906
                                    · linarith only [h0, h1906, hlam]
                                    · linarith only [h1697, h1906, hlam]
                                  · have p1898_0 := h1898c.1
                                    have p1898_1 := h1898c.2.1
                                    have p1898_2 := h1898c.2.2.1
                                    have p1898_3 := h1898c.2.2.2
                                    linarith only [h1698, h1878, h1886, h1896, hc12, hlam, hphi, ht01, ht0b, ht5b, p1898_1, u5ehi9]
                                  · have p1898_0 := h1898c.1
                                    have p1898_1 := h1898c.2.1
                                    have p1898_2 := h1898c.2.2.1
                                    have p1898_3 := h1898c.2.2.2
                                    rcases p1898_3 (m.d 0 1) (by simp) with h1910 | h1910
                                    · linarith only [h0, h1910, hlam]
                                    · linarith only [h1878, h1910, hlam]
                                  · have p1898_0 := h1898c.1
                                    have p1898_1 := h1898c.2.1
                                    have p1898_2 := h1898c.2.2.1
                                    have p1898_3 := h1898c.2.2.2
                                    linarith only [h1697, hlam, p1898_0]
                                  · have p1898_0 := h1898c.1
                                    have p1898_1 := h1898c.2.1
                                    have p1898_2 := h1898c.2.2.1
                                    have p1898_3 := h1898c.2.2.2
                                    linarith only [h1884, hlam, p1898_0]
                                  · have p1898_0 := h1898c.1
                                    have p1898_1 := h1898c.2.1
                                    have p1898_2 := h1898c.2.2.1
                                    have p1898_3 := h1898c.2.2.2
                                    linarith only [hlam, p1898_0]
                                  · have p1898_0 := h1898c.1
                                    have p1898_1 := h1898c.2.1
                                    have p1898_2 := h1898c.2.2.1
                                    have p1898_3 := h1898c.2.2.2
                                    linarith only [h1887, hlam, p1898_0]
                                  · have p1898_0 := h1898c.1
                                    have p1898_1 := h1898c.2.1
                                    have p1898_2 := h1898c.2.2.1
                                    have p1898_3 := h1898c.2.2.2
                                    linarith only [h1889, hlam, p1898_1]
                                  · have p1898_0 := h1898c.1
                                    have p1898_1 := h1898c.2.1
                                    have p1898_2 := h1898c.2.2.1
                                    have p1898_3 := h1898c.2.2.2
                                    linarith only [h1878, h1886, h1896, hc14, hlam, hphi, ht01, ht0b, ht5b, p1898_1, u5ehi9]
                                  · have p1898_0 := h1898c.1
                                    have p1898_1 := h1898c.2.1
                                    have p1898_2 := h1898c.2.2.1
                                    have p1898_3 := h1898c.2.2.2
                                    linarith only [h1885, hlam, p1898_0]
                                  · have p1898_0 := h1898c.1
                                    have p1898_1 := h1898c.2.1
                                    have p1898_2 := h1898c.2.2.1
                                    have p1898_3 := h1898c.2.2.2
                                    rcases p1898_3 (m.d 0 1) (by simp) with h1920 | h1920
                                    · linarith only [h1698, h1920, hlam]
                                    · linarith only [h1697, h1920, hlam]
                                  · have p1898_0 := h1898c.1
                                    have p1898_1 := h1898c.2.1
                                    have p1898_2 := h1898c.2.2.1
                                    have p1898_3 := h1898c.2.2.2
                                    linarith only [hlam, p1898_0]
                                  · have p1898_0 := h1898c.1
                                    have p1898_1 := h1898c.2.1
                                    have p1898_2 := h1898c.2.2.1
                                    have p1898_3 := h1898c.2.2.2
                                    rcases p1898_3 (m.d 0 1) (by simp) with h1924 | h1924
                                    · linarith only [h1698, h1924, hlam]
                                    · linarith only [h1878, h1924, hlam]
                                  · have p1898_0 := h1898c.1
                                    have p1898_1 := h1898c.2.1
                                    have p1898_2 := h1898c.2.2.1
                                    have p1898_3 := h1898c.2.2.2
                                    linarith only [h1878, hlam, p1898_0]
                                  · have p1898_0 := h1898c.1
                                    have p1898_1 := h1898c.2.1
                                    have p1898_2 := h1898c.2.2.1
                                    have p1898_3 := h1898c.2.2.2
                                    linarith only [h1886, hlam, p1898_0]
                                  · have p1898_0 := h1898c.1
                                    have p1898_1 := h1898c.2.1
                                    have p1898_2 := h1898c.2.2.1
                                    have p1898_3 := h1898c.2.2.2
                                    linarith only [hc13, hlam, hphi, ht34, ht45, p1898_1, u5elo1]
                                  · have p1898_0 := h1898c.1
                                    have p1898_1 := h1898c.2.1
                                    have p1898_2 := h1898c.2.2.1
                                    have p1898_3 := h1898c.2.2.2
                                    linarith only [h1891, hlam, p1898_0]
                                  · have p1898_0 := h1898c.1
                                    have p1898_1 := h1898c.2.1
                                    have p1898_2 := h1898c.2.2.1
                                    have p1898_3 := h1898c.2.2.2
                                    linarith only [hlam, p1898_0]
                                · linarith only [h1698, h1878, h1886, h1887, h1896, h1897, hlam]
                              · linarith only [h1698, h1878, h1887, h1891, h1892, h1896, hc23, hc34, hlam, hphi]
                        · linarith only [h1698, h1878, h1886, h1891, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi7]
                  · linarith only [h0, h1878, h1886, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
                · linarith only [h0, h1878, h1885, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
              · linarith only [h0, h1878, h1884, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
            · linarith only [h1698, h1878, h1883, hlam, hphi, u5ehi6, u5elo4]
        · linarith only [h1879, h1880, hc24, hlam, hphi, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1940 | h1940
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1941 | h1941
          · linarith only [h0, h1697, h1879, h1941, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1943 | h1943
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1944 | h1944
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1945 | h1945
                · linarith only [h0, h1878, h1879, h1945, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi6]
                · linarith only [h0, h1878, h1945, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
              · linarith only [h0, h1878, h1944, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
            · linarith only [h0, h1878, h1879, h1943, hlam, hphi, u5ehi6, u5elo4]
        · linarith only [h0, h1878, h1940, hlam, hphi, u5ehi6, u5elo2]
    · linarith only [h1697, h1878, hc13, hlam, hphi, ht34, ht45, u5elo1]

set_option maxHeartbeats 6588000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_LR_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1697 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1952 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1953 | h1953
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1954 | h1954
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1955 | h1955
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1956 | h1956
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1957 | h1957
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1958 | h1958
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1959 | h1959
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1960 | h1960
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1961 | h1961
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1962 | h1962
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1963 | h1963
                      · linarith only [h1697, h1952, h1958, h1963, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1965 | h1965
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1966 | h1966
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1967 | h1967
                            · linarith only [h1959, h1963, h1967, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1969 | h1969
                              · linarith only [h1959, h1963, h1965, h1969, hlam]
                              · rcases h1bigk with h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c | h1971c
                                · have p1971_0 := h1971c.1
                                  have p1971_1 := h1971c.2.1
                                  have p1971_2 := h1971c.2.2.1
                                  have p1971_3 := h1971c.2.2.2
                                  linarith only [hlam, p1971_0]
                                · have p1971_0 := h1971c.1
                                  have p1971_1 := h1971c.2.1
                                  have p1971_2 := h1971c.2.2.1
                                  have p1971_3 := h1971c.2.2.2
                                  linarith only [h0, hlam, p1971_0]
                                · have p1971_0 := h1971c.1
                                  have p1971_1 := h1971c.2.1
                                  have p1971_2 := h1971c.2.2.1
                                  have p1971_3 := h1971c.2.2.2
                                  linarith only [h1697, hlam, p1971_0]
                                · have p1971_0 := h1971c.1
                                  have p1971_1 := h1971c.2.1
                                  have p1971_2 := h1971c.2.2.1
                                  have p1971_3 := h1971c.2.2.2
                                  rcases p1971_3 (m.d 0 1) (by simp) with h1975 | h1975
                                  · rcases p1971_3 (m.d 1 2) (by simp) with h1976 | h1976
                                    · rcases p1971_3 (m.d 1 3) (by simp) with h1977 | h1977
                                      · rcases p1971_3 (m.d 1 4) (by simp) with h1978 | h1978
                                        · linarith only [h1978, hlam, p1971_0]
                                        · rcases p1971_3 (m.d 1 5) (by simp) with h1980 | h1980
                                          · linarith only [h1953, h1980, hlam]
                                          · linarith only [h1963, h1980, hlam]
                                      · linarith only [h1961, h1977, hlam]
                                    · linarith only [h1959, h1976, hlam]
                                  · linarith only [h1975, hlam, p1971_0]
                                · have p1971_0 := h1971c.1
                                  have p1971_1 := h1971c.2.1
                                  have p1971_2 := h1971c.2.2.1
                                  have p1971_3 := h1971c.2.2.2
                                  linarith only [h1697, h1958, h1960, h1966, hc12, hlam, hphi, ht01, ht0b, ht5b, p1971_1, u5ehi8]
                                · have p1971_0 := h1971c.1
                                  have p1971_1 := h1971c.2.1
                                  have p1971_2 := h1971c.2.2.1
                                  have p1971_3 := h1971c.2.2.2
                                  linarith only [h1952, h1957, h1959, h1963, h1965, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1971_1]
                                · have p1971_0 := h1971c.1
                                  have p1971_1 := h1971c.2.1
                                  have p1971_2 := h1971c.2.2.1
                                  have p1971_3 := h1971c.2.2.2
                                  linarith only [hlam, p1971_0]
                                · have p1971_0 := h1971c.1
                                  have p1971_1 := h1971c.2.1
                                  have p1971_2 := h1971c.2.2.1
                                  have p1971_3 := h1971c.2.2.2
                                  linarith only [h1697, h1952, h1957, h1959, h1963, h1965, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1971_1]
                                · have p1971_0 := h1971c.1
                                  have p1971_1 := h1971c.2.1
                                  have p1971_2 := h1971c.2.2.1
                                  have p1971_3 := h1971c.2.2.2
                                  linarith only [h0, h1952, h1957, h1963, hlam, p1971_2]
                                · have p1971_0 := h1971c.1
                                  have p1971_1 := h1971c.2.1
                                  have p1971_2 := h1971c.2.2.1
                                  have p1971_3 := h1971c.2.2.2
                                  rcases p1971_3 (m.d 0 1) (by simp) with h1991 | h1991
                                  · linarith only [h0, h1991, hlam]
                                  · linarith only [h1953, h1991, hlam]
                                · have p1971_0 := h1971c.1
                                  have p1971_1 := h1971c.2.1
                                  have p1971_2 := h1971c.2.2.1
                                  have p1971_3 := h1971c.2.2.2
                                  linarith only [h1952, h1957, h1958, h1959, h1963, h1965, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1971_1]
                                · have p1971_0 := h1971c.1
                                  have p1971_1 := h1971c.2.1
                                  have p1971_2 := h1971c.2.2.1
                                  have p1971_3 := h1971c.2.2.2
                                  linarith only [h1958, hlam, p1971_0]
                                · have p1971_0 := h1971c.1
                                  have p1971_1 := h1971c.2.1
                                  have p1971_2 := h1971c.2.2.1
                                  have p1971_3 := h1971c.2.2.2
                                  linarith only [hlam, p1971_0]
                                · have p1971_0 := h1971c.1
                                  have p1971_1 := h1971c.2.1
                                  have p1971_2 := h1971c.2.2.1
                                  have p1971_3 := h1971c.2.2.2
                                  linarith only [h1697, h1952, h1957, h1963, hlam, p1971_2]
                                · have p1971_0 := h1971c.1
                                  have p1971_1 := h1971c.2.1
                                  have p1971_2 := h1971c.2.2.1
                                  have p1971_3 := h1971c.2.2.2
                                  rcases p1971_3 (m.d 0 1) (by simp) with h1998 | h1998
                                  · linarith only [h1697, h1998, hlam]
                                  · linarith only [h1953, h1998, hlam]
                                · have p1971_0 := h1971c.1
                                  have p1971_1 := h1971c.2.1
                                  have p1971_2 := h1971c.2.2.1
                                  have p1971_3 := h1971c.2.2.2
                                  linarith only [h1952, hlam, p1971_0]
                                · have p1971_0 := h1971c.1
                                  have p1971_1 := h1971c.2.1
                                  have p1971_2 := h1971c.2.2.1
                                  have p1971_3 := h1971c.2.2.2
                                  linarith only [h1959, hlam, p1971_0]
                                · have p1971_0 := h1971c.1
                                  have p1971_1 := h1971c.2.1
                                  have p1971_2 := h1971c.2.2.1
                                  have p1971_3 := h1971c.2.2.2
                                  linarith only [h1961, hlam, p1971_1]
                                · have p1971_0 := h1971c.1
                                  have p1971_1 := h1971c.2.1
                                  have p1971_2 := h1971c.2.2.1
                                  have p1971_3 := h1971c.2.2.2
                                  linarith only [hlam, p1971_0]
                                · have p1971_0 := h1971c.1
                                  have p1971_1 := h1971c.2.1
                                  have p1971_2 := h1971c.2.2.1
                                  have p1971_3 := h1971c.2.2.2
                                  linarith only [h1963, hlam, p1971_1]
                                · have p1971_0 := h1971c.1
                                  have p1971_1 := h1971c.2.1
                                  have p1971_2 := h1971c.2.2.1
                                  have p1971_3 := h1971c.2.2.2
                                  linarith only [h1953, hlam, p1971_0]
                                · have p1971_0 := h1971c.1
                                  have p1971_1 := h1971c.2.1
                                  have p1971_2 := h1971c.2.2.1
                                  have p1971_3 := h1971c.2.2.2
                                  linarith only [h1960, hlam, p1971_0]
                                · have p1971_0 := h1971c.1
                                  have p1971_1 := h1971c.2.1
                                  have p1971_2 := h1971c.2.2.1
                                  have p1971_3 := h1971c.2.2.2
                                  linarith only [h1962, hlam, p1971_0]
                                · have p1971_0 := h1971c.1
                                  have p1971_1 := h1971c.2.1
                                  have p1971_2 := h1971c.2.2.1
                                  have p1971_3 := h1971c.2.2.2
                                  linarith only [h1959, h1965, hc34, hlam, hphi, ht45, p1971_1, u5elo1]
                                · have p1971_0 := h1971c.1
                                  have p1971_1 := h1971c.2.1
                                  have p1971_2 := h1971c.2.2.1
                                  have p1971_3 := h1971c.2.2.2
                                  linarith only [hlam, p1971_0]
                          · linarith only [h1697, h1952, h1957, h1962, h1963, h1965, h1966, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h1697, h1952, h1957, h1958, h1961, h1963, h1965, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h1697, h1962, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                  · linarith only [h1697, h1952, h1957, h1961, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
                · linarith only [h1697, h1952, h1957, h1958, h1960, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
              · linarith only [h1697, h1952, h1957, h1958, h1959, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
            · linarith only [h0, h1952, h1957, h1958, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2018 | h2018
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2019 | h2019
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2020 | h2020
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2021 | h2021
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2022 | h2022
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2023 | h2023
                      · linarith only [h1952, h1957, h2023, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2025 | h2025
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2026 | h2026
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2027 | h2027
                            · linarith only [h1952, h1957, h2019, h2027, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2029 | h2029
                              · linarith only [h1952, h1957, h2019, h2025, h2029, hlam]
                              · rcases h1bigk with h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c | h2031c
                                · have p2031_0 := h2031c.1
                                  have p2031_1 := h2031c.2.1
                                  have p2031_2 := h2031c.2.2.1
                                  have p2031_3 := h2031c.2.2.2
                                  linarith only [hlam, p2031_0]
                                · have p2031_0 := h2031c.1
                                  have p2031_1 := h2031c.2.1
                                  have p2031_2 := h2031c.2.2.1
                                  have p2031_3 := h2031c.2.2.2
                                  linarith only [h0, hlam, p2031_0]
                                · have p2031_0 := h2031c.1
                                  have p2031_1 := h2031c.2.1
                                  have p2031_2 := h2031c.2.2.1
                                  have p2031_3 := h2031c.2.2.2
                                  linarith only [h1697, hlam, p2031_0]
                                · have p2031_0 := h2031c.1
                                  have p2031_1 := h2031c.2.1
                                  have p2031_2 := h2031c.2.2.1
                                  have p2031_3 := h2031c.2.2.2
                                  rcases p2031_3 (m.d 0 1) (by simp) with h2035 | h2035
                                  · rcases p2031_3 (m.d 1 2) (by simp) with h2036 | h2036
                                    · rcases p2031_3 (m.d 1 3) (by simp) with h2037 | h2037
                                      · rcases p2031_3 (m.d 1 4) (by simp) with h2038 | h2038
                                        · linarith only [h2038, hlam, p2031_0]
                                        · rcases p2031_3 (m.d 1 5) (by simp) with h2040 | h2040
                                          · linarith only [h1953, h2040, hlam]
                                          · linarith only [h2023, h2040, hlam]
                                      · linarith only [h2021, h2037, hlam]
                                    · linarith only [h2019, h2036, hlam]
                                  · linarith only [h2035, hlam, p2031_0]
                                · have p2031_0 := h2031c.1
                                  have p2031_1 := h2031c.2.1
                                  have p2031_2 := h2031c.2.2.1
                                  have p2031_3 := h2031c.2.2.2
                                  linarith only [h1697, h2018, h2020, h2026, hc12, hlam, hphi, ht01, ht0b, ht5b, p2031_1, u5ehi8]
                                · have p2031_0 := h2031c.1
                                  have p2031_1 := h2031c.2.1
                                  have p2031_2 := h2031c.2.2.1
                                  have p2031_3 := h2031c.2.2.2
                                  linarith only [h1953, h2020, h2026, hc12, hlam, hphi, ht01, ht0b, ht5b, p2031_1, u5ehi8]
                                · have p2031_0 := h2031c.1
                                  have p2031_1 := h2031c.2.1
                                  have p2031_2 := h2031c.2.2.1
                                  have p2031_3 := h2031c.2.2.2
                                  linarith only [hlam, p2031_0]
                                · have p2031_0 := h2031c.1
                                  have p2031_1 := h2031c.2.1
                                  have p2031_2 := h2031c.2.2.1
                                  have p2031_3 := h2031c.2.2.2
                                  linarith only [h1697, hc01, hc12, hlam, hphi, p2031_1]
                                · have p2031_0 := h2031c.1
                                  have p2031_1 := h2031c.2.1
                                  have p2031_2 := h2031c.2.2.1
                                  have p2031_3 := h2031c.2.2.2
                                  rcases p2031_3 (m.d 0 1) (by simp) with h2050 | h2050
                                  · linarith only [h0, h2050, hlam]
                                  · linarith only [h1952, h2050, hlam]
                                · have p2031_0 := h2031c.1
                                  have p2031_1 := h2031c.2.1
                                  have p2031_2 := h2031c.2.2.1
                                  have p2031_3 := h2031c.2.2.2
                                  rcases p2031_3 (m.d 0 1) (by simp) with h2053 | h2053
                                  · linarith only [h0, h2053, hlam]
                                  · linarith only [h1953, h2053, hlam]
                                · have p2031_0 := h2031c.1
                                  have p2031_1 := h2031c.2.1
                                  have p2031_2 := h2031c.2.2.1
                                  have p2031_3 := h2031c.2.2.2
                                  linarith only [h1953, h2020, h2026, hc13, hlam, hphi, ht01, ht0b, ht5b, p2031_1, u5ehi8]
                                · have p2031_0 := h2031c.1
                                  have p2031_1 := h2031c.2.1
                                  have p2031_2 := h2031c.2.2.1
                                  have p2031_3 := h2031c.2.2.2
                                  linarith only [h2018, hlam, p2031_0]
                                · have p2031_0 := h2031c.1
                                  have p2031_1 := h2031c.2.1
                                  have p2031_2 := h2031c.2.2.1
                                  have p2031_3 := h2031c.2.2.2
                                  linarith only [hlam, p2031_0]
                                · have p2031_0 := h2031c.1
                                  have p2031_1 := h2031c.2.1
                                  have p2031_2 := h2031c.2.2.1
                                  have p2031_3 := h2031c.2.2.2
                                  rcases p2031_3 (m.d 0 1) (by simp) with h2059 | h2059
                                  · linarith only [h1697, h2059, hlam]
                                  · linarith only [h1952, h2059, hlam]
                                · have p2031_0 := h2031c.1
                                  have p2031_1 := h2031c.2.1
                                  have p2031_2 := h2031c.2.2.1
                                  have p2031_3 := h2031c.2.2.2
                                  rcases p2031_3 (m.d 0 1) (by simp) with h2062 | h2062
                                  · linarith only [h1697, h2062, hlam]
                                  · linarith only [h1953, h2062, hlam]
                                · have p2031_0 := h2031c.1
                                  have p2031_1 := h2031c.2.1
                                  have p2031_2 := h2031c.2.2.1
                                  have p2031_3 := h2031c.2.2.2
                                  linarith only [h1952, hlam, p2031_0]
                                · have p2031_0 := h2031c.1
                                  have p2031_1 := h2031c.2.1
                                  have p2031_2 := h2031c.2.2.1
                                  have p2031_3 := h2031c.2.2.2
                                  linarith only [h2019, hlam, p2031_0]
                                · have p2031_0 := h2031c.1
                                  have p2031_1 := h2031c.2.1
                                  have p2031_2 := h2031c.2.2.1
                                  have p2031_3 := h2031c.2.2.2
                                  linarith only [h2021, hlam, p2031_1]
                                · have p2031_0 := h2031c.1
                                  have p2031_1 := h2031c.2.1
                                  have p2031_2 := h2031c.2.2.1
                                  have p2031_3 := h2031c.2.2.2
                                  linarith only [hlam, p2031_0]
                                · have p2031_0 := h2031c.1
                                  have p2031_1 := h2031c.2.1
                                  have p2031_2 := h2031c.2.2.1
                                  have p2031_3 := h2031c.2.2.2
                                  linarith only [h2023, hlam, p2031_1]
                                · have p2031_0 := h2031c.1
                                  have p2031_1 := h2031c.2.1
                                  have p2031_2 := h2031c.2.2.1
                                  have p2031_3 := h2031c.2.2.2
                                  linarith only [h1953, hlam, p2031_0]
                                · have p2031_0 := h2031c.1
                                  have p2031_1 := h2031c.2.1
                                  have p2031_2 := h2031c.2.2.1
                                  have p2031_3 := h2031c.2.2.2
                                  linarith only [h2020, hlam, p2031_0]
                                · have p2031_0 := h2031c.1
                                  have p2031_1 := h2031c.2.1
                                  have p2031_2 := h2031c.2.2.1
                                  have p2031_3 := h2031c.2.2.2
                                  linarith only [h2022, hlam, p2031_0]
                                · have p2031_0 := h2031c.1
                                  have p2031_1 := h2031c.2.1
                                  have p2031_2 := h2031c.2.2.1
                                  have p2031_3 := h2031c.2.2.2
                                  linarith only [hc14, hlam, hphi, ht45, p2031_1, u5elo1]
                                · have p2031_0 := h2031c.1
                                  have p2031_1 := h2031c.2.1
                                  have p2031_2 := h2031c.2.2.1
                                  have p2031_3 := h2031c.2.2.2
                                  linarith only [hlam, p2031_0]
                          · linarith only [h1697, h1953, h2018, h2022, h2025, h2026, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h1956, h1957, h2025, hc23, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h1697, h1953, h2022, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi6]
                  · linarith only [h1697, h1953, h2020, h2021, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                · linarith only [h0, h1953, h2020, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
              · linarith only [h0, h1953, h2019, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
            · linarith only [h0, h1953, h2018, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
        · linarith only [h1697, h1952, h1956, hlam]
      · linarith only [h0, h1953, h1955, hlam, hphi, u5ehi6, u5elo2]
    · linarith only [h0, h1952, h1954, hlam]
  · linarith only [h1952, h1953, hc14, hlam, hphi, ht45, u5elo1]

set_option maxHeartbeats 6588000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_LR_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1697 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1952 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2086 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h2087 | h2087
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2088 | h2088
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2089 | h2089
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2090 | h2090
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2091 | h2091
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2092 | h2092
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2093 | h2093
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2094 | h2094
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2095 | h2095
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2096 | h2096
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2097 | h2097
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2098 | h2098
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2099 | h2099
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2100 | h2100
                            · linarith only [h2091, h2097, h2100, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                            · rcases h1bigk with h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [hlam, p2102_0]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [h0, hlam, p2102_0]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [h1697, hlam, p2102_0]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [h1952, hlam, p2102_0]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [h1952, h2093, h2094, h2099, h2100, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2102_1]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [h2086, h2093, h2099, h2100, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2102_1]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [hlam, p2102_0]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [h1697, h2086, h2093, h2099, h2100, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2102_1]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [h1952, h2086, h2093, h2099, h2100, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2102_1]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                rcases p2102_3 (m.d 0 1) (by simp) with h2112 | h2112
                                · linarith only [h0, h2112, hlam]
                                · linarith only [h2086, h2112, hlam]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [h2086, h2093, h2099, h2100, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2102_1]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [h2091, hlam, p2102_0]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [hlam, p2102_0]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [h1952, h2086, h2091, h2093, h2099, h2100, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2102_1]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                rcases p2102_3 (m.d 0 1) (by simp) with h2119 | h2119
                                · linarith only [h1697, h2119, hlam]
                                · linarith only [h2086, h2119, hlam]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [h2086, h2093, h2099, h2100, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2102_1]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [h2092, hlam, p2102_0]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [h2094, hlam, p2102_1]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [hlam, p2102_0]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                rcases p2102_3 (m.d 0 1) (by simp) with h2126 | h2126
                                · linarith only [h1952, h2126, hlam]
                                · linarith only [h2086, h2126, hlam]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [h2086, hlam, p2102_0]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [h2093, hlam, p2102_0]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [h2095, hlam, p2102_0]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [h2096, hlam, p2102_0]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [hlam, p2102_0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2134 | h2134
                            · linarith only [h2097, h2099, h2134, hlam]
                            · rcases h1bigk with h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c | h2136c
                              · have p2136_0 := h2136c.1
                                have p2136_1 := h2136c.2.1
                                have p2136_2 := h2136c.2.2.1
                                have p2136_3 := h2136c.2.2.2
                                linarith only [hlam, p2136_0]
                              · have p2136_0 := h2136c.1
                                have p2136_1 := h2136c.2.1
                                have p2136_2 := h2136c.2.2.1
                                have p2136_3 := h2136c.2.2.2
                                linarith only [h0, hlam, p2136_0]
                              · have p2136_0 := h2136c.1
                                have p2136_1 := h2136c.2.1
                                have p2136_2 := h2136c.2.2.1
                                have p2136_3 := h2136c.2.2.2
                                linarith only [h1697, hlam, p2136_0]
                              · have p2136_0 := h2136c.1
                                have p2136_1 := h2136c.2.1
                                have p2136_2 := h2136c.2.2.1
                                have p2136_3 := h2136c.2.2.2
                                linarith only [h1952, hlam, p2136_0]
                              · have p2136_0 := h2136c.1
                                have p2136_1 := h2136c.2.1
                                have p2136_2 := h2136c.2.2.1
                                have p2136_3 := h2136c.2.2.2
                                linarith only [h0, h2096, h2097, h2099, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2136_1]
                              · have p2136_0 := h2136c.1
                                have p2136_1 := h2136c.2.1
                                have p2136_2 := h2136c.2.2.1
                                have p2136_3 := h2136c.2.2.2
                                linarith only [h2086, h2096, h2097, h2099, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2136_1]
                              · have p2136_0 := h2136c.1
                                have p2136_1 := h2136c.2.1
                                have p2136_2 := h2136c.2.2.1
                                have p2136_3 := h2136c.2.2.2
                                linarith only [hlam, p2136_0]
                              · have p2136_0 := h2136c.1
                                have p2136_1 := h2136c.2.1
                                have p2136_2 := h2136c.2.2.1
                                have p2136_3 := h2136c.2.2.2
                                linarith only [h1697, h2086, h2096, h2097, h2099, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2136_1]
                              · have p2136_0 := h2136c.1
                                have p2136_1 := h2136c.2.1
                                have p2136_2 := h2136c.2.2.1
                                have p2136_3 := h2136c.2.2.2
                                linarith only [h1952, h2086, h2096, h2097, h2099, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2136_1]
                              · have p2136_0 := h2136c.1
                                have p2136_1 := h2136c.2.1
                                have p2136_2 := h2136c.2.2.1
                                have p2136_3 := h2136c.2.2.2
                                rcases p2136_3 (m.d 0 1) (by simp) with h2146 | h2146
                                · linarith only [h0, h2146, hlam]
                                · linarith only [h2086, h2146, hlam]
                              · have p2136_0 := h2136c.1
                                have p2136_1 := h2136c.2.1
                                have p2136_2 := h2136c.2.2.1
                                have p2136_3 := h2136c.2.2.2
                                linarith only [h2086, h2096, h2097, h2099, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2136_1]
                              · have p2136_0 := h2136c.1
                                have p2136_1 := h2136c.2.1
                                have p2136_2 := h2136c.2.2.1
                                have p2136_3 := h2136c.2.2.2
                                linarith only [h2091, hlam, p2136_0]
                              · have p2136_0 := h2136c.1
                                have p2136_1 := h2136c.2.1
                                have p2136_2 := h2136c.2.2.1
                                have p2136_3 := h2136c.2.2.2
                                linarith only [hlam, p2136_0]
                              · have p2136_0 := h2136c.1
                                have p2136_1 := h2136c.2.1
                                have p2136_2 := h2136c.2.2.1
                                have p2136_3 := h2136c.2.2.2
                                linarith only [h1952, h2086, h2091, h2096, h2097, h2099, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2136_1]
                              · have p2136_0 := h2136c.1
                                have p2136_1 := h2136c.2.1
                                have p2136_2 := h2136c.2.2.1
                                have p2136_3 := h2136c.2.2.2
                                rcases p2136_3 (m.d 0 1) (by simp) with h2153 | h2153
                                · linarith only [h1697, h2153, hlam]
                                · linarith only [h2086, h2153, hlam]
                              · have p2136_0 := h2136c.1
                                have p2136_1 := h2136c.2.1
                                have p2136_2 := h2136c.2.2.1
                                have p2136_3 := h2136c.2.2.2
                                linarith only [h2086, h2096, h2097, h2099, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2136_1]
                              · have p2136_0 := h2136c.1
                                have p2136_1 := h2136c.2.1
                                have p2136_2 := h2136c.2.2.1
                                have p2136_3 := h2136c.2.2.2
                                linarith only [h2092, hlam, p2136_0]
                              · have p2136_0 := h2136c.1
                                have p2136_1 := h2136c.2.1
                                have p2136_2 := h2136c.2.2.1
                                have p2136_3 := h2136c.2.2.2
                                linarith only [h2094, hlam, p2136_1]
                              · have p2136_0 := h2136c.1
                                have p2136_1 := h2136c.2.1
                                have p2136_2 := h2136c.2.2.1
                                have p2136_3 := h2136c.2.2.2
                                linarith only [hlam, p2136_0]
                              · have p2136_0 := h2136c.1
                                have p2136_1 := h2136c.2.1
                                have p2136_2 := h2136c.2.2.1
                                have p2136_3 := h2136c.2.2.2
                                rcases p2136_3 (m.d 0 1) (by simp) with h2160 | h2160
                                · linarith only [h1952, h2160, hlam]
                                · linarith only [h2086, h2160, hlam]
                              · have p2136_0 := h2136c.1
                                have p2136_1 := h2136c.2.1
                                have p2136_2 := h2136c.2.2.1
                                have p2136_3 := h2136c.2.2.2
                                linarith only [h2086, hlam, p2136_0]
                              · have p2136_0 := h2136c.1
                                have p2136_1 := h2136c.2.1
                                have p2136_2 := h2136c.2.2.1
                                have p2136_3 := h2136c.2.2.2
                                linarith only [h2093, hlam, p2136_0]
                              · have p2136_0 := h2136c.1
                                have p2136_1 := h2136c.2.1
                                have p2136_2 := h2136c.2.2.1
                                have p2136_3 := h2136c.2.2.2
                                linarith only [h2095, hlam, p2136_0]
                              · have p2136_0 := h2136c.1
                                have p2136_1 := h2136c.2.1
                                have p2136_2 := h2136c.2.2.1
                                have p2136_3 := h2136c.2.2.2
                                linarith only [h2096, hlam, p2136_0]
                              · have p2136_0 := h2136c.1
                                have p2136_1 := h2136c.2.1
                                have p2136_2 := h2136c.2.2.1
                                have p2136_3 := h2136c.2.2.2
                                linarith only [hlam, p2136_0]
                        · linarith only [h2095, h2097, h2098, hc34, hlam, hphi, ht45, u5elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2169 | h2169
                        · linarith only [h2089, h2097, h2169, hc03, hlam, hphi, ht0b, ht5b, u5ehi8]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2171 | h2171
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2172 | h2172
                            · rcases h1bigk with h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c | h2173c
                              · have p2173_0 := h2173c.1
                                have p2173_1 := h2173c.2.1
                                have p2173_2 := h2173c.2.2.1
                                have p2173_3 := h2173c.2.2.2
                                linarith only [hlam, p2173_0]
                              · have p2173_0 := h2173c.1
                                have p2173_1 := h2173c.2.1
                                have p2173_2 := h2173c.2.2.1
                                have p2173_3 := h2173c.2.2.2
                                linarith only [h0, hlam, p2173_0]
                              · have p2173_0 := h2173c.1
                                have p2173_1 := h2173c.2.1
                                have p2173_2 := h2173c.2.2.1
                                have p2173_3 := h2173c.2.2.2
                                linarith only [h1697, hlam, p2173_0]
                              · have p2173_0 := h2173c.1
                                have p2173_1 := h2173c.2.1
                                have p2173_2 := h2173c.2.2.1
                                have p2173_3 := h2173c.2.2.2
                                linarith only [h1952, hlam, p2173_0]
                              · have p2173_0 := h2173c.1
                                have p2173_1 := h2173c.2.1
                                have p2173_2 := h2173c.2.2.1
                                have p2173_3 := h2173c.2.2.2
                                linarith only [h1952, h2091, h2094, hc12, hlam, hphi, ht01, ht0b, ht5b, p2173_1, u5ehi6]
                              · have p2173_0 := h2173c.1
                                have p2173_1 := h2173c.2.1
                                have p2173_2 := h2173c.2.2.1
                                have p2173_3 := h2173c.2.2.2
                                linarith only [h2086, h2095, h2169, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2173_1]
                              · have p2173_0 := h2173c.1
                                have p2173_1 := h2173c.2.1
                                have p2173_2 := h2173c.2.2.1
                                have p2173_3 := h2173c.2.2.2
                                linarith only [hlam, p2173_0]
                              · have p2173_0 := h2173c.1
                                have p2173_1 := h2173c.2.1
                                have p2173_2 := h2173c.2.2.1
                                have p2173_3 := h2173c.2.2.2
                                linarith only [h1697, hc01, hc12, hlam, hphi, p2173_1]
                              · have p2173_0 := h2173c.1
                                have p2173_1 := h2173c.2.1
                                have p2173_2 := h2173c.2.2.1
                                have p2173_3 := h2173c.2.2.2
                                linarith only [h1952, h2086, h2095, h2169, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2173_1]
                              · have p2173_0 := h2173c.1
                                have p2173_1 := h2173c.2.1
                                have p2173_2 := h2173c.2.2.1
                                have p2173_3 := h2173c.2.2.2
                                rcases p2173_3 (m.d 0 1) (by simp) with h2183 | h2183
                                · linarith only [h0, h2183, hlam]
                                · linarith only [h2086, h2183, hlam]
                              · have p2173_0 := h2173c.1
                                have p2173_1 := h2173c.2.1
                                have p2173_2 := h2173c.2.2.1
                                have p2173_3 := h2173c.2.2.2
                                linarith only [h2086, h2095, h2169, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2173_1]
                              · have p2173_0 := h2173c.1
                                have p2173_1 := h2173c.2.1
                                have p2173_2 := h2173c.2.2.1
                                have p2173_3 := h2173c.2.2.2
                                linarith only [h2091, hlam, p2173_0]
                              · have p2173_0 := h2173c.1
                                have p2173_1 := h2173c.2.1
                                have p2173_2 := h2173c.2.2.1
                                have p2173_3 := h2173c.2.2.2
                                linarith only [hlam, p2173_0]
                              · have p2173_0 := h2173c.1
                                have p2173_1 := h2173c.2.1
                                have p2173_2 := h2173c.2.2.1
                                have p2173_3 := h2173c.2.2.2
                                linarith only [h1952, h2086, h2091, h2095, h2169, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2173_1]
                              · have p2173_0 := h2173c.1
                                have p2173_1 := h2173c.2.1
                                have p2173_2 := h2173c.2.2.1
                                have p2173_3 := h2173c.2.2.2
                                rcases p2173_3 (m.d 0 1) (by simp) with h2190 | h2190
                                · linarith only [h1697, h2190, hlam]
                                · linarith only [h2086, h2190, hlam]
                              · have p2173_0 := h2173c.1
                                have p2173_1 := h2173c.2.1
                                have p2173_2 := h2173c.2.2.1
                                have p2173_3 := h2173c.2.2.2
                                linarith only [h2086, h2095, h2169, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2173_1]
                              · have p2173_0 := h2173c.1
                                have p2173_1 := h2173c.2.1
                                have p2173_2 := h2173c.2.2.1
                                have p2173_3 := h2173c.2.2.2
                                linarith only [h2092, hlam, p2173_0]
                              · have p2173_0 := h2173c.1
                                have p2173_1 := h2173c.2.1
                                have p2173_2 := h2173c.2.2.1
                                have p2173_3 := h2173c.2.2.2
                                linarith only [h2094, hlam, p2173_1]
                              · have p2173_0 := h2173c.1
                                have p2173_1 := h2173c.2.1
                                have p2173_2 := h2173c.2.2.1
                                have p2173_3 := h2173c.2.2.2
                                linarith only [hlam, p2173_0]
                              · have p2173_0 := h2173c.1
                                have p2173_1 := h2173c.2.1
                                have p2173_2 := h2173c.2.2.1
                                have p2173_3 := h2173c.2.2.2
                                rcases p2173_3 (m.d 0 1) (by simp) with h2197 | h2197
                                · linarith only [h1952, h2197, hlam]
                                · linarith only [h2086, h2197, hlam]
                              · have p2173_0 := h2173c.1
                                have p2173_1 := h2173c.2.1
                                have p2173_2 := h2173c.2.2.1
                                have p2173_3 := h2173c.2.2.2
                                linarith only [h2086, hlam, p2173_0]
                              · have p2173_0 := h2173c.1
                                have p2173_1 := h2173c.2.1
                                have p2173_2 := h2173c.2.2.1
                                have p2173_3 := h2173c.2.2.2
                                linarith only [h2093, hlam, p2173_0]
                              · have p2173_0 := h2173c.1
                                have p2173_1 := h2173c.2.1
                                have p2173_2 := h2173c.2.2.1
                                have p2173_3 := h2173c.2.2.2
                                linarith only [h2095, hlam, p2173_0]
                              · have p2173_0 := h2173c.1
                                have p2173_1 := h2173c.2.1
                                have p2173_2 := h2173c.2.2.1
                                have p2173_3 := h2173c.2.2.2
                                linarith only [h2096, hlam, p2173_0]
                              · have p2173_0 := h2173c.1
                                have p2173_1 := h2173c.2.1
                                have p2173_2 := h2173c.2.2.1
                                have p2173_3 := h2173c.2.2.2
                                linarith only [hlam, p2173_0]
                            · linarith only [h2087, h2097, h2171, h2172, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2206 | h2206
                            · rcases h1bigk with h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c | h2207c
                              · have p2207_0 := h2207c.1
                                have p2207_1 := h2207c.2.1
                                have p2207_2 := h2207c.2.2.1
                                have p2207_3 := h2207c.2.2.2
                                linarith only [hlam, p2207_0]
                              · have p2207_0 := h2207c.1
                                have p2207_1 := h2207c.2.1
                                have p2207_2 := h2207c.2.2.1
                                have p2207_3 := h2207c.2.2.2
                                linarith only [h0, hlam, p2207_0]
                              · have p2207_0 := h2207c.1
                                have p2207_1 := h2207c.2.1
                                have p2207_2 := h2207c.2.2.1
                                have p2207_3 := h2207c.2.2.2
                                linarith only [h1697, hlam, p2207_0]
                              · have p2207_0 := h2207c.1
                                have p2207_1 := h2207c.2.1
                                have p2207_2 := h2207c.2.2.1
                                have p2207_3 := h2207c.2.2.2
                                linarith only [h1952, hlam, p2207_0]
                              · have p2207_0 := h2207c.1
                                have p2207_1 := h2207c.2.1
                                have p2207_2 := h2207c.2.2.1
                                have p2207_3 := h2207c.2.2.2
                                linarith only [h0, h2095, h2097, h2171, h2206, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2207_1]
                              · have p2207_0 := h2207c.1
                                have p2207_1 := h2207c.2.1
                                have p2207_2 := h2207c.2.2.1
                                have p2207_3 := h2207c.2.2.2
                                linarith only [h2086, h2095, h2097, h2171, h2206, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2207_1]
                              · have p2207_0 := h2207c.1
                                have p2207_1 := h2207c.2.1
                                have p2207_2 := h2207c.2.2.1
                                have p2207_3 := h2207c.2.2.2
                                linarith only [hlam, p2207_0]
                              · have p2207_0 := h2207c.1
                                have p2207_1 := h2207c.2.1
                                have p2207_2 := h2207c.2.2.1
                                have p2207_3 := h2207c.2.2.2
                                linarith only [h1697, hc01, hc12, hlam, hphi, p2207_1]
                              · have p2207_0 := h2207c.1
                                have p2207_1 := h2207c.2.1
                                have p2207_2 := h2207c.2.2.1
                                have p2207_3 := h2207c.2.2.2
                                linarith only [h1952, h2086, h2095, h2097, h2171, h2206, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2207_1]
                              · have p2207_0 := h2207c.1
                                have p2207_1 := h2207c.2.1
                                have p2207_2 := h2207c.2.2.1
                                have p2207_3 := h2207c.2.2.2
                                rcases p2207_3 (m.d 0 1) (by simp) with h2217 | h2217
                                · linarith only [h0, h2217, hlam]
                                · linarith only [h2086, h2217, hlam]
                              · have p2207_0 := h2207c.1
                                have p2207_1 := h2207c.2.1
                                have p2207_2 := h2207c.2.2.1
                                have p2207_3 := h2207c.2.2.2
                                linarith only [h2086, h2095, h2097, h2171, h2206, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2207_1]
                              · have p2207_0 := h2207c.1
                                have p2207_1 := h2207c.2.1
                                have p2207_2 := h2207c.2.2.1
                                have p2207_3 := h2207c.2.2.2
                                linarith only [h2091, hlam, p2207_0]
                              · have p2207_0 := h2207c.1
                                have p2207_1 := h2207c.2.1
                                have p2207_2 := h2207c.2.2.1
                                have p2207_3 := h2207c.2.2.2
                                linarith only [hlam, p2207_0]
                              · have p2207_0 := h2207c.1
                                have p2207_1 := h2207c.2.1
                                have p2207_2 := h2207c.2.2.1
                                have p2207_3 := h2207c.2.2.2
                                linarith only [h1952, h2086, h2091, h2095, h2097, h2171, h2206, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2207_1]
                              · have p2207_0 := h2207c.1
                                have p2207_1 := h2207c.2.1
                                have p2207_2 := h2207c.2.2.1
                                have p2207_3 := h2207c.2.2.2
                                rcases p2207_3 (m.d 0 1) (by simp) with h2224 | h2224
                                · linarith only [h1697, h2224, hlam]
                                · linarith only [h2086, h2224, hlam]
                              · have p2207_0 := h2207c.1
                                have p2207_1 := h2207c.2.1
                                have p2207_2 := h2207c.2.2.1
                                have p2207_3 := h2207c.2.2.2
                                linarith only [h2086, h2095, h2097, h2171, h2206, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2207_1]
                              · have p2207_0 := h2207c.1
                                have p2207_1 := h2207c.2.1
                                have p2207_2 := h2207c.2.2.1
                                have p2207_3 := h2207c.2.2.2
                                linarith only [h2092, hlam, p2207_0]
                              · have p2207_0 := h2207c.1
                                have p2207_1 := h2207c.2.1
                                have p2207_2 := h2207c.2.2.1
                                have p2207_3 := h2207c.2.2.2
                                linarith only [h2094, hlam, p2207_1]
                              · have p2207_0 := h2207c.1
                                have p2207_1 := h2207c.2.1
                                have p2207_2 := h2207c.2.2.1
                                have p2207_3 := h2207c.2.2.2
                                linarith only [hlam, p2207_0]
                              · have p2207_0 := h2207c.1
                                have p2207_1 := h2207c.2.1
                                have p2207_2 := h2207c.2.2.1
                                have p2207_3 := h2207c.2.2.2
                                rcases p2207_3 (m.d 0 1) (by simp) with h2231 | h2231
                                · linarith only [h1952, h2231, hlam]
                                · linarith only [h2086, h2231, hlam]
                              · have p2207_0 := h2207c.1
                                have p2207_1 := h2207c.2.1
                                have p2207_2 := h2207c.2.2.1
                                have p2207_3 := h2207c.2.2.2
                                linarith only [h2086, hlam, p2207_0]
                              · have p2207_0 := h2207c.1
                                have p2207_1 := h2207c.2.1
                                have p2207_2 := h2207c.2.2.1
                                have p2207_3 := h2207c.2.2.2
                                linarith only [h2093, hlam, p2207_0]
                              · have p2207_0 := h2207c.1
                                have p2207_1 := h2207c.2.1
                                have p2207_2 := h2207c.2.2.1
                                have p2207_3 := h2207c.2.2.2
                                linarith only [h2095, hlam, p2207_0]
                              · have p2207_0 := h2207c.1
                                have p2207_1 := h2207c.2.1
                                have p2207_2 := h2207c.2.2.1
                                have p2207_3 := h2207c.2.2.2
                                linarith only [h2096, hlam, p2207_0]
                              · have p2207_0 := h2207c.1
                                have p2207_1 := h2207c.2.1
                                have p2207_2 := h2207c.2.2.1
                                have p2207_3 := h2207c.2.2.2
                                linarith only [hlam, p2207_0]
                            · linarith only [h2097, h2206, hc23, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h1952, h2086, h2090, h2096, hc04, hlam, hphi, ht0b, ht5b, u5ehi6]
                  · linarith only [h1952, h2086, h2093, h2094, h2095, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                · linarith only [h1697, h2086, h2093, h2094, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
              · linarith only [h1697, h2089, h2091, h2093, hc34, hlam, hphi, ht45, u5elo2]
            · linarith only [h1697, h2086, h2091, h2092, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
          · linarith only [h0, h2086, h2091, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
        · linarith only [h1952, h2086, h2090, hlam, hphi, u5ehi6, u5elo4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2247 | h2247
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2248 | h2248
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2249 | h2249
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2250 | h2250
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2251 | h2251
                · linarith only [h1697, h2086, h2089, h2248, h2250, h2251, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                · linarith only [h1697, h2086, h2250, h2251, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
              · linarith only [h2248, h2250, hc23, hlam, hphi, ht34, ht45, u5elo2]
            · linarith only [h1697, h2086, h2248, h2249, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
          · linarith only [h0, h2086, h2248, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
        · linarith only [h1952, h2086, h2247, hlam, hphi, u5ehi6, u5elo4]
    · linarith only [h2087, h2088, hc24, hlam, hphi, ht45, u5elo2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2259 | h2259
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2260 | h2260
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2261 | h2261
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2262 | h2262
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2263 | h2263
            · linarith only [h0, h2086, h2087, h2263, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi6]
            · linarith only [h0, h2086, h2263, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
          · linarith only [h0, h2086, h2262, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
        · linarith only [h0, h2086, h2087, h2261, hlam, hphi, u5ehi6, u5elo4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2268 | h2268
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2269 | h2269
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2270 | h2270
            · linarith only [h0, h2086, h2087, h2270, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi6]
            · linarith only [h0, h2086, h2270, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
          · linarith only [h0, h2086, h2269, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi6]
        · linarith only [h1697, h2086, h2260, h2268, hlam, hphi, u5ehi6, u5elo4]
    · linarith only [h0, h2086, h2259, hlam, hphi, u5ehi6, u5elo2]

end R2N4
