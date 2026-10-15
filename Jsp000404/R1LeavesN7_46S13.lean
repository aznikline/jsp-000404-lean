import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6072000 in
set_option maxHeartbeats 6072000 in
theorem r1l7_20_12_14_M_LI_L_0_L_I_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1694 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1695 | h1695
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1696 | h1696
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1697 | h1697
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1698 | h1698
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1699 | h1699
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1700 | h1700
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1701 | h1701
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1702 | h1702
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1703 | h1703
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1704 | h1704
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1705 | h1705
                      · linarith only [h0, h1694, h1705, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h0, h1694, h1700, h1703, h1705, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1704, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1703, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1710 | h1710
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1711 | h1711
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1712 | h1712
                      · linarith only [h0, h1694, h1712, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h0, h1694, h1700, h1712, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1711, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1694, h1710, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1717 | h1717
                · linarith only [h1700, h1701, h1717, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1719 | h1719
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1720 | h1720
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1721 | h1721
                      · linarith only [h0, h1694, h1721, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h1700, h1701, h1719, h1721, hc23, hc35, hlam, hphi]
                    · linarith only [h0, h1720, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1719, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1726 | h1726
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1727 | h1727
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1728 | h1728
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1729 | h1729
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1730 | h1730
                      · linarith only [h1694, h1700, h1726, h1730, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1732 | h1732
                        · linarith only [h0, h1695, h1730, h1732, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · linarith only [h1700, h1726, h1728, h1732, hc23, hc34, hlam, hphi]
                    · linarith only [h0, h1729, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1728, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h1700, h1726, h1727, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1738 | h1738
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1739 | h1739
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1740 | h1740
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1741 | h1741
                      · linarith only [h1694, h1700, h1741, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1743 | h1743
                        · linarith only [h1694, h1726, h1743, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1745 | h1745
                          · linarith only [h0, h1695, h1745, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · linarith only [h0, h1695, h1738, h1741, h1745, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1740, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1739, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1750 | h1750
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1751 | h1751
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1752 | h1752
                      · linarith only [h1694, h1700, h1752, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1754 | h1754
                        · linarith only [h1694, h1726, h1754, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1756 | h1756
                          · linarith only [h1695, h1738, h1756, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1758 | h1758
                            · linarith only [h1694, h1700, h1750, h1758, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1760 | h1760
                              · linarith only [h0, h1698, h1738, h1760, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1762 | h1762
                                · rcases h0bigk with h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [hlam, p1763_0]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [h0, hlam, p1763_1]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [h0, h1694, h1750, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1763_1, u2elo1]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1763_1, u2elo1]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1763_1, u2elo1]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [h0, hc01, hlam, hphi, ht12, p1763_1, u2elo1]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [hlam, p1763_0]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    rcases p1763_3 (m.d 0 1) (by simp) with h1771 | h1771
                                    · linarith only [h0, h1771, hlam]
                                    · linarith only [h1694, h1771, hlam]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    rcases p1763_3 (m.d 0 1) (by simp) with h1774 | h1774
                                    · linarith only [h0, h1774, hlam]
                                    · linarith only [h1695, h1774, hlam]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    rcases p1763_3 (m.d 0 1) (by simp) with h1777 | h1777
                                    · linarith only [h0, h1777, hlam]
                                    · linarith only [h1696, h1777, hlam]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [h1694, hlam, p1763_1]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [h1697, hlam, p1763_1]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [hlam, p1763_0]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [h1700, hlam, p1763_1]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [h1726, hlam, p1763_1]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [h1695, hlam, p1763_0]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [h1698, hlam, p1763_0]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [h1694, h1738, h1750, h1762, hc23, hc34, hlam, hphi, p1763_1]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [hlam, p1763_0]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [h1738, hlam, p1763_0]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [h1696, hlam, p1763_0]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [h1699, hlam, p1763_1]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [h0, h1694, h1696, h1750, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1763_1, u2elo1]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [h0, h1696, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1763_1, u2elo1]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [hlam, p1763_0]
                                · rcases h0bigk with h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c
                                  · have p1795_0 := h1795c.1
                                    have p1795_1 := h1795c.2.1
                                    have p1795_2 := h1795c.2.2.1
                                    have p1795_3 := h1795c.2.2.2
                                    linarith only [hlam, p1795_0]
                                  · have p1795_0 := h1795c.1
                                    have p1795_1 := h1795c.2.1
                                    have p1795_2 := h1795c.2.2.1
                                    have p1795_3 := h1795c.2.2.2
                                    linarith only [h0, hlam, p1795_1]
                                  · have p1795_0 := h1795c.1
                                    have p1795_1 := h1795c.2.1
                                    have p1795_2 := h1795c.2.2.1
                                    have p1795_3 := h1795c.2.2.2
                                    linarith only [h0, h1694, h1750, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1795_1, u2elo1]
                                  · have p1795_0 := h1795c.1
                                    have p1795_1 := h1795c.2.1
                                    have p1795_2 := h1795c.2.2.1
                                    have p1795_3 := h1795c.2.2.2
                                    linarith only [h0, h1695, h1750, h1752, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1795_1, u2elo1]
                                  · have p1795_0 := h1795c.1
                                    have p1795_1 := h1795c.2.1
                                    have p1795_2 := h1795c.2.2.1
                                    have p1795_3 := h1795c.2.2.2
                                    linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1795_1, u2elo1]
                                  · have p1795_0 := h1795c.1
                                    have p1795_1 := h1795c.2.1
                                    have p1795_2 := h1795c.2.2.1
                                    have p1795_3 := h1795c.2.2.2
                                    linarith only [h0, hc01, hlam, hphi, ht12, p1795_1, u2elo1]
                                  · have p1795_0 := h1795c.1
                                    have p1795_1 := h1795c.2.1
                                    have p1795_2 := h1795c.2.2.1
                                    have p1795_3 := h1795c.2.2.2
                                    linarith only [hlam, p1795_0]
                                  · have p1795_0 := h1795c.1
                                    have p1795_1 := h1795c.2.1
                                    have p1795_2 := h1795c.2.2.1
                                    have p1795_3 := h1795c.2.2.2
                                    rcases p1795_3 (m.d 0 1) (by simp) with h1803 | h1803
                                    · linarith only [h0, h1803, hlam]
                                    · linarith only [h1694, h1803, hlam]
                                  · have p1795_0 := h1795c.1
                                    have p1795_1 := h1795c.2.1
                                    have p1795_2 := h1795c.2.2.1
                                    have p1795_3 := h1795c.2.2.2
                                    rcases p1795_3 (m.d 0 1) (by simp) with h1806 | h1806
                                    · linarith only [h0, h1806, hlam]
                                    · linarith only [h1695, h1806, hlam]
                                  · have p1795_0 := h1795c.1
                                    have p1795_1 := h1795c.2.1
                                    have p1795_2 := h1795c.2.2.1
                                    have p1795_3 := h1795c.2.2.2
                                    rcases p1795_3 (m.d 0 1) (by simp) with h1809 | h1809
                                    · linarith only [h0, h1809, hlam]
                                    · linarith only [h1696, h1809, hlam]
                                  · have p1795_0 := h1795c.1
                                    have p1795_1 := h1795c.2.1
                                    have p1795_2 := h1795c.2.2.1
                                    have p1795_3 := h1795c.2.2.2
                                    linarith only [h1694, hlam, p1795_1]
                                  · have p1795_0 := h1795c.1
                                    have p1795_1 := h1795c.2.1
                                    have p1795_2 := h1795c.2.2.1
                                    have p1795_3 := h1795c.2.2.2
                                    linarith only [h1697, hlam, p1795_1]
                                  · have p1795_0 := h1795c.1
                                    have p1795_1 := h1795c.2.1
                                    have p1795_2 := h1795c.2.2.1
                                    have p1795_3 := h1795c.2.2.2
                                    linarith only [hlam, p1795_0]
                                  · have p1795_0 := h1795c.1
                                    have p1795_1 := h1795c.2.1
                                    have p1795_2 := h1795c.2.2.1
                                    have p1795_3 := h1795c.2.2.2
                                    linarith only [h1700, hlam, p1795_1]
                                  · have p1795_0 := h1795c.1
                                    have p1795_1 := h1795c.2.1
                                    have p1795_2 := h1795c.2.2.1
                                    have p1795_3 := h1795c.2.2.2
                                    linarith only [h1726, hlam, p1795_1]
                                  · have p1795_0 := h1795c.1
                                    have p1795_1 := h1795c.2.1
                                    have p1795_2 := h1795c.2.2.1
                                    have p1795_3 := h1795c.2.2.2
                                    linarith only [h1695, hlam, p1795_0]
                                  · have p1795_0 := h1795c.1
                                    have p1795_1 := h1795c.2.1
                                    have p1795_2 := h1795c.2.2.1
                                    have p1795_3 := h1795c.2.2.2
                                    linarith only [h1698, hlam, p1795_0]
                                  · have p1795_0 := h1795c.1
                                    have p1795_1 := h1795c.2.1
                                    have p1795_2 := h1795c.2.2.1
                                    have p1795_3 := h1795c.2.2.2
                                    linarith only [h0, h1694, h1695, h1750, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1795_1, u2elo1]
                                  · have p1795_0 := h1795c.1
                                    have p1795_1 := h1795c.2.1
                                    have p1795_2 := h1795c.2.2.1
                                    have p1795_3 := h1795c.2.2.2
                                    linarith only [hlam, p1795_0]
                                  · have p1795_0 := h1795c.1
                                    have p1795_1 := h1795c.2.1
                                    have p1795_2 := h1795c.2.2.1
                                    have p1795_3 := h1795c.2.2.2
                                    linarith only [h1738, hlam, p1795_0]
                                  · have p1795_0 := h1795c.1
                                    have p1795_1 := h1795c.2.1
                                    have p1795_2 := h1795c.2.2.1
                                    have p1795_3 := h1795c.2.2.2
                                    linarith only [h1696, hlam, p1795_0]
                                  · have p1795_0 := h1795c.1
                                    have p1795_1 := h1795c.2.1
                                    have p1795_2 := h1795c.2.2.1
                                    have p1795_3 := h1795c.2.2.2
                                    linarith only [h1699, hlam, p1795_1]
                                  · have p1795_0 := h1795c.1
                                    have p1795_1 := h1795c.2.1
                                    have p1795_2 := h1795c.2.2.1
                                    have p1795_3 := h1795c.2.2.2
                                    linarith only [h0, h1694, h1696, h1750, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1795_1, u2elo1]
                                  · have p1795_0 := h1795c.1
                                    have p1795_1 := h1795c.2.1
                                    have p1795_2 := h1795c.2.2.1
                                    have p1795_3 := h1795c.2.2.2
                                    linarith only [h0, h1696, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1795_1, u2elo1]
                                  · have p1795_0 := h1795c.1
                                    have p1795_1 := h1795c.2.1
                                    have p1795_2 := h1795c.2.2.1
                                    have p1795_3 := h1795c.2.2.2
                                    linarith only [hlam, p1795_0]
                    · linarith only [h0, h1751, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1694, h1750, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
          · linarith only [h0, h1696, h1699, hlam]
        · linarith only [h0, h1695, h1698, hlam]
      · linarith only [h0, h1694, h1697, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1832 | h1832
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1833 | h1833
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1834 | h1834
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1835 | h1835
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1836 | h1836
              · linarith only [h1694, h1696, h1836, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1838 | h1838
                · linarith only [h1694, h1696, h1835, h1838, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1840 | h1840
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1841 | h1841
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1842 | h1842
                      · linarith only [h0, h1694, h1842, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h0, h1694, h1835, h1840, h1842, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1841, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1840, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1847 | h1847
              · linarith only [h1694, h1696, h1847, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1849 | h1849
                · linarith only [h1695, h1696, h1849, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1851 | h1851
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1852 | h1852
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1853 | h1853
                      · linarith only [h1694, h1835, h1853, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1855 | h1855
                        · linarith only [h0, h1694, h1847, h1855, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1857 | h1857
                          · linarith only [h0, h1695, h1857, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1859 | h1859
                            · linarith only [h0, h1832, h1835, h1859, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1861 | h1861
                              · linarith only [h1695, h1696, h1852, h1857, h1861, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1863 | h1863
                                · linarith only [h1694, h1696, h1851, h1857, h1863, hc23, hc34, hlam, hphi]
                                · rcases h0bigk with h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c | h1865c
                                  · have p1865_0 := h1865c.1
                                    have p1865_1 := h1865c.2.1
                                    have p1865_2 := h1865c.2.2.1
                                    have p1865_3 := h1865c.2.2.2
                                    linarith only [hlam, p1865_0]
                                  · have p1865_0 := h1865c.1
                                    have p1865_1 := h1865c.2.1
                                    have p1865_2 := h1865c.2.2.1
                                    have p1865_3 := h1865c.2.2.2
                                    linarith only [h0, hlam, p1865_1]
                                  · have p1865_0 := h1865c.1
                                    have p1865_1 := h1865c.2.1
                                    have p1865_2 := h1865c.2.2.1
                                    have p1865_3 := h1865c.2.2.2
                                    linarith only [h0, h1694, h1851, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1865_1, u2elo1]
                                  · have p1865_0 := h1865c.1
                                    have p1865_1 := h1865c.2.1
                                    have p1865_2 := h1865c.2.2.1
                                    have p1865_3 := h1865c.2.2.2
                                    linarith only [h0, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1865_1, u2elo1]
                                  · have p1865_0 := h1865c.1
                                    have p1865_1 := h1865c.2.1
                                    have p1865_2 := h1865c.2.2.1
                                    have p1865_3 := h1865c.2.2.2
                                    linarith only [h1696, hlam, p1865_1]
                                  · have p1865_0 := h1865c.1
                                    have p1865_1 := h1865c.2.1
                                    have p1865_2 := h1865c.2.2.1
                                    have p1865_3 := h1865c.2.2.2
                                    linarith only [h0, hc01, hlam, hphi, ht12, p1865_1, u2elo1]
                                  · have p1865_0 := h1865c.1
                                    have p1865_1 := h1865c.2.1
                                    have p1865_2 := h1865c.2.2.1
                                    have p1865_3 := h1865c.2.2.2
                                    linarith only [hlam, p1865_0]
                                  · have p1865_0 := h1865c.1
                                    have p1865_1 := h1865c.2.1
                                    have p1865_2 := h1865c.2.2.1
                                    have p1865_3 := h1865c.2.2.2
                                    rcases p1865_3 (m.d 0 1) (by simp) with h1873 | h1873
                                    · linarith only [h0, h1873, hlam]
                                    · linarith only [h1694, h1873, hlam]
                                  · have p1865_0 := h1865c.1
                                    have p1865_1 := h1865c.2.1
                                    have p1865_2 := h1865c.2.2.1
                                    have p1865_3 := h1865c.2.2.2
                                    rcases p1865_3 (m.d 0 1) (by simp) with h1876 | h1876
                                    · linarith only [h0, h1876, hlam]
                                    · linarith only [h1695, h1876, hlam]
                                  · have p1865_0 := h1865c.1
                                    have p1865_1 := h1865c.2.1
                                    have p1865_2 := h1865c.2.2.1
                                    have p1865_3 := h1865c.2.2.2
                                    linarith only [h0, h1695, h1696, h1851, h1853, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1865_1, u2elo1]
                                  · have p1865_0 := h1865c.1
                                    have p1865_1 := h1865c.2.1
                                    have p1865_2 := h1865c.2.2.1
                                    have p1865_3 := h1865c.2.2.2
                                    linarith only [h1694, hlam, p1865_1]
                                  · have p1865_0 := h1865c.1
                                    have p1865_1 := h1865c.2.1
                                    have p1865_2 := h1865c.2.2.1
                                    have p1865_3 := h1865c.2.2.2
                                    linarith only [h1832, hlam, p1865_1]
                                  · have p1865_0 := h1865c.1
                                    have p1865_1 := h1865c.2.1
                                    have p1865_2 := h1865c.2.2.1
                                    have p1865_3 := h1865c.2.2.2
                                    linarith only [hlam, p1865_0]
                                  · have p1865_0 := h1865c.1
                                    have p1865_1 := h1865c.2.1
                                    have p1865_2 := h1865c.2.2.1
                                    have p1865_3 := h1865c.2.2.2
                                    linarith only [h1835, hlam, p1865_1]
                                  · have p1865_0 := h1865c.1
                                    have p1865_1 := h1865c.2.1
                                    have p1865_2 := h1865c.2.2.1
                                    have p1865_3 := h1865c.2.2.2
                                    linarith only [h1847, hlam, p1865_1]
                                  · have p1865_0 := h1865c.1
                                    have p1865_1 := h1865c.2.1
                                    have p1865_2 := h1865c.2.2.1
                                    have p1865_3 := h1865c.2.2.2
                                    linarith only [h1695, hlam, p1865_0]
                                  · have p1865_0 := h1865c.1
                                    have p1865_1 := h1865c.2.1
                                    have p1865_2 := h1865c.2.2.1
                                    have p1865_3 := h1865c.2.2.2
                                    linarith only [h1833, hlam, p1865_0]
                                  · have p1865_0 := h1865c.1
                                    have p1865_1 := h1865c.2.1
                                    have p1865_2 := h1865c.2.2.1
                                    have p1865_3 := h1865c.2.2.2
                                    linarith only [h1694, h1695, h1696, h1851, h1855, hc23, hc35, hlam, hphi, p1865_1]
                                  · have p1865_0 := h1865c.1
                                    have p1865_1 := h1865c.2.1
                                    have p1865_2 := h1865c.2.2.1
                                    have p1865_3 := h1865c.2.2.2
                                    linarith only [hlam, p1865_0]
                                  · have p1865_0 := h1865c.1
                                    have p1865_1 := h1865c.2.1
                                    have p1865_2 := h1865c.2.2.1
                                    have p1865_3 := h1865c.2.2.2
                                    linarith only [h1849, hlam, p1865_0]
                                  · have p1865_0 := h1865c.1
                                    have p1865_1 := h1865c.2.1
                                    have p1865_2 := h1865c.2.2.1
                                    have p1865_3 := h1865c.2.2.2
                                    linarith only [h1694, h1851, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1865_1, u0elo4]
                                  · have p1865_0 := h1865c.1
                                    have p1865_1 := h1865c.2.1
                                    have p1865_2 := h1865c.2.2.1
                                    have p1865_3 := h1865c.2.2.2
                                    linarith only [h1834, hlam, p1865_1]
                                  · have p1865_0 := h1865c.1
                                    have p1865_1 := h1865c.2.1
                                    have p1865_2 := h1865c.2.2.1
                                    have p1865_3 := h1865c.2.2.2
                                    rcases p1865_3 (m.d 0 1) (by simp) with h1892 | h1892
                                    · linarith only [h1696, h1892, hlam]
                                    · linarith only [h1694, h1892, hlam]
                                  · have p1865_0 := h1865c.1
                                    have p1865_1 := h1865c.2.1
                                    have p1865_2 := h1865c.2.2.1
                                    have p1865_3 := h1865c.2.2.2
                                    rcases p1865_3 (m.d 0 1) (by simp) with h1895 | h1895
                                    · linarith only [h1696, h1895, hlam]
                                    · linarith only [h1695, h1895, hlam]
                                  · have p1865_0 := h1865c.1
                                    have p1865_1 := h1865c.2.1
                                    have p1865_2 := h1865c.2.2.1
                                    have p1865_3 := h1865c.2.2.2
                                    linarith only [hlam, p1865_0]
                    · linarith only [h0, h1852, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1694, h1851, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1901 | h1901
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1902 | h1902
              · linarith only [h0, h1694, h1834, h1902, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1904 | h1904
                · linarith only [h0, h1695, h1834, h1904, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1906 | h1906
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1907 | h1907
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1908 | h1908
                      · linarith only [h0, h1694, h1834, h1908, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                      · linarith only [h0, h1694, h1834, h1901, h1908, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · linarith only [h0, h1907, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1694, h1906, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1913 | h1913
              · linarith only [h0, h1695, h1834, h1901, h1913, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1915 | h1915
                · linarith only [h0, h1695, h1834, h1915, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1917 | h1917
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1918 | h1918
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1919 | h1919
                      · linarith only [h0, h1694, h1834, h1901, h1919, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1921 | h1921
                        · linarith only [h0, h1694, h1834, h1913, h1921, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1923 | h1923
                          · linarith only [h0, h1695, h1834, h1901, h1915, h1923, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1925 | h1925
                            · linarith only [h1694, h1901, h1917, h1925, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1927 | h1927
                              · linarith only [h1695, h1696, h1918, h1923, h1927, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1929 | h1929
                                · linarith only [h0, h1694, h1834, h1917, h1927, h1929, hc23, hc34, hlam, hphi]
                                · rcases h0bigk with h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c | h1931c
                                  · have p1931_0 := h1931c.1
                                    have p1931_1 := h1931c.2.1
                                    have p1931_2 := h1931c.2.2.1
                                    have p1931_3 := h1931c.2.2.2
                                    linarith only [hlam, p1931_0]
                                  · have p1931_0 := h1931c.1
                                    have p1931_1 := h1931c.2.1
                                    have p1931_2 := h1931c.2.2.1
                                    have p1931_3 := h1931c.2.2.2
                                    linarith only [h0, hlam, p1931_1]
                                  · have p1931_0 := h1931c.1
                                    have p1931_1 := h1931c.2.1
                                    have p1931_2 := h1931c.2.2.1
                                    have p1931_3 := h1931c.2.2.2
                                    linarith only [h0, h1694, h1834, h1917, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1931_1, u2elo4]
                                  · have p1931_0 := h1931c.1
                                    have p1931_1 := h1931c.2.1
                                    have p1931_2 := h1931c.2.2.1
                                    have p1931_3 := h1931c.2.2.2
                                    linarith only [h0, h1834, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1931_1, u2elo4]
                                  · have p1931_0 := h1931c.1
                                    have p1931_1 := h1931c.2.1
                                    have p1931_2 := h1931c.2.2.1
                                    have p1931_3 := h1931c.2.2.2
                                    linarith only [h1696, hlam, p1931_1]
                                  · have p1931_0 := h1931c.1
                                    have p1931_1 := h1931c.2.1
                                    have p1931_2 := h1931c.2.2.1
                                    have p1931_3 := h1931c.2.2.2
                                    linarith only [h1834, hc01, hlam, hphi, ht12, p1931_1, u2elo4]
                                  · have p1931_0 := h1931c.1
                                    have p1931_1 := h1931c.2.1
                                    have p1931_2 := h1931c.2.2.1
                                    have p1931_3 := h1931c.2.2.2
                                    linarith only [hlam, p1931_0]
                                  · have p1931_0 := h1931c.1
                                    have p1931_1 := h1931c.2.1
                                    have p1931_2 := h1931c.2.2.1
                                    have p1931_3 := h1931c.2.2.2
                                    linarith only [h1694, h1834, h1917, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1931_1, u2elo4]
                                  · have p1931_0 := h1931c.1
                                    have p1931_1 := h1931c.2.1
                                    have p1931_2 := h1931c.2.2.1
                                    have p1931_3 := h1931c.2.2.2
                                    linarith only [h1695, h1834, h1918, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1931_1, u2elo4]
                                  · have p1931_0 := h1931c.1
                                    have p1931_1 := h1931c.2.1
                                    have p1931_2 := h1931c.2.2.1
                                    have p1931_3 := h1931c.2.2.2
                                    linarith only [h1834, hlam, p1931_0]
                                  · have p1931_0 := h1931c.1
                                    have p1931_1 := h1931c.2.1
                                    have p1931_2 := h1931c.2.2.1
                                    have p1931_3 := h1931c.2.2.2
                                    linarith only [h1694, hlam, p1931_1]
                                  · have p1931_0 := h1931c.1
                                    have p1931_1 := h1931c.2.1
                                    have p1931_2 := h1931c.2.2.1
                                    have p1931_3 := h1931c.2.2.2
                                    linarith only [h1832, hlam, p1931_1]
                                  · have p1931_0 := h1931c.1
                                    have p1931_1 := h1931c.2.1
                                    have p1931_2 := h1931c.2.2.1
                                    have p1931_3 := h1931c.2.2.2
                                    linarith only [hlam, p1931_0]
                                  · have p1931_0 := h1931c.1
                                    have p1931_1 := h1931c.2.1
                                    have p1931_2 := h1931c.2.2.1
                                    have p1931_3 := h1931c.2.2.2
                                    linarith only [h1901, hlam, p1931_1]
                                  · have p1931_0 := h1931c.1
                                    have p1931_1 := h1931c.2.1
                                    have p1931_2 := h1931c.2.2.1
                                    have p1931_3 := h1931c.2.2.2
                                    linarith only [h1913, hlam, p1931_1]
                                  · have p1931_0 := h1931c.1
                                    have p1931_1 := h1931c.2.1
                                    have p1931_2 := h1931c.2.2.1
                                    have p1931_3 := h1931c.2.2.2
                                    linarith only [h1695, hlam, p1931_0]
                                  · have p1931_0 := h1931c.1
                                    have p1931_1 := h1931c.2.1
                                    have p1931_2 := h1931c.2.2.1
                                    have p1931_3 := h1931c.2.2.2
                                    linarith only [h1833, hlam, p1931_0]
                                  · have p1931_0 := h1931c.1
                                    have p1931_1 := h1931c.2.1
                                    have p1931_2 := h1931c.2.2.1
                                    have p1931_3 := h1931c.2.2.2
                                    linarith only [h1694, h1695, h1696, h1917, h1921, hc23, hc35, hlam, hphi, p1931_1]
                                  · have p1931_0 := h1931c.1
                                    have p1931_1 := h1931c.2.1
                                    have p1931_2 := h1931c.2.2.1
                                    have p1931_3 := h1931c.2.2.2
                                    linarith only [hlam, p1931_0]
                                  · have p1931_0 := h1931c.1
                                    have p1931_1 := h1931c.2.1
                                    have p1931_2 := h1931c.2.2.1
                                    have p1931_3 := h1931c.2.2.2
                                    linarith only [h1915, hlam, p1931_0]
                                  · have p1931_0 := h1931c.1
                                    have p1931_1 := h1931c.2.1
                                    have p1931_2 := h1931c.2.2.1
                                    have p1931_3 := h1931c.2.2.2
                                    linarith only [h1694, h1917, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1931_1, u0elo4]
                                  · have p1931_0 := h1931c.1
                                    have p1931_1 := h1931c.2.1
                                    have p1931_2 := h1931c.2.2.1
                                    have p1931_3 := h1931c.2.2.2
                                    linarith only [h1834, hc02, hlam, hphi, p1931_1, u2elo4]
                                  · have p1931_0 := h1931c.1
                                    have p1931_1 := h1931c.2.1
                                    have p1931_2 := h1931c.2.2.1
                                    have p1931_3 := h1931c.2.2.2
                                    rcases p1931_3 (m.d 0 1) (by simp) with h1954 | h1954
                                    · linarith only [h1696, h1954, hlam]
                                    · linarith only [h1694, h1954, hlam]
                                  · have p1931_0 := h1931c.1
                                    have p1931_1 := h1931c.2.1
                                    have p1931_2 := h1931c.2.2.1
                                    have p1931_3 := h1931c.2.2.2
                                    rcases p1931_3 (m.d 0 1) (by simp) with h1957 | h1957
                                    · linarith only [h1696, h1957, hlam]
                                    · linarith only [h1695, h1957, hlam]
                                  · have p1931_0 := h1931c.1
                                    have p1931_1 := h1931c.2.1
                                    have p1931_2 := h1931c.2.2.1
                                    have p1931_3 := h1931c.2.2.2
                                    linarith only [hlam, p1931_0]
                    · linarith only [h0, h1918, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1694, h1917, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
        · linarith only [h0, h1695, h1833, hlam]
      · linarith only [h0, h1694, h1832, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1965 | h1965
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1966 | h1966
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1967 | h1967
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1968 | h1968
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1969 | h1969
            · linarith only [h1694, h1695, h1969, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1971 | h1971
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1972 | h1972
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1973 | h1973
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1974 | h1974
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1975 | h1975
                      · linarith only [h1694, h1969, h1975, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1977 | h1977
                        · linarith only [h1694, h1695, h1974, h1977, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · linarith only [h1694, h1695, h1971, h1973, h1974, h1977, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1967, h1974, hlam]
                  · linarith only [h0, h1973, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h1694, h1695, h1971, h1972, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1983 | h1983
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1984 | h1984
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1985 | h1985
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1986 | h1986
                      · linarith only [h1694, h1969, h1986, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1988 | h1988
                        · linarith only [h1694, h1695, h1971, h1985, h1988, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1990 | h1990
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1991 | h1991
                            · linarith only [h1695, h1986, h1991, hc01, hlam, hphi, ht12, u2elo2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1993 | h1993
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1994 | h1994
                                · rcases h0bigk with h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c | h1995c
                                  · have p1995_0 := h1995c.1
                                    have p1995_1 := h1995c.2.1
                                    have p1995_2 := h1995c.2.2.1
                                    have p1995_3 := h1995c.2.2.2
                                    linarith only [hlam, p1995_0]
                                  · have p1995_0 := h1995c.1
                                    have p1995_1 := h1995c.2.1
                                    have p1995_2 := h1995c.2.2.1
                                    have p1995_3 := h1995c.2.2.2
                                    linarith only [h0, hlam, p1995_1]
                                  · have p1995_0 := h1995c.1
                                    have p1995_1 := h1995c.2.1
                                    have p1995_2 := h1995c.2.2.1
                                    have p1995_3 := h1995c.2.2.2
                                    linarith only [h1694, h1695, h1984, h1986, hc23, hc34, hlam, hphi, p1995_1]
                                  · have p1995_0 := h1995c.1
                                    have p1995_1 := h1995c.2.1
                                    have p1995_2 := h1995c.2.2.1
                                    have p1995_3 := h1995c.2.2.2
                                    linarith only [h1695, hlam, p1995_1]
                                  · have p1995_0 := h1995c.1
                                    have p1995_1 := h1995c.2.1
                                    have p1995_2 := h1995c.2.2.1
                                    have p1995_3 := h1995c.2.2.2
                                    linarith only [h1694, h1695, h1971, h1984, h1985, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1995_1, u2elo1]
                                  · have p1995_0 := h1995c.1
                                    have p1995_1 := h1995c.2.1
                                    have p1995_2 := h1995c.2.2.1
                                    have p1995_3 := h1995c.2.2.2
                                    linarith only [h0, hc01, hlam, hphi, ht12, p1995_1, u2elo1]
                                  · have p1995_0 := h1995c.1
                                    have p1995_1 := h1995c.2.1
                                    have p1995_2 := h1995c.2.2.1
                                    have p1995_3 := h1995c.2.2.2
                                    linarith only [hlam, p1995_0]
                                  · have p1995_0 := h1995c.1
                                    have p1995_1 := h1995c.2.1
                                    have p1995_2 := h1995c.2.2.1
                                    have p1995_3 := h1995c.2.2.2
                                    rcases p1995_3 (m.d 0 1) (by simp) with h2003 | h2003
                                    · linarith only [h0, h2003, hlam]
                                    · linarith only [h1694, h2003, hlam]
                                  · have p1995_0 := h1995c.1
                                    have p1995_1 := h1995c.2.1
                                    have p1995_2 := h1995c.2.2.1
                                    have p1995_3 := h1995c.2.2.2
                                    linarith only [h0, h1695, h1965, h1984, h1988, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1995_1, u2elo1]
                                  · have p1995_0 := h1995c.1
                                    have p1995_1 := h1995c.2.1
                                    have p1995_2 := h1995c.2.2.1
                                    have p1995_3 := h1995c.2.2.2
                                    rcases p1995_3 (m.d 0 1) (by simp) with h2007 | h2007
                                    · linarith only [h0, h2007, hlam]
                                    · linarith only [h1965, h2007, hlam]
                                  · have p1995_0 := h1995c.1
                                    have p1995_1 := h1995c.2.1
                                    have p1995_2 := h1995c.2.2.1
                                    have p1995_3 := h1995c.2.2.2
                                    linarith only [h1694, hlam, p1995_1]
                                  · have p1995_0 := h1995c.1
                                    have p1995_1 := h1995c.2.1
                                    have p1995_2 := h1995c.2.2.1
                                    have p1995_3 := h1995c.2.2.2
                                    linarith only [h1966, hlam, p1995_1]
                                  · have p1995_0 := h1995c.1
                                    have p1995_1 := h1995c.2.1
                                    have p1995_2 := h1995c.2.2.1
                                    have p1995_3 := h1995c.2.2.2
                                    linarith only [hlam, p1995_0]
                                  · have p1995_0 := h1995c.1
                                    have p1995_1 := h1995c.2.1
                                    have p1995_2 := h1995c.2.2.1
                                    have p1995_3 := h1995c.2.2.2
                                    linarith only [h1969, hlam, p1995_1]
                                  · have p1995_0 := h1995c.1
                                    have p1995_1 := h1995c.2.1
                                    have p1995_2 := h1995c.2.2.1
                                    have p1995_3 := h1995c.2.2.2
                                    linarith only [h1971, hlam, p1995_1]
                                  · have p1995_0 := h1995c.1
                                    have p1995_1 := h1995c.2.1
                                    have p1995_2 := h1995c.2.2.1
                                    have p1995_3 := h1995c.2.2.2
                                    linarith only [h1965, h1984, h1988, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1995_1, u0elo3]
                                  · have p1995_0 := h1995c.1
                                    have p1995_1 := h1995c.2.1
                                    have p1995_2 := h1995c.2.2.1
                                    have p1995_3 := h1995c.2.2.2
                                    linarith only [h1967, hlam, p1995_0]
                                  · have p1995_0 := h1995c.1
                                    have p1995_1 := h1995c.2.1
                                    have p1995_2 := h1995c.2.2.1
                                    have p1995_3 := h1995c.2.2.2
                                    rcases p1995_3 (m.d 0 1) (by simp) with h2017 | h2017
                                    · linarith only [h1695, h2017, hlam]
                                    · linarith only [h1694, h2017, hlam]
                                  · have p1995_0 := h1995c.1
                                    have p1995_1 := h1995c.2.1
                                    have p1995_2 := h1995c.2.2.1
                                    have p1995_3 := h1995c.2.2.2
                                    linarith only [hlam, p1995_0]
                                  · have p1995_0 := h1995c.1
                                    have p1995_1 := h1995c.2.1
                                    have p1995_2 := h1995c.2.2.1
                                    have p1995_3 := h1995c.2.2.2
                                    rcases p1995_3 (m.d 0 1) (by simp) with h2021 | h2021
                                    · linarith only [h1695, h2021, hlam]
                                    · linarith only [h1965, h2021, hlam]
                                  · have p1995_0 := h1995c.1
                                    have p1995_1 := h1995c.2.1
                                    have p1995_2 := h1995c.2.2.1
                                    have p1995_3 := h1995c.2.2.2
                                    linarith only [h1965, hlam, p1995_0]
                                  · have p1995_0 := h1995c.1
                                    have p1995_1 := h1995c.2.1
                                    have p1995_2 := h1995c.2.2.1
                                    have p1995_3 := h1995c.2.2.2
                                    linarith only [h1968, hlam, p1995_1]
                                  · have p1995_0 := h1995c.1
                                    have p1995_1 := h1995c.2.1
                                    have p1995_2 := h1995c.2.2.1
                                    have p1995_3 := h1995c.2.2.2
                                    linarith only [h0, h1694, h1965, h1984, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1995_1, u2elo1]
                                  · have p1995_0 := h1995c.1
                                    have p1995_1 := h1995c.2.1
                                    have p1995_2 := h1995c.2.2.1
                                    have p1995_3 := h1995c.2.2.2
                                    linarith only [h1983, hlam, p1995_1]
                                  · have p1995_0 := h1995c.1
                                    have p1995_1 := h1995c.2.1
                                    have p1995_2 := h1995c.2.2.1
                                    have p1995_3 := h1995c.2.2.2
                                    linarith only [hlam, p1995_0]
                                · linarith only [h1695, h1965, h1985, h1990, h1994, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · linarith only [h1695, h1965, h1985, h1990, h1993, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · linarith only [h1694, h1695, h1984, h1990, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h1985, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1694, h1984, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                · linarith only [h1695, h1965, h1983, hlam]
          · linarith only [h0, h1965, h1968, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2036 | h2036
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2037 | h2037
            · linarith only [h0, h1694, h1967, h2037, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2039 | h2039
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2040 | h2040
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2041 | h2041
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2042 | h2042
                    · linarith only [h0, h1967, h2042, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1694, h2041, h2042, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h2041, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h0, h1694, h1967, h2039, h2040, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2047 | h2047
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2048 | h2048
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2049 | h2049
                    · linarith only [h0, h1694, h1967, h2048, h2049, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1694, h2048, h2049, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1694, h2048, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                · linarith only [h1695, h1965, h2047, hlam]
          · linarith only [h0, h1965, h2036, hlam]
      · linarith only [h0, h1694, h1966, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2056 | h2056
      · rcases m.htr 0 2 4 (by decide) (by decide) with h2057 | h2057
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2058 | h2058
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2059 | h2059
            · linarith only [h1694, h1695, h2059, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2061 | h2061
              · linarith only [h1694, h1965, h2061, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2063 | h2063
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2064 | h2064
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2065 | h2065
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2066 | h2066
                      · linarith only [h1694, h2059, h2066, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2068 | h2068
                        · linarith only [h1694, h1695, h2061, h2065, h2068, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2070 | h2070
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h2071 | h2071
                            · linarith only [h1965, h2066, h2070, h2071, hc01, hlam, hphi, ht12, u2elo2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2073 | h2073
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2074 | h2074
                                · rcases h0bigk with h2075c | h2075c | h2075c | h2075c | h2075c | h2075c | h2075c | h2075c | h2075c | h2075c | h2075c | h2075c | h2075c | h2075c | h2075c | h2075c | h2075c | h2075c | h2075c | h2075c | h2075c | h2075c | h2075c | h2075c | h2075c
                                  · have p2075_0 := h2075c.1
                                    have p2075_1 := h2075c.2.1
                                    have p2075_2 := h2075c.2.2.1
                                    have p2075_3 := h2075c.2.2.2
                                    linarith only [hlam, p2075_0]
                                  · have p2075_0 := h2075c.1
                                    have p2075_1 := h2075c.2.1
                                    have p2075_2 := h2075c.2.2.1
                                    have p2075_3 := h2075c.2.2.2
                                    linarith only [h0, hlam, p2075_1]
                                  · have p2075_0 := h2075c.1
                                    have p2075_1 := h2075c.2.1
                                    have p2075_2 := h2075c.2.2.1
                                    have p2075_3 := h2075c.2.2.2
                                    linarith only [h1694, h1965, h2064, h2066, h2070, hc23, hc34, hlam, hphi, p2075_1]
                                  · have p2075_0 := h2075c.1
                                    have p2075_1 := h2075c.2.1
                                    have p2075_2 := h2075c.2.2.1
                                    have p2075_3 := h2075c.2.2.2
                                    linarith only [h1695, hlam, p2075_1]
                                  · have p2075_0 := h2075c.1
                                    have p2075_1 := h2075c.2.1
                                    have p2075_2 := h2075c.2.2.1
                                    have p2075_3 := h2075c.2.2.2
                                    linarith only [h1965, hlam, p2075_1]
                                  · have p2075_0 := h2075c.1
                                    have p2075_1 := h2075c.2.1
                                    have p2075_2 := h2075c.2.2.1
                                    have p2075_3 := h2075c.2.2.2
                                    linarith only [h0, hc01, hlam, hphi, ht12, p2075_1, u2elo1]
                                  · have p2075_0 := h2075c.1
                                    have p2075_1 := h2075c.2.1
                                    have p2075_2 := h2075c.2.2.1
                                    have p2075_3 := h2075c.2.2.2
                                    linarith only [hlam, p2075_0]
                                  · have p2075_0 := h2075c.1
                                    have p2075_1 := h2075c.2.1
                                    have p2075_2 := h2075c.2.2.1
                                    have p2075_3 := h2075c.2.2.2
                                    rcases p2075_3 (m.d 0 1) (by simp) with h2083 | h2083
                                    · linarith only [h0, h2083, hlam]
                                    · linarith only [h1694, h2083, hlam]
                                  · have p2075_0 := h2075c.1
                                    have p2075_1 := h2075c.2.1
                                    have p2075_2 := h2075c.2.2.1
                                    have p2075_3 := h2075c.2.2.2
                                    linarith only [h0, h1694, h1695, h2064, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2075_1, u2elo1]
                                  · have p2075_0 := h2075c.1
                                    have p2075_1 := h2075c.2.1
                                    have p2075_2 := h2075c.2.2.1
                                    have p2075_3 := h2075c.2.2.2
                                    linarith only [h0, h1694, h1965, h2064, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2075_1, u2elo1]
                                  · have p2075_0 := h2075c.1
                                    have p2075_1 := h2075c.2.1
                                    have p2075_2 := h2075c.2.2.1
                                    have p2075_3 := h2075c.2.2.2
                                    linarith only [h1694, hlam, p2075_1]
                                  · have p2075_0 := h2075c.1
                                    have p2075_1 := h2075c.2.1
                                    have p2075_2 := h2075c.2.2.1
                                    have p2075_3 := h2075c.2.2.2
                                    linarith only [h2056, hlam, p2075_1]
                                  · have p2075_0 := h2075c.1
                                    have p2075_1 := h2075c.2.1
                                    have p2075_2 := h2075c.2.2.1
                                    have p2075_3 := h2075c.2.2.2
                                    linarith only [hlam, p2075_0]
                                  · have p2075_0 := h2075c.1
                                    have p2075_1 := h2075c.2.1
                                    have p2075_2 := h2075c.2.2.1
                                    have p2075_3 := h2075c.2.2.2
                                    linarith only [h2059, hlam, p2075_1]
                                  · have p2075_0 := h2075c.1
                                    have p2075_1 := h2075c.2.1
                                    have p2075_2 := h2075c.2.2.1
                                    have p2075_3 := h2075c.2.2.2
                                    linarith only [h2061, hlam, p2075_1]
                                  · have p2075_0 := h2075c.1
                                    have p2075_1 := h2075c.2.1
                                    have p2075_2 := h2075c.2.2.1
                                    have p2075_3 := h2075c.2.2.2
                                    linarith only [h1694, h2064, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2075_1, u0elo3]
                                  · have p2075_0 := h2075c.1
                                    have p2075_1 := h2075c.2.1
                                    have p2075_2 := h2075c.2.2.1
                                    have p2075_3 := h2075c.2.2.2
                                    linarith only [h2057, hlam, p2075_0]
                                  · have p2075_0 := h2075c.1
                                    have p2075_1 := h2075c.2.1
                                    have p2075_2 := h2075c.2.2.1
                                    have p2075_3 := h2075c.2.2.2
                                    rcases p2075_3 (m.d 0 1) (by simp) with h2095 | h2095
                                    · linarith only [h1695, h2095, hlam]
                                    · linarith only [h1694, h2095, hlam]
                                  · have p2075_0 := h2075c.1
                                    have p2075_1 := h2075c.2.1
                                    have p2075_2 := h2075c.2.2.1
                                    have p2075_3 := h2075c.2.2.2
                                    linarith only [hlam, p2075_0]
                                  · have p2075_0 := h2075c.1
                                    have p2075_1 := h2075c.2.1
                                    have p2075_2 := h2075c.2.2.1
                                    have p2075_3 := h2075c.2.2.2
                                    linarith only [h1694, h1695, h1965, h2064, h2065, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2075_1, u2elo1]
                                  · have p2075_0 := h2075c.1
                                    have p2075_1 := h2075c.2.1
                                    have p2075_2 := h2075c.2.2.1
                                    have p2075_3 := h2075c.2.2.2
                                    linarith only [h1694, h2064, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2075_1, u0elo4]
                                  · have p2075_0 := h2075c.1
                                    have p2075_1 := h2075c.2.1
                                    have p2075_2 := h2075c.2.2.1
                                    have p2075_3 := h2075c.2.2.2
                                    linarith only [h2058, hlam, p2075_1]
                                  · have p2075_0 := h2075c.1
                                    have p2075_1 := h2075c.2.1
                                    have p2075_2 := h2075c.2.2.1
                                    have p2075_3 := h2075c.2.2.2
                                    rcases p2075_3 (m.d 0 1) (by simp) with h2102 | h2102
                                    · linarith only [h1965, h2102, hlam]
                                    · linarith only [h1694, h2102, hlam]
                                  · have p2075_0 := h2075c.1
                                    have p2075_1 := h2075c.2.1
                                    have p2075_2 := h2075c.2.2.1
                                    have p2075_3 := h2075c.2.2.2
                                    linarith only [h2063, hlam, p2075_1]
                                  · have p2075_0 := h2075c.1
                                    have p2075_1 := h2075c.2.1
                                    have p2075_2 := h2075c.2.2.1
                                    have p2075_3 := h2075c.2.2.2
                                    linarith only [hlam, p2075_0]
                                · linarith only [h0, h2057, h2073, h2074, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2108 | h2108
                                · rcases h0bigk with h2109c | h2109c | h2109c | h2109c | h2109c | h2109c | h2109c | h2109c | h2109c | h2109c | h2109c | h2109c | h2109c | h2109c | h2109c | h2109c | h2109c | h2109c | h2109c | h2109c | h2109c | h2109c | h2109c | h2109c | h2109c
                                  · have p2109_0 := h2109c.1
                                    have p2109_1 := h2109c.2.1
                                    have p2109_2 := h2109c.2.2.1
                                    have p2109_3 := h2109c.2.2.2
                                    linarith only [hlam, p2109_0]
                                  · have p2109_0 := h2109c.1
                                    have p2109_1 := h2109c.2.1
                                    have p2109_2 := h2109c.2.2.1
                                    have p2109_3 := h2109c.2.2.2
                                    linarith only [h0, hlam, p2109_1]
                                  · have p2109_0 := h2109c.1
                                    have p2109_1 := h2109c.2.1
                                    have p2109_2 := h2109c.2.2.1
                                    have p2109_3 := h2109c.2.2.2
                                    linarith only [h0, h1694, h2064, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2109_1, u2elo1]
                                  · have p2109_0 := h2109c.1
                                    have p2109_1 := h2109c.2.1
                                    have p2109_2 := h2109c.2.2.1
                                    have p2109_3 := h2109c.2.2.2
                                    linarith only [h1695, hlam, p2109_1]
                                  · have p2109_0 := h2109c.1
                                    have p2109_1 := h2109c.2.1
                                    have p2109_2 := h2109c.2.2.1
                                    have p2109_3 := h2109c.2.2.2
                                    linarith only [h1965, hlam, p2109_1]
                                  · have p2109_0 := h2109c.1
                                    have p2109_1 := h2109c.2.1
                                    have p2109_2 := h2109c.2.2.1
                                    have p2109_3 := h2109c.2.2.2
                                    linarith only [h0, hc01, hlam, hphi, ht12, p2109_1, u2elo1]
                                  · have p2109_0 := h2109c.1
                                    have p2109_1 := h2109c.2.1
                                    have p2109_2 := h2109c.2.2.1
                                    have p2109_3 := h2109c.2.2.2
                                    linarith only [hlam, p2109_0]
                                  · have p2109_0 := h2109c.1
                                    have p2109_1 := h2109c.2.1
                                    have p2109_2 := h2109c.2.2.1
                                    have p2109_3 := h2109c.2.2.2
                                    rcases p2109_3 (m.d 0 1) (by simp) with h2117 | h2117
                                    · linarith only [h0, h2117, hlam]
                                    · linarith only [h1694, h2117, hlam]
                                  · have p2109_0 := h2109c.1
                                    have p2109_1 := h2109c.2.1
                                    have p2109_2 := h2109c.2.2.1
                                    have p2109_3 := h2109c.2.2.2
                                    linarith only [h0, h2063, h2073, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2109_1, u2elo1]
                                  · have p2109_0 := h2109c.1
                                    have p2109_1 := h2109c.2.1
                                    have p2109_2 := h2109c.2.2.1
                                    have p2109_3 := h2109c.2.2.2
                                    linarith only [h0, h1694, h1965, h2064, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2109_1, u2elo1]
                                  · have p2109_0 := h2109c.1
                                    have p2109_1 := h2109c.2.1
                                    have p2109_2 := h2109c.2.2.1
                                    have p2109_3 := h2109c.2.2.2
                                    linarith only [h1694, hlam, p2109_1]
                                  · have p2109_0 := h2109c.1
                                    have p2109_1 := h2109c.2.1
                                    have p2109_2 := h2109c.2.2.1
                                    have p2109_3 := h2109c.2.2.2
                                    linarith only [h2056, hlam, p2109_1]
                                  · have p2109_0 := h2109c.1
                                    have p2109_1 := h2109c.2.1
                                    have p2109_2 := h2109c.2.2.1
                                    have p2109_3 := h2109c.2.2.2
                                    linarith only [hlam, p2109_0]
                                  · have p2109_0 := h2109c.1
                                    have p2109_1 := h2109c.2.1
                                    have p2109_2 := h2109c.2.2.1
                                    have p2109_3 := h2109c.2.2.2
                                    linarith only [h2059, hlam, p2109_1]
                                  · have p2109_0 := h2109c.1
                                    have p2109_1 := h2109c.2.1
                                    have p2109_2 := h2109c.2.2.1
                                    have p2109_3 := h2109c.2.2.2
                                    linarith only [h2061, hlam, p2109_1]
                                  · have p2109_0 := h2109c.1
                                    have p2109_1 := h2109c.2.1
                                    have p2109_2 := h2109c.2.2.1
                                    have p2109_3 := h2109c.2.2.2
                                    linarith only [h1694, h2064, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2109_1, u0elo3]
                                  · have p2109_0 := h2109c.1
                                    have p2109_1 := h2109c.2.1
                                    have p2109_2 := h2109c.2.2.1
                                    have p2109_3 := h2109c.2.2.2
                                    linarith only [h2057, hlam, p2109_0]
                                  · have p2109_0 := h2109c.1
                                    have p2109_1 := h2109c.2.1
                                    have p2109_2 := h2109c.2.2.1
                                    have p2109_3 := h2109c.2.2.2
                                    rcases p2109_3 (m.d 0 1) (by simp) with h2129 | h2129
                                    · linarith only [h1695, h2129, hlam]
                                    · linarith only [h1694, h2129, hlam]
                                  · have p2109_0 := h2109c.1
                                    have p2109_1 := h2109c.2.1
                                    have p2109_2 := h2109c.2.2.1
                                    have p2109_3 := h2109c.2.2.2
                                    linarith only [hlam, p2109_0]
                                  · have p2109_0 := h2109c.1
                                    have p2109_1 := h2109c.2.1
                                    have p2109_2 := h2109c.2.2.1
                                    have p2109_3 := h2109c.2.2.2
                                    linarith only [h1694, h1695, h1965, h2064, h2065, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2109_1, u2elo1]
                                  · have p2109_0 := h2109c.1
                                    have p2109_1 := h2109c.2.1
                                    have p2109_2 := h2109c.2.2.1
                                    have p2109_3 := h2109c.2.2.2
                                    linarith only [h1694, h2064, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2109_1, u0elo4]
                                  · have p2109_0 := h2109c.1
                                    have p2109_1 := h2109c.2.1
                                    have p2109_2 := h2109c.2.2.1
                                    have p2109_3 := h2109c.2.2.2
                                    linarith only [h2058, hlam, p2109_1]
                                  · have p2109_0 := h2109c.1
                                    have p2109_1 := h2109c.2.1
                                    have p2109_2 := h2109c.2.2.1
                                    have p2109_3 := h2109c.2.2.2
                                    rcases p2109_3 (m.d 0 1) (by simp) with h2136 | h2136
                                    · linarith only [h1965, h2136, hlam]
                                    · linarith only [h1694, h2136, hlam]
                                  · have p2109_0 := h2109c.1
                                    have p2109_1 := h2109c.2.1
                                    have p2109_2 := h2109c.2.2.1
                                    have p2109_3 := h2109c.2.2.2
                                    linarith only [h2063, hlam, p2109_1]
                                  · have p2109_0 := h2109c.1
                                    have p2109_1 := h2109c.2.1
                                    have p2109_2 := h2109c.2.2.1
                                    have p2109_3 := h2109c.2.2.2
                                    linarith only [hlam, p2109_0]
                                · linarith only [h1694, h1695, h2064, h2066, h2108, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h1695, h2063, h2070, hlam]
                    · linarith only [h0, h1694, h2064, h2065, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1694, h2064, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2145 | h2145
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2146 | h2146
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2147 | h2147
                      · linarith only [h1694, h1695, h2146, h2147, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2149 | h2149
                        · linarith only [h1694, h1695, h2146, h2149, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2151 | h2151
                          · linarith only [h1695, h2063, h2146, h2151, hc01, hlam, hphi, ht12, u2elo1]
                          · linarith only [h1694, h1695, h2145, h2151, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h1694, h2145, h2146, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1694, h2145, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2156 | h2156
            · linarith only [h1694, h1695, h2156, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2158 | h2158
              · linarith only [h0, h1694, h2058, h2158, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2160 | h2160
                · linarith only [h2057, h2058, h2160, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2162 | h2162
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2163 | h2163
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2164 | h2164
                      · linarith only [h1694, h2156, h2164, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h2166 | h2166
                        · linarith only [h1694, h1695, h2057, h2058, h2158, h2166, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h2168 | h2168
                          · linarith only [h1694, h1695, h2160, h2164, h2168, hc13, hc34, hlam, hphi]
                          · linarith only [h1694, h1695, h2162, h2168, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h2057, h2058, h2163, hc12, hlam, hphi, u2elo4]
                  · linarith only [h0, h2162, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h2173 | h2173
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2174 | h2174
            · linarith only [h0, h1694, h2057, h2174, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2176 | h2176
              · linarith only [h1694, h1965, h2176, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2178 | h2178
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2179 | h2179
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2180 | h2180
                    · linarith only [h1694, h1965, h2057, h2173, h2179, h2180, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1694, h2179, h2180, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h2179, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h2057, h2173, h2178, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h2185 | h2185
            · linarith only [h0, h1694, h2057, h2185, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h2187 | h2187
              · linarith only [h0, h1694, h2173, h2187, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h2189 | h2189
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2190 | h2190
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2191 | h2191
                    · linarith only [h0, h1694, h2057, h2190, h2191, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1694, h2190, h2191, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h2190, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h2195 | h2195
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h2196 | h2196
                    · linarith only [h0, h1694, h2057, h2195, h2196, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1694, h2195, h2196, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1694, h2195, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
      · linarith only [h0, h1694, h2056, hlam]

end R2N4
