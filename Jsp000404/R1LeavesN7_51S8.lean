import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5346000 in
set_option maxHeartbeats 5346000 in
theorem r1l7_11_13_25_L_I_L_I_H_L_x1_x1_x1_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1403 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1593 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1700 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h1701 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h1702 | h1702
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1703 | h1703
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1704 | h1704
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1705 | h1705
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1706 | h1706
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1707 | h1707
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1708 | h1708
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1709 | h1709
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1710 | h1710
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1711 | h1711
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1712 | h1712
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1713 | h1713
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1714 | h1714
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1715 | h1715
                            · rcases h1bigk with h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c
                              · have p1716_0 := h1716c.1
                                have p1716_1 := h1716c.2.1
                                have p1716_2 := h1716c.2.2.1
                                have p1716_3 := h1716c.2.2.2
                                linarith only [hlam, p1716_0]
                              · have p1716_0 := h1716c.1
                                have p1716_1 := h1716c.2.1
                                have p1716_2 := h1716c.2.2.1
                                have p1716_3 := h1716c.2.2.2
                                linarith only [h0, hlam, p1716_0]
                              · have p1716_0 := h1716c.1
                                have p1716_1 := h1716c.2.1
                                have p1716_2 := h1716c.2.2.1
                                have p1716_3 := h1716c.2.2.2
                                linarith only [h1403, hlam, p1716_0]
                              · have p1716_0 := h1716c.1
                                have p1716_1 := h1716c.2.1
                                have p1716_2 := h1716c.2.2.1
                                have p1716_3 := h1716c.2.2.2
                                linarith only [h1593, hlam, p1716_0]
                              · have p1716_0 := h1716c.1
                                have p1716_1 := h1716c.2.1
                                have p1716_2 := h1716c.2.2.1
                                have p1716_3 := h1716c.2.2.2
                                rcases p1716_3 (m.d 0 1) (by simp) with h1721 | h1721
                                · rcases p1716_3 (m.d 1 2) (by simp) with h1722 | h1722
                                  · rcases p1716_3 (m.d 1 3) (by simp) with h1723 | h1723
                                    · rcases p1716_3 (m.d 1 4) (by simp) with h1724 | h1724
                                      · rcases p1716_3 (m.d 1 5) (by simp) with h1725 | h1725
                                        · linarith only [h1725, hlam, p1716_0]
                                        · rcases h3bigk with h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c | h1727c
                                          · have p1727_0 := h1727c.1
                                            have p1727_1 := h1727c.2.1
                                            have p1727_2 := h1727c.2.2.1
                                            have p1727_3 := h1727c.2.2.2
                                            linarith only [hlam, p1727_0]
                                          · have p1727_0 := h1727c.1
                                            have p1727_1 := h1727c.2.1
                                            have p1727_2 := h1727c.2.2.1
                                            have p1727_3 := h1727c.2.2.2
                                            linarith only [h1403, hlam, p1727_1]
                                          · have p1727_0 := h1727c.1
                                            have p1727_1 := h1727c.2.1
                                            have p1727_2 := h1727c.2.2.1
                                            have p1727_3 := h1727c.2.2.2
                                            linarith only [h1712, h1715, hc03, hc45, hlam, hphi, ht0b, ht5b, p1727_1]
                                          · have p1727_0 := h1727c.1
                                            have p1727_1 := h1727c.2.1
                                            have p1727_2 := h1727c.2.2.1
                                            have p1727_3 := h1727c.2.2.2
                                            rcases p1727_3 (m.d 0 3) (by simp) with h1731 | h1731
                                            · rcases p1727_3 (m.d 1 3) (by simp) with h1732 | h1732
                                              · rcases p1727_3 (m.d 2 3) (by simp) with h1733 | h1733
                                                · linarith only [h1701, h1733, hlam]
                                                · linarith only [h1712, h1733, hlam]
                                              · linarith only [h1709, h1732, hlam]
                                            · linarith only [h1731, hlam, p1727_0]
                                          · have p1727_0 := h1727c.1
                                            have p1727_1 := h1727c.2.1
                                            have p1727_2 := h1727c.2.2.1
                                            have p1727_3 := h1727c.2.2.2
                                            rcases p1727_3 (m.d 0 3) (by simp) with h1738 | h1738
                                            · rcases p1727_3 (m.d 1 3) (by simp) with h1739 | h1739
                                              · rcases p1727_3 (m.d 2 3) (by simp) with h1740 | h1740
                                                · linarith only [h1701, h1740, hlam]
                                                · linarith only [h1713, h1740, hlam]
                                              · linarith only [h1710, h1739, hlam]
                                            · linarith only [h1738, hlam, p1727_0]
                                          · have p1727_0 := h1727c.1
                                            have p1727_1 := h1727c.2.1
                                            have p1727_2 := h1727c.2.2.1
                                            have p1727_3 := h1727c.2.2.2
                                            linarith only [h1403, h1706, h1708, h1713, h1715, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1716_1, p1727_1]
                                          · have p1727_0 := h1727c.1
                                            have p1727_1 := h1727c.2.1
                                            have p1727_2 := h1727c.2.2.1
                                            have p1727_3 := h1727c.2.2.2
                                            linarith only [hlam, p1727_0]
                                          · have p1727_0 := h1727c.1
                                            have p1727_1 := h1727c.2.1
                                            have p1727_2 := h1727c.2.2.1
                                            have p1727_3 := h1727c.2.2.2
                                            linarith only [h1706, h1712, h1715, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1727_1]
                                          · have p1727_0 := h1727c.1
                                            have p1727_1 := h1727c.2.1
                                            have p1727_2 := h1727c.2.2.1
                                            have p1727_3 := h1727c.2.2.2
                                            rcases p1727_3 (m.d 0 3) (by simp) with h1748 | h1748
                                            · linarith only [h1403, h1748, hlam]
                                            · linarith only [h1704, h1748, hlam]
                                          · have p1727_0 := h1727c.1
                                            have p1727_1 := h1727c.2.1
                                            have p1727_2 := h1727c.2.2.1
                                            have p1727_3 := h1727c.2.2.2
                                            linarith only [h1403, h1708, h1713, hlam, p1716_1, p1727_2]
                                          · have p1727_0 := h1727c.1
                                            have p1727_1 := h1727c.2.1
                                            have p1727_2 := h1727c.2.2.1
                                            have p1727_3 := h1727c.2.2.2
                                            linarith only [h1701, hlam, p1727_0]
                                          · have p1727_0 := h1727c.1
                                            have p1727_1 := h1727c.2.1
                                            have p1727_2 := h1727c.2.2.1
                                            have p1727_3 := h1727c.2.2.2
                                            linarith only [h1706, hlam, p1727_0]
                                          · have p1727_0 := h1727c.1
                                            have p1727_1 := h1727c.2.1
                                            have p1727_2 := h1727c.2.2.1
                                            have p1727_3 := h1727c.2.2.2
                                            linarith only [hlam, p1727_0]
                                          · have p1727_0 := h1727c.1
                                            have p1727_1 := h1727c.2.1
                                            have p1727_2 := h1727c.2.2.1
                                            have p1727_3 := h1727c.2.2.2
                                            linarith only [h1701, h1715, hc02, hc45, hlam, hphi, ht0b, ht5b, p1727_1]
                                          · have p1727_0 := h1727c.1
                                            have p1727_1 := h1727c.2.1
                                            have p1727_2 := h1727c.2.2.1
                                            have p1727_3 := h1727c.2.2.2
                                            rcases p1727_3 (m.d 0 3) (by simp) with h1756 | h1756
                                            · rcases p1727_3 (m.d 1 3) (by simp) with h1757 | h1757
                                              · rcases p1727_3 (m.d 2 3) (by simp) with h1758 | h1758
                                                · rcases p1727_3 (m.d 3 4) (by simp) with h1759 | h1759
                                                  · linarith only [h1712, h1759, hlam]
                                                  · linarith only [h1715, h1759, hlam]
                                                · linarith only [h1758, hlam, p1727_0]
                                              · linarith only [h1710, h1757, hlam]
                                            · linarith only [h1705, h1756, hlam]
                                          · have p1727_0 := h1727c.1
                                            have p1727_1 := h1727c.2.1
                                            have p1727_2 := h1727c.2.2.1
                                            have p1727_3 := h1727c.2.2.2
                                            linarith only [h1704, hlam, p1727_0]
                                          · have p1727_0 := h1727c.1
                                            have p1727_1 := h1727c.2.1
                                            have p1727_2 := h1727c.2.2.1
                                            have p1727_3 := h1727c.2.2.2
                                            linarith only [h1709, hlam, p1727_0]
                                          · have p1727_0 := h1727c.1
                                            have p1727_1 := h1727c.2.1
                                            have p1727_2 := h1727c.2.2.1
                                            have p1727_3 := h1727c.2.2.2
                                            linarith only [h1712, hlam, p1727_0]
                                          · have p1727_0 := h1727c.1
                                            have p1727_1 := h1727c.2.1
                                            have p1727_2 := h1727c.2.2.1
                                            have p1727_3 := h1727c.2.2.2
                                            linarith only [hlam, p1727_0]
                                          · have p1727_0 := h1727c.1
                                            have p1727_1 := h1727c.2.1
                                            have p1727_2 := h1727c.2.2.1
                                            have p1727_3 := h1727c.2.2.2
                                            linarith only [h0, h1701, h1712, h1715, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1727_1]
                                          · have p1727_0 := h1727c.1
                                            have p1727_1 := h1727c.2.1
                                            have p1727_2 := h1727c.2.2.1
                                            have p1727_3 := h1727c.2.2.2
                                            linarith only [h1705, hlam, p1727_0]
                                          · have p1727_0 := h1727c.1
                                            have p1727_1 := h1727c.2.1
                                            have p1727_2 := h1727c.2.2.1
                                            have p1727_3 := h1727c.2.2.2
                                            linarith only [h1710, hlam, p1727_0]
                                          · have p1727_0 := h1727c.1
                                            have p1727_1 := h1727c.2.1
                                            have p1727_2 := h1727c.2.2.1
                                            have p1727_3 := h1727c.2.2.2
                                            linarith only [h1713, hlam, p1727_0]
                                          · have p1727_0 := h1727c.1
                                            have p1727_1 := h1727c.2.1
                                            have p1727_2 := h1727c.2.2.1
                                            have p1727_3 := h1727c.2.2.2
                                            linarith only [h1715, hlam, p1727_0]
                                          · have p1727_0 := h1727c.1
                                            have p1727_1 := h1727c.2.1
                                            have p1727_2 := h1727c.2.2.1
                                            have p1727_3 := h1727c.2.2.2
                                            linarith only [hlam, p1727_0]
                                      · linarith only [h1711, h1724, hlam]
                                    · linarith only [h1710, h1723, hlam]
                                  · linarith only [h1708, h1722, hlam]
                                · linarith only [h1721, hlam, p1716_0]
                              · have p1716_0 := h1716c.1
                                have p1716_1 := h1716c.2.1
                                have p1716_2 := h1716c.2.2.1
                                have p1716_3 := h1716c.2.2.2
                                rcases p1716_3 (m.d 0 1) (by simp) with h1779 | h1779
                                · linarith only [h1779, hlam, p1716_0]
                                · rcases p1716_3 (m.d 1 2) (by simp) with h1781 | h1781
                                  · rcases p1716_3 (m.d 1 3) (by simp) with h1782 | h1782
                                    · linarith only [h1706, h1782, hlam]
                                    · linarith only [h1403, h1782, hlam]
                                  · linarith only [h1781, hlam, p1716_0]
                              · have p1716_0 := h1716c.1
                                have p1716_1 := h1716c.2.1
                                have p1716_2 := h1716c.2.2.1
                                have p1716_3 := h1716c.2.2.2
                                linarith only [hlam, p1716_0]
                              · have p1716_0 := h1716c.1
                                have p1716_1 := h1716c.2.1
                                have p1716_2 := h1716c.2.2.1
                                have p1716_3 := h1716c.2.2.2
                                linarith only [h1403, hc01, hc12, hlam, hphi, p1716_1]
                              · have p1716_0 := h1716c.1
                                have p1716_1 := h1716c.2.1
                                have p1716_2 := h1716c.2.2.1
                                have p1716_3 := h1716c.2.2.2
                                linarith only [h1593, h1700, h1708, h1713, h1715, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1716_1]
                              · have p1716_0 := h1716c.1
                                have p1716_1 := h1716c.2.1
                                have p1716_2 := h1716c.2.2.1
                                have p1716_3 := h1716c.2.2.2
                                rcases p1716_3 (m.d 0 1) (by simp) with h1789 | h1789
                                · linarith only [h0, h1789, hlam]
                                · linarith only [h1700, h1789, hlam]
                              · have p1716_0 := h1716c.1
                                have p1716_1 := h1716c.2.1
                                have p1716_2 := h1716c.2.2.1
                                have p1716_3 := h1716c.2.2.2
                                rcases p1716_3 (m.d 0 1) (by simp) with h1792 | h1792
                                · linarith only [h1792, hlam, p1716_0]
                                · rcases p1716_3 (m.d 1 2) (by simp) with h1794 | h1794
                                  · rcases p1716_3 (m.d 1 3) (by simp) with h1795 | h1795
                                    · rcases p1716_3 (m.d 1 4) (by simp) with h1796 | h1796
                                      · linarith only [h1709, h1796, hlam]
                                      · linarith only [h1593, h1796, hlam]
                                    · linarith only [h1795, hlam, p1716_0]
                                  · linarith only [h0, h1794, hlam]
                              · have p1716_0 := h1716c.1
                                have p1716_1 := h1716c.2.1
                                have p1716_2 := h1716c.2.2.1
                                have p1716_3 := h1716c.2.2.2
                                linarith only [h1706, hlam, p1716_1]
                              · have p1716_0 := h1716c.1
                                have p1716_1 := h1716c.2.1
                                have p1716_2 := h1716c.2.2.1
                                have p1716_3 := h1716c.2.2.2
                                linarith only [hlam, p1716_0]
                              · have p1716_0 := h1716c.1
                                have p1716_1 := h1716c.2.1
                                have p1716_2 := h1716c.2.2.1
                                have p1716_3 := h1716c.2.2.2
                                linarith only [h1593, h1700, h1706, h1708, h1713, h1715, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1716_1]
                              · have p1716_0 := h1716c.1
                                have p1716_1 := h1716c.2.1
                                have p1716_2 := h1716c.2.2.1
                                have p1716_3 := h1716c.2.2.2
                                rcases p1716_3 (m.d 0 1) (by simp) with h1804 | h1804
                                · linarith only [h1403, h1804, hlam]
                                · linarith only [h1700, h1804, hlam]
                              · have p1716_0 := h1716c.1
                                have p1716_1 := h1716c.2.1
                                have p1716_2 := h1716c.2.2.1
                                have p1716_3 := h1716c.2.2.2
                                rcases p1716_3 (m.d 0 1) (by simp) with h1807 | h1807
                                · linarith only [h1807, hlam, p1716_0]
                                · rcases p1716_3 (m.d 1 2) (by simp) with h1809 | h1809
                                  · rcases p1716_3 (m.d 1 3) (by simp) with h1810 | h1810
                                    · rcases p1716_3 (m.d 1 4) (by simp) with h1811 | h1811
                                      · rcases p1716_3 (m.d 1 5) (by simp) with h1812 | h1812
                                        · linarith only [h1711, h1812, hlam]
                                        · rcases h3bigk with h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c | h1814c
                                          · have p1814_0 := h1814c.1
                                            have p1814_1 := h1814c.2.1
                                            have p1814_2 := h1814c.2.2.1
                                            have p1814_3 := h1814c.2.2.2
                                            linarith only [hlam, p1814_0]
                                          · have p1814_0 := h1814c.1
                                            have p1814_1 := h1814c.2.1
                                            have p1814_2 := h1814c.2.2.1
                                            have p1814_3 := h1814c.2.2.2
                                            linarith only [h1403, hlam, p1814_1]
                                          · have p1814_0 := h1814c.1
                                            have p1814_1 := h1814c.2.1
                                            have p1814_2 := h1814c.2.2.1
                                            have p1814_3 := h1814c.2.2.2
                                            linarith only [h0, h1701, h1712, h1715, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1814_1]
                                          · have p1814_0 := h1814c.1
                                            have p1814_1 := h1814c.2.1
                                            have p1814_2 := h1814c.2.2.1
                                            have p1814_3 := h1814c.2.2.2
                                            rcases p1814_3 (m.d 0 3) (by simp) with h1818 | h1818
                                            · rcases p1814_3 (m.d 1 3) (by simp) with h1819 | h1819
                                              · rcases p1814_3 (m.d 2 3) (by simp) with h1820 | h1820
                                                · linarith only [h1701, h1820, hlam]
                                                · linarith only [h1712, h1820, hlam]
                                              · linarith only [h1709, h1819, hlam]
                                            · linarith only [h1818, hlam, p1814_0]
                                          · have p1814_0 := h1814c.1
                                            have p1814_1 := h1814c.2.1
                                            have p1814_2 := h1814c.2.2.1
                                            have p1814_3 := h1814c.2.2.2
                                            rcases p1814_3 (m.d 0 3) (by simp) with h1825 | h1825
                                            · rcases p1814_3 (m.d 1 3) (by simp) with h1826 | h1826
                                              · rcases p1814_3 (m.d 2 3) (by simp) with h1827 | h1827
                                                · linarith only [h1701, h1827, hlam]
                                                · linarith only [h1713, h1827, hlam]
                                              · linarith only [h1710, h1826, hlam]
                                            · linarith only [h1825, hlam, p1814_0]
                                          · have p1814_0 := h1814c.1
                                            have p1814_1 := h1814c.2.1
                                            have p1814_2 := h1814c.2.2.1
                                            have p1814_3 := h1814c.2.2.2
                                            linarith only [h1701, h1706, h1712, h1715, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1814_1]
                                          · have p1814_0 := h1814c.1
                                            have p1814_1 := h1814c.2.1
                                            have p1814_2 := h1814c.2.2.1
                                            have p1814_3 := h1814c.2.2.2
                                            linarith only [hlam, p1814_0]
                                          · have p1814_0 := h1814c.1
                                            have p1814_1 := h1814c.2.1
                                            have p1814_2 := h1814c.2.2.1
                                            have p1814_3 := h1814c.2.2.2
                                            linarith only [h1706, h1712, h1715, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1814_1]
                                          · have p1814_0 := h1814c.1
                                            have p1814_1 := h1814c.2.1
                                            have p1814_2 := h1814c.2.2.1
                                            have p1814_3 := h1814c.2.2.2
                                            rcases p1814_3 (m.d 0 3) (by simp) with h1835 | h1835
                                            · linarith only [h1403, h1835, hlam]
                                            · linarith only [h1704, h1835, hlam]
                                          · have p1814_0 := h1814c.1
                                            have p1814_1 := h1814c.2.1
                                            have p1814_2 := h1814c.2.2.1
                                            have p1814_3 := h1814c.2.2.2
                                            linarith only [h1700, h1708, h1709, h1713, hlam, p1716_1, p1814_2]
                                          · have p1814_0 := h1814c.1
                                            have p1814_1 := h1814c.2.1
                                            have p1814_2 := h1814c.2.2.1
                                            have p1814_3 := h1814c.2.2.2
                                            linarith only [h1701, hlam, p1814_0]
                                          · have p1814_0 := h1814c.1
                                            have p1814_1 := h1814c.2.1
                                            have p1814_2 := h1814c.2.2.1
                                            have p1814_3 := h1814c.2.2.2
                                            linarith only [h1706, hlam, p1814_0]
                                          · have p1814_0 := h1814c.1
                                            have p1814_1 := h1814c.2.1
                                            have p1814_2 := h1814c.2.2.1
                                            have p1814_3 := h1814c.2.2.2
                                            linarith only [hlam, p1814_0]
                                          · have p1814_0 := h1814c.1
                                            have p1814_1 := h1814c.2.1
                                            have p1814_2 := h1814c.2.2.1
                                            have p1814_3 := h1814c.2.2.2
                                            linarith only [h0, h1701, h1715, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1814_1]
                                          · have p1814_0 := h1814c.1
                                            have p1814_1 := h1814c.2.1
                                            have p1814_2 := h1814c.2.2.1
                                            have p1814_3 := h1814c.2.2.2
                                            rcases p1814_3 (m.d 0 3) (by simp) with h1843 | h1843
                                            · rcases p1814_3 (m.d 1 3) (by simp) with h1844 | h1844
                                              · rcases p1814_3 (m.d 2 3) (by simp) with h1845 | h1845
                                                · rcases p1814_3 (m.d 3 4) (by simp) with h1846 | h1846
                                                  · linarith only [h1712, h1846, hlam]
                                                  · linarith only [h1715, h1846, hlam]
                                                · linarith only [h1845, hlam, p1814_0]
                                              · linarith only [h1710, h1844, hlam]
                                            · linarith only [h1705, h1843, hlam]
                                          · have p1814_0 := h1814c.1
                                            have p1814_1 := h1814c.2.1
                                            have p1814_2 := h1814c.2.2.1
                                            have p1814_3 := h1814c.2.2.2
                                            linarith only [h1704, hlam, p1814_0]
                                          · have p1814_0 := h1814c.1
                                            have p1814_1 := h1814c.2.1
                                            have p1814_2 := h1814c.2.2.1
                                            have p1814_3 := h1814c.2.2.2
                                            linarith only [h1709, hlam, p1814_0]
                                          · have p1814_0 := h1814c.1
                                            have p1814_1 := h1814c.2.1
                                            have p1814_2 := h1814c.2.2.1
                                            have p1814_3 := h1814c.2.2.2
                                            linarith only [h1712, hlam, p1814_0]
                                          · have p1814_0 := h1814c.1
                                            have p1814_1 := h1814c.2.1
                                            have p1814_2 := h1814c.2.2.1
                                            have p1814_3 := h1814c.2.2.2
                                            linarith only [hlam, p1814_0]
                                          · have p1814_0 := h1814c.1
                                            have p1814_1 := h1814c.2.1
                                            have p1814_2 := h1814c.2.2.1
                                            have p1814_3 := h1814c.2.2.2
                                            linarith only [h0, h1701, h1712, h1715, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1814_1]
                                          · have p1814_0 := h1814c.1
                                            have p1814_1 := h1814c.2.1
                                            have p1814_2 := h1814c.2.2.1
                                            have p1814_3 := h1814c.2.2.2
                                            linarith only [h1705, hlam, p1814_0]
                                          · have p1814_0 := h1814c.1
                                            have p1814_1 := h1814c.2.1
                                            have p1814_2 := h1814c.2.2.1
                                            have p1814_3 := h1814c.2.2.2
                                            linarith only [h1710, hlam, p1814_0]
                                          · have p1814_0 := h1814c.1
                                            have p1814_1 := h1814c.2.1
                                            have p1814_2 := h1814c.2.2.1
                                            have p1814_3 := h1814c.2.2.2
                                            linarith only [h1713, hlam, p1814_0]
                                          · have p1814_0 := h1814c.1
                                            have p1814_1 := h1814c.2.1
                                            have p1814_2 := h1814c.2.2.1
                                            have p1814_3 := h1814c.2.2.2
                                            linarith only [h1715, hlam, p1814_0]
                                          · have p1814_0 := h1814c.1
                                            have p1814_1 := h1814c.2.1
                                            have p1814_2 := h1814c.2.2.1
                                            have p1814_3 := h1814c.2.2.2
                                            linarith only [hlam, p1814_0]
                                      · linarith only [h1811, hlam, p1716_0]
                                    · linarith only [h1403, h1810, hlam]
                                  · linarith only [h0, h1809, hlam]
                              · have p1716_0 := h1716c.1
                                have p1716_1 := h1716c.2.1
                                have p1716_2 := h1716c.2.2.1
                                have p1716_3 := h1716c.2.2.2
                                linarith only [h1707, hlam, p1716_1]
                              · have p1716_0 := h1716c.1
                                have p1716_1 := h1716c.2.1
                                have p1716_2 := h1716c.2.2.1
                                have p1716_3 := h1716c.2.2.2
                                linarith only [h1709, hlam, p1716_0]
                              · have p1716_0 := h1716c.1
                                have p1716_1 := h1716c.2.1
                                have p1716_2 := h1716c.2.2.1
                                have p1716_3 := h1716c.2.2.2
                                linarith only [hlam, p1716_0]
                              · have p1716_0 := h1716c.1
                                have p1716_1 := h1716c.2.1
                                have p1716_2 := h1716c.2.2.1
                                have p1716_3 := h1716c.2.2.2
                                rcases p1716_3 (m.d 0 1) (by simp) with h1868 | h1868
                                · linarith only [h1593, h1868, hlam]
                                · linarith only [h1700, h1868, hlam]
                              · have p1716_0 := h1716c.1
                                have p1716_1 := h1716c.2.1
                                have p1716_2 := h1716c.2.2.1
                                have p1716_3 := h1716c.2.2.2
                                linarith only [h1700, hlam, p1716_0]
                              · have p1716_0 := h1716c.1
                                have p1716_1 := h1716c.2.1
                                have p1716_2 := h1716c.2.2.1
                                have p1716_3 := h1716c.2.2.2
                                linarith only [h1708, hlam, p1716_1]
                              · have p1716_0 := h1716c.1
                                have p1716_1 := h1716c.2.1
                                have p1716_2 := h1716c.2.2.1
                                have p1716_3 := h1716c.2.2.2
                                linarith only [h1710, hlam, p1716_0]
                              · have p1716_0 := h1716c.1
                                have p1716_1 := h1716c.2.1
                                have p1716_2 := h1716c.2.2.1
                                have p1716_3 := h1716c.2.2.2
                                linarith only [h1711, hlam, p1716_0]
                              · have p1716_0 := h1716c.1
                                have p1716_1 := h1716c.2.1
                                have p1716_2 := h1716c.2.2.1
                                have p1716_3 := h1716c.2.2.2
                                linarith only [hlam, p1716_0]
                            · linarith only [h1715, hc34, hlam, hphi, ht45, u5elo4]
                          · linarith only [h1711, h1714, hc24, hlam, hphi, ht45, u5elo1]
                        · linarith only [h1713, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1879 | h1879
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1880 | h1880
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1881 | h1881
                            · rcases h1bigk with h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c | h1882c
                              · have p1882_0 := h1882c.1
                                have p1882_1 := h1882c.2.1
                                have p1882_2 := h1882c.2.2.1
                                have p1882_3 := h1882c.2.2.2
                                linarith only [hlam, p1882_0]
                              · have p1882_0 := h1882c.1
                                have p1882_1 := h1882c.2.1
                                have p1882_2 := h1882c.2.2.1
                                have p1882_3 := h1882c.2.2.2
                                linarith only [h0, hlam, p1882_0]
                              · have p1882_0 := h1882c.1
                                have p1882_1 := h1882c.2.1
                                have p1882_2 := h1882c.2.2.1
                                have p1882_3 := h1882c.2.2.2
                                linarith only [h1403, hlam, p1882_0]
                              · have p1882_0 := h1882c.1
                                have p1882_1 := h1882c.2.1
                                have p1882_2 := h1882c.2.2.1
                                have p1882_3 := h1882c.2.2.2
                                linarith only [h1593, hlam, p1882_0]
                              · have p1882_0 := h1882c.1
                                have p1882_1 := h1882c.2.1
                                have p1882_2 := h1882c.2.2.1
                                have p1882_3 := h1882c.2.2.2
                                rcases p1882_3 (m.d 0 1) (by simp) with h1887 | h1887
                                · rcases p1882_3 (m.d 1 2) (by simp) with h1888 | h1888
                                  · rcases p1882_3 (m.d 1 3) (by simp) with h1889 | h1889
                                    · rcases p1882_3 (m.d 1 4) (by simp) with h1890 | h1890
                                      · rcases p1882_3 (m.d 1 5) (by simp) with h1891 | h1891
                                        · linarith only [h1891, hlam, p1882_0]
                                        · rcases h3bigk with h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c | h1893c
                                          · have p1893_0 := h1893c.1
                                            have p1893_1 := h1893c.2.1
                                            have p1893_2 := h1893c.2.2.1
                                            have p1893_3 := h1893c.2.2.2
                                            linarith only [hlam, p1893_0]
                                          · have p1893_0 := h1893c.1
                                            have p1893_1 := h1893c.2.1
                                            have p1893_2 := h1893c.2.2.1
                                            have p1893_3 := h1893c.2.2.2
                                            linarith only [h1403, hlam, p1893_1]
                                          · have p1893_0 := h1893c.1
                                            have p1893_1 := h1893c.2.1
                                            have p1893_2 := h1893c.2.2.1
                                            have p1893_3 := h1893c.2.2.2
                                            rcases p1893_3 (m.d 0 3) (by simp) with h1896 | h1896
                                            · rcases p1893_3 (m.d 1 3) (by simp) with h1897 | h1897
                                              · rcases p1893_3 (m.d 2 3) (by simp) with h1898 | h1898
                                                · linarith only [h1701, h1898, hlam]
                                                · rcases p1893_3 (m.d 3 4) (by simp) with h1900 | h1900
                                                  · linarith only [h1704, h1900, hlam]
                                                  · linarith only [h1712, h1900, hlam]
                                              · linarith only [h1706, h1897, hlam]
                                            · linarith only [h1701, h1896, hlam]
                                          · have p1893_0 := h1893c.1
                                            have p1893_1 := h1893c.2.1
                                            have p1893_2 := h1893c.2.2.1
                                            have p1893_3 := h1893c.2.2.2
                                            linarith only [h1712, h1879, h1881, hc03, hc45, hlam, hphi, ht0b, ht5b, p1893_1]
                                          · have p1893_0 := h1893c.1
                                            have p1893_1 := h1893c.2.1
                                            have p1893_2 := h1893c.2.2.1
                                            have p1893_3 := h1893c.2.2.2
                                            linarith only [h1704, h1712, h1879, hlam, p1893_2]
                                          · have p1893_0 := h1893c.1
                                            have p1893_1 := h1893c.2.1
                                            have p1893_2 := h1893c.2.2.1
                                            have p1893_3 := h1893c.2.2.2
                                            linarith only [h1403, h1706, h1708, h1879, h1881, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1882_1, p1893_1]
                                          · have p1893_0 := h1893c.1
                                            have p1893_1 := h1893c.2.1
                                            have p1893_2 := h1893c.2.2.1
                                            have p1893_3 := h1893c.2.2.2
                                            linarith only [hlam, p1893_0]
                                          · have p1893_0 := h1893c.1
                                            have p1893_1 := h1893c.2.1
                                            have p1893_2 := h1893c.2.2.1
                                            have p1893_3 := h1893c.2.2.2
                                            rcases p1893_3 (m.d 0 3) (by simp) with h1909 | h1909
                                            · linarith only [h1403, h1909, hlam]
                                            · linarith only [h1701, h1909, hlam]
                                          · have p1893_0 := h1893c.1
                                            have p1893_1 := h1893c.2.1
                                            have p1893_2 := h1893c.2.2.1
                                            have p1893_3 := h1893c.2.2.2
                                            linarith only [h1706, h1712, h1879, h1881, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1893_1]
                                          · have p1893_0 := h1893c.1
                                            have p1893_1 := h1893c.2.1
                                            have p1893_2 := h1893c.2.2.1
                                            have p1893_3 := h1893c.2.2.2
                                            linarith only [h1403, h1708, h1879, hlam, p1882_1, p1893_2]
                                          · have p1893_0 := h1893c.1
                                            have p1893_1 := h1893c.2.1
                                            have p1893_2 := h1893c.2.2.1
                                            have p1893_3 := h1893c.2.2.2
                                            linarith only [h1701, hlam, p1893_0]
                                          · have p1893_0 := h1893c.1
                                            have p1893_1 := h1893c.2.1
                                            have p1893_2 := h1893c.2.2.1
                                            have p1893_3 := h1893c.2.2.2
                                            linarith only [h1706, hlam, p1893_0]
                                          · have p1893_0 := h1893c.1
                                            have p1893_1 := h1893c.2.1
                                            have p1893_2 := h1893c.2.2.1
                                            have p1893_3 := h1893c.2.2.2
                                            linarith only [hlam, p1893_0]
                                          · have p1893_0 := h1893c.1
                                            have p1893_1 := h1893c.2.1
                                            have p1893_2 := h1893c.2.2.1
                                            have p1893_3 := h1893c.2.2.2
                                            linarith only [h1712, hlam, p1893_0]
                                          · have p1893_0 := h1893c.1
                                            have p1893_1 := h1893c.2.1
                                            have p1893_2 := h1893c.2.2.1
                                            have p1893_3 := h1893c.2.2.2
                                            linarith only [h1704, h1712, h1881, hc03, hc45, hlam, hphi, ht0b, ht5b, p1893_1]
                                          · have p1893_0 := h1893c.1
                                            have p1893_1 := h1893c.2.1
                                            have p1893_2 := h1893c.2.2.1
                                            have p1893_3 := h1893c.2.2.2
                                            linarith only [h1704, hlam, p1893_0]
                                          · have p1893_0 := h1893c.1
                                            have p1893_1 := h1893c.2.1
                                            have p1893_2 := h1893c.2.2.1
                                            have p1893_3 := h1893c.2.2.2
                                            linarith only [h1709, hlam, p1893_0]
                                          · have p1893_0 := h1893c.1
                                            have p1893_1 := h1893c.2.1
                                            have p1893_2 := h1893c.2.2.1
                                            have p1893_3 := h1893c.2.2.2
                                            linarith only [h0, h1701, h1704, h1879, h1881, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1893_1]
                                          · have p1893_0 := h1893c.1
                                            have p1893_1 := h1893c.2.1
                                            have p1893_2 := h1893c.2.2.1
                                            have p1893_3 := h1893c.2.2.2
                                            linarith only [hlam, p1893_0]
                                          · have p1893_0 := h1893c.1
                                            have p1893_1 := h1893c.2.1
                                            have p1893_2 := h1893c.2.2.1
                                            have p1893_3 := h1893c.2.2.2
                                            rcases p1893_3 (m.d 0 3) (by simp) with h1923 | h1923
                                            · rcases p1893_3 (m.d 1 3) (by simp) with h1924 | h1924
                                              · rcases p1893_3 (m.d 2 3) (by simp) with h1925 | h1925
                                                · linarith only [h1712, h1925, hlam]
                                                · linarith only [h1879, h1925, hlam]
                                              · linarith only [h1710, h1924, hlam]
                                            · linarith only [h1705, h1923, hlam]
                                          · have p1893_0 := h1893c.1
                                            have p1893_1 := h1893c.2.1
                                            have p1893_2 := h1893c.2.2.1
                                            have p1893_3 := h1893c.2.2.2
                                            linarith only [h1705, hlam, p1893_0]
                                          · have p1893_0 := h1893c.1
                                            have p1893_1 := h1893c.2.1
                                            have p1893_2 := h1893c.2.2.1
                                            have p1893_3 := h1893c.2.2.2
                                            linarith only [h1710, hlam, p1893_0]
                                          · have p1893_0 := h1893c.1
                                            have p1893_1 := h1893c.2.1
                                            have p1893_2 := h1893c.2.2.1
                                            have p1893_3 := h1893c.2.2.2
                                            linarith only [h1879, hlam, p1893_0]
                                          · have p1893_0 := h1893c.1
                                            have p1893_1 := h1893c.2.1
                                            have p1893_2 := h1893c.2.2.1
                                            have p1893_3 := h1893c.2.2.2
                                            linarith only [h1881, hlam, p1893_0]
                                          · have p1893_0 := h1893c.1
                                            have p1893_1 := h1893c.2.1
                                            have p1893_2 := h1893c.2.2.1
                                            have p1893_3 := h1893c.2.2.2
                                            linarith only [hlam, p1893_0]
                                      · linarith only [h1711, h1890, hlam]
                                    · linarith only [h1710, h1889, hlam]
                                  · linarith only [h1708, h1888, hlam]
                                · linarith only [h1887, hlam, p1882_0]
                              · have p1882_0 := h1882c.1
                                have p1882_1 := h1882c.2.1
                                have p1882_2 := h1882c.2.2.1
                                have p1882_3 := h1882c.2.2.2
                                rcases p1882_3 (m.d 0 1) (by simp) with h1939 | h1939
                                · linarith only [h1939, hlam, p1882_0]
                                · rcases p1882_3 (m.d 1 2) (by simp) with h1941 | h1941
                                  · rcases p1882_3 (m.d 1 3) (by simp) with h1942 | h1942
                                    · linarith only [h1706, h1942, hlam]
                                    · linarith only [h1403, h1942, hlam]
                                  · linarith only [h1941, hlam, p1882_0]
                              · have p1882_0 := h1882c.1
                                have p1882_1 := h1882c.2.1
                                have p1882_2 := h1882c.2.2.1
                                have p1882_3 := h1882c.2.2.2
                                linarith only [hlam, p1882_0]
                              · have p1882_0 := h1882c.1
                                have p1882_1 := h1882c.2.1
                                have p1882_2 := h1882c.2.2.1
                                have p1882_3 := h1882c.2.2.2
                                linarith only [h1403, hc01, hc12, hlam, hphi, p1882_1]
                              · have p1882_0 := h1882c.1
                                have p1882_1 := h1882c.2.1
                                have p1882_2 := h1882c.2.2.1
                                have p1882_3 := h1882c.2.2.2
                                linarith only [h1593, h1700, h1708, h1879, h1881, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1882_1]
                              · have p1882_0 := h1882c.1
                                have p1882_1 := h1882c.2.1
                                have p1882_2 := h1882c.2.2.1
                                have p1882_3 := h1882c.2.2.2
                                rcases p1882_3 (m.d 0 1) (by simp) with h1949 | h1949
                                · linarith only [h0, h1949, hlam]
                                · linarith only [h1700, h1949, hlam]
                              · have p1882_0 := h1882c.1
                                have p1882_1 := h1882c.2.1
                                have p1882_2 := h1882c.2.2.1
                                have p1882_3 := h1882c.2.2.2
                                rcases p1882_3 (m.d 0 1) (by simp) with h1952 | h1952
                                · linarith only [h1952, hlam, p1882_0]
                                · rcases p1882_3 (m.d 1 2) (by simp) with h1954 | h1954
                                  · rcases p1882_3 (m.d 1 3) (by simp) with h1955 | h1955
                                    · rcases p1882_3 (m.d 1 4) (by simp) with h1956 | h1956
                                      · linarith only [h1709, h1956, hlam]
                                      · linarith only [h1593, h1956, hlam]
                                    · linarith only [h1955, hlam, p1882_0]
                                  · linarith only [h0, h1954, hlam]
                              · have p1882_0 := h1882c.1
                                have p1882_1 := h1882c.2.1
                                have p1882_2 := h1882c.2.2.1
                                have p1882_3 := h1882c.2.2.2
                                linarith only [h1706, hlam, p1882_1]
                              · have p1882_0 := h1882c.1
                                have p1882_1 := h1882c.2.1
                                have p1882_2 := h1882c.2.2.1
                                have p1882_3 := h1882c.2.2.2
                                linarith only [hlam, p1882_0]
                              · have p1882_0 := h1882c.1
                                have p1882_1 := h1882c.2.1
                                have p1882_2 := h1882c.2.2.1
                                have p1882_3 := h1882c.2.2.2
                                linarith only [h1593, h1706, hc01, hc12, hlam, hphi, p1882_1]
                              · have p1882_0 := h1882c.1
                                have p1882_1 := h1882c.2.1
                                have p1882_2 := h1882c.2.2.1
                                have p1882_3 := h1882c.2.2.2
                                rcases p1882_3 (m.d 0 1) (by simp) with h1964 | h1964
                                · linarith only [h1403, h1964, hlam]
                                · linarith only [h1700, h1964, hlam]
                              · have p1882_0 := h1882c.1
                                have p1882_1 := h1882c.2.1
                                have p1882_2 := h1882c.2.2.1
                                have p1882_3 := h1882c.2.2.2
                                rcases p1882_3 (m.d 0 1) (by simp) with h1967 | h1967
                                · linarith only [h1967, hlam, p1882_0]
                                · rcases p1882_3 (m.d 1 2) (by simp) with h1969 | h1969
                                  · rcases p1882_3 (m.d 1 3) (by simp) with h1970 | h1970
                                    · rcases p1882_3 (m.d 1 4) (by simp) with h1971 | h1971
                                      · rcases p1882_3 (m.d 1 5) (by simp) with h1972 | h1972
                                        · linarith only [h1711, h1972, hlam]
                                        · rcases h3bigk with h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c | h1974c
                                          · have p1974_0 := h1974c.1
                                            have p1974_1 := h1974c.2.1
                                            have p1974_2 := h1974c.2.2.1
                                            have p1974_3 := h1974c.2.2.2
                                            linarith only [hlam, p1974_0]
                                          · have p1974_0 := h1974c.1
                                            have p1974_1 := h1974c.2.1
                                            have p1974_2 := h1974c.2.2.1
                                            have p1974_3 := h1974c.2.2.2
                                            linarith only [h1403, hlam, p1974_1]
                                          · have p1974_0 := h1974c.1
                                            have p1974_1 := h1974c.2.1
                                            have p1974_2 := h1974c.2.2.1
                                            have p1974_3 := h1974c.2.2.2
                                            rcases p1974_3 (m.d 0 3) (by simp) with h1977 | h1977
                                            · rcases p1974_3 (m.d 1 3) (by simp) with h1978 | h1978
                                              · rcases p1974_3 (m.d 2 3) (by simp) with h1979 | h1979
                                                · linarith only [h1701, h1979, hlam]
                                                · rcases p1974_3 (m.d 3 4) (by simp) with h1981 | h1981
                                                  · linarith only [h1704, h1981, hlam]
                                                  · linarith only [h1712, h1981, hlam]
                                              · linarith only [h1706, h1978, hlam]
                                            · linarith only [h1701, h1977, hlam]
                                          · have p1974_0 := h1974c.1
                                            have p1974_1 := h1974c.2.1
                                            have p1974_2 := h1974c.2.2.1
                                            have p1974_3 := h1974c.2.2.2
                                            linarith only [h1712, h1879, h1881, hc03, hc45, hlam, hphi, ht0b, ht5b, p1974_1]
                                          · have p1974_0 := h1974c.1
                                            have p1974_1 := h1974c.2.1
                                            have p1974_2 := h1974c.2.2.1
                                            have p1974_3 := h1974c.2.2.2
                                            linarith only [h1704, h1712, h1879, hlam, p1974_2]
                                          · have p1974_0 := h1974c.1
                                            have p1974_1 := h1974c.2.1
                                            have p1974_2 := h1974c.2.2.1
                                            have p1974_3 := h1974c.2.2.2
                                            linarith only [h1704, h1712, h1879, h1881, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1974_1]
                                          · have p1974_0 := h1974c.1
                                            have p1974_1 := h1974c.2.1
                                            have p1974_2 := h1974c.2.2.1
                                            have p1974_3 := h1974c.2.2.2
                                            linarith only [hlam, p1974_0]
                                          · have p1974_0 := h1974c.1
                                            have p1974_1 := h1974c.2.1
                                            have p1974_2 := h1974c.2.2.1
                                            have p1974_3 := h1974c.2.2.2
                                            rcases p1974_3 (m.d 0 3) (by simp) with h1990 | h1990
                                            · linarith only [h1403, h1990, hlam]
                                            · linarith only [h1701, h1990, hlam]
                                          · have p1974_0 := h1974c.1
                                            have p1974_1 := h1974c.2.1
                                            have p1974_2 := h1974c.2.2.1
                                            have p1974_3 := h1974c.2.2.2
                                            linarith only [h1706, h1712, h1879, h1881, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1974_1]
                                          · have p1974_0 := h1974c.1
                                            have p1974_1 := h1974c.2.1
                                            have p1974_2 := h1974c.2.2.1
                                            have p1974_3 := h1974c.2.2.2
                                            linarith only [h1403, h1704, h1712, h1879, hlam, p1974_2]
                                          · have p1974_0 := h1974c.1
                                            have p1974_1 := h1974c.2.1
                                            have p1974_2 := h1974c.2.2.1
                                            have p1974_3 := h1974c.2.2.2
                                            linarith only [h1701, hlam, p1974_0]
                                          · have p1974_0 := h1974c.1
                                            have p1974_1 := h1974c.2.1
                                            have p1974_2 := h1974c.2.2.1
                                            have p1974_3 := h1974c.2.2.2
                                            linarith only [h1706, hlam, p1974_0]
                                          · have p1974_0 := h1974c.1
                                            have p1974_1 := h1974c.2.1
                                            have p1974_2 := h1974c.2.2.1
                                            have p1974_3 := h1974c.2.2.2
                                            linarith only [hlam, p1974_0]
                                          · have p1974_0 := h1974c.1
                                            have p1974_1 := h1974c.2.1
                                            have p1974_2 := h1974c.2.2.1
                                            have p1974_3 := h1974c.2.2.2
                                            linarith only [h1712, hlam, p1974_0]
                                          · have p1974_0 := h1974c.1
                                            have p1974_1 := h1974c.2.1
                                            have p1974_2 := h1974c.2.2.1
                                            have p1974_3 := h1974c.2.2.2
                                            linarith only [h1704, h1712, h1881, hc03, hc45, hlam, hphi, ht0b, ht5b, p1974_1]
                                          · have p1974_0 := h1974c.1
                                            have p1974_1 := h1974c.2.1
                                            have p1974_2 := h1974c.2.2.1
                                            have p1974_3 := h1974c.2.2.2
                                            linarith only [h1704, hlam, p1974_0]
                                          · have p1974_0 := h1974c.1
                                            have p1974_1 := h1974c.2.1
                                            have p1974_2 := h1974c.2.2.1
                                            have p1974_3 := h1974c.2.2.2
                                            linarith only [h1709, hlam, p1974_0]
                                          · have p1974_0 := h1974c.1
                                            have p1974_1 := h1974c.2.1
                                            have p1974_2 := h1974c.2.2.1
                                            have p1974_3 := h1974c.2.2.2
                                            linarith only [h0, h1701, h1704, h1879, h1881, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1974_1]
                                          · have p1974_0 := h1974c.1
                                            have p1974_1 := h1974c.2.1
                                            have p1974_2 := h1974c.2.2.1
                                            have p1974_3 := h1974c.2.2.2
                                            linarith only [hlam, p1974_0]
                                          · have p1974_0 := h1974c.1
                                            have p1974_1 := h1974c.2.1
                                            have p1974_2 := h1974c.2.2.1
                                            have p1974_3 := h1974c.2.2.2
                                            rcases p1974_3 (m.d 0 3) (by simp) with h2004 | h2004
                                            · rcases p1974_3 (m.d 1 3) (by simp) with h2005 | h2005
                                              · rcases p1974_3 (m.d 2 3) (by simp) with h2006 | h2006
                                                · linarith only [h1712, h2006, hlam]
                                                · linarith only [h1879, h2006, hlam]
                                              · linarith only [h1710, h2005, hlam]
                                            · linarith only [h1705, h2004, hlam]
                                          · have p1974_0 := h1974c.1
                                            have p1974_1 := h1974c.2.1
                                            have p1974_2 := h1974c.2.2.1
                                            have p1974_3 := h1974c.2.2.2
                                            linarith only [h1705, hlam, p1974_0]
                                          · have p1974_0 := h1974c.1
                                            have p1974_1 := h1974c.2.1
                                            have p1974_2 := h1974c.2.2.1
                                            have p1974_3 := h1974c.2.2.2
                                            linarith only [h1710, hlam, p1974_0]
                                          · have p1974_0 := h1974c.1
                                            have p1974_1 := h1974c.2.1
                                            have p1974_2 := h1974c.2.2.1
                                            have p1974_3 := h1974c.2.2.2
                                            linarith only [h1879, hlam, p1974_0]
                                          · have p1974_0 := h1974c.1
                                            have p1974_1 := h1974c.2.1
                                            have p1974_2 := h1974c.2.2.1
                                            have p1974_3 := h1974c.2.2.2
                                            linarith only [h1881, hlam, p1974_0]
                                          · have p1974_0 := h1974c.1
                                            have p1974_1 := h1974c.2.1
                                            have p1974_2 := h1974c.2.2.1
                                            have p1974_3 := h1974c.2.2.2
                                            linarith only [hlam, p1974_0]
                                      · linarith only [h1971, hlam, p1882_0]
                                    · linarith only [h1403, h1970, hlam]
                                  · linarith only [h0, h1969, hlam]
                              · have p1882_0 := h1882c.1
                                have p1882_1 := h1882c.2.1
                                have p1882_2 := h1882c.2.2.1
                                have p1882_3 := h1882c.2.2.2
                                linarith only [h1707, hlam, p1882_1]
                              · have p1882_0 := h1882c.1
                                have p1882_1 := h1882c.2.1
                                have p1882_2 := h1882c.2.2.1
                                have p1882_3 := h1882c.2.2.2
                                linarith only [h1709, hlam, p1882_0]
                              · have p1882_0 := h1882c.1
                                have p1882_1 := h1882c.2.1
                                have p1882_2 := h1882c.2.2.1
                                have p1882_3 := h1882c.2.2.2
                                linarith only [hlam, p1882_0]
                              · have p1882_0 := h1882c.1
                                have p1882_1 := h1882c.2.1
                                have p1882_2 := h1882c.2.2.1
                                have p1882_3 := h1882c.2.2.2
                                rcases p1882_3 (m.d 0 1) (by simp) with h2022 | h2022
                                · linarith only [h1593, h2022, hlam]
                                · linarith only [h1700, h2022, hlam]
                              · have p1882_0 := h1882c.1
                                have p1882_1 := h1882c.2.1
                                have p1882_2 := h1882c.2.2.1
                                have p1882_3 := h1882c.2.2.2
                                linarith only [h1700, hlam, p1882_0]
                              · have p1882_0 := h1882c.1
                                have p1882_1 := h1882c.2.1
                                have p1882_2 := h1882c.2.2.1
                                have p1882_3 := h1882c.2.2.2
                                linarith only [h1708, hlam, p1882_1]
                              · have p1882_0 := h1882c.1
                                have p1882_1 := h1882c.2.1
                                have p1882_2 := h1882c.2.2.1
                                have p1882_3 := h1882c.2.2.2
                                linarith only [h1710, hlam, p1882_0]
                              · have p1882_0 := h1882c.1
                                have p1882_1 := h1882c.2.1
                                have p1882_2 := h1882c.2.2.1
                                have p1882_3 := h1882c.2.2.2
                                linarith only [h1711, hlam, p1882_0]
                              · have p1882_0 := h1882c.1
                                have p1882_1 := h1882c.2.1
                                have p1882_2 := h1882c.2.2.1
                                have p1882_3 := h1882c.2.2.2
                                linarith only [hlam, p1882_0]
                            · linarith only [h1881, hc34, hlam, hphi, ht45, u5elo4]
                          · linarith only [h1711, h1712, h1880, hc23, hlam, hphi, ht34, ht45, u5elo1]
                        · linarith only [h1879, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h1711, hc14, hlam, hphi, ht45, u5elo4]
                  · linarith only [h1710, hc13, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h1403, h1704, h1709, hlam]
              · linarith only [h0, h1708, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h1702, h1707, hlam]
          · linarith only [h0, h1701, h1706, hlam]
        · linarith only [h1705, hc03, hlam, hphi, ht34, ht45, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2040 | h2040
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2041 | h2041
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2042 | h2042
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2043 | h2043
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2044 | h2044
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2045 | h2045
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2046 | h2046
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2047 | h2047
                      · linarith only [h1403, h1700, h1701, h1704, h2047, hc02, hc15, hlam, hphi, ht0b, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2049 | h2049
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2050 | h2050
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2051 | h2051
                            · rcases h1bigk with h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c | h2052c
                              · have p2052_0 := h2052c.1
                                have p2052_1 := h2052c.2.1
                                have p2052_2 := h2052c.2.2.1
                                have p2052_3 := h2052c.2.2.2
                                linarith only [hlam, p2052_0]
                              · have p2052_0 := h2052c.1
                                have p2052_1 := h2052c.2.1
                                have p2052_2 := h2052c.2.2.1
                                have p2052_3 := h2052c.2.2.2
                                linarith only [h0, hlam, p2052_0]
                              · have p2052_0 := h2052c.1
                                have p2052_1 := h2052c.2.1
                                have p2052_2 := h2052c.2.2.1
                                have p2052_3 := h2052c.2.2.2
                                linarith only [h1403, hlam, p2052_0]
                              · have p2052_0 := h2052c.1
                                have p2052_1 := h2052c.2.1
                                have p2052_2 := h2052c.2.2.1
                                have p2052_3 := h2052c.2.2.2
                                linarith only [h1593, hlam, p2052_0]
                              · have p2052_0 := h2052c.1
                                have p2052_1 := h2052c.2.1
                                have p2052_2 := h2052c.2.2.1
                                have p2052_3 := h2052c.2.2.2
                                linarith only [h1403, h1704, h2043, h2044, h2049, h2051, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p2052_1]
                              · have p2052_0 := h2052c.1
                                have p2052_1 := h2052c.2.1
                                have p2052_2 := h2052c.2.2.1
                                have p2052_3 := h2052c.2.2.2
                                rcases p2052_3 (m.d 0 1) (by simp) with h2058 | h2058
                                · linarith only [h2058, hlam, p2052_0]
                                · rcases p2052_3 (m.d 1 2) (by simp) with h2060 | h2060
                                  · rcases p2052_3 (m.d 1 3) (by simp) with h2061 | h2061
                                    · linarith only [h2041, h2061, hlam]
                                    · linarith only [h1403, h2061, hlam]
                                  · linarith only [h2060, hlam, p2052_0]
                              · have p2052_0 := h2052c.1
                                have p2052_1 := h2052c.2.1
                                have p2052_2 := h2052c.2.2.1
                                have p2052_3 := h2052c.2.2.2
                                linarith only [hlam, p2052_0]
                              · have p2052_0 := h2052c.1
                                have p2052_1 := h2052c.2.1
                                have p2052_2 := h2052c.2.2.1
                                have p2052_3 := h2052c.2.2.2
                                linarith only [h1403, h1704, h2044, hc01, hc12, hlam, hphi, p2052_1]
                              · have p2052_0 := h2052c.1
                                have p2052_1 := h2052c.2.1
                                have p2052_2 := h2052c.2.2.1
                                have p2052_3 := h2052c.2.2.2
                                linarith only [h1403, h1700, h1704, h2043, h2044, h2049, h2051, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2052_1]
                              · have p2052_0 := h2052c.1
                                have p2052_1 := h2052c.2.1
                                have p2052_2 := h2052c.2.2.1
                                have p2052_3 := h2052c.2.2.2
                                linarith only [h1403, h1700, h1704, h2041, h2044, hlam, p2052_2]
                              · have p2052_0 := h2052c.1
                                have p2052_1 := h2052c.2.1
                                have p2052_2 := h2052c.2.2.1
                                have p2052_3 := h2052c.2.2.2
                                rcases p2052_3 (m.d 0 1) (by simp) with h2069 | h2069
                                · linarith only [h2069, hlam, p2052_0]
                                · rcases p2052_3 (m.d 1 2) (by simp) with h2071 | h2071
                                  · rcases p2052_3 (m.d 1 3) (by simp) with h2072 | h2072
                                    · rcases p2052_3 (m.d 1 4) (by simp) with h2073 | h2073
                                      · linarith only [h2044, h2073, hlam]
                                      · linarith only [h1593, h2073, hlam]
                                    · linarith only [h2072, hlam, p2052_0]
                                  · linarith only [h0, h2071, hlam]
                              · have p2052_0 := h2052c.1
                                have p2052_1 := h2052c.2.1
                                have p2052_2 := h2052c.2.2.1
                                have p2052_3 := h2052c.2.2.2
                                linarith only [h2041, hlam, p2052_1]
                              · have p2052_0 := h2052c.1
                                have p2052_1 := h2052c.2.1
                                have p2052_2 := h2052c.2.2.1
                                have p2052_3 := h2052c.2.2.2
                                linarith only [hlam, p2052_0]
                              · have p2052_0 := h2052c.1
                                have p2052_1 := h2052c.2.1
                                have p2052_2 := h2052c.2.2.1
                                have p2052_3 := h2052c.2.2.2
                                linarith only [h1403, h1700, h1704, h2041, h2043, h2044, h2049, h2051, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2052_1]
                              · have p2052_0 := h2052c.1
                                have p2052_1 := h2052c.2.1
                                have p2052_2 := h2052c.2.2.1
                                have p2052_3 := h2052c.2.2.2
                                linarith only [h1403, h1700, h1704, h2044, hlam, p2052_2]
                              · have p2052_0 := h2052c.1
                                have p2052_1 := h2052c.2.1
                                have p2052_2 := h2052c.2.2.1
                                have p2052_3 := h2052c.2.2.2
                                rcases p2052_3 (m.d 0 1) (by simp) with h2082 | h2082
                                · linarith only [h2082, hlam, p2052_0]
                                · rcases p2052_3 (m.d 1 2) (by simp) with h2084 | h2084
                                  · rcases p2052_3 (m.d 1 3) (by simp) with h2085 | h2085
                                    · rcases p2052_3 (m.d 1 4) (by simp) with h2086 | h2086
                                      · rcases p2052_3 (m.d 1 5) (by simp) with h2087 | h2087
                                        · linarith only [h2046, h2087, hlam]
                                        · rcases h3bigk with h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c | h2089c
                                          · have p2089_0 := h2089c.1
                                            have p2089_1 := h2089c.2.1
                                            have p2089_2 := h2089c.2.2.1
                                            have p2089_3 := h2089c.2.2.2
                                            linarith only [hlam, p2089_0]
                                          · have p2089_0 := h2089c.1
                                            have p2089_1 := h2089c.2.1
                                            have p2089_2 := h2089c.2.2.1
                                            have p2089_3 := h2089c.2.2.2
                                            linarith only [h1403, hlam, p2089_1]
                                          · have p2089_0 := h2089c.1
                                            have p2089_1 := h2089c.2.1
                                            have p2089_2 := h2089c.2.2.1
                                            have p2089_3 := h2089c.2.2.2
                                            linarith only [h1704, h2044, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2089_1]
                                          · have p2089_0 := h2089c.1
                                            have p2089_1 := h2089c.2.1
                                            have p2089_2 := h2089c.2.2.1
                                            have p2089_3 := h2089c.2.2.2
                                            linarith only [h1704, hlam, p2089_0]
                                          · have p2089_0 := h2089c.1
                                            have p2089_1 := h2089c.2.1
                                            have p2089_2 := h2089c.2.2.1
                                            have p2089_3 := h2089c.2.2.2
                                            linarith only [h1704, h2044, h2051, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p2089_1]
                                          · have p2089_0 := h2089c.1
                                            have p2089_1 := h2089c.2.1
                                            have p2089_2 := h2089c.2.2.1
                                            have p2089_3 := h2089c.2.2.2
                                            rcases p2089_3 (m.d 0 3) (by simp) with h2095 | h2095
                                            · linarith only [h1403, h2095, hlam]
                                            · rcases p2089_3 (m.d 1 3) (by simp) with h2097 | h2097
                                              · rcases p2089_3 (m.d 2 3) (by simp) with h2098 | h2098
                                                · linarith only [h2041, h2098, hlam]
                                                · rcases p2089_3 (m.d 3 4) (by simp) with h2100 | h2100
                                                  · linarith only [h2044, h2100, hlam]
                                                  · linarith only [h1704, h2100, hlam]
                                              · linarith only [h1403, h2097, hlam]
                                          · have p2089_0 := h2089c.1
                                            have p2089_1 := h2089c.2.1
                                            have p2089_2 := h2089c.2.2.1
                                            have p2089_3 := h2089c.2.2.2
                                            linarith only [hlam, p2089_0]
                                          · have p2089_0 := h2089c.1
                                            have p2089_1 := h2089c.2.1
                                            have p2089_2 := h2089c.2.2.1
                                            have p2089_3 := h2089c.2.2.2
                                            rcases p2089_3 (m.d 0 3) (by simp) with h2105 | h2105
                                            · linarith only [h1403, h2105, hlam]
                                            · linarith only [h1701, h2105, hlam]
                                          · have p2089_0 := h2089c.1
                                            have p2089_1 := h2089c.2.1
                                            have p2089_2 := h2089c.2.2.1
                                            have p2089_3 := h2089c.2.2.2
                                            linarith only [h1403, h1700, h1704, h2041, h2043, h2049, h2051, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2089_1]
                                          · have p2089_0 := h2089c.1
                                            have p2089_1 := h2089c.2.1
                                            have p2089_2 := h2089c.2.2.1
                                            have p2089_3 := h2089c.2.2.2
                                            linarith only [h1403, h1700, h1704, h2043, h2044, h2049, hlam, p2089_2]
                                          · have p2089_0 := h2089c.1
                                            have p2089_1 := h2089c.2.1
                                            have p2089_2 := h2089c.2.2.1
                                            have p2089_3 := h2089c.2.2.2
                                            linarith only [h1701, hlam, p2089_0]
                                          · have p2089_0 := h2089c.1
                                            have p2089_1 := h2089c.2.1
                                            have p2089_2 := h2089c.2.2.1
                                            have p2089_3 := h2089c.2.2.2
                                            linarith only [h2041, hlam, p2089_0]
                                          · have p2089_0 := h2089c.1
                                            have p2089_1 := h2089c.2.1
                                            have p2089_2 := h2089c.2.2.1
                                            have p2089_3 := h2089c.2.2.2
                                            linarith only [hlam, p2089_0]
                                          · have p2089_0 := h2089c.1
                                            have p2089_1 := h2089c.2.1
                                            have p2089_2 := h2089c.2.2.1
                                            have p2089_3 := h2089c.2.2.2
                                            linarith only [h2047, hlam, p2089_0]
                                          · have p2089_0 := h2089c.1
                                            have p2089_1 := h2089c.2.1
                                            have p2089_2 := h2089c.2.2.1
                                            have p2089_3 := h2089c.2.2.2
                                            linarith only [h1701, h1704, h2044, h2051, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p2089_1]
                                          · have p2089_0 := h2089c.1
                                            have p2089_1 := h2089c.2.1
                                            have p2089_2 := h2089c.2.2.1
                                            have p2089_3 := h2089c.2.2.2
                                            linarith only [h1403, h1700, h2043, h2044, h2049, h2051, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p2089_1]
                                          · have p2089_0 := h2089c.1
                                            have p2089_1 := h2089c.2.1
                                            have p2089_2 := h2089c.2.2.1
                                            have p2089_3 := h2089c.2.2.2
                                            linarith only [h2044, hlam, p2089_0]
                                          · have p2089_0 := h2089c.1
                                            have p2089_1 := h2089c.2.1
                                            have p2089_2 := h2089c.2.2.1
                                            have p2089_3 := h2089c.2.2.2
                                            linarith only [h2041, h2044, h2049, h2051, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2089_1]
                                          · have p2089_0 := h2089c.1
                                            have p2089_1 := h2089c.2.1
                                            have p2089_2 := h2089c.2.2.1
                                            have p2089_3 := h2089c.2.2.2
                                            linarith only [hlam, p2089_0]
                                          · have p2089_0 := h2089c.1
                                            have p2089_1 := h2089c.2.1
                                            have p2089_2 := h2089c.2.2.1
                                            have p2089_3 := h2089c.2.2.2
                                            rcases p2089_3 (m.d 0 3) (by simp) with h2119 | h2119
                                            · linarith only [h1704, h2119, hlam]
                                            · linarith only [h2040, h2119, hlam]
                                          · have p2089_0 := h2089c.1
                                            have p2089_1 := h2089c.2.1
                                            have p2089_2 := h2089c.2.2.1
                                            have p2089_3 := h2089c.2.2.2
                                            linarith only [h2040, hlam, p2089_0]
                                          · have p2089_0 := h2089c.1
                                            have p2089_1 := h2089c.2.1
                                            have p2089_2 := h2089c.2.2.1
                                            have p2089_3 := h2089c.2.2.2
                                            linarith only [h2045, hlam, p2089_0]
                                          · have p2089_0 := h2089c.1
                                            have p2089_1 := h2089c.2.1
                                            have p2089_2 := h2089c.2.2.1
                                            have p2089_3 := h2089c.2.2.2
                                            linarith only [h2049, hlam, p2089_0]
                                          · have p2089_0 := h2089c.1
                                            have p2089_1 := h2089c.2.1
                                            have p2089_2 := h2089c.2.2.1
                                            have p2089_3 := h2089c.2.2.2
                                            linarith only [h2051, hlam, p2089_0]
                                          · have p2089_0 := h2089c.1
                                            have p2089_1 := h2089c.2.1
                                            have p2089_2 := h2089c.2.2.1
                                            have p2089_3 := h2089c.2.2.2
                                            linarith only [hlam, p2089_0]
                                      · linarith only [h2086, hlam, p2052_0]
                                    · linarith only [h1403, h2085, hlam]
                                  · linarith only [h0, h2084, hlam]
                              · have p2052_0 := h2052c.1
                                have p2052_1 := h2052c.2.1
                                have p2052_2 := h2052c.2.2.1
                                have p2052_3 := h2052c.2.2.2
                                linarith only [h2042, hlam, p2052_1]
                              · have p2052_0 := h2052c.1
                                have p2052_1 := h2052c.2.1
                                have p2052_2 := h2052c.2.2.1
                                have p2052_3 := h2052c.2.2.2
                                linarith only [h2044, hlam, p2052_0]
                              · have p2052_0 := h2052c.1
                                have p2052_1 := h2052c.2.1
                                have p2052_2 := h2052c.2.2.1
                                have p2052_3 := h2052c.2.2.2
                                linarith only [hlam, p2052_0]
                              · have p2052_0 := h2052c.1
                                have p2052_1 := h2052c.2.1
                                have p2052_2 := h2052c.2.2.1
                                have p2052_3 := h2052c.2.2.2
                                rcases p2052_3 (m.d 0 1) (by simp) with h2133 | h2133
                                · linarith only [h1593, h2133, hlam]
                                · linarith only [h1700, h2133, hlam]
                              · have p2052_0 := h2052c.1
                                have p2052_1 := h2052c.2.1
                                have p2052_2 := h2052c.2.2.1
                                have p2052_3 := h2052c.2.2.2
                                linarith only [h1700, hlam, p2052_0]
                              · have p2052_0 := h2052c.1
                                have p2052_1 := h2052c.2.1
                                have p2052_2 := h2052c.2.2.1
                                have p2052_3 := h2052c.2.2.2
                                linarith only [h2043, hlam, p2052_1]
                              · have p2052_0 := h2052c.1
                                have p2052_1 := h2052c.2.1
                                have p2052_2 := h2052c.2.2.1
                                have p2052_3 := h2052c.2.2.2
                                linarith only [h2045, hlam, p2052_0]
                              · have p2052_0 := h2052c.1
                                have p2052_1 := h2052c.2.1
                                have p2052_2 := h2052c.2.2.1
                                have p2052_3 := h2052c.2.2.2
                                linarith only [h2046, hlam, p2052_0]
                              · have p2052_0 := h2052c.1
                                have p2052_1 := h2052c.2.1
                                have p2052_2 := h2052c.2.2.1
                                have p2052_3 := h2052c.2.2.2
                                linarith only [hlam, p2052_0]
                            · linarith only [h2051, hc34, hlam, hphi, ht45, u5elo4]
                          · linarith only [h2046, h2050, hc24, hlam, hphi, ht45, u5elo1]
                        · linarith only [h2049, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h2046, hc14, hlam, hphi, ht45, u5elo4]
                  · linarith only [h1403, h1704, h2044, h2045, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2146 | h2146
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2147 | h2147
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2148 | h2148
                      · linarith only [h1403, h1700, h2043, h2044, h2148, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2150 | h2150
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2151 | h2151
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2152 | h2152
                            · rcases h1bigk with h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c | h2153c
                              · have p2153_0 := h2153c.1
                                have p2153_1 := h2153c.2.1
                                have p2153_2 := h2153c.2.2.1
                                have p2153_3 := h2153c.2.2.2
                                linarith only [hlam, p2153_0]
                              · have p2153_0 := h2153c.1
                                have p2153_1 := h2153c.2.1
                                have p2153_2 := h2153c.2.2.1
                                have p2153_3 := h2153c.2.2.2
                                linarith only [h0, hlam, p2153_0]
                              · have p2153_0 := h2153c.1
                                have p2153_1 := h2153c.2.1
                                have p2153_2 := h2153c.2.2.1
                                have p2153_3 := h2153c.2.2.2
                                linarith only [h1403, hlam, p2153_0]
                              · have p2153_0 := h2153c.1
                                have p2153_1 := h2153c.2.1
                                have p2153_2 := h2153c.2.2.1
                                have p2153_3 := h2153c.2.2.2
                                linarith only [h1593, hlam, p2153_0]
                              · have p2153_0 := h2153c.1
                                have p2153_1 := h2153c.2.1
                                have p2153_2 := h2153c.2.2.1
                                have p2153_3 := h2153c.2.2.2
                                linarith only [h1403, h2043, h2044, h2150, h2152, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2153_1]
                              · have p2153_0 := h2153c.1
                                have p2153_1 := h2153c.2.1
                                have p2153_2 := h2153c.2.2.1
                                have p2153_3 := h2153c.2.2.2
                                rcases p2153_3 (m.d 0 1) (by simp) with h2159 | h2159
                                · linarith only [h2159, hlam, p2153_0]
                                · rcases p2153_3 (m.d 1 2) (by simp) with h2161 | h2161
                                  · rcases p2153_3 (m.d 1 3) (by simp) with h2162 | h2162
                                    · linarith only [h2041, h2162, hlam]
                                    · linarith only [h1403, h2162, hlam]
                                  · linarith only [h2161, hlam, p2153_0]
                              · have p2153_0 := h2153c.1
                                have p2153_1 := h2153c.2.1
                                have p2153_2 := h2153c.2.2.1
                                have p2153_3 := h2153c.2.2.2
                                linarith only [hlam, p2153_0]
                              · have p2153_0 := h2153c.1
                                have p2153_1 := h2153c.2.1
                                have p2153_2 := h2153c.2.2.1
                                have p2153_3 := h2153c.2.2.2
                                linarith only [h1403, hc01, hc12, hlam, hphi, p2153_1]
                              · have p2153_0 := h2153c.1
                                have p2153_1 := h2153c.2.1
                                have p2153_2 := h2153c.2.2.1
                                have p2153_3 := h2153c.2.2.2
                                linarith only [h1403, h1700, h2043, h2044, h2150, h2152, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2153_1]
                              · have p2153_0 := h2153c.1
                                have p2153_1 := h2153c.2.1
                                have p2153_2 := h2153c.2.2.1
                                have p2153_3 := h2153c.2.2.2
                                rcases p2153_3 (m.d 0 1) (by simp) with h2169 | h2169
                                · linarith only [h0, h2169, hlam]
                                · linarith only [h1700, h2169, hlam]
                              · have p2153_0 := h2153c.1
                                have p2153_1 := h2153c.2.1
                                have p2153_2 := h2153c.2.2.1
                                have p2153_3 := h2153c.2.2.2
                                linarith only [h1700, h2043, h2044, h2150, h2152, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2153_1]
                              · have p2153_0 := h2153c.1
                                have p2153_1 := h2153c.2.1
                                have p2153_2 := h2153c.2.2.1
                                have p2153_3 := h2153c.2.2.2
                                linarith only [h2041, hlam, p2153_1]
                              · have p2153_0 := h2153c.1
                                have p2153_1 := h2153c.2.1
                                have p2153_2 := h2153c.2.2.1
                                have p2153_3 := h2153c.2.2.2
                                linarith only [hlam, p2153_0]
                              · have p2153_0 := h2153c.1
                                have p2153_1 := h2153c.2.1
                                have p2153_2 := h2153c.2.2.1
                                have p2153_3 := h2153c.2.2.2
                                linarith only [h2044, hlam, p2153_1]
                              · have p2153_0 := h2153c.1
                                have p2153_1 := h2153c.2.1
                                have p2153_2 := h2153c.2.2.1
                                have p2153_3 := h2153c.2.2.2
                                rcases p2153_3 (m.d 0 1) (by simp) with h2176 | h2176
                                · linarith only [h1403, h2176, hlam]
                                · linarith only [h1700, h2176, hlam]
                              · have p2153_0 := h2153c.1
                                have p2153_1 := h2153c.2.1
                                have p2153_2 := h2153c.2.2.1
                                have p2153_3 := h2153c.2.2.2
                                rcases p2153_3 (m.d 0 1) (by simp) with h2179 | h2179
                                · linarith only [h2179, hlam, p2153_0]
                                · rcases p2153_3 (m.d 1 2) (by simp) with h2181 | h2181
                                  · rcases p2153_3 (m.d 1 3) (by simp) with h2182 | h2182
                                    · linarith only [h2044, h2182, hlam]
                                    · linarith only [h1403, h2182, hlam]
                                  · linarith only [h0, h2181, hlam]
                              · have p2153_0 := h2153c.1
                                have p2153_1 := h2153c.2.1
                                have p2153_2 := h2153c.2.2.1
                                have p2153_3 := h2153c.2.2.2
                                linarith only [h2042, hlam, p2153_1]
                              · have p2153_0 := h2153c.1
                                have p2153_1 := h2153c.2.1
                                have p2153_2 := h2153c.2.2.1
                                have p2153_3 := h2153c.2.2.2
                                linarith only [h1403, h1700, h2042, h2043, h2150, h2152, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2153_1]
                              · have p2153_0 := h2153c.1
                                have p2153_1 := h2153c.2.1
                                have p2153_2 := h2153c.2.2.1
                                have p2153_3 := h2153c.2.2.2
                                linarith only [hlam, p2153_0]
                              · have p2153_0 := h2153c.1
                                have p2153_1 := h2153c.2.1
                                have p2153_2 := h2153c.2.2.1
                                have p2153_3 := h2153c.2.2.2
                                rcases p2153_3 (m.d 0 1) (by simp) with h2189 | h2189
                                · linarith only [h1593, h2189, hlam]
                                · linarith only [h1700, h2189, hlam]
                              · have p2153_0 := h2153c.1
                                have p2153_1 := h2153c.2.1
                                have p2153_2 := h2153c.2.2.1
                                have p2153_3 := h2153c.2.2.2
                                linarith only [h1700, hlam, p2153_0]
                              · have p2153_0 := h2153c.1
                                have p2153_1 := h2153c.2.1
                                have p2153_2 := h2153c.2.2.1
                                have p2153_3 := h2153c.2.2.2
                                linarith only [h2043, hlam, p2153_1]
                              · have p2153_0 := h2153c.1
                                have p2153_1 := h2153c.2.1
                                have p2153_2 := h2153c.2.2.1
                                have p2153_3 := h2153c.2.2.2
                                linarith only [h2146, hlam, p2153_0]
                              · have p2153_0 := h2153c.1
                                have p2153_1 := h2153c.2.1
                                have p2153_2 := h2153c.2.2.1
                                have p2153_3 := h2153c.2.2.2
                                linarith only [h2147, hlam, p2153_0]
                              · have p2153_0 := h2153c.1
                                have p2153_1 := h2153c.2.1
                                have p2153_2 := h2153c.2.2.1
                                have p2153_3 := h2153c.2.2.2
                                linarith only [hlam, p2153_0]
                            · linarith only [h2152, hc34, hlam, hphi, ht45, u5elo4]
                          · linarith only [h1403, h1700, h2044, h2147, h2148, h2151, hc23, hc34, hlam, hphi]
                        · linarith only [h2150, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h1593, h2147, hc04, hlam, hphi, ht45, u5elo4]
                  · linarith only [h1403, h2146, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · linarith only [h0, h2043, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h1403, h1700, h1702, h2041, h2042, hc02, hc15, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h1701, h2041, hlam]
        · linarith only [h1403, h1700, h2040, hc15, hlam, hphi, u5elo3]
    · linarith only [h1703, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2207 | h2207
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2208 | h2208
      · linarith only [h1701, h1702, h2208, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2210 | h2210
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2211 | h2211
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2212 | h2212
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2213 | h2213
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2214 | h2214
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2215 | h2215
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2216 | h2216
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2217 | h2217
                      · linarith only [h1403, h1700, h1701, h2208, h2213, h2217, hc02, hc25, hlam, hphi, ht0b, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2219 | h2219
                        · linarith only [h1701, h1702, h2211, h2214, h2217, h2219, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h2219, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h1702, h2212, h2216, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h2215, hc13, hlam, hphi, ht34, ht45, u5elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2224 | h2224
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2225 | h2225
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2226 | h2226
                      · linarith only [h1403, h1700, h2213, h2214, h2226, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2228 | h2228
                        · linarith only [h1701, h1702, h2212, h2228, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h2228, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h1702, h2212, h2225, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h1403, h1700, h2213, h2224, hc25, hlam, hphi, u5elo3]
              · linarith only [h2213, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2234 | h2234
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2235 | h2235
                · linarith only [h1403, h1700, h2208, h2211, h2212, h2234, h2235, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2237 | h2237
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2238 | h2238
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2239 | h2239
                      · linarith only [h0, h1701, h2212, h2235, h2239, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2241 | h2241
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2242 | h2242
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2243 | h2243
                            · rcases h1bigk with h2244c | h2244c | h2244c | h2244c | h2244c | h2244c | h2244c | h2244c | h2244c | h2244c | h2244c | h2244c | h2244c | h2244c | h2244c | h2244c | h2244c | h2244c | h2244c | h2244c | h2244c | h2244c | h2244c | h2244c | h2244c
                              · have p2244_0 := h2244c.1
                                have p2244_1 := h2244c.2.1
                                have p2244_2 := h2244c.2.2.1
                                have p2244_3 := h2244c.2.2.2
                                linarith only [hlam, p2244_0]
                              · have p2244_0 := h2244c.1
                                have p2244_1 := h2244c.2.1
                                have p2244_2 := h2244c.2.2.1
                                have p2244_3 := h2244c.2.2.2
                                linarith only [h0, hlam, p2244_0]
                              · have p2244_0 := h2244c.1
                                have p2244_1 := h2244c.2.1
                                have p2244_2 := h2244c.2.2.1
                                have p2244_3 := h2244c.2.2.2
                                linarith only [h1403, hlam, p2244_0]
                              · have p2244_0 := h2244c.1
                                have p2244_1 := h2244c.2.1
                                have p2244_2 := h2244c.2.2.1
                                have p2244_3 := h2244c.2.2.2
                                linarith only [h1593, hlam, p2244_0]
                              · have p2244_0 := h2244c.1
                                have p2244_1 := h2244c.2.1
                                have p2244_2 := h2244c.2.2.1
                                have p2244_3 := h2244c.2.2.2
                                linarith only [h0, h2212, h2234, h2239, h2241, h2243, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2244_1]
                              · have p2244_0 := h2244c.1
                                have p2244_1 := h2244c.2.1
                                have p2244_2 := h2244c.2.2.1
                                have p2244_3 := h2244c.2.2.2
                                linarith only [h2212, h2239, hc01, hc34, hlam, hphi, ht12, ht23, p2244_1]
                              · have p2244_0 := h2244c.1
                                have p2244_1 := h2244c.2.1
                                have p2244_2 := h2244c.2.2.1
                                have p2244_3 := h2244c.2.2.2
                                linarith only [hlam, p2244_0]
                              · have p2244_0 := h2244c.1
                                have p2244_1 := h2244c.2.1
                                have p2244_2 := h2244c.2.2.1
                                have p2244_3 := h2244c.2.2.2
                                linarith only [h1403, h1700, h2212, h2234, h2239, h2241, h2243, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2244_1]
                              · have p2244_0 := h2244c.1
                                have p2244_1 := h2244c.2.1
                                have p2244_2 := h2244c.2.2.1
                                have p2244_3 := h2244c.2.2.2
                                linarith only [h2212, hlam, p2244_0]
                              · have p2244_0 := h2244c.1
                                have p2244_1 := h2244c.2.1
                                have p2244_2 := h2244c.2.2.1
                                have p2244_3 := h2244c.2.2.2
                                rcases p2244_3 (m.d 0 1) (by simp) with h2254 | h2254
                                · linarith only [h0, h2254, hlam]
                                · linarith only [h1700, h2254, hlam]
                              · have p2244_0 := h2244c.1
                                have p2244_1 := h2244c.2.1
                                have p2244_2 := h2244c.2.2.1
                                have p2244_3 := h2244c.2.2.2
                                linarith only [h1700, h2211, h2212, h2234, h2239, h2241, h2243, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2244_1]
                              · have p2244_0 := h2244c.1
                                have p2244_1 := h2244c.2.1
                                have p2244_2 := h2244c.2.2.1
                                have p2244_3 := h2244c.2.2.2
                                linarith only [h2211, hlam, p2244_1]
                              · have p2244_0 := h2244c.1
                                have p2244_1 := h2244c.2.1
                                have p2244_2 := h2244c.2.2.1
                                have p2244_3 := h2244c.2.2.2
                                linarith only [hlam, p2244_0]
                              · have p2244_0 := h2244c.1
                                have p2244_1 := h2244c.2.1
                                have p2244_2 := h2244c.2.2.1
                                have p2244_3 := h2244c.2.2.2
                                linarith only [h2235, hlam, p2244_1]
                              · have p2244_0 := h2244c.1
                                have p2244_1 := h2244c.2.1
                                have p2244_2 := h2244c.2.2.1
                                have p2244_3 := h2244c.2.2.2
                                rcases p2244_3 (m.d 0 1) (by simp) with h2261 | h2261
                                · linarith only [h1403, h2261, hlam]
                                · linarith only [h1700, h2261, hlam]
                              · have p2244_0 := h2244c.1
                                have p2244_1 := h2244c.2.1
                                have p2244_2 := h2244c.2.2.1
                                have p2244_3 := h2244c.2.2.2
                                rcases p2244_3 (m.d 0 1) (by simp) with h2264 | h2264
                                · linarith only [h2264, hlam, p2244_0]
                                · rcases p2244_3 (m.d 1 2) (by simp) with h2266 | h2266
                                  · linarith only [h2212, h2266, hlam]
                                  · linarith only [h0, h2266, hlam]
                              · have p2244_0 := h2244c.1
                                have p2244_1 := h2244c.2.1
                                have p2244_2 := h2244c.2.2.1
                                have p2244_3 := h2244c.2.2.2
                                linarith only [h0, h1700, h2234, h2241, h2243, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p2244_1]
                              · have p2244_0 := h2244c.1
                                have p2244_1 := h2244c.2.1
                                have p2244_2 := h2244c.2.2.1
                                have p2244_3 := h2244c.2.2.2
                                linarith only [h1403, h1700, h2212, h2234, h2239, h2241, h2243, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2244_1]
                              · have p2244_0 := h2244c.1
                                have p2244_1 := h2244c.2.1
                                have p2244_2 := h2244c.2.2.1
                                have p2244_3 := h2244c.2.2.2
                                linarith only [hlam, p2244_0]
                              · have p2244_0 := h2244c.1
                                have p2244_1 := h2244c.2.1
                                have p2244_2 := h2244c.2.2.1
                                have p2244_3 := h2244c.2.2.2
                                rcases p2244_3 (m.d 0 1) (by simp) with h2272 | h2272
                                · linarith only [h1593, h2272, hlam]
                                · linarith only [h1700, h2272, hlam]
                              · have p2244_0 := h2244c.1
                                have p2244_1 := h2244c.2.1
                                have p2244_2 := h2244c.2.2.1
                                have p2244_3 := h2244c.2.2.2
                                linarith only [h1700, hlam, p2244_0]
                              · have p2244_0 := h2244c.1
                                have p2244_1 := h2244c.2.1
                                have p2244_2 := h2244c.2.2.1
                                have p2244_3 := h2244c.2.2.2
                                linarith only [h2234, hlam, p2244_1]
                              · have p2244_0 := h2244c.1
                                have p2244_1 := h2244c.2.1
                                have p2244_2 := h2244c.2.2.1
                                have p2244_3 := h2244c.2.2.2
                                linarith only [h2237, hlam, p2244_0]
                              · have p2244_0 := h2244c.1
                                have p2244_1 := h2244c.2.1
                                have p2244_2 := h2244c.2.2.1
                                have p2244_3 := h2244c.2.2.2
                                linarith only [h2238, hlam, p2244_0]
                              · have p2244_0 := h2244c.1
                                have p2244_1 := h2244c.2.1
                                have p2244_2 := h2244c.2.2.1
                                have p2244_3 := h2244c.2.2.2
                                linarith only [hlam, p2244_0]
                            · linarith only [h2239, h2243, hc24, hlam, hphi, ht45, u5elo4]
                          · linarith only [h1403, h1700, h2211, h2212, h2238, h2242, hlam]
                        · linarith only [h2241, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h2238, hc14, hlam, hphi, ht45, u5elo4]
                  · linarith only [h1403, h2237, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · linarith only [h1403, h1700, h2211, h2234, hc15, hlam, hphi, u5elo2]
          · linarith only [h0, h1700, h1701, h2211, hc02, hc15, hlam, hphi, ht0b, ht5b]
        · linarith only [h1403, h1700, h2210, hc15, hlam, hphi, u5elo3]
    · linarith only [h2207, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]

end R2N4
