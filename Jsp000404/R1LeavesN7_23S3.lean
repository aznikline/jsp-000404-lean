import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_23S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6424000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s3_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 5 (by decide) (by decide) with h1702 | h1702
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1703 | h1703
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1704 | h1704
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1705 | h1705
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1706 | h1706
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1707 | h1707
            · linarith only [h0, h1702, h1704, h1707, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1709 | h1709
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1710 | h1710
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1711 | h1711
                  · linarith only [h1702, h1704, h1711, h3, h7, hc13, hlam, hphi, u1ehi4]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1713 | h1713
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1714 | h1714
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1715 | h1715
                        · rcases h2bigk with h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c | h1716c
                          · have p1716_0 := h1716c.1
                            have p1716_1 := h1716c.2.1
                            have p1716_2 := h1716c.2.2.1
                            have p1716_3 := h1716c.2.2.2
                            linarith only [hlam, p1716_0]
                          · have p1716_0 := h1716c.1
                            have p1716_1 := h1716c.2.1
                            have p1716_2 := h1716c.2.2.1
                            have p1716_3 := h1716c.2.2.2
                            linarith only [h0, h1704, h1713, hc01, hc35, hlam, hphi, ht0b, ht5b, p1716_1]
                          · have p1716_0 := h1716c.1
                            have p1716_1 := h1716c.2.1
                            have p1716_2 := h1716c.2.2.1
                            have p1716_3 := h1716c.2.2.2
                            rcases p1716_3 (m.d 0 2) (by simp) with h1719 | h1719
                            · rcases p1716_3 (m.d 1 2) (by simp) with h1720 | h1720
                              · linarith only [h0, h1720, hlam]
                              · linarith only [h1704, h1720, hlam]
                            · linarith only [h1719, hlam, p1716_0]
                          · have p1716_0 := h1716c.1
                            have p1716_1 := h1716c.2.1
                            have p1716_2 := h1716c.2.2.1
                            have p1716_3 := h1716c.2.2.2
                            rcases p1716_3 (m.d 0 2) (by simp) with h1724 | h1724
                            · rcases p1716_3 (m.d 1 2) (by simp) with h1725 | h1725
                              · linarith only [h0, h1725, hlam]
                              · linarith only [h1705, h1725, hlam]
                            · linarith only [h1724, hlam, p1716_0]
                          · have p1716_0 := h1716c.1
                            have p1716_1 := h1716c.2.1
                            have p1716_2 := h1716c.2.2.1
                            have p1716_3 := h1716c.2.2.2
                            rcases p1716_3 (m.d 0 2) (by simp) with h1729 | h1729
                            · rcases p1716_3 (m.d 1 2) (by simp) with h1730 | h1730
                              · linarith only [h0, h1730, hlam]
                              · linarith only [h1706, h1730, hlam]
                            · linarith only [h1729, hlam, p1716_0]
                          · have p1716_0 := h1716c.1
                            have p1716_1 := h1716c.2.1
                            have p1716_2 := h1716c.2.2.1
                            have p1716_3 := h1716c.2.2.2
                            linarith only [h0, hlam, p1716_1]
                          · have p1716_0 := h1716c.1
                            have p1716_1 := h1716c.2.1
                            have p1716_2 := h1716c.2.2.1
                            have p1716_3 := h1716c.2.2.2
                            linarith only [hlam, p1716_0]
                          · have p1716_0 := h1716c.1
                            have p1716_1 := h1716c.2.1
                            have p1716_2 := h1716c.2.2.1
                            have p1716_3 := h1716c.2.2.2
                            linarith only [h0, h1713, h1715, hc01, hc45, hlam, hphi, ht0b, ht5b, p1716_1]
                          · have p1716_0 := h1716c.1
                            have p1716_1 := h1716c.2.1
                            have p1716_2 := h1716c.2.2.1
                            have p1716_3 := h1716c.2.2.2
                            linarith only [h0, h1711, h1713, h1715, hc01, hc45, hlam, hphi, ht0b, ht5b, p1716_1]
                          · have p1716_0 := h1716c.1
                            have p1716_1 := h1716c.2.1
                            have p1716_2 := h1716c.2.2.1
                            have p1716_3 := h1716c.2.2.2
                            rcases p1716_3 (m.d 0 2) (by simp) with h1738 | h1738
                            · rcases p1716_3 (m.d 1 2) (by simp) with h1739 | h1739
                              · rcases p1716_3 (m.d 2 3) (by simp) with h1740 | h1740
                                · linarith only [h1704, h1740, hlam]
                                · linarith only [h1713, h1740, hlam]
                              · linarith only [h1739, hlam, p1716_0]
                            · linarith only [h1738, h6, hlam]
                          · have p1716_0 := h1716c.1
                            have p1716_1 := h1716c.2.1
                            have p1716_2 := h1716c.2.2.1
                            have p1716_3 := h1716c.2.2.2
                            linarith only [h4, hlam, p1716_0]
                          · have p1716_0 := h1716c.1
                            have p1716_1 := h1716c.2.1
                            have p1716_2 := h1716c.2.2.1
                            have p1716_3 := h1716c.2.2.2
                            linarith only [h1704, hlam, p1716_0]
                          · have p1716_0 := h1716c.1
                            have p1716_1 := h1716c.2.1
                            have p1716_2 := h1716c.2.2.1
                            have p1716_3 := h1716c.2.2.2
                            linarith only [hlam, p1716_0]
                          · have p1716_0 := h1716c.1
                            have p1716_1 := h1716c.2.1
                            have p1716_2 := h1716c.2.2.1
                            have p1716_3 := h1716c.2.2.2
                            linarith only [h1711, hlam, p1716_1]
                          · have p1716_0 := h1716c.1
                            have p1716_1 := h1716c.2.1
                            have p1716_2 := h1716c.2.2.1
                            have p1716_3 := h1716c.2.2.2
                            linarith only [h0, h1704, hc01, hc25, hlam, hphi, ht0b, ht5b, p1716_1]
                          · have p1716_0 := h1716c.1
                            have p1716_1 := h1716c.2.1
                            have p1716_2 := h1716c.2.2.1
                            have p1716_3 := h1716c.2.2.2
                            linarith only [h5, hlam, p1716_0]
                          · have p1716_0 := h1716c.1
                            have p1716_1 := h1716c.2.1
                            have p1716_2 := h1716c.2.2.1
                            have p1716_3 := h1716c.2.2.2
                            linarith only [h1705, hlam, p1716_0]
                          · have p1716_0 := h1716c.1
                            have p1716_1 := h1716c.2.1
                            have p1716_2 := h1716c.2.2.1
                            have p1716_3 := h1716c.2.2.2
                            linarith only [h0, h1705, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1716_1]
                          · have p1716_0 := h1716c.1
                            have p1716_1 := h1716c.2.1
                            have p1716_2 := h1716c.2.2.1
                            have p1716_3 := h1716c.2.2.2
                            linarith only [hlam, p1716_0]
                          · have p1716_0 := h1716c.1
                            have p1716_1 := h1716c.2.1
                            have p1716_2 := h1716c.2.2.1
                            have p1716_3 := h1716c.2.2.2
                            linarith only [h0, h1705, h1713, h1715, hc01, hc45, hlam, hphi, ht0b, ht5b, p1716_1]
                          · have p1716_0 := h1716c.1
                            have p1716_1 := h1716c.2.1
                            have p1716_2 := h1716c.2.2.1
                            have p1716_3 := h1716c.2.2.2
                            linarith only [h6, hlam, p1716_0]
                          · have p1716_0 := h1716c.1
                            have p1716_1 := h1716c.2.1
                            have p1716_2 := h1716c.2.2.1
                            have p1716_3 := h1716c.2.2.2
                            linarith only [h1706, hlam, p1716_0]
                          · have p1716_0 := h1716c.1
                            have p1716_1 := h1716c.2.1
                            have p1716_2 := h1716c.2.2.1
                            have p1716_3 := h1716c.2.2.2
                            linarith only [h1713, hlam, p1716_0]
                          · have p1716_0 := h1716c.1
                            have p1716_1 := h1716c.2.1
                            have p1716_2 := h1716c.2.2.1
                            have p1716_3 := h1716c.2.2.2
                            linarith only [h1714, hlam, p1716_1]
                          · have p1716_0 := h1716c.1
                            have p1716_1 := h1716c.2.1
                            have p1716_2 := h1716c.2.2.1
                            have p1716_3 := h1716c.2.2.2
                            linarith only [hlam, p1716_0]
                        · linarith only [h1702, h1715, h3, h7, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi4]
                      · linarith only [h0, h1705, h1710, h1711, h1713, h1714, hc01, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h1702, h1713, h7, hc23, hc34, hlam, hphi]
                · linarith only [h1703, h1710, h7, hc34, hlam, hphi, ht12, ht23, u1ehi3]
              · linarith only [h1702, h1709, h7, hc34, hlam, hphi, ht12, ht23, u1ehi2]
          · linarith only [h1702, h1706, h6, h7, hc34, hlam, hphi, ht12, ht23, u1ehi1]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1766 | h1766
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1767 | h1767
            · linarith only [h1702, h1704, h1705, h1767, h7, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1769 | h1769
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1770 | h1770
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1771 | h1771
                  · linarith only [h1704, h1705, h1769, h1771, h5, h7, hc23, hlam, hphi, ht12, u1ehi4]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1773 | h1773
                    · linarith only [h0, h1704, h1705, h1773, h5, hc01, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h1702, h1773, h7, hc23, hc34, hlam, hphi]
                · linarith only [h1703, h1704, h1705, h1769, h1770, h7, hc34, hlam, hphi, ht12, ht23, u1ehi4]
              · linarith only [h1702, h1769, h7, hc13, hc34, hlam, hphi]
          · linarith only [h1702, h1704, h1766, h6, h7, hc34, hlam, hphi, ht12, ht23, u1ehi2]
      · linarith only [h1704, h4, h7, hc34, hlam, hphi, ht12, ht23, u1ehi1]
    · linarith only [h1702, h1703, h7, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1781 | h1781
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1782 | h1782
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1783 | h1783
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1784 | h1784
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1785 | h1785
            · linarith only [h1, h1785, h7, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1787 | h1787
              · linarith only [h1, h1702, h1787, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1789 | h1789
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1790 | h1790
                  · linarith only [h1, h1782, h1790, h7, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1792 | h1792
                    · linarith only [h1, h1702, h1782, h1792, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1794 | h1794
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1795 | h1795
                        · rcases h2bigk with h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c | h1796c
                          · have p1796_0 := h1796c.1
                            have p1796_1 := h1796c.2.1
                            have p1796_2 := h1796c.2.2.1
                            have p1796_3 := h1796c.2.2.2
                            linarith only [hlam, p1796_0]
                          · have p1796_0 := h1796c.1
                            have p1796_1 := h1796c.2.1
                            have p1796_2 := h1796c.2.2.1
                            have p1796_3 := h1796c.2.2.2
                            linarith only [h1783, h1794, hc02, hc45, hlam, hphi, ht0b, ht5b, p1796_1]
                          · have p1796_0 := h1796c.1
                            have p1796_1 := h1796c.2.1
                            have p1796_2 := h1796c.2.2.1
                            have p1796_3 := h1796c.2.2.2
                            rcases p1796_3 (m.d 0 2) (by simp) with h1799 | h1799
                            · rcases p1796_3 (m.d 1 2) (by simp) with h1800 | h1800
                              · linarith only [h0, h1800, hlam]
                              · linarith only [h1782, h1800, hlam]
                            · linarith only [h1799, hlam, p1796_0]
                          · have p1796_0 := h1796c.1
                            have p1796_1 := h1796c.2.1
                            have p1796_2 := h1796c.2.2.1
                            have p1796_3 := h1796c.2.2.2
                            rcases p1796_3 (m.d 0 2) (by simp) with h1804 | h1804
                            · rcases p1796_3 (m.d 1 2) (by simp) with h1805 | h1805
                              · linarith only [h0, h1805, hlam]
                              · linarith only [h1783, h1805, hlam]
                            · linarith only [h1804, hlam, p1796_0]
                          · have p1796_0 := h1796c.1
                            have p1796_1 := h1796c.2.1
                            have p1796_2 := h1796c.2.2.1
                            have p1796_3 := h1796c.2.2.2
                            rcases p1796_3 (m.d 0 2) (by simp) with h1809 | h1809
                            · rcases p1796_3 (m.d 1 2) (by simp) with h1810 | h1810
                              · linarith only [h0, h1810, hlam]
                              · linarith only [h1784, h1810, hlam]
                            · linarith only [h1809, hlam, p1796_0]
                          · have p1796_0 := h1796c.1
                            have p1796_1 := h1796c.2.1
                            have p1796_2 := h1796c.2.2.1
                            have p1796_3 := h1796c.2.2.2
                            linarith only [h0, hlam, p1796_1]
                          · have p1796_0 := h1796c.1
                            have p1796_1 := h1796c.2.1
                            have p1796_2 := h1796c.2.2.1
                            have p1796_3 := h1796c.2.2.2
                            linarith only [hlam, p1796_0]
                          · have p1796_0 := h1796c.1
                            have p1796_1 := h1796c.2.1
                            have p1796_2 := h1796c.2.2.1
                            have p1796_3 := h1796c.2.2.2
                            rcases p1796_3 (m.d 0 2) (by simp) with h1816 | h1816
                            · rcases p1796_3 (m.d 1 2) (by simp) with h1817 | h1817
                              · rcases p1796_3 (m.d 2 3) (by simp) with h1818 | h1818
                                · linarith only [h1818, hlam, p1796_0]
                                · rcases p1796_3 (m.d 2 4) (by simp) with h1820 | h1820
                                  · linarith only [h1783, h1820, hlam]
                                  · linarith only [h1790, h1820, hlam]
                              · linarith only [h1817, hlam, p1796_0]
                            · linarith only [h1816, h4, hlam]
                          · have p1796_0 := h1796c.1
                            have p1796_1 := h1796c.2.1
                            have p1796_2 := h1796c.2.2.1
                            have p1796_3 := h1796c.2.2.2
                            linarith only [h0, h1794, hc01, hc45, hlam, hphi, ht0b, ht5b, p1796_1]
                          · have p1796_0 := h1796c.1
                            have p1796_1 := h1796c.2.1
                            have p1796_2 := h1796c.2.2.1
                            have p1796_3 := h1796c.2.2.2
                            rcases p1796_3 (m.d 0 2) (by simp) with h1826 | h1826
                            · rcases p1796_3 (m.d 1 2) (by simp) with h1827 | h1827
                              · rcases p1796_3 (m.d 2 3) (by simp) with h1828 | h1828
                                · linarith only [h1782, h1828, hlam]
                                · rcases p1796_3 (m.d 2 4) (by simp) with h1830 | h1830
                                  · linarith only [h1783, h1830, hlam]
                                  · linarith only [h1794, h1830, hlam]
                              · linarith only [h1827, hlam, p1796_0]
                            · linarith only [h1826, h6, hlam]
                          · have p1796_0 := h1796c.1
                            have p1796_1 := h1796c.2.1
                            have p1796_2 := h1796c.2.2.1
                            have p1796_3 := h1796c.2.2.2
                            linarith only [h4, hlam, p1796_0]
                          · have p1796_0 := h1796c.1
                            have p1796_1 := h1796c.2.1
                            have p1796_2 := h1796c.2.2.1
                            have p1796_3 := h1796c.2.2.2
                            linarith only [h1782, hlam, p1796_0]
                          · have p1796_0 := h1796c.1
                            have p1796_1 := h1796c.2.1
                            have p1796_2 := h1796c.2.2.1
                            have p1796_3 := h1796c.2.2.2
                            linarith only [hlam, p1796_0]
                          · have p1796_0 := h1796c.1
                            have p1796_1 := h1796c.2.1
                            have p1796_2 := h1796c.2.2.1
                            have p1796_3 := h1796c.2.2.2
                            linarith only [h1790, hlam, p1796_1]
                          · have p1796_0 := h1796c.1
                            have p1796_1 := h1796c.2.1
                            have p1796_2 := h1796c.2.2.1
                            have p1796_3 := h1796c.2.2.2
                            linarith only [h1792, hlam, p1796_1]
                          · have p1796_0 := h1796c.1
                            have p1796_1 := h1796c.2.1
                            have p1796_2 := h1796c.2.2.1
                            have p1796_3 := h1796c.2.2.2
                            linarith only [h5, hlam, p1796_0]
                          · have p1796_0 := h1796c.1
                            have p1796_1 := h1796c.2.1
                            have p1796_2 := h1796c.2.2.1
                            have p1796_3 := h1796c.2.2.2
                            linarith only [h1783, hlam, p1796_0]
                          · have p1796_0 := h1796c.1
                            have p1796_1 := h1796c.2.1
                            have p1796_2 := h1796c.2.2.1
                            have p1796_3 := h1796c.2.2.2
                            linarith only [h0, h1783, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1796_1]
                          · have p1796_0 := h1796c.1
                            have p1796_1 := h1796c.2.1
                            have p1796_2 := h1796c.2.2.1
                            have p1796_3 := h1796c.2.2.2
                            linarith only [hlam, p1796_0]
                          · have p1796_0 := h1796c.1
                            have p1796_1 := h1796c.2.1
                            have p1796_2 := h1796c.2.2.1
                            have p1796_3 := h1796c.2.2.2
                            linarith only [h0, h1783, hc01, hc25, hlam, hphi, ht0b, ht5b, p1796_1]
                          · have p1796_0 := h1796c.1
                            have p1796_1 := h1796c.2.1
                            have p1796_2 := h1796c.2.2.1
                            have p1796_3 := h1796c.2.2.2
                            linarith only [h6, hlam, p1796_0]
                          · have p1796_0 := h1796c.1
                            have p1796_1 := h1796c.2.1
                            have p1796_2 := h1796c.2.2.1
                            have p1796_3 := h1796c.2.2.2
                            linarith only [h1784, hlam, p1796_0]
                          · have p1796_0 := h1796c.1
                            have p1796_1 := h1796c.2.1
                            have p1796_2 := h1796c.2.2.1
                            have p1796_3 := h1796c.2.2.2
                            linarith only [h0, h1784, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1796_1]
                          · have p1796_0 := h1796c.1
                            have p1796_1 := h1796c.2.1
                            have p1796_2 := h1796c.2.2.1
                            have p1796_3 := h1796c.2.2.2
                            linarith only [h1794, hlam, p1796_1]
                          · have p1796_0 := h1796c.1
                            have p1796_1 := h1796c.2.1
                            have p1796_2 := h1796c.2.2.1
                            have p1796_3 := h1796c.2.2.2
                            linarith only [hlam, p1796_0]
                        · linarith only [h1, h1795, h7, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1851 | h1851
                        · rcases h2bigk with h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [hlam, p1852_0]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [h0, h1783, h1789, h1790, h1794, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1852_1]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            rcases p1852_3 (m.d 0 2) (by simp) with h1855 | h1855
                            · rcases p1852_3 (m.d 1 2) (by simp) with h1856 | h1856
                              · linarith only [h0, h1856, hlam]
                              · linarith only [h1782, h1856, hlam]
                            · linarith only [h1855, hlam, p1852_0]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            rcases p1852_3 (m.d 0 2) (by simp) with h1860 | h1860
                            · rcases p1852_3 (m.d 1 2) (by simp) with h1861 | h1861
                              · linarith only [h0, h1861, hlam]
                              · linarith only [h1783, h1861, hlam]
                            · linarith only [h1860, hlam, p1852_0]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            rcases p1852_3 (m.d 0 2) (by simp) with h1865 | h1865
                            · rcases p1852_3 (m.d 1 2) (by simp) with h1866 | h1866
                              · linarith only [h0, h1866, hlam]
                              · linarith only [h1784, h1866, hlam]
                            · linarith only [h1865, hlam, p1852_0]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [h0, hlam, p1852_1]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [hlam, p1852_0]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            rcases p1852_3 (m.d 0 2) (by simp) with h1872 | h1872
                            · rcases p1852_3 (m.d 1 2) (by simp) with h1873 | h1873
                              · rcases p1852_3 (m.d 2 3) (by simp) with h1874 | h1874
                                · linarith only [h1874, hlam, p1852_0]
                                · rcases p1852_3 (m.d 2 4) (by simp) with h1876 | h1876
                                  · linarith only [h1783, h1876, hlam]
                                  · linarith only [h1790, h1876, hlam]
                              · linarith only [h1873, hlam, p1852_0]
                            · linarith only [h1872, h4, hlam]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            rcases p1852_3 (m.d 0 2) (by simp) with h1881 | h1881
                            · rcases p1852_3 (m.d 1 2) (by simp) with h1882 | h1882
                              · rcases p1852_3 (m.d 2 3) (by simp) with h1883 | h1883
                                · linarith only [h1782, h1883, hlam]
                                · rcases p1852_3 (m.d 2 4) (by simp) with h1885 | h1885
                                  · linarith only [h1885, hlam, p1852_0]
                                  · rcases p1852_3 (m.d 2 5) (by simp) with h1887 | h1887
                                    · linarith only [h1784, h1887, hlam]
                                    · linarith only [h1794, h1887, hlam]
                              · linarith only [h1882, hlam, p1852_0]
                            · linarith only [h1881, h5, hlam]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            rcases p1852_3 (m.d 0 2) (by simp) with h1892 | h1892
                            · rcases p1852_3 (m.d 1 2) (by simp) with h1893 | h1893
                              · rcases p1852_3 (m.d 2 3) (by simp) with h1894 | h1894
                                · linarith only [h1782, h1894, hlam]
                                · rcases p1852_3 (m.d 2 4) (by simp) with h1896 | h1896
                                  · linarith only [h1783, h1896, hlam]
                                  · rcases p1852_3 (m.d 2 5) (by simp) with h1898 | h1898
                                    · linarith only [h1898, hlam, p1852_0]
                                    · rcases h2emax with h1900 | h1900 | h1900 | h1900 | h1900
                                      · linarith only [h0, h1783, h1789, h1790, h1794, h1900, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                                      · linarith only [h1783, h1789, h1790, h1794, h1900, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                                      · rcases h4bigk with h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c | h1903c
                                        · have p1903_0 := h1903c.1
                                          have p1903_1 := h1903c.2.1
                                          have p1903_2 := h1903c.2.2.1
                                          have p1903_3 := h1903c.2.2.2
                                          linarith only [hlam, p1903_0]
                                        · have p1903_0 := h1903c.1
                                          have p1903_1 := h1903c.2.1
                                          have p1903_2 := h1903c.2.2.1
                                          have p1903_3 := h1903c.2.2.2
                                          linarith only [h1789, h1790, h1794, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1903_1]
                                        · have p1903_0 := h1903c.1
                                          have p1903_1 := h1903c.2.1
                                          have p1903_2 := h1903c.2.2.1
                                          have p1903_3 := h1903c.2.2.2
                                          rcases p1903_3 (m.d 0 4) (by simp) with h1906 | h1906
                                          · rcases p1903_3 (m.d 1 4) (by simp) with h1907 | h1907
                                            · linarith only [h1907, h2, hlam]
                                            · linarith only [h1783, h1907, hlam]
                                          · linarith only [h1906, h5, hlam]
                                        · have p1903_0 := h1903c.1
                                          have p1903_1 := h1903c.2.1
                                          have p1903_2 := h1903c.2.2.1
                                          have p1903_3 := h1903c.2.2.2
                                          linarith only [h7, hlam, p1903_1]
                                        · have p1903_0 := h1903c.1
                                          have p1903_1 := h1903c.2.1
                                          have p1903_2 := h1903c.2.2.1
                                          have p1903_3 := h1903c.2.2.2
                                          linarith only [h1790, h1794, h7, hc23, hc34, hlam, hphi, p1903_1]
                                        · have p1903_0 := h1903c.1
                                          have p1903_1 := h1903c.2.1
                                          have p1903_2 := h1903c.2.2.1
                                          have p1903_3 := h1903c.2.2.2
                                          linarith only [h2, hlam, p1903_0]
                                        · have p1903_0 := h1903c.1
                                          have p1903_1 := h1903c.2.1
                                          have p1903_2 := h1903c.2.2.1
                                          have p1903_3 := h1903c.2.2.2
                                          linarith only [hlam, p1903_0]
                                        · have p1903_0 := h1903c.1
                                          have p1903_1 := h1903c.2.1
                                          have p1903_2 := h1903c.2.2.1
                                          have p1903_3 := h1903c.2.2.2
                                          rcases p1903_3 (m.d 0 4) (by simp) with h1915 | h1915
                                          · rcases p1903_3 (m.d 1 4) (by simp) with h1916 | h1916
                                            · rcases p1903_3 (m.d 2 4) (by simp) with h1917 | h1917
                                              · linarith only [h1783, h1917, hlam]
                                              · rcases p1903_3 (m.d 3 4) (by simp) with h1919 | h1919
                                                · rcases p1903_3 (m.d 4 5) (by simp) with h1920 | h1920
                                                  · linarith only [h1789, h1920, hlam]
                                                  · linarith only [h1794, h1920, hlam]
                                                · linarith only [h1790, h1919, hlam]
                                            · linarith only [h1783, h1916, hlam]
                                          · linarith only [h1915, h5, hlam]
                                        · have p1903_0 := h1903c.1
                                          have p1903_1 := h1903c.2.1
                                          have p1903_2 := h1903c.2.2.1
                                          have p1903_3 := h1903c.2.2.2
                                          linarith only [h1785, hlam, p1903_1]
                                        · have p1903_0 := h1903c.1
                                          have p1903_1 := h1903c.2.1
                                          have p1903_2 := h1903c.2.2.1
                                          have p1903_3 := h1903c.2.2.2
                                          linarith only [h0, h1783, h1790, h1794, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1903_1]
                                        · have p1903_0 := h1903c.1
                                          have p1903_1 := h1903c.2.1
                                          have p1903_2 := h1903c.2.2.1
                                          have p1903_3 := h1903c.2.2.2
                                          linarith only [h5, hlam, p1903_0]
                                        · have p1903_0 := h1903c.1
                                          have p1903_1 := h1903c.2.1
                                          have p1903_2 := h1903c.2.2.1
                                          have p1903_3 := h1903c.2.2.2
                                          linarith only [h1783, hlam, p1903_0]
                                        · have p1903_0 := h1903c.1
                                          have p1903_1 := h1903c.2.1
                                          have p1903_2 := h1903c.2.2.1
                                          have p1903_3 := h1903c.2.2.2
                                          linarith only [hlam, p1903_0]
                                        · have p1903_0 := h1903c.1
                                          have p1903_1 := h1903c.2.1
                                          have p1903_2 := h1903c.2.2.1
                                          have p1903_3 := h1903c.2.2.2
                                          linarith only [h1790, hlam, p1903_1]
                                        · have p1903_0 := h1903c.1
                                          have p1903_1 := h1903c.2.1
                                          have p1903_2 := h1903c.2.2.1
                                          have p1903_3 := h1903c.2.2.2
                                          linarith only [h1794, hlam, p1903_0]
                                        · have p1903_0 := h1903c.1
                                          have p1903_1 := h1903c.2.1
                                          have p1903_2 := h1903c.2.2.1
                                          have p1903_3 := h1903c.2.2.2
                                          linarith only [h2, hc34, hlam, hphi, ht12, ht23, p1903_1, u1ehi3]
                                        · have p1903_0 := h1903c.1
                                          have p1903_1 := h1903c.2.1
                                          have p1903_2 := h1903c.2.2.1
                                          have p1903_3 := h1903c.2.2.2
                                          linarith only [h1789, hc34, hlam, hphi, ht12, ht23, p1903_1, u1ehi4]
                                        · have p1903_0 := h1903c.1
                                          have p1903_1 := h1903c.2.1
                                          have p1903_2 := h1903c.2.2.1
                                          have p1903_3 := h1903c.2.2.2
                                          rcases p1903_3 (m.d 0 4) (by simp) with h1935 | h1935
                                          · linarith only [h1935, h7, hlam]
                                          · linarith only [h1935, h5, hlam]
                                        · have p1903_0 := h1903c.1
                                          have p1903_1 := h1903c.2.1
                                          have p1903_2 := h1903c.2.2.1
                                          have p1903_3 := h1903c.2.2.2
                                          linarith only [hlam, p1903_0]
                                        · have p1903_0 := h1903c.1
                                          have p1903_1 := h1903c.2.1
                                          have p1903_2 := h1903c.2.2.1
                                          have p1903_3 := h1903c.2.2.2
                                          linarith only [h1790, h1794, hc23, hc34, hlam, hphi, p1903_1]
                                        · have p1903_0 := h1903c.1
                                          have p1903_1 := h1903c.2.1
                                          have p1903_2 := h1903c.2.2.1
                                          have p1903_3 := h1903c.2.2.2
                                          linarith only [h1781, hlam, p1903_0]
                                        · have p1903_0 := h1903c.1
                                          have p1903_1 := h1903c.2.1
                                          have p1903_2 := h1903c.2.2.1
                                          have p1903_3 := h1903c.2.2.2
                                          linarith only [h1789, hlam, p1903_0]
                                        · have p1903_0 := h1903c.1
                                          have p1903_1 := h1903c.2.1
                                          have p1903_2 := h1903c.2.2.1
                                          have p1903_3 := h1903c.2.2.2
                                          linarith only [h1789, h1790, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1903_1]
                                        · have p1903_0 := h1903c.1
                                          have p1903_1 := h1903c.2.1
                                          have p1903_2 := h1903c.2.2.1
                                          have p1903_3 := h1903c.2.2.2
                                          linarith only [h1851, hlam, p1903_0]
                                        · have p1903_0 := h1903c.1
                                          have p1903_1 := h1903c.2.1
                                          have p1903_2 := h1903c.2.2.1
                                          have p1903_3 := h1903c.2.2.2
                                          linarith only [hlam, p1903_0]
                                      · rcases h4bigk with h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c
                                        · have p1945_0 := h1945c.1
                                          have p1945_1 := h1945c.2.1
                                          have p1945_2 := h1945c.2.2.1
                                          have p1945_3 := h1945c.2.2.2
                                          linarith only [hlam, p1945_0]
                                        · have p1945_0 := h1945c.1
                                          have p1945_1 := h1945c.2.1
                                          have p1945_2 := h1945c.2.2.1
                                          have p1945_3 := h1945c.2.2.2
                                          linarith only [h7, hc34, hlam, hphi, ht12, ht23, p1945_1, u1ehi3]
                                        · have p1945_0 := h1945c.1
                                          have p1945_1 := h1945c.2.1
                                          have p1945_2 := h1945c.2.2.1
                                          have p1945_3 := h1945c.2.2.2
                                          rcases p1945_3 (m.d 0 4) (by simp) with h1948 | h1948
                                          · rcases p1945_3 (m.d 1 4) (by simp) with h1949 | h1949
                                            · linarith only [h1949, h2, hlam]
                                            · linarith only [h1783, h1949, hlam]
                                          · linarith only [h1948, h5, hlam]
                                        · have p1945_0 := h1945c.1
                                          have p1945_1 := h1945c.2.1
                                          have p1945_2 := h1945c.2.2.1
                                          have p1945_3 := h1945c.2.2.2
                                          linarith only [h7, hlam, p1945_1]
                                        · have p1945_0 := h1945c.1
                                          have p1945_1 := h1945c.2.1
                                          have p1945_2 := h1945c.2.2.1
                                          have p1945_3 := h1945c.2.2.2
                                          linarith only [h1790, h1794, h7, hc23, hc34, hlam, hphi, p1945_1]
                                        · have p1945_0 := h1945c.1
                                          have p1945_1 := h1945c.2.1
                                          have p1945_2 := h1945c.2.2.1
                                          have p1945_3 := h1945c.2.2.2
                                          linarith only [h2, hlam, p1945_0]
                                        · have p1945_0 := h1945c.1
                                          have p1945_1 := h1945c.2.1
                                          have p1945_2 := h1945c.2.2.1
                                          have p1945_3 := h1945c.2.2.2
                                          linarith only [hlam, p1945_0]
                                        · have p1945_0 := h1945c.1
                                          have p1945_1 := h1945c.2.1
                                          have p1945_2 := h1945c.2.2.1
                                          have p1945_3 := h1945c.2.2.2
                                          rcases p1945_3 (m.d 0 4) (by simp) with h1957 | h1957
                                          · rcases p1945_3 (m.d 1 4) (by simp) with h1958 | h1958
                                            · rcases p1945_3 (m.d 2 4) (by simp) with h1959 | h1959
                                              · linarith only [h1783, h1959, hlam]
                                              · rcases p1945_3 (m.d 3 4) (by simp) with h1961 | h1961
                                                · rcases p1945_3 (m.d 4 5) (by simp) with h1962 | h1962
                                                  · linarith only [h1789, h1962, hlam]
                                                  · linarith only [h1794, h1962, hlam]
                                                · linarith only [h1790, h1961, hlam]
                                            · linarith only [h1783, h1958, hlam]
                                          · linarith only [h1957, h5, hlam]
                                        · have p1945_0 := h1945c.1
                                          have p1945_1 := h1945c.2.1
                                          have p1945_2 := h1945c.2.2.1
                                          have p1945_3 := h1945c.2.2.2
                                          linarith only [h1785, hlam, p1945_1]
                                        · have p1945_0 := h1945c.1
                                          have p1945_1 := h1945c.2.1
                                          have p1945_2 := h1945c.2.2.1
                                          have p1945_3 := h1945c.2.2.2
                                          linarith only [h1790, h1794, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1945_1]
                                        · have p1945_0 := h1945c.1
                                          have p1945_1 := h1945c.2.1
                                          have p1945_2 := h1945c.2.2.1
                                          have p1945_3 := h1945c.2.2.2
                                          linarith only [h5, hlam, p1945_0]
                                        · have p1945_0 := h1945c.1
                                          have p1945_1 := h1945c.2.1
                                          have p1945_2 := h1945c.2.2.1
                                          have p1945_3 := h1945c.2.2.2
                                          linarith only [h1783, hlam, p1945_0]
                                        · have p1945_0 := h1945c.1
                                          have p1945_1 := h1945c.2.1
                                          have p1945_2 := h1945c.2.2.1
                                          have p1945_3 := h1945c.2.2.2
                                          linarith only [hlam, p1945_0]
                                        · have p1945_0 := h1945c.1
                                          have p1945_1 := h1945c.2.1
                                          have p1945_2 := h1945c.2.2.1
                                          have p1945_3 := h1945c.2.2.2
                                          linarith only [h1790, hlam, p1945_1]
                                        · have p1945_0 := h1945c.1
                                          have p1945_1 := h1945c.2.1
                                          have p1945_2 := h1945c.2.2.1
                                          have p1945_3 := h1945c.2.2.2
                                          linarith only [h1794, hlam, p1945_0]
                                        · have p1945_0 := h1945c.1
                                          have p1945_1 := h1945c.2.1
                                          have p1945_2 := h1945c.2.2.1
                                          have p1945_3 := h1945c.2.2.2
                                          linarith only [h2, hc34, hlam, hphi, ht12, ht23, p1945_1, u1ehi3]
                                        · have p1945_0 := h1945c.1
                                          have p1945_1 := h1945c.2.1
                                          have p1945_2 := h1945c.2.2.1
                                          have p1945_3 := h1945c.2.2.2
                                          linarith only [hc34, hlam, hphi, ht12, ht23, p1945_1, u1ehi3]
                                        · have p1945_0 := h1945c.1
                                          have p1945_1 := h1945c.2.1
                                          have p1945_2 := h1945c.2.2.1
                                          have p1945_3 := h1945c.2.2.2
                                          rcases p1945_3 (m.d 0 4) (by simp) with h1977 | h1977
                                          · linarith only [h1977, h7, hlam]
                                          · linarith only [h1977, h5, hlam]
                                        · have p1945_0 := h1945c.1
                                          have p1945_1 := h1945c.2.1
                                          have p1945_2 := h1945c.2.2.1
                                          have p1945_3 := h1945c.2.2.2
                                          linarith only [hlam, p1945_0]
                                        · have p1945_0 := h1945c.1
                                          have p1945_1 := h1945c.2.1
                                          have p1945_2 := h1945c.2.2.1
                                          have p1945_3 := h1945c.2.2.2
                                          linarith only [h1790, h1794, hc23, hc34, hlam, hphi, p1945_1]
                                        · have p1945_0 := h1945c.1
                                          have p1945_1 := h1945c.2.1
                                          have p1945_2 := h1945c.2.2.1
                                          have p1945_3 := h1945c.2.2.2
                                          linarith only [h1781, hlam, p1945_0]
                                        · have p1945_0 := h1945c.1
                                          have p1945_1 := h1945c.2.1
                                          have p1945_2 := h1945c.2.2.1
                                          have p1945_3 := h1945c.2.2.2
                                          linarith only [h1789, hlam, p1945_0]
                                        · have p1945_0 := h1945c.1
                                          have p1945_1 := h1945c.2.1
                                          have p1945_2 := h1945c.2.2.1
                                          have p1945_3 := h1945c.2.2.2
                                          linarith only [h1789, h1790, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1945_1]
                                        · have p1945_0 := h1945c.1
                                          have p1945_1 := h1945c.2.1
                                          have p1945_2 := h1945c.2.2.1
                                          have p1945_3 := h1945c.2.2.2
                                          linarith only [h1851, hlam, p1945_0]
                                        · have p1945_0 := h1945c.1
                                          have p1945_1 := h1945c.2.1
                                          have p1945_2 := h1945c.2.2.1
                                          have p1945_3 := h1945c.2.2.2
                                          linarith only [hlam, p1945_0]
                                      · rcases h4bigk with h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c | h1987c
                                        · have p1987_0 := h1987c.1
                                          have p1987_1 := h1987c.2.1
                                          have p1987_2 := h1987c.2.2.1
                                          have p1987_3 := h1987c.2.2.2
                                          linarith only [hlam, p1987_0]
                                        · have p1987_0 := h1987c.1
                                          have p1987_1 := h1987c.2.1
                                          have p1987_2 := h1987c.2.2.1
                                          have p1987_3 := h1987c.2.2.2
                                          linarith only [h7, hc34, hlam, hphi, ht12, ht23, p1987_1, u1ehi3]
                                        · have p1987_0 := h1987c.1
                                          have p1987_1 := h1987c.2.1
                                          have p1987_2 := h1987c.2.2.1
                                          have p1987_3 := h1987c.2.2.2
                                          rcases p1987_3 (m.d 0 4) (by simp) with h1990 | h1990
                                          · rcases p1987_3 (m.d 1 4) (by simp) with h1991 | h1991
                                            · linarith only [h1991, h2, hlam]
                                            · linarith only [h1783, h1991, hlam]
                                          · linarith only [h1990, h5, hlam]
                                        · have p1987_0 := h1987c.1
                                          have p1987_1 := h1987c.2.1
                                          have p1987_2 := h1987c.2.2.1
                                          have p1987_3 := h1987c.2.2.2
                                          linarith only [h7, hlam, p1987_1]
                                        · have p1987_0 := h1987c.1
                                          have p1987_1 := h1987c.2.1
                                          have p1987_2 := h1987c.2.2.1
                                          have p1987_3 := h1987c.2.2.2
                                          linarith only [h1790, h1794, h7, hc23, hc34, hlam, hphi, p1987_1]
                                        · have p1987_0 := h1987c.1
                                          have p1987_1 := h1987c.2.1
                                          have p1987_2 := h1987c.2.2.1
                                          have p1987_3 := h1987c.2.2.2
                                          linarith only [h2, hlam, p1987_0]
                                        · have p1987_0 := h1987c.1
                                          have p1987_1 := h1987c.2.1
                                          have p1987_2 := h1987c.2.2.1
                                          have p1987_3 := h1987c.2.2.2
                                          linarith only [hlam, p1987_0]
                                        · have p1987_0 := h1987c.1
                                          have p1987_1 := h1987c.2.1
                                          have p1987_2 := h1987c.2.2.1
                                          have p1987_3 := h1987c.2.2.2
                                          rcases p1987_3 (m.d 0 4) (by simp) with h1999 | h1999
                                          · rcases p1987_3 (m.d 1 4) (by simp) with h2000 | h2000
                                            · rcases p1987_3 (m.d 2 4) (by simp) with h2001 | h2001
                                              · linarith only [h1783, h2001, hlam]
                                              · rcases p1987_3 (m.d 3 4) (by simp) with h2003 | h2003
                                                · rcases p1987_3 (m.d 4 5) (by simp) with h2004 | h2004
                                                  · linarith only [h1789, h2004, hlam]
                                                  · linarith only [h1794, h2004, hlam]
                                                · linarith only [h1790, h2003, hlam]
                                            · linarith only [h1783, h2000, hlam]
                                          · linarith only [h1999, h5, hlam]
                                        · have p1987_0 := h1987c.1
                                          have p1987_1 := h1987c.2.1
                                          have p1987_2 := h1987c.2.2.1
                                          have p1987_3 := h1987c.2.2.2
                                          linarith only [h1785, hlam, p1987_1]
                                        · have p1987_0 := h1987c.1
                                          have p1987_1 := h1987c.2.1
                                          have p1987_2 := h1987c.2.2.1
                                          have p1987_3 := h1987c.2.2.2
                                          linarith only [h1790, h1794, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1987_1]
                                        · have p1987_0 := h1987c.1
                                          have p1987_1 := h1987c.2.1
                                          have p1987_2 := h1987c.2.2.1
                                          have p1987_3 := h1987c.2.2.2
                                          linarith only [h5, hlam, p1987_0]
                                        · have p1987_0 := h1987c.1
                                          have p1987_1 := h1987c.2.1
                                          have p1987_2 := h1987c.2.2.1
                                          have p1987_3 := h1987c.2.2.2
                                          linarith only [h1783, hlam, p1987_0]
                                        · have p1987_0 := h1987c.1
                                          have p1987_1 := h1987c.2.1
                                          have p1987_2 := h1987c.2.2.1
                                          have p1987_3 := h1987c.2.2.2
                                          linarith only [hlam, p1987_0]
                                        · have p1987_0 := h1987c.1
                                          have p1987_1 := h1987c.2.1
                                          have p1987_2 := h1987c.2.2.1
                                          have p1987_3 := h1987c.2.2.2
                                          linarith only [h1790, hlam, p1987_1]
                                        · have p1987_0 := h1987c.1
                                          have p1987_1 := h1987c.2.1
                                          have p1987_2 := h1987c.2.2.1
                                          have p1987_3 := h1987c.2.2.2
                                          linarith only [h1794, hlam, p1987_0]
                                        · have p1987_0 := h1987c.1
                                          have p1987_1 := h1987c.2.1
                                          have p1987_2 := h1987c.2.2.1
                                          have p1987_3 := h1987c.2.2.2
                                          linarith only [h2, hc34, hlam, hphi, ht12, ht23, p1987_1, u1ehi3]
                                        · have p1987_0 := h1987c.1
                                          have p1987_1 := h1987c.2.1
                                          have p1987_2 := h1987c.2.2.1
                                          have p1987_3 := h1987c.2.2.2
                                          linarith only [hc34, hlam, hphi, ht12, ht23, p1987_1, u1ehi3]
                                        · have p1987_0 := h1987c.1
                                          have p1987_1 := h1987c.2.1
                                          have p1987_2 := h1987c.2.2.1
                                          have p1987_3 := h1987c.2.2.2
                                          rcases p1987_3 (m.d 0 4) (by simp) with h2019 | h2019
                                          · linarith only [h2019, h7, hlam]
                                          · linarith only [h2019, h5, hlam]
                                        · have p1987_0 := h1987c.1
                                          have p1987_1 := h1987c.2.1
                                          have p1987_2 := h1987c.2.2.1
                                          have p1987_3 := h1987c.2.2.2
                                          linarith only [hlam, p1987_0]
                                        · have p1987_0 := h1987c.1
                                          have p1987_1 := h1987c.2.1
                                          have p1987_2 := h1987c.2.2.1
                                          have p1987_3 := h1987c.2.2.2
                                          linarith only [h1790, h1794, hc23, hc34, hlam, hphi, p1987_1]
                                        · have p1987_0 := h1987c.1
                                          have p1987_1 := h1987c.2.1
                                          have p1987_2 := h1987c.2.2.1
                                          have p1987_3 := h1987c.2.2.2
                                          linarith only [h1781, hlam, p1987_0]
                                        · have p1987_0 := h1987c.1
                                          have p1987_1 := h1987c.2.1
                                          have p1987_2 := h1987c.2.2.1
                                          have p1987_3 := h1987c.2.2.2
                                          linarith only [h1789, hlam, p1987_0]
                                        · have p1987_0 := h1987c.1
                                          have p1987_1 := h1987c.2.1
                                          have p1987_2 := h1987c.2.2.1
                                          have p1987_3 := h1987c.2.2.2
                                          linarith only [h1789, h1790, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1987_1]
                                        · have p1987_0 := h1987c.1
                                          have p1987_1 := h1987c.2.1
                                          have p1987_2 := h1987c.2.2.1
                                          have p1987_3 := h1987c.2.2.2
                                          linarith only [h1851, hlam, p1987_0]
                                        · have p1987_0 := h1987c.1
                                          have p1987_1 := h1987c.2.1
                                          have p1987_2 := h1987c.2.2.1
                                          have p1987_3 := h1987c.2.2.2
                                          linarith only [hlam, p1987_0]
                              · linarith only [h1893, hlam, p1852_0]
                            · linarith only [h1892, h6, hlam]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [h4, hlam, p1852_0]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [h1782, hlam, p1852_0]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [hlam, p1852_0]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [h1790, hlam, p1852_1]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [h1792, hlam, p1852_1]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [h5, hlam, p1852_0]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [h1783, hlam, p1852_0]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [h0, h1783, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1852_1]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [hlam, p1852_0]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [h1794, hlam, p1852_0]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [h6, hlam, p1852_0]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [h1784, hlam, p1852_0]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [h0, h1784, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1852_1]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [h0, h1783, h1789, h1794, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1852_1]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [hlam, p1852_0]
                        · linarith only [h1789, h1851, h2, h7, hlam]
                · linarith only [h1781, h1785, h1789, h7, hc34, hlam, hphi, ht12, ht23, u1ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2048 | h2048
            · linarith only [h1, h2048, h7, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2050 | h2050
              · linarith only [h0, h1702, h1783, h1784, h2048, h2050, h6, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2052 | h2052
                · linarith only [h1783, h1784, h2052, hlam]
                · linarith only [h1781, h2052, h7, hc34, hlam, hphi, ht12, ht23, u1ehi3]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2055 | h2055
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2056 | h2056
            · linarith only [h1, h1702, h1783, h2, h2056, h7, hc35, hlam, hphi, ht12, ht23, u1ehi1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2058 | h2058
              · linarith only [h1, h1702, h2058, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2060 | h2060
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2061 | h2061
                  · linarith only [h1783, h2061, h5, h7, hc23, hlam, hphi, ht12, u1ehi1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2063 | h2063
                    · linarith only [h0, h1, h1702, h1782, h1783, h2063, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2065 | h2065
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2066 | h2066
                        · rcases h2bigk with h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c
                          · have p2067_0 := h2067c.1
                            have p2067_1 := h2067c.2.1
                            have p2067_2 := h2067c.2.2.1
                            have p2067_3 := h2067c.2.2.2
                            linarith only [hlam, p2067_0]
                          · have p2067_0 := h2067c.1
                            have p2067_1 := h2067c.2.1
                            have p2067_2 := h2067c.2.2.1
                            have p2067_3 := h2067c.2.2.2
                            rcases p2067_3 (m.d 0 2) (by simp) with h2069 | h2069
                            · rcases p2067_3 (m.d 1 2) (by simp) with h2070 | h2070
                              · linarith only [h0, h2070, hlam]
                              · rcases p2067_3 (m.d 2 3) (by simp) with h2072 | h2072
                                · linarith only [h2072, h4, hlam]
                                · rcases p2067_3 (m.d 2 4) (by simp) with h2074 | h2074
                                  · linarith only [h2074, h5, hlam]
                                  · linarith only [h1783, h2074, hlam]
                            · linarith only [h0, h2069, hlam]
                          · have p2067_0 := h2067c.1
                            have p2067_1 := h2067c.2.1
                            have p2067_2 := h2067c.2.2.1
                            have p2067_3 := h2067c.2.2.2
                            linarith only [h1783, h2055, h2063, h5, hlam, p2067_2]
                          · have p2067_0 := h2067c.1
                            have p2067_1 := h2067c.2.1
                            have p2067_2 := h2067c.2.2.1
                            have p2067_3 := h2067c.2.2.2
                            linarith only [h0, h1783, h2055, h2063, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2067_1]
                          · have p2067_0 := h2067c.1
                            have p2067_1 := h2067c.2.1
                            have p2067_2 := h2067c.2.2.1
                            have p2067_3 := h2067c.2.2.2
                            linarith only [h1783, h2055, h5, hlam, p2067_2]
                          · have p2067_0 := h2067c.1
                            have p2067_1 := h2067c.2.1
                            have p2067_2 := h2067c.2.2.1
                            have p2067_3 := h2067c.2.2.2
                            linarith only [h0, hlam, p2067_1]
                          · have p2067_0 := h2067c.1
                            have p2067_1 := h2067c.2.1
                            have p2067_2 := h2067c.2.2.1
                            have p2067_3 := h2067c.2.2.2
                            linarith only [hlam, p2067_0]
                          · have p2067_0 := h2067c.1
                            have p2067_1 := h2067c.2.1
                            have p2067_2 := h2067c.2.2.1
                            have p2067_3 := h2067c.2.2.2
                            linarith only [h1783, h5, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2067_1]
                          · have p2067_0 := h2067c.1
                            have p2067_1 := h2067c.2.1
                            have p2067_2 := h2067c.2.2.1
                            have p2067_3 := h2067c.2.2.2
                            linarith only [h1783, hlam, p2067_0]
                          · have p2067_0 := h2067c.1
                            have p2067_1 := h2067c.2.1
                            have p2067_2 := h2067c.2.2.1
                            have p2067_3 := h2067c.2.2.2
                            linarith only [h1783, h5, hc02, hc25, hlam, hphi, ht0b, ht5b, p2067_1]
                          · have p2067_0 := h2067c.1
                            have p2067_1 := h2067c.2.1
                            have p2067_2 := h2067c.2.2.1
                            have p2067_3 := h2067c.2.2.2
                            linarith only [h4, hlam, p2067_0]
                          · have p2067_0 := h2067c.1
                            have p2067_1 := h2067c.2.1
                            have p2067_2 := h2067c.2.2.1
                            have p2067_3 := h2067c.2.2.2
                            linarith only [h1782, hlam, p2067_0]
                          · have p2067_0 := h2067c.1
                            have p2067_1 := h2067c.2.1
                            have p2067_2 := h2067c.2.2.1
                            have p2067_3 := h2067c.2.2.2
                            linarith only [hlam, p2067_0]
                          · have p2067_0 := h2067c.1
                            have p2067_1 := h2067c.2.1
                            have p2067_2 := h2067c.2.2.1
                            have p2067_3 := h2067c.2.2.2
                            linarith only [h2061, hlam, p2067_1]
                          · have p2067_0 := h2067c.1
                            have p2067_1 := h2067c.2.1
                            have p2067_2 := h2067c.2.2.1
                            have p2067_3 := h2067c.2.2.2
                            linarith only [h2063, hlam, p2067_1]
                          · have p2067_0 := h2067c.1
                            have p2067_1 := h2067c.2.1
                            have p2067_2 := h2067c.2.2.1
                            have p2067_3 := h2067c.2.2.2
                            linarith only [h5, hlam, p2067_0]
                          · have p2067_0 := h2067c.1
                            have p2067_1 := h2067c.2.1
                            have p2067_2 := h2067c.2.2.1
                            have p2067_3 := h2067c.2.2.2
                            linarith only [h5, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2067_1, u1ehi1]
                          · have p2067_0 := h2067c.1
                            have p2067_1 := h2067c.2.1
                            have p2067_2 := h2067c.2.2.1
                            have p2067_3 := h2067c.2.2.2
                            rcases p2067_3 (m.d 0 2) (by simp) with h2093 | h2093
                            · rcases p2067_3 (m.d 1 2) (by simp) with h2094 | h2094
                              · linarith only [h1783, h2094, hlam]
                              · linarith only [h1782, h2094, hlam]
                            · linarith only [h2093, h4, hlam]
                          · have p2067_0 := h2067c.1
                            have p2067_1 := h2067c.2.1
                            have p2067_2 := h2067c.2.2.1
                            have p2067_3 := h2067c.2.2.2
                            linarith only [hlam, p2067_0]
                          · have p2067_0 := h2067c.1
                            have p2067_1 := h2067c.2.1
                            have p2067_2 := h2067c.2.2.1
                            have p2067_3 := h2067c.2.2.2
                            rcases p2067_3 (m.d 0 2) (by simp) with h2099 | h2099
                            · rcases p2067_3 (m.d 1 2) (by simp) with h2100 | h2100
                              · linarith only [h1783, h2100, hlam]
                              · linarith only [h2055, h2100, hlam]
                            · linarith only [h2099, h6, hlam]
                          · have p2067_0 := h2067c.1
                            have p2067_1 := h2067c.2.1
                            have p2067_2 := h2067c.2.2.1
                            have p2067_3 := h2067c.2.2.2
                            linarith only [h6, hlam, p2067_0]
                          · have p2067_0 := h2067c.1
                            have p2067_1 := h2067c.2.1
                            have p2067_2 := h2067c.2.2.1
                            have p2067_3 := h2067c.2.2.2
                            linarith only [h2055, hlam, p2067_0]
                          · have p2067_0 := h2067c.1
                            have p2067_1 := h2067c.2.1
                            have p2067_2 := h2067c.2.2.1
                            have p2067_3 := h2067c.2.2.2
                            linarith only [h0, h2055, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2067_1]
                          · have p2067_0 := h2067c.1
                            have p2067_1 := h2067c.2.1
                            have p2067_2 := h2067c.2.2.1
                            have p2067_3 := h2067c.2.2.2
                            linarith only [h2065, hlam, p2067_1]
                          · have p2067_0 := h2067c.1
                            have p2067_1 := h2067c.2.1
                            have p2067_2 := h2067c.2.2.1
                            have p2067_3 := h2067c.2.2.2
                            linarith only [hlam, p2067_0]
                        · linarith only [h1783, h2066, h5, h7, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                      · linarith only [h1783, h2055, h2060, h2065, hlam]
                · linarith only [h1781, h2060, h7, hc34, hlam, hphi, ht12, ht23, u1ehi3]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2112 | h2112
            · linarith only [h1, h1783, h2112, h5, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2114 | h2114
              · linarith only [h1, h1702, h2114, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2116 | h2116
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2117 | h2117
                  · linarith only [h2117, h4, h7, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2119 | h2119
                    · linarith only [h1702, h1781, h1782, h2055, h2119, h6, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2121 | h2121
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2122 | h2122
                        · rcases h2bigk with h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c | h2123c
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [hlam, p2123_0]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            rcases p2123_3 (m.d 0 2) (by simp) with h2125 | h2125
                            · rcases p2123_3 (m.d 1 2) (by simp) with h2126 | h2126
                              · linarith only [h0, h2126, hlam]
                              · rcases p2123_3 (m.d 2 3) (by simp) with h2128 | h2128
                                · linarith only [h2128, h4, hlam]
                                · rcases p2123_3 (m.d 2 4) (by simp) with h2130 | h2130
                                  · linarith only [h2130, h5, hlam]
                                  · linarith only [h1783, h2130, hlam]
                            · linarith only [h0, h2125, hlam]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [h1782, h2055, h2121, h5, hlam, p2123_2]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [h0, h1782, h2055, h2121, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2123_1]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [h0, h2055, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2123_1, u1ehi1]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [h0, hlam, p2123_1]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [hlam, p2123_0]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [h0, h2055, h2121, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2123_1]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [h1783, hlam, p2123_0]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [h2055, hlam, p2123_0]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [h4, hlam, p2123_0]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [h1782, hlam, p2123_0]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [hlam, p2123_0]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [h2117, hlam, p2123_1]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [h2119, hlam, p2123_1]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [h5, hlam, p2123_0]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [h0, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2123_1, u1ehi1]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            rcases p2123_3 (m.d 0 2) (by simp) with h2149 | h2149
                            · rcases p2123_3 (m.d 1 2) (by simp) with h2150 | h2150
                              · linarith only [h1783, h2150, hlam]
                              · linarith only [h1782, h2150, hlam]
                            · linarith only [h2149, h4, hlam]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [hlam, p2123_0]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [h0, h1782, h2055, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p2123_1, u1ehi2]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [h6, hlam, p2123_0]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [h1782, hc25, hlam, hphi, ht12, p2123_1, u1ehi2]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            rcases p2123_3 (m.d 0 2) (by simp) with h2158 | h2158
                            · rcases p2123_3 (m.d 1 2) (by simp) with h2159 | h2159
                              · linarith only [h2055, h2159, hlam]
                              · linarith only [h1782, h2159, hlam]
                            · linarith only [h2158, h4, hlam]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [h2121, hlam, p2123_1]
                          · have p2123_0 := h2123c.1
                            have p2123_1 := h2123c.2.1
                            have p2123_2 := h2123c.2.2.1
                            have p2123_3 := h2123c.2.2.2
                            linarith only [hlam, p2123_0]
                        · linarith only [h1, h2122, h7, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                      · linarith only [h1783, h2116, h2121, hlam]
                · linarith only [h1781, h2116, h7, hc34, hlam, hphi, ht12, ht23, u1ehi3]
      · linarith only [h1782, h4, h7, hc34, hlam, hphi, ht12, ht23, u1ehi1]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2169 | h2169
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2170 | h2170
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2171 | h2171
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2172 | h2172
            · linarith only [h1, h2172, h7, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2174 | h2174
              · linarith only [h1, h1702, h2174, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2176 | h2176
                · linarith only [h1781, h2, h2176, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2178 | h2178
                  · linarith only [h1, h2169, h2178, h7, hc12, hlam, hphi, u1ehi2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2180 | h2180
                    · linarith only [h1, h1702, h2169, h2180, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2182 | h2182
                      · linarith only [h0, h1, h1781, h2170, h2182, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2184 | h2184
                        · linarith only [h1, h1781, h2184, h7, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                        · linarith only [h1, h2184, h7, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2187 | h2187
            · linarith only [h1, h2187, h7, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2189 | h2189
              · linarith only [h1, h1702, h2171, h2189, h6, h7, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2191 | h2191
                · linarith only [h0, h1781, h2170, h2171, h2191, h6, h7, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2193 | h2193
                  · linarith only [h1, h2193, h7, hc23, hlam, hphi, ht12, u1ehi2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2195 | h2195
                    · linarith only [h1702, h2170, h2171, h2193, h2195, h6, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2197 | h2197
                      · linarith only [h1781, h2170, h2171, h2197, h6, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2199 | h2199
                        · linarith only [h1781, h2170, h2171, h2193, h2199, h6, hc23, hc34, hlam, hphi]
                        · linarith only [h1, h2199, h7, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
        · linarith only [h1781, h2170, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
      · linarith only [h2169, h4, h7, hc34, hlam, hphi, ht12, ht23, u1ehi1]

set_option maxHeartbeats 6424000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s3_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s3_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4 h5 h6 h7
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s3_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4 h5 h6 h7

set_option maxHeartbeats 6424000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s3_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 4 (by decide) (by decide) with h2204 | h2204
  · rcases m.htr 0 3 5 (by decide) (by decide) with h2205 | h2205
    · linarith only [h2205, h4, h6, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2207 | h2207
      · linarith only [h2204, h2207, h4, h6, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2209 | h2209
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2210 | h2210
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2211 | h2211
            · linarith only [h2, h2204, h2211, h4, h6, hc12, hlam, hphi, u1ehi3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2213 | h2213
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2214 | h2214
                · linarith only [h2, h2204, h2205, h2214, hc13, hlam, hphi, u1ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2216 | h2216
                  · linarith only [h2, h2207, h2216, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2218 | h2218
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2219 | h2219
                      · linarith only [h0, h1, h2205, h2209, h2219, h6, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2221 | h2221
                        · linarith only [h0, h2, h2207, h2209, h2218, h2219, h2221, h6, hc35, hlam, hphi, ht12, ht23, u1ehi3]
                        · linarith only [h0, h2209, h2218, h2221, h6, hc34, hc45, hlam, hphi]
                    · linarith only [h2204, h2205, h2218, hc23, hc35, hlam, hphi]
              · linarith only [h2204, h2205, h2213, hc13, hc35, hlam, hphi]
          · linarith only [h2210, h5, h6, hc12, hc25, hlam, hphi]
        · linarith only [h2209, h4, h6, hc25, hlam, hphi, ht12, u1ehi1]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h2228 | h2228
    · linarith only [h2228, h4, h6, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2230 | h2230
      · linarith only [h2230, h5, h6, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2232 | h2232
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2233 | h2233
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2234 | h2234
            · linarith only [h0, h2234, h6, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2236 | h2236
              · linarith only [h1, h2204, h2236, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2238 | h2238
                · linarith only [h1, h2228, h2238, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2240 | h2240
                  · linarith only [h2, h2230, h2240, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2242 | h2242
                    · linarith only [h0, h1, h2204, h2232, h2242, h6, hc25, hlam, hphi, ht12, u1ehi2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2244 | h2244
                      · linarith only [h0, h1, h2228, h2233, h2242, h2244, h6, hc25, hlam, hphi, ht12, u1ehi2]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2246 | h2246
                        · linarith only [h0, h1, h2204, h2230, h2233, h2244, h2246, h6, hc35, hlam, hphi, ht12, ht23, u1ehi2]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2248 | h2248
                          · linarith only [h0, h2233, h2242, h2246, h2248, h6, hc23, hc34, hlam, hphi]
                          · linarith only [h1, h2204, h2248, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
          · linarith only [h2233, h5, h6, hc12, hc25, hlam, hphi]
        · linarith only [h2232, h4, h6, hc25, hlam, hphi, ht12, u1ehi1]

set_option maxHeartbeats 6424000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s3_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s3_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4 h5 h6
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s3_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4 h5 h6

set_option maxHeartbeats 6424000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s3_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h2253 | h2253
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2254 | h2254
    · linarith only [h2254, h4, h5, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2256 | h2256
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2257 | h2257
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2258 | h2258
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2259 | h2259
            · linarith only [h0, h2253, h2259, h5, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2261 | h2261
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2262 | h2262
                · linarith only [h2254, h2256, h2258, h2262, h3, hc12, hlam, hphi, u1ehi4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2264 | h2264
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2265 | h2265
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2266 | h2266
                      · linarith only [h2254, h2256, h2266, h3, hc23, hlam, hphi, ht12, u1ehi4]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2268 | h2268
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2269 | h2269
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2270 | h2270
                            · rcases h2bigk with h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c | h2271c
                              · have p2271_0 := h2271c.1
                                have p2271_1 := h2271c.2.1
                                have p2271_2 := h2271c.2.2.1
                                have p2271_3 := h2271c.2.2.2
                                linarith only [hlam, p2271_0]
                              · have p2271_0 := h2271c.1
                                have p2271_1 := h2271c.2.1
                                have p2271_2 := h2271c.2.2.1
                                have p2271_3 := h2271c.2.2.2
                                linarith only [h2258, h2268, h2270, hc02, hc45, hlam, hphi, ht0b, ht5b, p2271_1]
                              · have p2271_0 := h2271c.1
                                have p2271_1 := h2271c.2.1
                                have p2271_2 := h2271c.2.2.1
                                have p2271_3 := h2271c.2.2.2
                                linarith only [h2266, h2268, h2270, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2271_1]
                              · have p2271_0 := h2271c.1
                                have p2271_1 := h2271c.2.1
                                have p2271_2 := h2271c.2.2.1
                                have p2271_3 := h2271c.2.2.2
                                linarith only [h5, hlam, p2271_0]
                              · have p2271_0 := h2271c.1
                                have p2271_1 := h2271c.2.1
                                have p2271_2 := h2271c.2.2.1
                                have p2271_3 := h2271c.2.2.2
                                rcases p2271_3 (m.d 0 2) (by simp) with h2276 | h2276
                                · rcases p2271_3 (m.d 1 2) (by simp) with h2277 | h2277
                                  · linarith only [h0, h2277, hlam]
                                  · linarith only [h2261, h2277, hlam]
                                · linarith only [h2276, hlam, p2271_0]
                              · have p2271_0 := h2271c.1
                                have p2271_1 := h2271c.2.1
                                have p2271_2 := h2271c.2.2.1
                                have p2271_3 := h2271c.2.2.2
                                linarith only [h0, hlam, p2271_1]
                              · have p2271_0 := h2271c.1
                                have p2271_1 := h2271c.2.1
                                have p2271_2 := h2271c.2.2.1
                                have p2271_3 := h2271c.2.2.2
                                linarith only [hlam, p2271_0]
                              · have p2271_0 := h2271c.1
                                have p2271_1 := h2271c.2.1
                                have p2271_2 := h2271c.2.2.1
                                have p2271_3 := h2271c.2.2.2
                                linarith only [h0, h2268, h2270, hc01, hc45, hlam, hphi, ht0b, ht5b, p2271_1]
                              · have p2271_0 := h2271c.1
                                have p2271_1 := h2271c.2.1
                                have p2271_2 := h2271c.2.2.1
                                have p2271_3 := h2271c.2.2.2
                                linarith only [h2259, hlam, p2271_0]
                              · have p2271_0 := h2271c.1
                                have p2271_1 := h2271c.2.1
                                have p2271_2 := h2271c.2.2.1
                                have p2271_3 := h2271c.2.2.2
                                rcases p2271_3 (m.d 0 2) (by simp) with h2285 | h2285
                                · rcases p2271_3 (m.d 1 2) (by simp) with h2286 | h2286
                                  · rcases p2271_3 (m.d 2 3) (by simp) with h2287 | h2287
                                    · linarith only [h2258, h2287, hlam]
                                    · linarith only [h2268, h2287, hlam]
                                  · linarith only [h2286, hlam, p2271_0]
                                · linarith only [h2253, h2285, hlam]
                              · have p2271_0 := h2271c.1
                                have p2271_1 := h2271c.2.1
                                have p2271_2 := h2271c.2.2.1
                                have p2271_3 := h2271c.2.2.2
                                linarith only [h4, hlam, p2271_0]
                              · have p2271_0 := h2271c.1
                                have p2271_1 := h2271c.2.1
                                have p2271_2 := h2271c.2.2.1
                                have p2271_3 := h2271c.2.2.2
                                linarith only [h2258, hlam, p2271_0]
                              · have p2271_0 := h2271c.1
                                have p2271_1 := h2271c.2.1
                                have p2271_2 := h2271c.2.2.1
                                have p2271_3 := h2271c.2.2.2
                                linarith only [hlam, p2271_0]
                              · have p2271_0 := h2271c.1
                                have p2271_1 := h2271c.2.1
                                have p2271_2 := h2271c.2.2.1
                                have p2271_3 := h2271c.2.2.2
                                linarith only [h2266, hlam, p2271_1]
                              · have p2271_0 := h2271c.1
                                have p2271_1 := h2271c.2.1
                                have p2271_2 := h2271c.2.2.1
                                have p2271_3 := h2271c.2.2.2
                                linarith only [h2266, h2268, h2270, h4, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2271_1]
                              · have p2271_0 := h2271c.1
                                have p2271_1 := h2271c.2.1
                                have p2271_2 := h2271c.2.2.1
                                have p2271_3 := h2271c.2.2.2
                                linarith only [h0, h2266, hc34, hlam, hphi, ht12, ht23, p2271_1, u1ehi1]
                              · have p2271_0 := h2271c.1
                                have p2271_1 := h2271c.2.1
                                have p2271_2 := h2271c.2.2.1
                                have p2271_3 := h2271c.2.2.2
                                linarith only [h2258, h2264, h2266, hc34, hlam, hphi, ht12, ht23, p2271_1, u1ehi4]
                              · have p2271_0 := h2271c.1
                                have p2271_1 := h2271c.2.1
                                have p2271_2 := h2271c.2.2.1
                                have p2271_3 := h2271c.2.2.2
                                rcases p2271_3 (m.d 0 2) (by simp) with h2299 | h2299
                                · linarith only [h2299, h5, hlam]
                                · linarith only [h2299, h4, hlam]
                              · have p2271_0 := h2271c.1
                                have p2271_1 := h2271c.2.1
                                have p2271_2 := h2271c.2.2.1
                                have p2271_3 := h2271c.2.2.2
                                linarith only [hlam, p2271_0]
                              · have p2271_0 := h2271c.1
                                have p2271_1 := h2271c.2.1
                                have p2271_2 := h2271c.2.2.1
                                have p2271_3 := h2271c.2.2.2
                                rcases p2271_3 (m.d 0 2) (by simp) with h2303 | h2303
                                · linarith only [h2303, h5, hlam]
                                · linarith only [h2253, h2303, hlam]
                              · have p2271_0 := h2271c.1
                                have p2271_1 := h2271c.2.1
                                have p2271_2 := h2271c.2.2.1
                                have p2271_3 := h2271c.2.2.2
                                linarith only [h2253, hlam, p2271_0]
                              · have p2271_0 := h2271c.1
                                have p2271_1 := h2271c.2.1
                                have p2271_2 := h2271c.2.2.1
                                have p2271_3 := h2271c.2.2.2
                                linarith only [h2261, hlam, p2271_0]
                              · have p2271_0 := h2271c.1
                                have p2271_1 := h2271c.2.1
                                have p2271_2 := h2271c.2.2.1
                                have p2271_3 := h2271c.2.2.2
                                linarith only [h2268, hlam, p2271_0]
                              · have p2271_0 := h2271c.1
                                have p2271_1 := h2271c.2.1
                                have p2271_2 := h2271c.2.2.1
                                have p2271_3 := h2271c.2.2.2
                                linarith only [h2269, hlam, p2271_1]
                              · have p2271_0 := h2271c.1
                                have p2271_1 := h2271c.2.1
                                have p2271_2 := h2271c.2.2.1
                                have p2271_3 := h2271c.2.2.2
                                linarith only [hlam, p2271_0]
                            · linarith only [h0, h2258, h2266, h2270, h5, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h1, h2264, h2265, h2269, h4, h5, hlam]
                        · linarith only [h2256, h2266, h2268, h4, h5, hc23, hc34, hlam, hphi]
                    · linarith only [h2254, h2257, h2265, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                  · linarith only [h2256, h2264, h4, h5, hc24, hlam, hphi, ht12, u1ehi2]
              · linarith only [h2253, h2261, h5, hc12, hc24, hlam, hphi]
          · linarith only [h2258, h4, h5, hc24, hlam, hphi, ht12, u1ehi1]
        · linarith only [h2256, h2257, h4, h5, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2319 | h2319
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2320 | h2320
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2321 | h2321
            · linarith only [h0, h2321, h5, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2323 | h2323
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2324 | h2324
                · linarith only [h1, h2254, h2324, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2326 | h2326
                  · linarith only [h1, h2256, h2326, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2328 | h2328
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2329 | h2329
                      · linarith only [h0, h1, h2254, h2320, h2329, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2331 | h2331
                        · linarith only [h0, h1, h2256, h2320, h2329, h2331, h5, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2333 | h2333
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2334 | h2334
                            · rcases h2bigk with h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c | h2335c
                              · have p2335_0 := h2335c.1
                                have p2335_1 := h2335c.2.1
                                have p2335_2 := h2335c.2.2.1
                                have p2335_3 := h2335c.2.2.2
                                linarith only [hlam, p2335_0]
                              · have p2335_0 := h2335c.1
                                have p2335_1 := h2335c.2.1
                                have p2335_2 := h2335c.2.2.1
                                have p2335_3 := h2335c.2.2.2
                                linarith only [h2329, h5, hc12, hc34, hlam, hphi, ht23, p2335_1]
                              · have p2335_0 := h2335c.1
                                have p2335_1 := h2335c.2.1
                                have p2335_2 := h2335c.2.2.1
                                have p2335_3 := h2335c.2.2.2
                                linarith only [h2329, h5, hc23, hc34, hlam, hphi, p2335_1]
                              · have p2335_0 := h2335c.1
                                have p2335_1 := h2335c.2.1
                                have p2335_2 := h2335c.2.2.1
                                have p2335_3 := h2335c.2.2.2
                                linarith only [h5, hlam, p2335_0]
                              · have p2335_0 := h2335c.1
                                have p2335_1 := h2335c.2.1
                                have p2335_2 := h2335c.2.2.1
                                have p2335_3 := h2335c.2.2.2
                                linarith only [h2329, h2331, h5, hc23, hc34, hlam, hphi, p2335_1]
                              · have p2335_0 := h2335c.1
                                have p2335_1 := h2335c.2.1
                                have p2335_2 := h2335c.2.2.1
                                have p2335_3 := h2335c.2.2.2
                                linarith only [h0, hlam, p2335_1]
                              · have p2335_0 := h2335c.1
                                have p2335_1 := h2335c.2.1
                                have p2335_2 := h2335c.2.2.1
                                have p2335_3 := h2335c.2.2.2
                                linarith only [hlam, p2335_0]
                              · have p2335_0 := h2335c.1
                                have p2335_1 := h2335c.2.1
                                have p2335_2 := h2335c.2.2.1
                                have p2335_3 := h2335c.2.2.2
                                linarith only [h0, h2329, h5, hc23, hc34, hlam, hphi, p2335_1]
                              · have p2335_0 := h2335c.1
                                have p2335_1 := h2335c.2.1
                                have p2335_2 := h2335c.2.2.1
                                have p2335_3 := h2335c.2.2.2
                                linarith only [h2321, hlam, p2335_0]
                              · have p2335_0 := h2335c.1
                                have p2335_1 := h2335c.2.1
                                have p2335_2 := h2335c.2.2.1
                                have p2335_3 := h2335c.2.2.2
                                linarith only [h0, h2329, h2331, h5, hc23, hc34, hlam, hphi, p2335_1]
                              · have p2335_0 := h2335c.1
                                have p2335_1 := h2335c.2.1
                                have p2335_2 := h2335c.2.2.1
                                have p2335_3 := h2335c.2.2.2
                                linarith only [h4, hlam, p2335_0]
                              · have p2335_0 := h2335c.1
                                have p2335_1 := h2335c.2.1
                                have p2335_2 := h2335c.2.2.1
                                have p2335_3 := h2335c.2.2.2
                                linarith only [h2320, hlam, p2335_0]
                              · have p2335_0 := h2335c.1
                                have p2335_1 := h2335c.2.1
                                have p2335_2 := h2335c.2.2.1
                                have p2335_3 := h2335c.2.2.2
                                linarith only [hlam, p2335_0]
                              · have p2335_0 := h2335c.1
                                have p2335_1 := h2335c.2.1
                                have p2335_2 := h2335c.2.2.1
                                have p2335_3 := h2335c.2.2.2
                                linarith only [h2329, hlam, p2335_1]
                              · have p2335_0 := h2335c.1
                                have p2335_1 := h2335c.2.1
                                have p2335_2 := h2335c.2.2.1
                                have p2335_3 := h2335c.2.2.2
                                linarith only [h2331, hlam, p2335_1]
                              · have p2335_0 := h2335c.1
                                have p2335_1 := h2335c.2.1
                                have p2335_2 := h2335c.2.2.1
                                have p2335_3 := h2335c.2.2.2
                                linarith only [h0, h2329, hc34, hlam, hphi, ht12, ht23, p2335_1, u1ehi1]
                              · have p2335_0 := h2335c.1
                                have p2335_1 := h2335c.2.1
                                have p2335_2 := h2335c.2.2.1
                                have p2335_3 := h2335c.2.2.2
                                linarith only [h2320, h2329, hc34, hlam, hphi, ht12, ht23, p2335_1, u1ehi2]
                              · have p2335_0 := h2335c.1
                                have p2335_1 := h2335c.2.1
                                have p2335_2 := h2335c.2.2.1
                                have p2335_3 := h2335c.2.2.2
                                rcases p2335_3 (m.d 0 2) (by simp) with h2353 | h2353
                                · linarith only [h2353, h5, hlam]
                                · linarith only [h2353, h4, hlam]
                              · have p2335_0 := h2335c.1
                                have p2335_1 := h2335c.2.1
                                have p2335_2 := h2335c.2.2.1
                                have p2335_3 := h2335c.2.2.2
                                linarith only [hlam, p2335_0]
                              · have p2335_0 := h2335c.1
                                have p2335_1 := h2335c.2.1
                                have p2335_2 := h2335c.2.2.1
                                have p2335_3 := h2335c.2.2.2
                                rcases p2335_3 (m.d 0 2) (by simp) with h2357 | h2357
                                · linarith only [h2357, h5, hlam]
                                · linarith only [h2253, h2357, hlam]
                              · have p2335_0 := h2335c.1
                                have p2335_1 := h2335c.2.1
                                have p2335_2 := h2335c.2.2.1
                                have p2335_3 := h2335c.2.2.2
                                linarith only [h2253, hlam, p2335_0]
                              · have p2335_0 := h2335c.1
                                have p2335_1 := h2335c.2.1
                                have p2335_2 := h2335c.2.2.1
                                have p2335_3 := h2335c.2.2.2
                                linarith only [h2323, hlam, p2335_0]
                              · have p2335_0 := h2335c.1
                                have p2335_1 := h2335c.2.1
                                have p2335_2 := h2335c.2.2.1
                                have p2335_3 := h2335c.2.2.2
                                linarith only [h2253, h2329, h5, hc23, hc34, hlam, hphi, p2335_1]
                              · have p2335_0 := h2335c.1
                                have p2335_1 := h2335c.2.1
                                have p2335_2 := h2335c.2.2.1
                                have p2335_3 := h2335c.2.2.2
                                linarith only [h2333, hlam, p2335_1]
                              · have p2335_0 := h2335c.1
                                have p2335_1 := h2335c.2.1
                                have p2335_2 := h2335c.2.2.1
                                have p2335_3 := h2335c.2.2.2
                                linarith only [hlam, p2335_0]
                            · linarith only [h0, h2323, h2329, h2333, h2334, h5, hlam]
                          · linarith only [h0, h2333, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                    · linarith only [h2253, h2319, h2328, h5, hc24, hlam, hphi, ht12, u1ehi3]
              · linarith only [h2253, h2323, h5, hc12, hc24, hlam, hphi]
          · linarith only [h2320, h4, h5, hc24, hlam, hphi, ht12, u1ehi1]
        · linarith only [h2253, h2319, h5, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2371 | h2371
    · linarith only [h2371, h4, h5, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2373 | h2373
      · linarith only [h2253, h2373, h4, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2375 | h2375
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2376 | h2376
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2377 | h2377
            · linarith only [h0, h2377, h5, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2379 | h2379
              · linarith only [h1, h2253, h2379, h4, hc12, hlam, hphi, u1ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2381 | h2381
                · linarith only [h1, h2371, h2381, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2383 | h2383
                  · linarith only [h1, h2373, h2383, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2385 | h2385
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2386 | h2386
                      · linarith only [h0, h1, h2371, h2376, h2386, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2388 | h2388
                        · linarith only [h0, h2373, h2376, h2386, h2388, h3, h5, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2390 | h2390
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2391 | h2391
                            · rcases h2bigk with h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c | h2392c
                              · have p2392_0 := h2392c.1
                                have p2392_1 := h2392c.2.1
                                have p2392_2 := h2392c.2.2.1
                                have p2392_3 := h2392c.2.2.2
                                linarith only [hlam, p2392_0]
                              · have p2392_0 := h2392c.1
                                have p2392_1 := h2392c.2.1
                                have p2392_2 := h2392c.2.2.1
                                have p2392_3 := h2392c.2.2.2
                                linarith only [h2253, h2386, h2390, hc12, hc34, hlam, hphi, ht23, p2392_1]
                              · have p2392_0 := h2392c.1
                                have p2392_1 := h2392c.2.1
                                have p2392_2 := h2392c.2.2.1
                                have p2392_3 := h2392c.2.2.2
                                linarith only [h2253, h2386, h2390, hc23, hc34, hlam, hphi, p2392_1]
                              · have p2392_0 := h2392c.1
                                have p2392_1 := h2392c.2.1
                                have p2392_2 := h2392c.2.2.1
                                have p2392_3 := h2392c.2.2.2
                                linarith only [h5, hlam, p2392_0]
                              · have p2392_0 := h2392c.1
                                have p2392_1 := h2392c.2.1
                                have p2392_2 := h2392c.2.2.1
                                have p2392_3 := h2392c.2.2.2
                                linarith only [h2253, hlam, p2392_0]
                              · have p2392_0 := h2392c.1
                                have p2392_1 := h2392c.2.1
                                have p2392_2 := h2392c.2.2.1
                                have p2392_3 := h2392c.2.2.2
                                linarith only [h0, hlam, p2392_1]
                              · have p2392_0 := h2392c.1
                                have p2392_1 := h2392c.2.1
                                have p2392_2 := h2392c.2.2.1
                                have p2392_3 := h2392c.2.2.2
                                linarith only [hlam, p2392_0]
                              · have p2392_0 := h2392c.1
                                have p2392_1 := h2392c.2.1
                                have p2392_2 := h2392c.2.2.1
                                have p2392_3 := h2392c.2.2.2
                                linarith only [h0, h2253, h2386, h2390, hc23, hc34, hlam, hphi, p2392_1]
                              · have p2392_0 := h2392c.1
                                have p2392_1 := h2392c.2.1
                                have p2392_2 := h2392c.2.2.1
                                have p2392_3 := h2392c.2.2.2
                                linarith only [h2377, hlam, p2392_0]
                              · have p2392_0 := h2392c.1
                                have p2392_1 := h2392c.2.1
                                have p2392_2 := h2392c.2.2.1
                                have p2392_3 := h2392c.2.2.2
                                linarith only [h2379, hlam, p2392_0]
                              · have p2392_0 := h2392c.1
                                have p2392_1 := h2392c.2.1
                                have p2392_2 := h2392c.2.2.1
                                have p2392_3 := h2392c.2.2.2
                                linarith only [h4, hlam, p2392_0]
                              · have p2392_0 := h2392c.1
                                have p2392_1 := h2392c.2.1
                                have p2392_2 := h2392c.2.2.1
                                have p2392_3 := h2392c.2.2.2
                                linarith only [h2376, hlam, p2392_0]
                              · have p2392_0 := h2392c.1
                                have p2392_1 := h2392c.2.1
                                have p2392_2 := h2392c.2.2.1
                                have p2392_3 := h2392c.2.2.2
                                linarith only [hlam, p2392_0]
                              · have p2392_0 := h2392c.1
                                have p2392_1 := h2392c.2.1
                                have p2392_2 := h2392c.2.2.1
                                have p2392_3 := h2392c.2.2.2
                                linarith only [h2386, hlam, p2392_1]
                              · have p2392_0 := h2392c.1
                                have p2392_1 := h2392c.2.1
                                have p2392_2 := h2392c.2.2.1
                                have p2392_3 := h2392c.2.2.2
                                linarith only [h2388, hlam, p2392_1]
                              · have p2392_0 := h2392c.1
                                have p2392_1 := h2392c.2.1
                                have p2392_2 := h2392c.2.2.1
                                have p2392_3 := h2392c.2.2.2
                                linarith only [h0, h2386, hc34, hlam, hphi, ht12, ht23, p2392_1, u1ehi1]
                              · have p2392_0 := h2392c.1
                                have p2392_1 := h2392c.2.1
                                have p2392_2 := h2392c.2.2.1
                                have p2392_3 := h2392c.2.2.2
                                linarith only [h2376, h2386, hc34, hlam, hphi, ht12, ht23, p2392_1, u1ehi2]
                              · have p2392_0 := h2392c.1
                                have p2392_1 := h2392c.2.1
                                have p2392_2 := h2392c.2.2.1
                                have p2392_3 := h2392c.2.2.2
                                rcases p2392_3 (m.d 0 2) (by simp) with h2410 | h2410
                                · linarith only [h2410, h5, hlam]
                                · linarith only [h2410, h4, hlam]
                              · have p2392_0 := h2392c.1
                                have p2392_1 := h2392c.2.1
                                have p2392_2 := h2392c.2.2.1
                                have p2392_3 := h2392c.2.2.2
                                linarith only [hlam, p2392_0]
                              · have p2392_0 := h2392c.1
                                have p2392_1 := h2392c.2.1
                                have p2392_2 := h2392c.2.2.1
                                have p2392_3 := h2392c.2.2.2
                                linarith only [h1, h2253, h2386, h4, hc34, hlam, hphi, ht12, ht23, p2392_1, u1ehi2]
                              · have p2392_0 := h2392c.1
                                have p2392_1 := h2392c.2.1
                                have p2392_2 := h2392c.2.2.1
                                have p2392_3 := h2392c.2.2.2
                                linarith only [h1, h4, hc25, hlam, hphi, ht12, p2392_1, u1ehi2]
                              · have p2392_0 := h2392c.1
                                have p2392_1 := h2392c.2.1
                                have p2392_2 := h2392c.2.2.1
                                have p2392_3 := h2392c.2.2.2
                                linarith only [h2376, h2388, hc35, hlam, hphi, ht12, ht23, p2392_1, u1ehi2]
                              · have p2392_0 := h2392c.1
                                have p2392_1 := h2392c.2.1
                                have p2392_2 := h2392c.2.2.1
                                have p2392_3 := h2392c.2.2.2
                                rcases p2392_3 (m.d 0 2) (by simp) with h2417 | h2417
                                · linarith only [h2253, h2417, hlam]
                                · linarith only [h2417, h4, hlam]
                              · have p2392_0 := h2392c.1
                                have p2392_1 := h2392c.2.1
                                have p2392_2 := h2392c.2.2.1
                                have p2392_3 := h2392c.2.2.2
                                linarith only [h2390, hlam, p2392_1]
                              · have p2392_0 := h2392c.1
                                have p2392_1 := h2392c.2.1
                                have p2392_2 := h2392c.2.2.1
                                have p2392_3 := h2392c.2.2.2
                                linarith only [hlam, p2392_0]
                            · linarith only [h1, h2386, h2391, h4, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                          · linarith only [h2, h2385, h2390, h5, hlam]
                    · linarith only [h2375, h2385, h5, hc24, hlam, hphi, ht12, u1ehi3]
          · linarith only [h2376, h4, h5, hc12, hc24, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2426 | h2426
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2427 | h2427
            · linarith only [h0, h2427, h5, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2429 | h2429
              · linarith only [h0, h2253, h2429, h3, h5, hc24, hlam, hphi, ht12, u1ehi4]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2431 | h2431
                · linarith only [h1, h2371, h2431, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2433 | h2433
                  · linarith only [h1, h2373, h2433, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2435 | h2435
                    · linarith only [h1, h2, h2375, h2435, h4, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2437 | h2437
                      · linarith only [h1, h2371, h2437, hc23, hlam, hphi, ht12, u1ehi2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2439 | h2439
                        · linarith only [h2373, h2426, h2439, h3, hc12, hlam, hphi, u1ehi4]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2441 | h2441
                          · linarith only [h0, h2375, h2426, h2437, h2441, h5, hc23, hc34, hlam, hphi]
                          · linarith only [h1, h2441, h4, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
          · linarith only [h2426, h4, h5, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 6424000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s3_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s3_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4 h5
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s3_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4 h5

end R2N4
