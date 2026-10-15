import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_52S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4970000 in
theorem r1l7_10_12_25_L_I_L_0_H_I_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1797 | h1797
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1798 | h1798
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1799 | h1799
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1800 | h1800
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1801 | h1801
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1802 | h1802
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1803 | h1803
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1804 | h1804
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1805 | h1805
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1806 | h1806
                    · linarith only [h0, h1797, h1806, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1797, h1801, h1804, h1806, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h0, h1805, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h1804, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1811 | h1811
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1812 | h1812
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1813 | h1813
                    · linarith only [h0, h1797, h1813, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1797, h1801, h1811, h1813, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h0, h1812, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h1811, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1818 | h1818
              · linarith only [h1801, h1802, h1818, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1820 | h1820
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1821 | h1821
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1822 | h1822
                    · linarith only [h0, h1797, h1822, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h1801, h1802, h1820, h1822, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h1821, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h1798, h1801, h1802, h1820, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1827 | h1827
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1828 | h1828
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1829 | h1829
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1830 | h1830
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1831 | h1831
                    · linarith only [h0, h1797, h1801, h1831, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1833 | h1833
                      · linarith only [h0, h1797, h1833, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · linarith only [h1801, h1827, h1829, h1833, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h1830, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h1829, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h1801, h1827, h1828, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1839 | h1839
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1840 | h1840
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1841 | h1841
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1842 | h1842
                    · linarith only [h0, h1797, h1842, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1844 | h1844
                      · linarith only [h0, h1797, h1827, h1844, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1846 | h1846
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1847 | h1847
                          · linarith only [h0, h1797, h1827, h1840, h1847, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1849 | h1849
                            · rcases h0emin with h1850 | h1850 | h1850 | h1850 | h1850
                              · linarith only [h0, h1850, hlam, ht01, ht12, u2elo1]
                              · linarith only [h0, h1850, hlam, ht01, ht12, u2elo1]
                              · linarith only [h1827, h1849, h1850, hc34, hlam, ht01, ht12, ht23]
                              · rcases h5bigk with h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c | h1854c
                                · have p1854_0 := h1854c.1
                                  have p1854_1 := h1854c.2.1
                                  have p1854_2 := h1854c.2.2.1
                                  have p1854_3 := h1854c.2.2.2
                                  linarith only [hlam, p1854_0]
                                · have p1854_0 := h1854c.1
                                  have p1854_1 := h1854c.2.1
                                  have p1854_2 := h1854c.2.2.1
                                  have p1854_3 := h1854c.2.2.2
                                  linarith only [h0, h1798, h1840, h1844, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1854_1, u2elo1]
                                · have p1854_0 := h1854c.1
                                  have p1854_1 := h1854c.2.1
                                  have p1854_2 := h1854c.2.2.1
                                  have p1854_3 := h1854c.2.2.2
                                  linarith only [h0, h1798, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1854_1, u2elo1]
                                · have p1854_0 := h1854c.1
                                  have p1854_1 := h1854c.2.1
                                  have p1854_2 := h1854c.2.2.1
                                  have p1854_3 := h1854c.2.2.2
                                  linarith only [h1827, hlam, p1854_1]
                                · have p1854_0 := h1854c.1
                                  have p1854_1 := h1854c.2.1
                                  have p1854_2 := h1854c.2.2.1
                                  have p1854_3 := h1854c.2.2.2
                                  linarith only [h0, h1798, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1854_1, u2elo1]
                                · have p1854_0 := h1854c.1
                                  have p1854_1 := h1854c.2.1
                                  have p1854_2 := h1854c.2.2.1
                                  have p1854_3 := h1854c.2.2.2
                                  linarith only [h1798, hlam, p1854_0]
                                · have p1854_0 := h1854c.1
                                  have p1854_1 := h1854c.2.1
                                  have p1854_2 := h1854c.2.2.1
                                  have p1854_3 := h1854c.2.2.2
                                  linarith only [hlam, p1854_0]
                                · have p1854_0 := h1854c.1
                                  have p1854_1 := h1854c.2.1
                                  have p1854_2 := h1854c.2.2.1
                                  have p1854_3 := h1854c.2.2.2
                                  linarith only [h0, h1798, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1854_1, u2elo1]
                                · have p1854_0 := h1854c.1
                                  have p1854_1 := h1854c.2.1
                                  have p1854_2 := h1854c.2.2.1
                                  have p1854_3 := h1854c.2.2.2
                                  linarith only [h1844, hlam, p1854_1]
                                · have p1854_0 := h1854c.1
                                  have p1854_1 := h1854c.2.1
                                  have p1854_2 := h1854c.2.2.1
                                  have p1854_3 := h1854c.2.2.2
                                  linarith only [h0, h1798, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1854_1, u2elo1]
                                · have p1854_0 := h1854c.1
                                  have p1854_1 := h1854c.2.1
                                  have p1854_2 := h1854c.2.2.1
                                  have p1854_3 := h1854c.2.2.2
                                  linarith only [h1800, hlam, p1854_1]
                                · have p1854_0 := h1854c.1
                                  have p1854_1 := h1854c.2.1
                                  have p1854_2 := h1854c.2.2.1
                                  have p1854_3 := h1854c.2.2.2
                                  linarith only [h1841, hlam, p1854_1]
                                · have p1854_0 := h1854c.1
                                  have p1854_1 := h1854c.2.1
                                  have p1854_2 := h1854c.2.2.1
                                  have p1854_3 := h1854c.2.2.2
                                  linarith only [hlam, p1854_0]
                                · have p1854_0 := h1854c.1
                                  have p1854_1 := h1854c.2.1
                                  have p1854_2 := h1854c.2.2.1
                                  have p1854_3 := h1854c.2.2.2
                                  linarith only [h1847, hlam, p1854_1]
                                · have p1854_0 := h1854c.1
                                  have p1854_1 := h1854c.2.1
                                  have p1854_2 := h1854c.2.2.1
                                  have p1854_3 := h1854c.2.2.2
                                  linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1854_1, u2elo4]
                                · have p1854_0 := h1854c.1
                                  have p1854_1 := h1854c.2.1
                                  have p1854_2 := h1854c.2.2.1
                                  have p1854_3 := h1854c.2.2.2
                                  linarith only [h1827, h1849, hc03, hc34, hlam, hphi, p1854_1]
                                · have p1854_0 := h1854c.1
                                  have p1854_1 := h1854c.2.1
                                  have p1854_2 := h1854c.2.2.1
                                  have p1854_3 := h1854c.2.2.2
                                  linarith only [h1840, h1844, h1849, hc23, hc34, hlam, hphi, p1854_1]
                                · have p1854_0 := h1854c.1
                                  have p1854_1 := h1854c.2.1
                                  have p1854_2 := h1854c.2.2.1
                                  have p1854_3 := h1854c.2.2.2
                                  linarith only [h1847, h1849, hc23, hc34, hlam, hphi, p1854_1]
                                · have p1854_0 := h1854c.1
                                  have p1854_1 := h1854c.2.1
                                  have p1854_2 := h1854c.2.2.1
                                  have p1854_3 := h1854c.2.2.2
                                  linarith only [hlam, p1854_0]
                                · have p1854_0 := h1854c.1
                                  have p1854_1 := h1854c.2.1
                                  have p1854_2 := h1854c.2.2.1
                                  have p1854_3 := h1854c.2.2.2
                                  rcases p1854_3 (m.d 0 5) (by simp) with h1874 | h1874
                                  · linarith only [h1827, h1874, hlam]
                                  · linarith only [h1839, h1874, hlam]
                                · have p1854_0 := h1854c.1
                                  have p1854_1 := h1854c.2.1
                                  have p1854_2 := h1854c.2.2.1
                                  have p1854_3 := h1854c.2.2.2
                                  linarith only [h1839, hlam, p1854_0]
                                · have p1854_0 := h1854c.1
                                  have p1854_1 := h1854c.2.1
                                  have p1854_2 := h1854c.2.2.1
                                  have p1854_3 := h1854c.2.2.2
                                  linarith only [h1846, hlam, p1854_0]
                                · have p1854_0 := h1854c.1
                                  have p1854_1 := h1854c.2.1
                                  have p1854_2 := h1854c.2.2.1
                                  have p1854_3 := h1854c.2.2.2
                                  linarith only [h1846, h1847, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1854_1]
                                · have p1854_0 := h1854c.1
                                  have p1854_1 := h1854c.2.1
                                  have p1854_2 := h1854c.2.2.1
                                  have p1854_3 := h1854c.2.2.2
                                  linarith only [h1849, hlam, p1854_0]
                                · have p1854_0 := h1854c.1
                                  have p1854_1 := h1854c.2.1
                                  have p1854_2 := h1854c.2.2.1
                                  have p1854_3 := h1854c.2.2.2
                                  linarith only [hlam, p1854_0]
                              · linarith only [h0, h1798, h1850, hlam, ht01, ht12, u2elo1]
                            · linarith only [h1801, h1839, h1849, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1884 | h1884
                          · linarith only [h0, h1797, h1840, h1884, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1886 | h1886
                            · rcases h0emin with h1887 | h1887 | h1887 | h1887 | h1887
                              · linarith only [h0, h1887, hlam, ht01, ht12, u2elo1]
                              · linarith only [h0, h1887, hlam, ht01, ht12, u2elo1]
                              · linarith only [h0, h1797, h1887, hlam, ht01, ht12, u2elo1]
                              · rcases h5bigk with h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c | h1891c
                                · have p1891_0 := h1891c.1
                                  have p1891_1 := h1891c.2.1
                                  have p1891_2 := h1891c.2.2.1
                                  have p1891_3 := h1891c.2.2.2
                                  linarith only [hlam, p1891_0]
                                · have p1891_0 := h1891c.1
                                  have p1891_1 := h1891c.2.1
                                  have p1891_2 := h1891c.2.2.1
                                  have p1891_3 := h1891c.2.2.2
                                  linarith only [h0, h1798, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1891_1, u2elo1]
                                · have p1891_0 := h1891c.1
                                  have p1891_1 := h1891c.2.1
                                  have p1891_2 := h1891c.2.2.1
                                  have p1891_3 := h1891c.2.2.2
                                  linarith only [h0, h1798, h1884, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1891_1, u2elo1]
                                · have p1891_0 := h1891c.1
                                  have p1891_1 := h1891c.2.1
                                  have p1891_2 := h1891c.2.2.1
                                  have p1891_3 := h1891c.2.2.2
                                  linarith only [h1827, hlam, p1891_1]
                                · have p1891_0 := h1891c.1
                                  have p1891_1 := h1891c.2.1
                                  have p1891_2 := h1891c.2.2.1
                                  have p1891_3 := h1891c.2.2.2
                                  linarith only [h0, h1798, h1842, h1846, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1891_1, u2elo1]
                                · have p1891_0 := h1891c.1
                                  have p1891_1 := h1891c.2.1
                                  have p1891_2 := h1891c.2.2.1
                                  have p1891_3 := h1891c.2.2.2
                                  linarith only [h1798, hlam, p1891_0]
                                · have p1891_0 := h1891c.1
                                  have p1891_1 := h1891c.2.1
                                  have p1891_2 := h1891c.2.2.1
                                  have p1891_3 := h1891c.2.2.2
                                  linarith only [hlam, p1891_0]
                                · have p1891_0 := h1891c.1
                                  have p1891_1 := h1891c.2.1
                                  have p1891_2 := h1891c.2.2.1
                                  have p1891_3 := h1891c.2.2.2
                                  linarith only [h0, h1798, h1884, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1891_1, u2elo1]
                                · have p1891_0 := h1891c.1
                                  have p1891_1 := h1891c.2.1
                                  have p1891_2 := h1891c.2.2.1
                                  have p1891_3 := h1891c.2.2.2
                                  linarith only [h1844, hlam, p1891_1]
                                · have p1891_0 := h1891c.1
                                  have p1891_1 := h1891c.2.1
                                  have p1891_2 := h1891c.2.2.1
                                  have p1891_3 := h1891c.2.2.2
                                  linarith only [h1846, hlam, p1891_1]
                                · have p1891_0 := h1891c.1
                                  have p1891_1 := h1891c.2.1
                                  have p1891_2 := h1891c.2.2.1
                                  have p1891_3 := h1891c.2.2.2
                                  linarith only [h1800, hlam, p1891_1]
                                · have p1891_0 := h1891c.1
                                  have p1891_1 := h1891c.2.1
                                  have p1891_2 := h1891c.2.2.1
                                  have p1891_3 := h1891c.2.2.2
                                  linarith only [h1841, hlam, p1891_1]
                                · have p1891_0 := h1891c.1
                                  have p1891_1 := h1891c.2.1
                                  have p1891_2 := h1891c.2.2.1
                                  have p1891_3 := h1891c.2.2.2
                                  linarith only [hlam, p1891_0]
                                · have p1891_0 := h1891c.1
                                  have p1891_1 := h1891c.2.1
                                  have p1891_2 := h1891c.2.2.1
                                  have p1891_3 := h1891c.2.2.2
                                  linarith only [h1884, hlam, p1891_1]
                                · have p1891_0 := h1891c.1
                                  have p1891_1 := h1891c.2.1
                                  have p1891_2 := h1891c.2.2.1
                                  have p1891_3 := h1891c.2.2.2
                                  linarith only [h1840, h1842, h1846, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1891_1, u2elo4]
                                · have p1891_0 := h1891c.1
                                  have p1891_1 := h1891c.2.1
                                  have p1891_2 := h1891c.2.2.1
                                  have p1891_3 := h1891c.2.2.2
                                  linarith only [h1827, hc03, hc35, hlam, hphi, p1891_1]
                                · have p1891_0 := h1891c.1
                                  have p1891_1 := h1891c.2.1
                                  have p1891_2 := h1891c.2.2.1
                                  have p1891_3 := h1891c.2.2.2
                                  linarith only [h1840, h1844, hc23, hc35, hlam, hphi, p1891_1]
                                · have p1891_0 := h1891c.1
                                  have p1891_1 := h1891c.2.1
                                  have p1891_2 := h1891c.2.2.1
                                  have p1891_3 := h1891c.2.2.2
                                  linarith only [h1884, hc23, hc35, hlam, hphi, p1891_1]
                                · have p1891_0 := h1891c.1
                                  have p1891_1 := h1891c.2.1
                                  have p1891_2 := h1891c.2.2.1
                                  have p1891_3 := h1891c.2.2.2
                                  linarith only [hlam, p1891_0]
                                · have p1891_0 := h1891c.1
                                  have p1891_1 := h1891c.2.1
                                  have p1891_2 := h1891c.2.2.1
                                  have p1891_3 := h1891c.2.2.2
                                  linarith only [h1840, h1842, h1846, h1886, hc23, hc34, hlam, hphi, p1891_1]
                                · have p1891_0 := h1891c.1
                                  have p1891_1 := h1891c.2.1
                                  have p1891_2 := h1891c.2.2.1
                                  have p1891_3 := h1891c.2.2.2
                                  linarith only [h1839, hlam, p1891_0]
                                · have p1891_0 := h1891c.1
                                  have p1891_1 := h1891c.2.1
                                  have p1891_2 := h1891c.2.2.1
                                  have p1891_3 := h1891c.2.2.2
                                  linarith only [h1840, h1842, h1846, hc23, hc45, hlam, hphi, ht34, p1891_1]
                                · have p1891_0 := h1891c.1
                                  have p1891_1 := h1891c.2.1
                                  have p1891_2 := h1891c.2.2.1
                                  have p1891_3 := h1891c.2.2.2
                                  linarith only [h0, h1798, h1839, h1884, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1891_1, u2elo1]
                                · have p1891_0 := h1891c.1
                                  have p1891_1 := h1891c.2.1
                                  have p1891_2 := h1891c.2.2.1
                                  have p1891_3 := h1891c.2.2.2
                                  linarith only [h1886, hlam, p1891_0]
                                · have p1891_0 := h1891c.1
                                  have p1891_1 := h1891c.2.1
                                  have p1891_2 := h1891c.2.2.1
                                  have p1891_3 := h1891c.2.2.2
                                  linarith only [hlam, p1891_0]
                              · linarith only [h0, h1798, h1887, hlam, ht01, ht12, u2elo1]
                            · linarith only [h0, h1797, h1798, h1801, h1839, h1840, h1886, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h0, h1841, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h1797, h1840, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1921 | h1921
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1922 | h1922
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1923 | h1923
                    · linarith only [h0, h1797, h1801, h1923, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1925 | h1925
                      · linarith only [h0, h1797, h1925, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1927 | h1927
                        · linarith only [h0, h1797, h1798, h1801, h1839, h1921, h1927, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1929 | h1929
                          · linarith only [h0, h1797, h1827, h1921, h1929, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1931 | h1931
                            · rcases h0emin with h1932 | h1932 | h1932 | h1932 | h1932
                              · linarith only [h0, h1932, hlam, ht01, ht12, u2elo1]
                              · linarith only [h1932, hlam, ht01, ht12, u2elo0]
                              · linarith only [h0, h1798, h1801, h1839, h1921, h1923, h1927, h1931, h1932, hc23, hc34, hlam, hphi, ht01, ht12, u2elo1]
                              · linarith only [h0, h1798, h1839, h1921, h1923, h1927, h1931, h1932, hc23, hc34, hlam, hphi, ht01, ht12, u2elo1]
                              · linarith only [h0, h1798, h1932, hlam, ht01, ht12, u2elo1]
                            · rcases h0emin with h1938 | h1938 | h1938 | h1938 | h1938
                              · linarith only [h0, h1938, hlam, ht01, ht12, u2elo1]
                              · linarith only [h0, h1938, hlam, ht01, ht12, u2elo1]
                              · linarith only [h0, h1797, h1938, hlam, ht01, ht12, u2elo1]
                              · linarith only [h0, h1798, h1801, h1921, h1923, h1927, h1931, h1938, hc23, hc45, hlam, hphi, ht01, ht12, ht34, u2elo1]
                              · linarith only [h0, h1798, h1938, hlam, ht01, ht12, u2elo1]
                  · linarith only [h0, h1922, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h1797, h1921, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
        · linarith only [h0, h1798, h1800, hlam]
      · linarith only [h0, h1797, h1799, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1948 | h1948
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1949 | h1949
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1950 | h1950
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1951 | h1951
            · linarith only [h1797, h1798, h1951, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1953 | h1953
              · linarith only [h1797, h1798, h1950, h1953, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1955 | h1955
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1956 | h1956
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1957 | h1957
                    · linarith only [h1797, h1798, h1956, h1957, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h1797, h1798, h1950, h1955, h1956, h1957, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h1949, h1956, hc12, hlam, hphi, u2elo0]
                · linarith only [h0, h1797, h1950, h1955, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1962 | h1962
            · linarith only [h1797, h1798, h1962, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1964 | h1964
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1965 | h1965
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1966 | h1966
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1967 | h1967
                    · linarith only [h1797, h1798, h1950, h1966, h1967, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1969 | h1969
                      · linarith only [h1797, h1798, h1962, h1969, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1971 | h1971
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1972 | h1972
                          · linarith only [h1798, h1969, h1972, hc01, hlam, hphi, ht12, u2elo2]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1974 | h1974
                            · rcases h0emin with h1975 | h1975 | h1975 | h1975 | h1975
                              · linarith only [h1798, h1971, h1975, hc14, hlam, ht01]
                              · linarith only [h1975, hlam, ht01, ht12, u2elo0]
                              · linarith only [h0, h1797, h1975, hlam, ht01, ht12, u2elo1]
                              · rcases h5bigk with h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c | h1979c
                                · have p1979_0 := h1979c.1
                                  have p1979_1 := h1979c.2.1
                                  have p1979_2 := h1979c.2.2.1
                                  have p1979_3 := h1979c.2.2.2
                                  linarith only [hlam, p1979_0]
                                · have p1979_0 := h1979c.1
                                  have p1979_1 := h1979c.2.1
                                  have p1979_2 := h1979c.2.2.1
                                  have p1979_3 := h1979c.2.2.2
                                  linarith only [h1798, hlam, p1979_1]
                                · have p1979_0 := h1979c.1
                                  have p1979_1 := h1979c.2.1
                                  have p1979_2 := h1979c.2.2.1
                                  have p1979_3 := h1979c.2.2.2
                                  linarith only [h1798, h1966, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1979_1, u2elo1]
                                · have p1979_0 := h1979c.1
                                  have p1979_1 := h1979c.2.1
                                  have p1979_2 := h1979c.2.2.1
                                  have p1979_3 := h1979c.2.2.2
                                  linarith only [h1962, hlam, p1979_1]
                                · have p1979_0 := h1979c.1
                                  have p1979_1 := h1979c.2.1
                                  have p1979_2 := h1979c.2.2.1
                                  have p1979_3 := h1979c.2.2.2
                                  linarith only [h1798, h1966, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1979_1, u2elo1]
                                · have p1979_0 := h1979c.1
                                  have p1979_1 := h1979c.2.1
                                  have p1979_2 := h1979c.2.2.1
                                  have p1979_3 := h1979c.2.2.2
                                  linarith only [h1966, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1979_1, u2elo1]
                                · have p1979_0 := h1979c.1
                                  have p1979_1 := h1979c.2.1
                                  have p1979_2 := h1979c.2.2.1
                                  have p1979_3 := h1979c.2.2.2
                                  linarith only [hlam, p1979_0]
                                · have p1979_0 := h1979c.1
                                  have p1979_1 := h1979c.2.1
                                  have p1979_2 := h1979c.2.2.1
                                  have p1979_3 := h1979c.2.2.2
                                  linarith only [h1966, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1979_1, u2elo1]
                                · have p1979_0 := h1979c.1
                                  have p1979_1 := h1979c.2.1
                                  have p1979_2 := h1979c.2.2.1
                                  have p1979_3 := h1979c.2.2.2
                                  linarith only [h1969, hlam, p1979_1]
                                · have p1979_0 := h1979c.1
                                  have p1979_1 := h1979c.2.1
                                  have p1979_2 := h1979c.2.2.1
                                  have p1979_3 := h1979c.2.2.2
                                  linarith only [h1966, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1979_1, u2elo1]
                                · have p1979_0 := h1979c.1
                                  have p1979_1 := h1979c.2.1
                                  have p1979_2 := h1979c.2.2.1
                                  have p1979_3 := h1979c.2.2.2
                                  linarith only [h1949, hlam, p1979_1]
                                · have p1979_0 := h1979c.1
                                  have p1979_1 := h1979c.2.1
                                  have p1979_2 := h1979c.2.2.1
                                  have p1979_3 := h1979c.2.2.2
                                  linarith only [h1966, hlam, p1979_1]
                                · have p1979_0 := h1979c.1
                                  have p1979_1 := h1979c.2.1
                                  have p1979_2 := h1979c.2.2.1
                                  have p1979_3 := h1979c.2.2.2
                                  linarith only [hlam, p1979_0]
                                · have p1979_0 := h1979c.1
                                  have p1979_1 := h1979c.2.1
                                  have p1979_2 := h1979c.2.2.1
                                  have p1979_3 := h1979c.2.2.2
                                  linarith only [h1972, hlam, p1979_1]
                                · have p1979_0 := h1979c.1
                                  have p1979_1 := h1979c.2.1
                                  have p1979_2 := h1979c.2.2.1
                                  have p1979_3 := h1979c.2.2.2
                                  linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1979_1, u2elo4]
                                · have p1979_0 := h1979c.1
                                  have p1979_1 := h1979c.2.1
                                  have p1979_2 := h1979c.2.2.1
                                  have p1979_3 := h1979c.2.2.2
                                  linarith only [h1797, h1798, h1965, hc23, hc35, hlam, hphi, p1979_1]
                                · have p1979_0 := h1979c.1
                                  have p1979_1 := h1979c.2.1
                                  have p1979_2 := h1979c.2.2.1
                                  have p1979_3 := h1979c.2.2.2
                                  linarith only [h1797, h1798, h1965, hc23, hc35, hlam, hphi, p1979_1]
                                · have p1979_0 := h1979c.1
                                  have p1979_1 := h1979c.2.1
                                  have p1979_2 := h1979c.2.2.1
                                  have p1979_3 := h1979c.2.2.2
                                  linarith only [h1972, hc23, hc35, hlam, hphi, p1979_1]
                                · have p1979_0 := h1979c.1
                                  have p1979_1 := h1979c.2.1
                                  have p1979_2 := h1979c.2.2.1
                                  have p1979_3 := h1979c.2.2.2
                                  linarith only [hlam, p1979_0]
                                · have p1979_0 := h1979c.1
                                  have p1979_1 := h1979c.2.1
                                  have p1979_2 := h1979c.2.2.1
                                  have p1979_3 := h1979c.2.2.2
                                  rcases p1979_3 (m.d 0 5) (by simp) with h1999 | h1999
                                  · linarith only [h1962, h1999, hlam]
                                  · linarith only [h1964, h1999, hlam]
                                · have p1979_0 := h1979c.1
                                  have p1979_1 := h1979c.2.1
                                  have p1979_2 := h1979c.2.2.1
                                  have p1979_3 := h1979c.2.2.2
                                  linarith only [h1964, hlam, p1979_0]
                                · have p1979_0 := h1979c.1
                                  have p1979_1 := h1979c.2.1
                                  have p1979_2 := h1979c.2.2.1
                                  have p1979_3 := h1979c.2.2.2
                                  linarith only [h1971, hlam, p1979_0]
                                · have p1979_0 := h1979c.1
                                  have p1979_1 := h1979c.2.1
                                  have p1979_2 := h1979c.2.2.1
                                  have p1979_3 := h1979c.2.2.2
                                  linarith only [h1972, hc23, hc45, hlam, hphi, ht34, p1979_1]
                                · have p1979_0 := h1979c.1
                                  have p1979_1 := h1979c.2.1
                                  have p1979_2 := h1979c.2.2.1
                                  have p1979_3 := h1979c.2.2.2
                                  linarith only [h1974, hlam, p1979_0]
                                · have p1979_0 := h1979c.1
                                  have p1979_1 := h1979c.2.1
                                  have p1979_2 := h1979c.2.2.1
                                  have p1979_3 := h1979c.2.2.2
                                  linarith only [hlam, p1979_0]
                              · linarith only [h1798, h1966, h1975, hlam, ht01, ht12, u2elo1]
                            · linarith only [h1950, h1964, h1974, hlam]
                        · linarith only [h1797, h1798, h1950, h1964, h1965, h1971, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h1797, h1965, h1966, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                · linarith only [h0, h1797, h1965, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2012 | h2012
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2013 | h2013
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2014 | h2014
                    · linarith only [h1797, h1798, h2013, h2014, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2016 | h2016
                      · linarith only [h1797, h1798, h2013, h2016, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2018 | h2018
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2019 | h2019
                          · linarith only [h1798, h2016, h2019, hc01, hlam, hphi, ht12, u2elo2]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2021 | h2021
                            · rcases h0emin with h2022 | h2022 | h2022 | h2022 | h2022
                              · linarith only [h1798, h2013, h2022, hc12, hlam, ht01]
                              · linarith only [h2022, hlam, ht01, ht12, u2elo0]
                              · linarith only [h0, h1797, h2022, hlam, ht01, ht12, u2elo1]
                              · linarith only [h0, h1797, h1964, h2012, h2014, h2018, h2022, hc23, hc34, hlam, hphi, ht01, ht12, u2elo1]
                              · linarith only [h0, h1797, h1964, h2012, h2014, h2018, h2022, hc23, hc34, hlam, hphi, ht01, ht12, u2elo1]
                            · linarith only [h2014, h2018, h2021, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2029 | h2029
                          · linarith only [h1797, h1798, h2012, h2016, h2029, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2031 | h2031
                            · linarith only [h1797, h1798, h2012, h2018, h2031, hc23, hc34, hlam, hphi]
                            · rcases h0emin with h2033 | h2033 | h2033 | h2033 | h2033
                              · linarith only [h1798, h2013, h2033, hlam, ht01, ht12, u2elo1]
                              · linarith only [h0, h2033, hlam, ht01, ht12, u2elo1]
                              · linarith only [h1797, h1798, h1950, h2012, h2013, h2033, hc23, hc34, hlam, hphi, ht01, ht12, u2elo1]
                              · linarith only [h1797, h1798, h1950, h2012, h2013, h2031, h2033, hc23, hc45, hlam, hphi, ht01, ht12, ht34, u2elo1]
                              · linarith only [h1798, h2013, h2033, hlam, ht01, ht12, u2elo1]
                  · linarith only [h0, h1949, h2013, hlam]
                · linarith only [h0, h1797, h2012, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2041 | h2041
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2042 | h2042
            · linarith only [h1797, h1798, h2042, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2044 | h2044
              · linarith only [h0, h1797, h1949, h2041, h2044, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2046 | h2046
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2047 | h2047
                  · linarith only [h0, h1949, h2047, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h1797, h2046, h2047, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                · linarith only [h0, h2046, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2051 | h2051
            · linarith only [h0, h1797, h1949, h2051, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2053 | h2053
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2054 | h2054
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2055 | h2055
                  · linarith only [h0, h1797, h1949, h2054, h2055, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h0, h1797, h2054, h2055, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                · linarith only [h0, h1797, h2054, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2059 | h2059
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2060 | h2060
                  · linarith only [h1949, h2060, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h1797, h2059, h2060, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                · linarith only [h0, h1797, h2059, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
      · linarith only [h0, h1797, h1948, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2065 | h2065
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2066 | h2066
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2067 | h2067
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2068 | h2068
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2069 | h2069
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2070 | h2070
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2071 | h2071
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2072 | h2072
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2073 | h2073
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2074 | h2074
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2075 | h2075
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2076 | h2076
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2077 | h2077
                            · rcases h0emin with h2078 | h2078 | h2078 | h2078 | h2078
                              · linarith only [h1797, h2078, hc13, hlam, ht01]
                              · linarith only [h2078, hlam, ht01, ht12, u2elo0]
                              · linarith only [h2066, h2078, hlam, ht01, ht12, u2elo0]
                              · linarith only [h2066, h2068, h2078, hlam, ht01, ht12, u2elo0]
                              · linarith only [h1797, h2065, h2078, hc13, hlam, ht01]
                            · linarith only [h1797, h2065, h2071, h2075, h2077, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · linarith only [h1797, h2065, h2071, h2074, h2076, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2086 | h2086
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2087 | h2087
                            · linarith only [h2073, h2075, h2087, hlam]
                            · rcases h0emin with h2089 | h2089 | h2089 | h2089 | h2089
                              · linarith only [h1797, h2071, h2089, hlam, ht01, ht12, u2elo1]
                              · linarith only [h0, h2089, hlam, ht01, ht12, u2elo1]
                              · linarith only [h0, h2066, h2089, hlam, ht01, ht12, u2elo1]
                              · linarith only [h0, h2066, h2068, h2089, hlam, ht01, ht12, u2elo1]
                              · linarith only [h1797, h2065, h2071, h2089, hlam, ht01, ht12, u2elo1]
                          · linarith only [h1797, h2065, h2071, h2074, h2086, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h1797, h2066, h2069, h2074, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h1797, h2068, h2073, hlam]
                  · linarith only [h0, h2072, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h2065, h2071, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2100 | h2100
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2101 | h2101
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2102 | h2102
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2103 | h2103
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2104 | h2104
                        · linarith only [h0, h2065, h2068, h2070, h2104, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2106 | h2106
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2107 | h2107
                            · linarith only [h1797, h2065, h2100, h2102, h2104, h2107, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · rcases h0emin with h2109 | h2109 | h2109 | h2109 | h2109
                              · linarith only [h1797, h2100, h2109, hlam, ht01, ht12, u2elo1]
                              · linarith only [h0, h2109, hlam, ht01, ht12, u2elo1]
                              · linarith only [h0, h2066, h2109, hlam, ht01, ht12, u2elo1]
                              · linarith only [h1797, h2065, h2070, h2100, h2101, h2106, h2107, h2109, hc34, hc45, hlam, hphi, ht01, ht12, u2elo1]
                              · linarith only [h1797, h2065, h2100, h2109, hlam, ht01, ht12, u2elo1]
                          · linarith only [h1797, h2065, h2100, h2103, h2106, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h1797, h2066, h2069, h2103, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h1797, h2068, h2102, hlam]
                  · linarith only [h0, h2101, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h2065, h2100, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
            · linarith only [h1797, h2065, h2069, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2121 | h2121
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2122 | h2122
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2123 | h2123
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2124 | h2124
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2125 | h2125
                    · linarith only [h1797, h2065, h2068, h2123, h2124, h2125, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2127 | h2127
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2128 | h2128
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2129 | h2129
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2130 | h2130
                            · rcases h0emin with h2131 | h2131 | h2131 | h2131 | h2131
                              · linarith only [h0, h2131, hlam, ht01, ht12, u2elo1]
                              · linarith only [h0, h2131, hlam, ht01, ht12, u2elo1]
                              · linarith only [h1797, h2123, h2131, hlam, ht01, ht12, u2elo1]
                              · rcases h5bigk with h2135c | h2135c | h2135c | h2135c | h2135c | h2135c | h2135c | h2135c | h2135c | h2135c | h2135c | h2135c | h2135c | h2135c | h2135c | h2135c | h2135c | h2135c | h2135c | h2135c | h2135c | h2135c | h2135c | h2135c | h2135c
                                · have p2135_0 := h2135c.1
                                  have p2135_1 := h2135c.2.1
                                  have p2135_2 := h2135c.2.2.1
                                  have p2135_3 := h2135c.2.2.2
                                  linarith only [hlam, p2135_0]
                                · have p2135_0 := h2135c.1
                                  have p2135_1 := h2135c.2.1
                                  have p2135_2 := h2135c.2.2.1
                                  have p2135_3 := h2135c.2.2.2
                                  linarith only [h1797, h2065, h2123, h2124, h2129, h2130, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2135_1, u2elo1]
                                · have p2135_0 := h2135c.1
                                  have p2135_1 := h2135c.2.1
                                  have p2135_2 := h2135c.2.2.1
                                  have p2135_3 := h2135c.2.2.2
                                  linarith only [h1797, h2065, h2123, h2129, h2130, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2135_1, u2elo1]
                                · have p2135_0 := h2135c.1
                                  have p2135_1 := h2135c.2.1
                                  have p2135_2 := h2135c.2.2.1
                                  have p2135_3 := h2135c.2.2.2
                                  linarith only [h1797, h2065, h2123, h2130, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2135_1, u2elo1]
                                · have p2135_0 := h2135c.1
                                  have p2135_1 := h2135c.2.1
                                  have p2135_2 := h2135c.2.2.1
                                  have p2135_3 := h2135c.2.2.2
                                  linarith only [h1797, h2065, h2123, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2135_1, u2elo1]
                                · have p2135_0 := h2135c.1
                                  have p2135_1 := h2135c.2.1
                                  have p2135_2 := h2135c.2.2.1
                                  have p2135_3 := h2135c.2.2.2
                                  linarith only [h2065, hlam, p2135_0]
                                · have p2135_0 := h2135c.1
                                  have p2135_1 := h2135c.2.1
                                  have p2135_2 := h2135c.2.2.1
                                  have p2135_3 := h2135c.2.2.2
                                  linarith only [hlam, p2135_0]
                                · have p2135_0 := h2135c.1
                                  have p2135_1 := h2135c.2.1
                                  have p2135_2 := h2135c.2.2.1
                                  have p2135_3 := h2135c.2.2.2
                                  linarith only [h1797, h2065, h2123, h2129, h2130, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2135_1, u2elo1]
                                · have p2135_0 := h2135c.1
                                  have p2135_1 := h2135c.2.1
                                  have p2135_2 := h2135c.2.2.1
                                  have p2135_3 := h2135c.2.2.2
                                  linarith only [h1797, h2065, h2123, h2130, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2135_1, u2elo1]
                                · have p2135_0 := h2135c.1
                                  have p2135_1 := h2135c.2.1
                                  have p2135_2 := h2135c.2.2.1
                                  have p2135_3 := h2135c.2.2.2
                                  linarith only [h1797, h2065, h2123, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2135_1, u2elo1]
                                · have p2135_0 := h2135c.1
                                  have p2135_1 := h2135c.2.1
                                  have p2135_2 := h2135c.2.2.1
                                  have p2135_3 := h2135c.2.2.2
                                  linarith only [h2067, hlam, p2135_1]
                                · have p2135_0 := h2135c.1
                                  have p2135_1 := h2135c.2.1
                                  have p2135_2 := h2135c.2.2.1
                                  have p2135_3 := h2135c.2.2.2
                                  linarith only [h2124, hlam, p2135_1]
                                · have p2135_0 := h2135c.1
                                  have p2135_1 := h2135c.2.1
                                  have p2135_2 := h2135c.2.2.1
                                  have p2135_3 := h2135c.2.2.2
                                  linarith only [hlam, p2135_0]
                                · have p2135_0 := h2135c.1
                                  have p2135_1 := h2135c.2.1
                                  have p2135_2 := h2135c.2.2.1
                                  have p2135_3 := h2135c.2.2.2
                                  linarith only [h2130, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2135_1, u2elo4]
                                · have p2135_0 := h2135c.1
                                  have p2135_1 := h2135c.2.1
                                  have p2135_2 := h2135c.2.2.1
                                  have p2135_3 := h2135c.2.2.2
                                  linarith only [h1797, h2065, h2123, h2124, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2135_1, u2elo1]
                                · have p2135_0 := h2135c.1
                                  have p2135_1 := h2135c.2.1
                                  have p2135_2 := h2135c.2.2.1
                                  have p2135_3 := h2135c.2.2.2
                                  linarith only [h2121, hlam, p2135_0]
                                · have p2135_0 := h2135c.1
                                  have p2135_1 := h2135c.2.1
                                  have p2135_2 := h2135c.2.2.1
                                  have p2135_3 := h2135c.2.2.2
                                  linarith only [h2127, hlam, p2135_0]
                                · have p2135_0 := h2135c.1
                                  have p2135_1 := h2135c.2.1
                                  have p2135_2 := h2135c.2.2.1
                                  have p2135_3 := h2135c.2.2.2
                                  linarith only [h2129, hlam, p2135_0]
                                · have p2135_0 := h2135c.1
                                  have p2135_1 := h2135c.2.1
                                  have p2135_2 := h2135c.2.2.1
                                  have p2135_3 := h2135c.2.2.2
                                  linarith only [hlam, p2135_0]
                                · have p2135_0 := h2135c.1
                                  have p2135_1 := h2135c.2.1
                                  have p2135_2 := h2135c.2.2.1
                                  have p2135_3 := h2135c.2.2.2
                                  linarith only [h1797, h2121, h2123, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2135_1, u2elo1]
                                · have p2135_0 := h2135c.1
                                  have p2135_1 := h2135c.2.1
                                  have p2135_2 := h2135c.2.2.1
                                  have p2135_3 := h2135c.2.2.2
                                  linarith only [h2122, hlam, p2135_0]
                                · have p2135_0 := h2135c.1
                                  have p2135_1 := h2135c.2.1
                                  have p2135_2 := h2135c.2.2.1
                                  have p2135_3 := h2135c.2.2.2
                                  linarith only [h2128, hlam, p2135_0]
                                · have p2135_0 := h2135c.1
                                  have p2135_1 := h2135c.2.1
                                  have p2135_2 := h2135c.2.2.1
                                  have p2135_3 := h2135c.2.2.2
                                  linarith only [h2122, hc04, hc25, hlam, hphi, ht0b, ht5b, p2135_1]
                                · have p2135_0 := h2135c.1
                                  have p2135_1 := h2135c.2.1
                                  have p2135_2 := h2135c.2.2.1
                                  have p2135_3 := h2135c.2.2.2
                                  linarith only [h2130, hlam, p2135_0]
                                · have p2135_0 := h2135c.1
                                  have p2135_1 := h2135c.2.1
                                  have p2135_2 := h2135c.2.2.1
                                  have p2135_3 := h2135c.2.2.2
                                  linarith only [hlam, p2135_0]
                              · linarith only [h1797, h2065, h2123, h2131, hc12, hlam, ht01]
                            · linarith only [h1797, h2065, h2125, h2128, h2130, hlam]
                          · linarith only [h1797, h2121, h2125, h2129, hc23, hc34, hlam, hphi]
                        · linarith only [h1797, h2065, h2122, h2124, h2125, h2128, hc04, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h1797, h2121, h2127, hlam]
                  · linarith only [h1797, h2123, h2124, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h2065, h2123, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
              · linarith only [h1797, h2065, h2068, h2122, hlam]
            · linarith only [h1797, h2065, h2121, hlam]
        · linarith only [h0, h2065, h2067, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2171 | h2171
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2172 | h2172
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2173 | h2173
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2174 | h2174
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2175 | h2175
                · linarith only [h0, h2066, h2175, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h2065, h2175, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2178 | h2178
                · linarith only [h0, h2065, h2066, h2178, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                · linarith only [h0, h2065, h2178, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
            · linarith only [h0, h2065, h2066, h2173, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2182 | h2182
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2183 | h2183
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2184 | h2184
                · linarith only [h0, h2065, h2066, h2184, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                · linarith only [h0, h2065, h2184, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
              · linarith only [h0, h2065, h2066, h2172, h2183, hlam]
            · linarith only [h0, h2065, h2066, h2182, hlam]
        · linarith only [h0, h2065, h2171, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2190 | h2190
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2191 | h2191
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2192 | h2192
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2193 | h2193
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2194 | h2194
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2195 | h2195
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2196 | h2196
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2197 | h2197
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2198 | h2198
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2199 | h2199
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2200 | h2200
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2201 | h2201
                            · rcases h0emin with h2202 | h2202 | h2202 | h2202 | h2202
                              · linarith only [h2065, h2195, h2197, h2199, h2202, hlam, ht01, ht12, u2elo1]
                              · linarith only [h2202, hlam, ht01, ht12, u2elo0]
                              · linarith only [h1797, h2195, h2202, hlam, ht01, ht12, u2elo1]
                              · linarith only [h1797, h2192, h2195, h2202, hlam, ht01, ht12, u2elo1]
                              · linarith only [h1797, h2192, h2194, h2195, h2202, hlam, ht01, ht12, u2elo1]
                            · rcases h0emin with h2208 | h2208 | h2208 | h2208 | h2208
                              · linarith only [h2065, h2195, h2197, h2199, h2208, hlam, ht01, ht12, u2elo1]
                              · linarith only [h0, h2208, hlam, ht01, ht12, u2elo1]
                              · linarith only [h1797, h2195, h2208, hlam, ht01, ht12, u2elo1]
                              · linarith only [h1797, h2192, h2195, h2208, hlam, ht01, ht12, u2elo1]
                              · linarith only [h1797, h2192, h2194, h2195, h2208, hlam, ht01, ht12, u2elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2214 | h2214
                            · rcases h0emin with h2215 | h2215 | h2215 | h2215 | h2215
                              · linarith only [h2065, h2195, h2197, h2199, h2215, hlam, ht01, ht12, u2elo1]
                              · linarith only [h0, h2215, hlam, ht01, ht12, u2elo1]
                              · linarith only [h1797, h2195, h2215, hlam, ht01, ht12, u2elo1]
                              · linarith only [h1797, h2192, h2195, h2215, hlam, ht01, ht12, u2elo1]
                              · linarith only [h1797, h2192, h2194, h2195, h2215, hlam, ht01, ht12, u2elo1]
                            · rcases h0emin with h2221 | h2221 | h2221 | h2221 | h2221
                              · linarith only [h2065, h2195, h2197, h2199, h2221, hlam, ht01, ht12, u2elo1]
                              · linarith only [h0, h2221, hlam, ht01, ht12, u2elo1]
                              · linarith only [h1797, h2195, h2221, hlam, ht01, ht12, u2elo1]
                              · linarith only [h1797, h2192, h2195, h2221, hlam, ht01, ht12, u2elo1]
                              · linarith only [h1797, h2192, h2194, h2195, h2221, hlam, ht01, ht12, u2elo1]
                        · linarith only [h1797, h2065, h2192, h2194, h2195, h2199, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h1797, h2193, h2198, hlam]
                    · linarith only [h1797, h2192, h2197, hlam]
                  · linarith only [h0, h2196, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h2195, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2232 | h2232
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2233 | h2233
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2234 | h2234
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2235 | h2235
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2236 | h2236
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2237 | h2237
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2238 | h2238
                            · linarith only [h2192, h2194, h2238, hlam]
                            · rcases h0emin with h2240 | h2240 | h2240 | h2240 | h2240
                              · linarith only [h2065, h2240, hc15, hlam, ht01]
                              · linarith only [h2240, hlam, ht01, ht12, u2elo0]
                              · linarith only [h0, h2190, h2240, hlam, ht01, ht12, u2elo1]
                              · linarith only [h2194, h2236, h2240, hc14, hlam, ht01]
                              · linarith only [h2194, h2236, h2240, hc14, hlam, ht01]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2246 | h2246
                            · linarith only [h0, h2190, h2192, h2193, h2194, h2237, h2246, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · rcases h0emin with h2248 | h2248 | h2248 | h2248 | h2248
                              · linarith only [h0, h2248, hlam, ht01, ht12, u2elo1]
                              · linarith only [h0, h2248, hlam, ht01, ht12, u2elo1]
                              · linarith only [h0, h2190, h2248, hlam, ht01, ht12, u2elo1]
                              · linarith only [h2194, h2248, hc45, hlam, ht01, ht12, ht23, ht34]
                              · linarith only [h0, h2191, h2248, hlam, ht01, ht12, u2elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2254 | h2254
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2255 | h2255
                            · linarith only [h0, h2190, h2192, h2194, h2255, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · rcases h0emin with h2257 | h2257 | h2257 | h2257 | h2257
                              · linarith only [h2065, h2257, hc15, hlam, ht01]
                              · linarith only [h0, h2257, hlam, ht01, ht12, u2elo1]
                              · linarith only [h0, h2190, h2257, hlam, ht01, ht12, u2elo1]
                              · linarith only [h0, h2190, h2192, h2257, hlam, ht01, ht12, u2elo1]
                              · linarith only [h0, h2190, h2193, h2257, hlam, ht01, ht12, u2elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2263 | h2263
                            · linarith only [h0, h2190, h2192, h2236, h2263, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · rcases h0emin with h2265 | h2265 | h2265 | h2265 | h2265
                              · linarith only [h2065, h2232, h2235, h2265, hlam, ht01, ht12, u2elo1]
                              · linarith only [h0, h2265, hlam, ht01, ht12, u2elo1]
                              · linarith only [h0, h2190, h2265, hlam, ht01, ht12, u2elo1]
                              · linarith only [h0, h2190, h2192, h2265, hlam, ht01, ht12, u2elo1]
                              · linarith only [h0, h2190, h2193, h2265, hlam, ht01, ht12, u2elo1]
                      · linarith only [h0, h1797, h2190, h2193, h2235, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h1797, h2192, h2234, hlam]
                  · linarith only [h0, h2233, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h2232, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2275 | h2275
              · linarith only [h2192, h2193, h2275, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2277 | h2277
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2278 | h2278
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2279 | h2279
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2280 | h2280
                      · linarith only [h2192, h2193, h2277, h2280, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2282 | h2282
                        · linarith only [h2279, h2280, h2282, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2284 | h2284
                          · linarith only [h2190, h2280, h2284, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2286 | h2286
                            · linarith only [h1797, h2192, h2280, h2282, h2286, hlam]
                            · rcases h0emin with h2288 | h2288 | h2288 | h2288 | h2288
                              · linarith only [h1797, h2288, hc13, hlam, ht01]
                              · linarith only [h0, h2288, hlam, ht01, ht12, u2elo1]
                              · linarith only [h1797, h2280, h2286, h2288, hc45, hlam, ht01, ht12, ht23, ht34]
                              · linarith only [h1797, h2192, h2280, h2286, h2288, hc45, hlam, ht01, ht12, ht23, ht34]
                              · linarith only [h0, h2191, h2288, hlam, ht01, ht12, u2elo1]
                    · linarith only [h1797, h2192, h2279, hlam]
                  · linarith only [h0, h2191, h2278, hlam]
                · linarith only [h0, h2277, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2297 | h2297
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2298 | h2298
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2299 | h2299
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2300 | h2300
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2301 | h2301
                    · linarith only [h2192, h2297, h2299, h2301, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2303 | h2303
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2304 | h2304
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2305 | h2305
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2306 | h2306
                            · rcases h0emin with h2307 | h2307 | h2307 | h2307 | h2307
                              · linarith only [h0, h2307, hlam, ht01, ht12, u2elo1]
                              · linarith only [h0, h2307, hlam, ht01, ht12, u2elo1]
                              · linarith only [h1797, h2299, h2307, hlam, ht01, ht12, u2elo1]
                              · rcases h5bigk with h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c | h2311c
                                · have p2311_0 := h2311c.1
                                  have p2311_1 := h2311c.2.1
                                  have p2311_2 := h2311c.2.2.1
                                  have p2311_3 := h2311c.2.2.2
                                  linarith only [hlam, p2311_0]
                                · have p2311_0 := h2311c.1
                                  have p2311_1 := h2311c.2.1
                                  have p2311_2 := h2311c.2.2.1
                                  have p2311_3 := h2311c.2.2.2
                                  linarith only [h2065, hlam, p2311_1]
                                · have p2311_0 := h2311c.1
                                  have p2311_1 := h2311c.2.1
                                  have p2311_2 := h2311c.2.2.1
                                  have p2311_3 := h2311c.2.2.2
                                  linarith only [h1797, h2297, h2299, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p2311_1, u2elo1]
                                · have p2311_0 := h2311c.1
                                  have p2311_1 := h2311c.2.1
                                  have p2311_2 := h2311c.2.2.1
                                  have p2311_3 := h2311c.2.2.2
                                  linarith only [h1797, h2297, h2299, h2306, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2311_1, u2elo1]
                                · have p2311_0 := h2311c.1
                                  have p2311_1 := h2311c.2.1
                                  have p2311_2 := h2311c.2.2.1
                                  have p2311_3 := h2311c.2.2.2
                                  linarith only [h1797, h2297, h2299, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2311_1, u2elo1]
                                · have p2311_0 := h2311c.1
                                  have p2311_1 := h2311c.2.1
                                  have p2311_2 := h2311c.2.2.1
                                  have p2311_3 := h2311c.2.2.2
                                  linarith only [h2299, h2303, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2311_1, u2elo1]
                                · have p2311_0 := h2311c.1
                                  have p2311_1 := h2311c.2.1
                                  have p2311_2 := h2311c.2.2.1
                                  have p2311_3 := h2311c.2.2.2
                                  linarith only [hlam, p2311_0]
                                · have p2311_0 := h2311c.1
                                  have p2311_1 := h2311c.2.1
                                  have p2311_2 := h2311c.2.2.1
                                  have p2311_3 := h2311c.2.2.2
                                  linarith only [h2299, h2303, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p2311_1, u2elo1]
                                · have p2311_0 := h2311c.1
                                  have p2311_1 := h2311c.2.1
                                  have p2311_2 := h2311c.2.2.1
                                  have p2311_3 := h2311c.2.2.2
                                  linarith only [h2299, h2303, h2306, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2311_1, u2elo1]
                                · have p2311_0 := h2311c.1
                                  have p2311_1 := h2311c.2.1
                                  have p2311_2 := h2311c.2.2.1
                                  have p2311_3 := h2311c.2.2.2
                                  linarith only [h2299, h2303, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2311_1, u2elo1]
                                · have p2311_0 := h2311c.1
                                  have p2311_1 := h2311c.2.1
                                  have p2311_2 := h2311c.2.2.1
                                  have p2311_3 := h2311c.2.2.2
                                  linarith only [h2191, hlam, p2311_1]
                                · have p2311_0 := h2311c.1
                                  have p2311_1 := h2311c.2.1
                                  have p2311_2 := h2311c.2.2.1
                                  have p2311_3 := h2311c.2.2.2
                                  linarith only [h2300, hlam, p2311_1]
                                · have p2311_0 := h2311c.1
                                  have p2311_1 := h2311c.2.1
                                  have p2311_2 := h2311c.2.2.1
                                  have p2311_3 := h2311c.2.2.2
                                  linarith only [hlam, p2311_0]
                                · have p2311_0 := h2311c.1
                                  have p2311_1 := h2311c.2.1
                                  have p2311_2 := h2311c.2.2.1
                                  have p2311_3 := h2311c.2.2.2
                                  linarith only [h2306, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2311_1, u2elo4]
                                · have p2311_0 := h2311c.1
                                  have p2311_1 := h2311c.2.1
                                  have p2311_2 := h2311c.2.2.1
                                  have p2311_3 := h2311c.2.2.2
                                  linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2311_1, u2elo4]
                                · have p2311_0 := h2311c.1
                                  have p2311_1 := h2311c.2.1
                                  have p2311_2 := h2311c.2.2.1
                                  have p2311_3 := h2311c.2.2.2
                                  linarith only [h2297, hlam, p2311_0]
                                · have p2311_0 := h2311c.1
                                  have p2311_1 := h2311c.2.1
                                  have p2311_2 := h2311c.2.2.1
                                  have p2311_3 := h2311c.2.2.2
                                  linarith only [h2303, hlam, p2311_0]
                                · have p2311_0 := h2311c.1
                                  have p2311_1 := h2311c.2.1
                                  have p2311_2 := h2311c.2.2.1
                                  have p2311_3 := h2311c.2.2.2
                                  linarith only [h2305, hlam, p2311_0]
                                · have p2311_0 := h2311c.1
                                  have p2311_1 := h2311c.2.1
                                  have p2311_2 := h2311c.2.2.1
                                  have p2311_3 := h2311c.2.2.2
                                  linarith only [hlam, p2311_0]
                                · have p2311_0 := h2311c.1
                                  have p2311_1 := h2311c.2.1
                                  have p2311_2 := h2311c.2.2.1
                                  have p2311_3 := h2311c.2.2.2
                                  linarith only [h1797, h2297, h2299, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2311_1, u2elo1]
                                · have p2311_0 := h2311c.1
                                  have p2311_1 := h2311c.2.1
                                  have p2311_2 := h2311c.2.2.1
                                  have p2311_3 := h2311c.2.2.2
                                  linarith only [h2298, hlam, p2311_0]
                                · have p2311_0 := h2311c.1
                                  have p2311_1 := h2311c.2.1
                                  have p2311_2 := h2311c.2.2.1
                                  have p2311_3 := h2311c.2.2.2
                                  linarith only [h2304, hlam, p2311_0]
                                · have p2311_0 := h2311c.1
                                  have p2311_1 := h2311c.2.1
                                  have p2311_2 := h2311c.2.2.1
                                  have p2311_3 := h2311c.2.2.2
                                  linarith only [h2298, hc04, hc25, hlam, hphi, ht0b, ht5b, p2311_1]
                                · have p2311_0 := h2311c.1
                                  have p2311_1 := h2311c.2.1
                                  have p2311_2 := h2311c.2.2.1
                                  have p2311_3 := h2311c.2.2.2
                                  linarith only [h2306, hlam, p2311_0]
                                · have p2311_0 := h2311c.1
                                  have p2311_1 := h2311c.2.1
                                  have p2311_2 := h2311c.2.2.1
                                  have p2311_3 := h2311c.2.2.2
                                  linarith only [hlam, p2311_0]
                              · linarith only [h2065, h2299, h2303, h2307, hlam, ht01, ht12, u2elo1]
                            · linarith only [h1797, h2065, h2192, h2298, h2299, h2303, h2306, hc01, hlam, hphi, ht12, u2elo1]
                          · linarith only [h1797, h2297, h2301, h2305, hc23, hc34, hlam, hphi]
                        · linarith only [h2065, h2298, h2301, h2303, h2304, hlam]
                      · linarith only [h1797, h2297, h2303, hlam]
                  · linarith only [h0, h2300, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h2299, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h2192, h2297, h2298, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2345 | h2345
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2346 | h2346
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2347 | h2347
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2348 | h2348
                    · linarith only [h1797, h2192, h2346, h2348, hc01, hlam, hphi, ht12, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2350 | h2350
                      · linarith only [h2297, h2348, h2350, hc03, hc34, hlam, hphi]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2352 | h2352
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2353 | h2353
                          · linarith only [h2190, h2350, h2353, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2355 | h2355
                            · rcases h0emin with h2356 | h2356 | h2356 | h2356 | h2356
                              · linarith only [h1797, h2356, hc13, hlam, ht01]
                              · linarith only [h0, h2356, hlam, ht01, ht12, u2elo1]
                              · linarith only [h1797, h2350, h2355, h2356, hc34, hlam, ht01, ht12, ht23]
                              · rcases h5bigk with h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c | h2360c
                                · have p2360_0 := h2360c.1
                                  have p2360_1 := h2360c.2.1
                                  have p2360_2 := h2360c.2.2.1
                                  have p2360_3 := h2360c.2.2.2
                                  linarith only [hlam, p2360_0]
                                · have p2360_0 := h2360c.1
                                  have p2360_1 := h2360c.2.1
                                  have p2360_2 := h2360c.2.2.1
                                  have p2360_3 := h2360c.2.2.2
                                  linarith only [h2065, hlam, p2360_1]
                                · have p2360_0 := h2360c.1
                                  have p2360_1 := h2360c.2.1
                                  have p2360_2 := h2360c.2.2.1
                                  have p2360_3 := h2360c.2.2.2
                                  linarith only [h2065, h2347, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p2360_1, u2elo1]
                                · have p2360_0 := h2360c.1
                                  have p2360_1 := h2360c.2.1
                                  have p2360_2 := h2360c.2.2.1
                                  have p2360_3 := h2360c.2.2.2
                                  linarith only [h2297, hlam, p2360_1]
                                · have p2360_0 := h2360c.1
                                  have p2360_1 := h2360c.2.1
                                  have p2360_2 := h2360c.2.2.1
                                  have p2360_3 := h2360c.2.2.2
                                  linarith only [h2065, h2347, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2360_1, u2elo1]
                                · have p2360_0 := h2360c.1
                                  have p2360_1 := h2360c.2.1
                                  have p2360_2 := h2360c.2.2.1
                                  have p2360_3 := h2360c.2.2.2
                                  linarith only [h2347, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2360_1, u2elo1]
                                · have p2360_0 := h2360c.1
                                  have p2360_1 := h2360c.2.1
                                  have p2360_2 := h2360c.2.2.1
                                  have p2360_3 := h2360c.2.2.2
                                  linarith only [hlam, p2360_0]
                                · have p2360_0 := h2360c.1
                                  have p2360_1 := h2360c.2.1
                                  have p2360_2 := h2360c.2.2.1
                                  have p2360_3 := h2360c.2.2.2
                                  linarith only [h2347, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p2360_1, u2elo1]
                                · have p2360_0 := h2360c.1
                                  have p2360_1 := h2360c.2.1
                                  have p2360_2 := h2360c.2.2.1
                                  have p2360_3 := h2360c.2.2.2
                                  linarith only [h2350, hlam, p2360_1]
                                · have p2360_0 := h2360c.1
                                  have p2360_1 := h2360c.2.1
                                  have p2360_2 := h2360c.2.2.1
                                  have p2360_3 := h2360c.2.2.2
                                  linarith only [h2347, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2360_1, u2elo1]
                                · have p2360_0 := h2360c.1
                                  have p2360_1 := h2360c.2.1
                                  have p2360_2 := h2360c.2.2.1
                                  have p2360_3 := h2360c.2.2.2
                                  linarith only [h2191, hlam, p2360_1]
                                · have p2360_0 := h2360c.1
                                  have p2360_1 := h2360c.2.1
                                  have p2360_2 := h2360c.2.2.1
                                  have p2360_3 := h2360c.2.2.2
                                  linarith only [h2347, hlam, p2360_1]
                                · have p2360_0 := h2360c.1
                                  have p2360_1 := h2360c.2.1
                                  have p2360_2 := h2360c.2.2.1
                                  have p2360_3 := h2360c.2.2.2
                                  linarith only [hlam, p2360_0]
                                · have p2360_0 := h2360c.1
                                  have p2360_1 := h2360c.2.1
                                  have p2360_2 := h2360c.2.2.1
                                  have p2360_3 := h2360c.2.2.2
                                  linarith only [h2353, hlam, p2360_1]
                                · have p2360_0 := h2360c.1
                                  have p2360_1 := h2360c.2.1
                                  have p2360_2 := h2360c.2.2.1
                                  have p2360_3 := h2360c.2.2.2
                                  linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2360_1, u2elo4]
                                · have p2360_0 := h2360c.1
                                  have p2360_1 := h2360c.2.1
                                  have p2360_2 := h2360c.2.2.1
                                  have p2360_3 := h2360c.2.2.2
                                  linarith only [h1797, h2297, h2355, hc01, hc34, hlam, hphi, ht12, ht23, p2360_1]
                                · have p2360_0 := h2360c.1
                                  have p2360_1 := h2360c.2.1
                                  have p2360_2 := h2360c.2.2.1
                                  have p2360_3 := h2360c.2.2.2
                                  linarith only [h2065, h2355, hc01, hc34, hlam, hphi, ht12, ht23, p2360_1]
                                · have p2360_0 := h2360c.1
                                  have p2360_1 := h2360c.2.1
                                  have p2360_2 := h2360c.2.2.1
                                  have p2360_3 := h2360c.2.2.2
                                  linarith only [h2353, h2355, hc23, hc34, hlam, hphi, p2360_1]
                                · have p2360_0 := h2360c.1
                                  have p2360_1 := h2360c.2.1
                                  have p2360_2 := h2360c.2.2.1
                                  have p2360_3 := h2360c.2.2.2
                                  linarith only [hlam, p2360_0]
                                · have p2360_0 := h2360c.1
                                  have p2360_1 := h2360c.2.1
                                  have p2360_2 := h2360c.2.2.1
                                  have p2360_3 := h2360c.2.2.2
                                  rcases p2360_3 (m.d 0 5) (by simp) with h2380 | h2380
                                  · linarith only [h2297, h2380, hlam]
                                  · linarith only [h2345, h2380, hlam]
                                · have p2360_0 := h2360c.1
                                  have p2360_1 := h2360c.2.1
                                  have p2360_2 := h2360c.2.2.1
                                  have p2360_3 := h2360c.2.2.2
                                  linarith only [h2345, hlam, p2360_0]
                                · have p2360_0 := h2360c.1
                                  have p2360_1 := h2360c.2.1
                                  have p2360_2 := h2360c.2.2.1
                                  have p2360_3 := h2360c.2.2.2
                                  linarith only [h2352, hlam, p2360_0]
                                · have p2360_0 := h2360c.1
                                  have p2360_1 := h2360c.2.1
                                  have p2360_2 := h2360c.2.2.1
                                  have p2360_3 := h2360c.2.2.2
                                  linarith only [h2353, hc23, hc45, hlam, hphi, ht34, p2360_1]
                                · have p2360_0 := h2360c.1
                                  have p2360_1 := h2360c.2.1
                                  have p2360_2 := h2360c.2.2.1
                                  have p2360_3 := h2360c.2.2.2
                                  linarith only [h2355, hlam, p2360_0]
                                · have p2360_0 := h2360c.1
                                  have p2360_1 := h2360c.2.1
                                  have p2360_2 := h2360c.2.2.1
                                  have p2360_3 := h2360c.2.2.2
                                  linarith only [hlam, p2360_0]
                              · linarith only [h0, h2191, h2356, hlam, ht01, ht12, u2elo1]
                            · linarith only [h0, h1797, h2191, h2192, h2345, h2355, hc01, hlam, hphi, ht12, u2elo1]
                        · linarith only [h1797, h2192, h2345, h2348, h2352, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h2347, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h2346, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2393 | h2393
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2394 | h2394
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2395 | h2395
                    · linarith only [h1797, h2192, h2393, h2395, hc01, hlam, hphi, ht12, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2397 | h2397
                      · linarith only [h1797, h2297, h2395, h2397, hc01, hc34, hlam, hphi, ht12, ht23]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2399 | h2399
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2400 | h2400
                          · linarith only [h1797, h2397, h2400, hc01, hlam, hphi, ht12, u2elo2]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2402 | h2402
                            · rcases h0emin with h2403 | h2403 | h2403 | h2403 | h2403
                              · linarith only [h1797, h2403, hc13, hlam, ht01]
                              · linarith only [h0, h2403, hlam, ht01, ht12, u2elo1]
                              · linarith only [h2192, h2345, h2395, h2399, h2403, hc34, hlam, ht01, ht12, ht23]
                              · linarith only [h2345, h2395, h2399, h2403, hc34, hlam, ht01, ht12, ht23]
                              · linarith only [h2345, h2395, h2399, h2403, hc34, hlam, ht01, ht12, ht23]
                            · linarith only [h2395, h2399, h2402, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2410 | h2410
                          · linarith only [h0, h2190, h2297, h2410, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2412 | h2412
                            · linarith only [h1797, h2395, h2399, h2412, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h1797, h2395, h2412, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h0, h2191, h2394, hlam]
                · linarith only [h0, h2393, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2417 | h2417
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2418 | h2418
            · linarith only [h2190, h2191, h2418, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2420 | h2420
              · linarith only [h2190, h2191, h2417, h2420, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2422 | h2422
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2423 | h2423
                  · linarith only [h2190, h2191, h2423, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h0, h2423, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h2422, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2427 | h2427
            · linarith only [h2190, h2191, h2427, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2429 | h2429
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2430 | h2430
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2431 | h2431
                  · linarith only [h2191, h2431, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h2431, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h2430, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2435 | h2435
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2436 | h2436
                  · linarith only [h2191, h2436, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h2436, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h2435, hc01, hlam, hphi, ht12, u2elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2440 | h2440
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2441 | h2441
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2442 | h2442
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2443 | h2443
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2444 | h2444
                · linarith only [h2190, h2444, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h2444, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2447 | h2447
                · linarith only [h2190, h2440, h2447, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                · linarith only [h0, h2447, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h2190, h2440, h2442, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2451 | h2451
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2452 | h2452
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2453 | h2453
                · linarith only [h2190, h2453, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h2453, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h2190, h2440, h2441, h2452, hlam]
            · linarith only [h2190, h2440, h2451, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2458 | h2458
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2459 | h2459
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2460 | h2460
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2461 | h2461
                · linarith only [h0, h2190, h2461, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h2461, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2464 | h2464
                · linarith only [h0, h2190, h2464, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h2464, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2467 | h2467
              · linarith only [h2458, h2459, h2467, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2469 | h2469
                · linarith only [h0, h2190, h2469, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h2469, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2472 | h2472
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2473 | h2473
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2474 | h2474
                · linarith only [h0, h2190, h2474, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h2474, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h2458, h2472, h2473, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2478 | h2478
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2479 | h2479
                · linarith only [h0, h2190, h2479, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h2479, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2482 | h2482
                · linarith only [h0, h2190, h2482, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h2482, hc01, hlam, hphi, ht12, u2elo2]

set_option maxHeartbeats 4970000 in
theorem r1l7_10_12_25_L_I_L_0_H_I (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_12_25_L_I_L_0_H_I_x0 m hb0 hb2 hb5 h0
  · exact r1l7_10_12_25_L_I_L_0_H_I_x1 m hb0 hb2 hb5 h0

end R2N4
